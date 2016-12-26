#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/ip_icmp.h>
#include <netinet/ip_var.h>
#include <arpa/inet.h>
#include <ctype.h>
#include <err.h>
#include <errno.h>
#include <math.h>
#include <netdb.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <termios.h>
#include <netinet/in.h>
#include <time.h>
#include <unistd.h>


#define DEBUG 1
#define BUFSIZE 65535
#include <sys/tree.h>

static long version=0;
int fd;
FILE *logfile;

void lowstr(char* text);

uint16_t in_cksum(uint16_t *addr, int len) {
    int nleft = len;
    int sum = 0;
    uint16_t *w = addr;
    uint16_t answer = 0;

    while (nleft > 1) {
        sum += *w++;
        nleft -= 2;
    }

    if (nleft == 1) {
        *(uint8_t *) (&answer) = *(uint8_t *) w;
        sum += answer;
    }
    sum = (sum >> 16) + (sum & 0xFFFF);
    sum += (sum >> 16);
    answer = ~sum;
    return (answer);
}
struct psd_tcp {
    struct in_addr src;
    struct in_addr dst;
    unsigned char pad;
    unsigned char proto;
    unsigned short tcp_len;
    struct tcphdr tcp;
};
unsigned short in_cksum_tcp(int src, int dst, unsigned short *addr, int len) {
    struct psd_tcp *buf=alloca(len+sizeof(struct psd_tcp));
    u_short ans;
    memset(buf, 0, len);
    buf->src.s_addr = src;
    buf->dst.s_addr = dst;
    buf->pad = 0;
    buf->proto = IPPROTO_TCP;
    buf->tcp_len = htons(len);
    memcpy(&(buf->tcp), addr, len);
    ans = in_cksum((unsigned short *)buf, 12 + len);
    return (ans);
}

struct session {
    //This is key
    uint32_t src_ip;
    uint32_t dst_ip;
    uint16_t src_port;
    uint16_t dst_port;
    //Attributes
    uint64_t seq;
    uint16_t buflen;
    uint16_t datalen;
    uint8_t clear;
    uint8_t dnt;
    struct timespec lastread;
    char *buffer;
    char allowed;
    RB_ENTRY(session) links;
};
RB_HEAD(sessions_tree, session) sessions;

int session_cmp(struct session *left, struct session *right){
    return memcmp(left,right,12);
};
RB_GENERATE(sessions_tree, session, links, session_cmp );

int quote(char* s1, char* s2){
    char *op=s2;
    while((*s1) != 0){
        if((unsigned char)(*s1)>=127){
            op+=sprintf(op,"%%%02x",(unsigned char)(*s1));
        }else{
            (*op++)=(*s1);
        }
        s1++;
    }
    (*op)=0;
    return op-s2;
};

struct url {
    int id;
    long version;
    TAILQ_ENTRY(url) entries;
    int params;
    char pathname[];
};

struct hostname {
    TAILQ_HEAD(hosturls,url) urls;
    struct url any;
    RB_ENTRY(hostname) links;
    char hostname[];
};
RB_HEAD(host_tree, hostname) hosts;

int host_cmp(struct hostname *left, struct hostname *right){
    return strcmp(left->hostname,right->hostname);
};
RB_GENERATE(host_tree, hostname, links, host_cmp );

void dels (struct session *sess){
    RB_REMOVE(sessions_tree,&sessions,sess);
    if(sess->buffer)
        free(sess->buffer);
    free(sess);
}

void alarm_handler(int signal){
    struct session *sess=RB_MIN(sessions_tree,&sessions);
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC,&now);
    int cnt=0;
    int mem=0;
    while(sess){
        int idle=now.tv_sec-sess->lastread.tv_sec;
        //printf("sess %p last %d bl %d dl %d\n",sess,idle,sess->buflen,sess->datalen);
        if(idle>300){
            struct session *nsess=RB_NEXT(sessions_tree,&sessions,sess);
            dels(sess);
            sess=nsess;
        }else{
            cnt++;
            mem+=sizeof(struct session)+sess->buflen;
            sess=RB_NEXT(sessions_tree,&sessions,sess);
        }
    }
#ifdef DEBUG
    printf("STAT: sessions %d, using %d bytes\n",cnt,mem);
#endif
    alarm(5);
}

void addsite(int id, int params, char *hostname, char *path){
    struct hostname *h=malloc(sizeof(struct hostname)+strlen(hostname)+1);
    strcpy(h->hostname,hostname);
    struct hostname *h1=RB_INSERT(host_tree,&hosts,h);
    if(h1){
        free(h);
        h=h1;
    }else{
        TAILQ_INIT(&h->urls);
    }
    if(path[0]=='*'){
        h->any.id=id;
        h->any.version=version;
    }else{
        if(h->any.version<version) //remove any
            h->any.id=0;
        struct url *u1;
        TAILQ_FOREACH(u1,&h->urls,entries){
            if(strcmp(path,u1->pathname)==0){
                u1->params=params;
                u1->id=id;
                u1->version=version;
                return;
            }
        }
        struct url *u=malloc(sizeof(struct url)+1+strlen(path));
        u->id=id;
        u->version=version;
        u->params=params;
        strcpy(u->pathname,path);
        TAILQ_INSERT_TAIL(&h->urls,u,entries);
    }
}

int cleanupdb(long version){
    struct hostname *h=RB_MIN(host_tree,&hosts);
    int c=0;
    while(h){
        //printf("add id:%d, hostname: %s, path: %s\n",id,hostname,path);
        struct url *u,*u1;
        TAILQ_FOREACH_SAFE(u,&h->urls,entries,u1){
            if(u->version<version){
                TAILQ_REMOVE(&h->urls,u,entries);
#ifdef DEBUG
                printf("remove path: http:// %s %s %d %ld\n",h->hostname,u->pathname,u->id,u->version);
#endif
                free(u);
                c++;
            }
        }
        h=RB_NEXT(host_tree,&hosts,h);
    }
    return c;
}

void reload(int signal){
    FILE *f;
    f=fopen("/root/domains.lst","r");
    if(!f){
        printf("Can't open file: %s\n",strerror(errno));
        return;
    }
    version++;
    char buffer[1024];
    int add=0;
    while(!feof(f)){
        fgets(buffer,1024,f);
        lowstr(buffer);
        char *i=index(buffer,'\n');
        if(i) *i='\0';
        //printf("==%s==\n",buffer);
        i=index(buffer,' '); /*hostname*/
        if(i){
            *(i++)='\0';
        }
    }
    int rem=cleanupdb(version);
    printf("%d records found, %d removed\n",add,rem);
    if(logfile)
        fclose(logfile);
    logfile=fopen("/var/log/zapretssl.log","a");
}

struct hostname *findhost(char* hn){
    struct hostname *fh=alloca(sizeof(struct hostname)+strlen(hn)+1);
    strcpy(fh->hostname,hn);
    return RB_FIND(host_tree,&hosts,fh);
}
void lowstr(char* text) {
    int length = strlen(text);
    int i;
    for (i = 0; i < length; i++)
        if ((text[i] >= 65) && (text[i] <= 90))
            text[i] = text[i] | 32;
}


void make_rst_server(struct ip *hdr, struct tcphdr *tcph, struct sockaddr *sin){
	uint8_t *rstpkt=calloc(60,1);
	struct ip ip;
	struct tcphdr tcp;

	ip.ip_hl = 0x5;
	ip.ip_v = 0x4;
	ip.ip_tos = 0x0;
	ip.ip_len = htons(sizeof(struct ip) + sizeof(struct tcphdr));
	ip.ip_id = htons(12830);
	ip.ip_off = 0x0;
	ip.ip_ttl = 64;
	ip.ip_p = IPPROTO_TCP;
	ip.ip_sum = 0x0;
	ip.ip_src.s_addr = hdr->ip_src.s_addr;
	ip.ip_dst.s_addr = hdr->ip_dst.s_addr;
	ip.ip_sum = in_cksum((unsigned short *)&ip, sizeof(struct ip));
	memcpy(rstpkt, &ip, sizeof(struct ip));


	tcp.th_sport = tcph->th_sport;
	tcp.th_dport = tcph->th_dport;
	tcp.th_seq = tcph->th_seq;
	tcp.th_ack = tcph->th_ack;
	tcp.th_off = sizeof(struct tcphdr) / 4;
	tcp.th_flags = TH_RST|TH_ACK;
	//tcp.th_flags = TH_ACK|TH_PUSH|TH_FIN;
	tcp.th_win = htons(32768);
	tcp.th_sum = 0;
	tcp.th_sum = in_cksum_tcp(ip.ip_src.s_addr, ip.ip_dst.s_addr,
			(unsigned short *)&tcp, sizeof(struct tcphdr));

	memcpy((rstpkt + sizeof(struct ip)), &tcp, sizeof(struct tcphdr));

	int v=sendto(fd, rstpkt, 60, 0, sin, sizeof(struct sockaddr));
	if (v < 0)  {
		perror("sendto");
		exit(1);
	}
}

void make_rst_client(struct ip *hdr, struct tcphdr *tcph, struct sockaddr *sin){
	uint8_t *rstpkt=calloc(60,1);
	struct ip ip;
	struct tcphdr tcp;

	ip.ip_hl = 0x5;
	ip.ip_v = 0x4;
	ip.ip_tos = 0x0;
	ip.ip_len = htons(sizeof(struct ip) + sizeof(struct tcphdr));
	ip.ip_id = htons(12830);
	ip.ip_off = 0x0;
	ip.ip_ttl = 64;
	ip.ip_p = IPPROTO_TCP;
	ip.ip_sum = 0x0;
	ip.ip_src.s_addr = hdr->ip_dst.s_addr;
	ip.ip_dst.s_addr = hdr->ip_src.s_addr;
	ip.ip_sum = in_cksum((unsigned short *)&ip, sizeof(struct ip));
	memcpy(rstpkt, &ip, sizeof(struct ip));


	tcp.th_sport = tcph->th_dport;
	tcp.th_dport = tcph->th_sport;
	tcp.th_seq = tcph->th_ack?tcph->th_ack:0;
	tcp.th_ack = tcph->th_seq;
	tcp.th_off = sizeof(struct tcphdr) / 4;
	//tcp.th_flags = TH_RST|TH_ACK;
	//tcp.th_flags = TH_ACK|TH_PUSH|TH_FIN;
	tcp.th_flags = TH_ACK|TH_FIN;
	tcp.th_win = htons(32768);
	tcp.th_sum = 0;
	tcp.th_sum = in_cksum_tcp(ip.ip_src.s_addr, ip.ip_dst.s_addr,
			(unsigned short *)&tcp, sizeof(struct tcphdr));

	memcpy((rstpkt + sizeof(struct ip)), &tcp, sizeof(struct tcphdr));

	int v=sendto(fd, rstpkt, 60, 0, sin, sizeof(struct sockaddr));
	if (v < 0){
		perror("sendto");
		exit(1);
	}
}

int main(int argc, char **argv) {
	int             ret;
	struct sockaddr_in bindPort, sin;
	unsigned char   packet[BUFSIZE];

	struct sockaddr_in sin_any;
	sin_any.sin_addr.s_addr=INADDR_ANY;

	RB_INIT(&sessions);
	RB_INIT(&hosts);

	signal(SIGALRM,alarm_handler);
	alarm(5);
	signal(SIGHUP,reload);
	reload(0);

	/*
	   if (argc != 2) {
	   fprintf(stderr, "Usage: %s <port number>\n", argv[0]);
	   exit(1);
	   }*/

	bindPort.sin_family = AF_INET;
	bindPort.sin_port = htons(20); //htons(atol(argv[1]));
	bindPort.sin_addr.s_addr = 0;

	fprintf(stderr, "%s:Creating a socket\n", argv[0]);
	/* open a divert socket */
	fd = socket(AF_INET, SOCK_RAW, IPPROTO_DIVERT);

	if (fd == -1) {
		fprintf(stderr, "%salarm_handler:We could not open a divert socket\n", argv[0]);
		exit(1);
	}

	fprintf(stderr, "%s:Binding a socket\n", argv[0]);
	ret = bind(fd, (struct sockaddr*)&bindPort, sizeof(struct sockaddr_in));

	if (ret != 0) {
		close(fd);
		fprintf(stderr, "%s: Error bind(): %s", argv[0], strerror(ret));
		exit(2);
	}
	printf("%s: Waiting for data...\n", argv[0]);
	/* read data in */

	size_t sinlen = sizeof(struct sockaddr_in);
	while (1) {
		int readn = recvfrom(fd, packet, BUFSIZE, 0, (struct sockaddr*)&sin, (socklen_t*)&sinlen);
		struct ip   *hdr;
		hdr = (struct ip *) packet;
		int pass=1;
		if(hdr->ip_p != 6) goto bypass;//not TCP
		uint16_t hlen=hdr->ip_hl*4;
		struct tcphdr *tcph=(void*)packet+hlen;
		uint8_t *thdr = packet+hlen;
		//uint16_t plen=hdr->ip_len-hlen;

		uint16_t sport=ntohs(tcph->th_sport);
		uint16_t dport=ntohs(tcph->th_dport);

		struct session tmps;
		tmps.src_ip=hdr->ip_src.s_addr;
		tmps.dst_ip=hdr->ip_dst.s_addr;
		tmps.src_port=sport;
		tmps.dst_port=dport;
		struct session *sess;
		char dstbuf[32];
		inet_ntop(AF_INET,&hdr->ip_dst, dstbuf, 30);
		char srcbuf[32];
		inet_ntop(AF_INET,&hdr->ip_src, srcbuf, 30);


		uint8_t  tlen=(thdr[12]>>4)*4;
		uint16_t dataoff=hlen+tlen;
		uint16_t datalen=readn-dataoff;


		if((sess=RB_FIND(sessions_tree,&sessions,&tmps))==NULL){
			if(!(tcph->th_flags & TH_FIN) && !(tcph->th_flags & TH_RST)){
				sess=calloc(sizeof(struct session),1);
				sess->src_ip=hdr->ip_src.s_addr;
				sess->dst_ip=hdr->ip_dst.s_addr;
				sess->src_port=sport;
				sess->dst_port=dport;
				struct session *s=RB_INSERT(sessions_tree,&sessions,sess);
#ifdef DEBUG
				printf("Creating session for %s:%d -> %s:%d %p\n",
						srcbuf, sport,
						dstbuf, dport,s);
#endif
			}else{
#ifdef DEBUG
				printf("Session not found, but not creating for %s:%d -> %s:%d %p\n",
						srcbuf, sport,
						dstbuf, dport,sess);
#endif
			}
		}
		if(sess && (sess->dnt || sess->allowed))
			goto bypass;
		uint64_t dseq=ntohl(tcph->th_seq);

#ifdef DEBUG
		if(datalen){
			printf("%s:%d -> %s:%d, data %d, seq %ld\n", srcbuf, sport, dstbuf, dport, datalen, dseq);
		}
#endif

		if(!datalen || !sess) goto bypass;
#ifdef DEBUG2
		{
			char tbuf[128];
			bzero(tbuf,128);
			int i;
#define min(a,b) (a<b?a:b)
			uint8_t bp=0;
			for(i=0;i<=datalen && bp<125;i++,bp++){
				if(b<32 || b>127){
					sprintf(tbuf+bp,"%02x ",b);
					bp+=2;
				}else{
					sprintf(tbuf+bp,"%c",b);
				}
			}
			printf("Data: %d =%s=\n",datalen,tbuf);
		}
#endif

		if(!sess->datalen){
			sess->seq=dseq;
		}

		if(sess->buflen<datalen+sess->datalen+1){
			sess->buflen=((datalen+sess->datalen+512)>>8)<<8;
			sess->buffer=realloc(sess->buffer,sess->buflen);
			if(!sess->buffer){
				fprintf(stderr,"ERROR: Can't allocate memory at %s:%d",__FUNCTION__,__LINE__);
			}
		}

		if(dseq<sess->seq+sess->datalen){
#ifdef DEBUG
			printf("Dup\n");
#endif
			goto bypass;
		}
		if(dseq>(sess->seq+sess->datalen)){
#ifdef DEBUG
			printf("Out of order packet\n");
#endif
			goto bypass;
		}
		memcpy(sess->buffer+sess->datalen,packet+dataoff,datalen);
		//printf("Append %d at %d\n",datalen,sess->datalen);
		sess->datalen+=datalen;
		sess->buffer[sess->datalen]='\0';


		//char *aftereob=NULL;

		//process:

		if(sess->buffer[0]!=0x16){ //expected Handshake
			sess->dnt=1;
			goto bypass;
		}
		if(sess->buflen<10) goto bypass;
		uint16_t full_length=(sess->buffer[3]<<8)|sess->buffer[4];
		if(sess->buflen<full_length+5)
			goto bypass;
		if(sess->buffer[5]!=0x01){ //expected ClientHello
			sess->dnt=1;
			goto bypass;
		}
		printf("Process %d\n",sess->datalen);
#ifdef DEBUG1
		{
			int i;
#define min(a,b) (a<b?a:b)
			printf("BUF: %d =\n",sess->datalen);
			for(i=0;i<=sess->datalen;i++){
				if(i%16==0){
					printf("%4x: ",i);
				}
				uint8_t b=sess->buffer[i];
				if(b<32 || b>127){
					printf("%02x ",b);
				}else{
					printf(" %c ",b);
				}
				if(i%16 == 15)
					printf("\n");
			}
			printf("\n====\n");
		}
#endif
		uint8_t temp_len;
		uint8_t *pointer=(uint8_t*)(sess->buffer+5);
		uint8_t *endofbuf=(uint8_t*)(sess->buffer+full_length+5);
		//printf("skipped1 %x\n",(long)pointer-(long)sess->buffer);
		pointer+=6+32; //session id;
		//printf("skipped2 %x (%x)\n",(long)pointer-(long)sess->buffer,*pointer);
		pointer+=(*pointer)+1; //skip session id;
		//printf("skipped3 %x (%x)\n",(long)pointer-(long)sess->buffer,*pointer);
		temp_len=((*pointer)<<8)|(*(pointer+1));
		pointer+=2+temp_len; //skip cipher suite
		//printf("skipped4 %x (%x)\n",(long)pointer-(long)sess->buffer,*pointer);
		pointer+=(*pointer)+1; //skip compression suite
		//printf("skipped5 %x (%x)\n",(long)pointer-(long)sess->buffer,*pointer);
		char* namebuf=NULL;
		if((pointer+2)<endofbuf){
			temp_len=((*pointer)<<8)|(*(pointer+1));
			//printf("Ext len %x\n",temp_len);
			if(temp_len){
				pointer+=2;
				while(pointer<endofbuf){
					uint16_t ext_id=((*pointer)<<8)|(*(pointer+1));
					temp_len=((*pointer+2)<<8)|(*(pointer+3));
					//printf("Ext %04x len %04x\n",ext_id,temp_len);
					if(ext_id==0){
						temp_len=((*pointer+7)<<8)|(*(pointer+8));
						namebuf=alloca(temp_len+1);
						strncpy(namebuf,(const char*)(pointer+9),temp_len);
						int c=strncmp("www.bet-at-home.com",namebuf,temp_len);
						printf("Found SNI hostname -%s- %d\n",namebuf,c);
						if(c==0){
							printf("Clear \n\n");
							sess->clear=1;
						}
						break;
					}
					pointer+=temp_len+4;
				}
			}
		}

		if(!sess->clear)
			sess->dnt=1;
		else{
			if(logfile)
				fprintf(logfile,"KILL SESSION!!!!!! %s\n",namebuf);
			printf("KILL SESSION!!!!!! %s\n",namebuf);
		}

		if(sess->clear){
			pass=0;
			make_rst_server(hdr,tcph,(struct sockaddr *)&sin);
			make_rst_client(hdr,tcph,(struct sockaddr *)&sin);
			dels(sess);
			continue;
		}
bypass:
		if(sess){
			if(tcph->th_flags & TH_FIN){
				dels(sess);
			}else{
				clock_gettime(CLOCK_MONOTONIC,&sess->lastread);
			}
		}
		if(pass)
			sendto(fd, packet, readn, 0, (struct sockaddr*)&sin, sinlen);
	}
}
