// SPDX-License-Identifier: Apache-2.0
// §AR-workspace.filesystem: Descriptor-relative, bounded snapshots; no guest code runs in this
// reader.
#include "m3_sha256.h"
#define TREE_MAX (4u*1024u*1024u)
#define EXPORT_MAX (16u*1024u*1024u)
static int digest_text(const char *s) {
    if(strlen(s)!=64)return 0;
    for(unsigned i=0;i<64;i++)if(!((s[i]>='0'&&s[i]<='9')||(s[i]>='a'&&s[i]<='f')))return 0;
    return 1;
}
static int hex_digit(unsigned char c){return c>='0'&&c<='9'?c-'0':c>='a'&&c<='f'?c-'a'+10:-1;}
static int utf8_path(const unsigned char *p) {
    while(*p){uint32_t value;unsigned length;unsigned char c=*p++;
        if(c<0x80)continue;
        if(c>=0xc2&&c<=0xdf){value=c&31;length=1;}
        else if(c>=0xe0&&c<=0xef){value=c&15;length=2;}
        else if(c>=0xf0&&c<=0xf4){value=c&7;length=3;}else return -1;
        unsigned total=length;
        while(length--){c=*p++;if((c&0xc0)!=0x80)return -1;value=(value<<6)|(c&63);}
        if((total==2&&value<0x800)||(total==3&&value<0x10000)||value>0x10ffff||(value>=0xd800&&value<=0xdfff))return -1;
    }return 0;
}
static int decode_path(const char *hex,char path[4096]) {
    size_t size=strlen(hex);if(!size||size%2||size/2>4095)return -1;
    for(size_t i=0;i<size/2;i++){int a=hex_digit(hex[i*2]),b=hex_digit(hex[i*2+1]);if(a<0||b<0||!(a||b))return -1;path[i]=(char)(a*16+b);}
    path[size/2]=0;if(utf8_path((unsigned char *)path))return -1;
    unsigned depth=0;const char *p=path;
    while(*p){const char *end=strchr(p,'/');size_t n=end?(size_t)(end-p):strlen(p);
        if(!n||n>255||(n==1&&p[0]=='.')||(n==2&&!memcmp(p,"..",2))||++depth>64)return -1;
        if(!end)break;
        p=end+1;if(!*p)return -1;
    }
    return !strcmp(path,".tmp")||!strncmp(path,".tmp/",5)?-1:0;
}
static int trusted_regular(int fd,uint64_t bound) {
    struct stat s;
    if(fstat(fd,&s)||!S_ISREG(s.st_mode)||s.st_uid||s.st_gid||(s.st_mode&0022)||s.st_size<0||(uint64_t)s.st_size>bound){errno=EINVAL;return -1;}return 0;
}
static int blob_open(const char *digest,uint64_t bound) {
    if(!digest_text(digest)){errno=EINVAL;return -1;}
    char path[128];snprintf(path,sizeof(path),"/m3-inputs/blobs/%s",digest);
    int fd=open(path,O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK);
    if(fd>=0&&trusted_regular(fd,bound)){close(fd);return -1;}return fd;
}
static int copy_hash(int source,int dest,uint64_t bound,uint64_t *size,char digest[65]) {
    struct m3_sha hash;sha_init(&hash);unsigned char buffer[16384];uint64_t count=0;
    for(;;){ssize_t n=read(source,buffer,sizeof(buffer));if(n<0&&errno==EINTR)continue;if(n<0)return -1;if(!n)break;
        if((uint64_t)n>bound-count){errno=EFBIG;return -1;}count+=(uint64_t)n;
        sha_update(&hash,buffer,(size_t)n);if(dest>=0&&write_all(dest,buffer,(size_t)n))return -1;
    }
    unsigned char bytes[32];sha_final(&hash,bytes);sha_hex(bytes,digest);*size=count;return 0;
}
static int parent_directory(int root,char *path,char **base) {
    int parent=fcntl(root,F_DUPFD_CLOEXEC,3);if(parent<0)return -1;
    char *p=path,*slash;
    while((slash=strchr(p,'/'))){*slash=0;int next=openat(parent,p,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);close(parent);if(next<0)return -1;parent=next;p=slash+1;}
    *base=p;return parent;
}
static int import_tree(const char *digest) {
    if(!strcmp(digest,"none"))return 0;
    if(!digest_text(digest)){errno=EINVAL;return -1;}
    char source[128];snprintf(source,sizeof(source),"/m3-inputs/trees/%s",digest);
    int fd=open(source,O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK);if(fd<0)return -1;
    if(trusted_regular(fd,TREE_MAX)){close(fd);return -1;}
    char *data=calloc(1,TREE_MAX+1);if(!data){close(fd);return -1;}
    size_t used=0;int failed=0;
    while(used<TREE_MAX){ssize_t n=read(fd,data+used,TREE_MAX-used);if(n<0&&errno==EINTR)continue;if(n<0){failed=1;break;}if(!n)break;used+=(size_t)n;}
    char extra;ssize_t more=read(fd,&extra,1);close(fd);
    struct m3_sha hash;unsigned char raw[32];char actual[65];sha_init(&hash);sha_update(&hash,data,used);sha_final(&hash,raw);sha_hex(raw,actual);
    if(failed||more!=0||strcmp(actual,digest)||used<8||memcmp(data,"LCTREE1\n",8)||data[used-1]!='\n'||memchr(data,0,used)){free(data);errno=EINVAL;return -1;}
    int root=open(workspace,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);if(root<0){free(data);return -1;}
    uint64_t bytes=0,entries=2;char *line=data+8;
    while(*line){char *end=strchr(line,'\n');*end=0;char *fields[6]={0};unsigned count=0;char *p=line;
        for(;;){if(count==6){failed=1;break;}fields[count++]=p;char *space=strchr(p,' ');if(!space)break;*space=0;p=space+1;}
        int directory=count==2&&!strcmp(fields[0],"D");int regular=count==5&&!strcmp(fields[0],"F");
        char path[4096];uint64_t size=0;
        if(failed||(!directory&&!regular)||decode_path(fields[directory?1:2],path)||++entries>policy.inodes||
           (regular&&( (strcmp(fields[1],"0")&&strcmp(fields[1],"1"))||number(fields[3],&size)||
             (fields[3][0]=='0'&&fields[3][1])||!digest_text(fields[4])||size>policy.space-bytes))){failed=1;errno=EINVAL;break;}
        char *base;int parent=parent_directory(root,path,&base);if(parent<0){failed=1;break;}
        if(directory){if(mkdirat(parent,base,0700)||fchownat(parent,base,run_uid,run_uid,AT_SYMLINK_NOFOLLOW))failed=1;}
        else {
            int input=blob_open(fields[4],size),output=-1;
            if(input>=0)output=openat(parent,base,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
            uint64_t copied=0;char got[65];
            if(input<0||output<0||copy_hash(input,output,size,&copied,got)||copied!=size||strcmp(got,fields[4])||
               fchown(output,run_uid,run_uid)||fchmod(output,fields[1][0]=='1'?0700:0600))failed=1;
            if(input>=0)close(input);
            if(output>=0&&close(output))failed=1;
            bytes+=size;
        }
        close(parent);if(failed)break;line=end+1;
    }
    close(root);free(data);if(failed){if(!errno)errno=EINVAL;return -1;}return 0;
}
static int snapshot_stdin(const char *digest) {
    if(!strcmp(digest,"none"))return open("/dev/null",O_RDONLY|O_CLOEXEC);
    int source=blob_open(digest,policy.in);if(source<0)return -1;
    int target=(int)syscall(SYS_memfd_create,"m3-stdin",3u);uint64_t count;char got[65];
    int failed=target<0||copy_hash(source,target,policy.in,&count,got)||strcmp(got,digest)||
        fcntl(target,F_ADD_SEALS,F_SEAL_SEAL|F_SEAL_SHRINK|F_SEAL_GROW|F_SEAL_WRITE)||lseek(target,0,SEEK_SET)<0;
    close(source);if(failed){if(target>=0)close(target);errno=EINVAL;return -1;}return target;
}
// §FS-workspace.filesystem: The scope is extinct before export; names are hex, never destination
// paths.
struct export_state { int manifest,blobs;uint64_t entries,bytes,manifest_bytes;uint32_t omitted;struct m3_sha hash; };
static int export_line(struct export_state *s,const char *line) {
    size_t n=strlen(line);if(n>EXPORT_MAX-s->manifest_bytes){errno=EFBIG;return -1;}
    if(write_all(s->manifest,line,n))return -1;
    sha_update(&s->hash,line,n);s->manifest_bytes+=n;return 0;
}
static int export_directory(struct export_state *s,int dir,const char *prefix,unsigned depth) {
    if(depth>64){errno=ELOOP;return -1;}
    int duplicate=fcntl(dir,F_DUPFD_CLOEXEC,3);if(duplicate<0)return -1;
    DIR *stream=fdopendir(duplicate);if(!stream){close(duplicate);return -1;}int result=0;
    for(;;){errno=0;struct dirent *entry=readdir(stream);if(!entry){if(errno)result=-1;break;}
        if(!strcmp(entry->d_name,".")||!strcmp(entry->d_name,".."))continue;
        char name[4096],hex[8191],line[8350];size_t pre=strlen(prefix),len=strlen(entry->d_name);
        if(pre+(pre?1:0)+len>4095||++s->entries>policy.inodes){errno=EFBIG;result=-1;break;}
        memcpy(name,prefix,pre);if(pre)name[pre++]='/';memcpy(name+pre,entry->d_name,len+1);
        const char digits[]="0123456789abcdef";for(size_t i=0;i<pre+len;i++){hex[2*i]=digits[(unsigned char)name[i]>>4];hex[2*i+1]=digits[(unsigned char)name[i]&15];}hex[2*(pre+len)]=0;
        struct stat st;if(fstatat(dir,entry->d_name,&st,AT_SYMLINK_NOFOLLOW)){result=-1;break;}
        if(S_ISDIR(st.st_mode)){
            snprintf(line,sizeof(line),"D %s\n",hex);int child=openat(dir,entry->d_name,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
            if(child<0||export_line(s,line)||export_directory(s,child,name,depth+1))result=-1;
            if(child>=0)close(child);
        }else if(S_ISREG(st.st_mode)){
            int input=openat(dir,entry->d_name,O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK);
            int output=openat(s->blobs,".copy",O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);uint64_t count=0;char digest[65];
            if(input<0||output<0||copy_hash(input,output,policy.space-s->bytes,&count,digest))result=-1;
            if(input>=0)close(input);
            if(output>=0){if(fsync(output))result=-1;if(close(output))result=-1;}
            if(!result){s->bytes+=count;if(renameat(s->blobs,".copy",s->blobs,digest))result=-1;
                snprintf(line,sizeof(line),"F %u %s %"PRIu64" %s\n",(st.st_mode&0111)?1:0,hex,count,digest);if(export_line(s,line))result=-1;}
        }else{snprintf(line,sizeof(line),"O %s\n",hex);s->omitted++;if(export_line(s,line))result=-1;}
        if(result)break;
    }
    int saved=errno;closedir(stream);errno=saved;return result;
}
static int export_workspace(struct result *r) {
    if(!policy.export_files){r->export_state=0;return 0;}
    uint64_t populated;if(cg_read("cgroup.events","populated",&populated)||populated){r->export_state=3;return -1;}
    r->export_state=2;
    int root=open(workspace,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
    int result=open(result_path,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);if(root<0||result<0){if(root>=0)close(root);if(result>=0)close(result);return -1;}
    struct export_state s={.manifest=-1,.blobs=-1};sha_init(&s.hash);
    int failed=mkdirat(result,"blobs",0700);
    if(!failed){s.blobs=openat(result,"blobs",O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);s.manifest=openat(result,"export.partial",O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
        failed=s.blobs<0||s.manifest<0||export_line(&s,"LCEXPORT1\n")||export_directory(&s,root,"",0)||fsync(s.manifest);}
    if(s.manifest>=0&&close(s.manifest))failed=1;
    if(s.blobs>=0)close(s.blobs);
    if(!failed&&renameat(result,"export.partial",result,"export.manifest"))failed=1;
    if(!failed){sha_final(&s.hash,r->export_digest);r->export_state=1;}
    r->omitted=s.omitted;close(root);close(result);return failed?-1:0;
}
