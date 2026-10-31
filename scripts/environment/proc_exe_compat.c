#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
 static ssize_t (*real_readlink)(const char*,char*,size_t)=NULL;
 if(!real_readlink) real_readlink=dlsym(RTLD_NEXT,"readlink");
 if(strncmp(path,"/proc/",6)==0) {
   const char *p=path+6; while(isdigit((unsigned char)*p)) p++;
   if(p>path+6 && strcmp(p,"/exe")==0) return real_readlink("/proc/self/exe",buf,bufsiz);
 }
 return real_readlink(path,buf,bufsiz);
}
