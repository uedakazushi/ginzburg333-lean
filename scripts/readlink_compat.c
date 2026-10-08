#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
/* The sandbox PID namespace and /proc use different PID numbers.
   Resolve only this process's executable through the equivalent self path. */
ssize_t readlink(const char *path, char *buf, size_t n) {
    static ssize_t (*real_readlink)(const char *, char *, size_t);
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof own_exe, "/proc/%d/exe", (int)getpid());
    return real_readlink(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path, buf, n);
}
