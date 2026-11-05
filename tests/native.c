#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
#include <signal.h>
extern uint64_t sum_bytes(const uint8_t*, uint64_t);
extern uint64_t beyond(const uint8_t*, uint64_t);
extern uint64_t omit(const uint8_t*, uint64_t);
extern uint64_t ret_probe(void);
int main(void) {
  uint8_t b[4096];
  assert(sum_bytes(NULL,0)==0);
  for(unsigned mode=0;mode<4;mode++) {
    for(unsigned i=0;i<4096;i++) b[i]=mode==0?0:mode==1?255:mode==2?(uint8_t)i:(uint8_t)(i*73+19);
    uint64_t expected=0;
    for(unsigned n=0;n<=4096;n++) {
      assert(sum_bytes(b,n)==expected);
      if(n<4096) expected+=b[n];
    }
  }
  b[0]=42; assert(omit(b,1)==0);
  assert(ret_probe()==8);
  long page=sysconf(_SC_PAGESIZE);
  void *guard=mmap(NULL,(size_t)page,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  assert(guard!=MAP_FAILED);
  assert(sum_bytes(guard,0)==0);
  pid_t pid=fork(); assert(pid>=0);
  if(pid==0) {
    struct rlimit lim={0,0}; setrlimit(RLIMIT_CORE,&lim);
    (void)beyond(guard,0); _exit(0);
  }
  int status; assert(waitpid(pid,&status,0)==pid);
  assert(WIFSIGNALED(status) && WTERMSIG(status)==SIGSEGV);
  munmap(guard,(size_t)page);
  puts("native: 16388 buffer cases; return stack delta 8; omission 0 != 42; beyond SIGSEGV on empty guard buffer");
}
