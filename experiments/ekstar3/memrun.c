/* memrun CMD ARGS...: run a command, then print its wall time and peak RSS (MB) on stderr. */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <time.h>
int main(int argc, char **argv) {
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  pid_t p = fork();
  if (p == 0) { execvp(argv[1], argv + 1); perror("exec"); _exit(127); }
  int st; waitpid(p, &st, 0);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  struct rusage ru; getrusage(RUSAGE_CHILDREN, &ru);
  fprintf(stderr, "time %.1f s, peak %ld MB, exit %d\n",
          (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9, ru.ru_maxrss / 1024,
          WIFEXITED(st) ? WEXITSTATUS(st) : -1);
  return WIFEXITED(st) ? WEXITSTATUS(st) : 1;
}
