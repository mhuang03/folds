/* pieces.c: polytope decomposition of T(N,k).
 * A valid k-sequence x_1..x_k is classified by
 *   - its order type pi (the permutation pattern of x_1..x_k), and
 *   - the sign matrix sigma_ij (i<j): +1 if x_j is in the right arm of x_i
 *     (x_i < x_j <= floor((N+x_i)/2)), -1 if in the left arm (ceil((x_i+1)/2) <= x_j < x_i),
 *     0 otherwise.
 * Given (pi, sigma) every condition is a linear inequality in (x, N), so each class is the
 * set of lattice points of one parametric polytope; validity means every column of sigma
 * sums to 0.  This program prints, for each N, the count of every nonempty class.
 * usage: pieces K Nmin Nmax   (K <= 7)
 * Empirical fact (checked, see FINDINGS.txt): for a VALID sequence sigma is a function of the
 * order type, so the classes are indexed by order types alone; a violation is reported on stderr.
 * Output lines:  N key count     with key = pi-code * 3^(K(K-1)/2) + sigma-code. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static int N, K, X[8], used[1024];
static u64 *cnt, *sigof; static int npairs; static u64 nsig; static u64 conflicts;

static int sgn(int x, int c){ /* phi_x(c) */
  if (c > x && 2*c <= N + x) return 1;
  if (c < x && 2*c >= x + 1) return -1;
  return 0;
}
static void leaf(void){
  /* order type code: Lehmer code of ranks */
  int code = 0;
  for (int i = 0; i < K; i++){ int r = 0; for (int j = i+1; j < K; j++) if (X[j] < X[i]) r++; code = code*(K-i) + r; }
  u64 s = 0;
  for (int j = 1; j < K; j++) for (int i = 0; i < j; i++) s = s*3 + (sgn(X[i], X[j]) + 1);
  if (cnt[code] && sigof[code] != s) conflicts++;   /* two sign classes for one order type */
  sigof[code] = s; cnt[code]++;
}
static void dfs(int d){
  if (d == K){ leaf(); return; }
  for (int m = 1; m <= N; m++){ if (used[m]) continue;
    int f = 0; for (int i = 0; i < d; i++) f += sgn(X[i], m);
    if (f) continue;
    X[d] = m; used[m] = 1; dfs(d+1); used[m] = 0; }
}
int main(int argc, char **argv){
  K = atoi(argv[1]); int a = atoi(argv[2]), b = atoi(argv[3]);
  npairs = K*(K-1)/2; nsig = 1; for (int i = 0; i < npairs; i++) nsig *= 3;
  u64 fact = 1; for (int i = 2; i <= K; i++) fact *= i;
  cnt = calloc((size_t)fact, sizeof(u64)); sigof = calloc((size_t)fact, sizeof(u64));
  for (N = a; N <= b; N++){
    memset(cnt, 0, (size_t)fact*sizeof(u64)); conflicts = 0;
    dfs(0);
    if (conflicts) fprintf(stderr, "N=%d: %llu sequences whose order type has two sign classes\n", N, conflicts);
    for (u64 i = 0; i < (u64)fact; i++) if (cnt[i]) printf("%d %llu %llu\n", N, i*nsig + sigof[i], cnt[i]);
    fflush(stdout);
  }
}
