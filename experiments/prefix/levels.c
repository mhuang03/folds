/* levels.c: full subset DP for one N (N <= 24).  For each size j prints
 *   j  T(N,j)=sum_{|S|=j} g(S)   V(N,j)=#{|S|=j: g(S)>0}
 *      C(N,j)=sum_{|S|=j} g(S)*[g(S^c)>0]   (valid prefixes that can be completed)
 *      W(N,j)=#{|S|=j: g(S)>0 and g(S^c)>0} (live sets)
 * usage: levels N */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
int main(int argc, char **argv){
  int N = atoi(argv[1]); u64 full = (1ULL << N) - 1;
  u64 *g = calloc(1ULL << N, sizeof(u64));
  u64 Lm[64], Rm[64];
  for (int m = 1; m <= N; m++){ int D = m-1 < N-m ? m-1 : N-m; Lm[m] = Rm[m] = 0;
    for (int d = 1; d <= D; d++){ Lm[m] |= 1ULL << (m-d-1); Rm[m] |= 1ULL << (m+d-1); } }
  g[0] = 1;
  for (u64 S = 0; S < full; S++){ if (!g[S]) continue;
    for (int m = 1; m <= N; m++){ u64 b = 1ULL << (m-1); if (S & b) continue;
      if (__builtin_popcountll(S & Lm[m]) == __builtin_popcountll(S & Rm[m])) g[S|b] += g[S]; } }
  u64 T[64] = {0}, V[64] = {0}, C[64] = {0}, W[64] = {0};
  for (u64 S = 0; S <= full; S++){ if (!g[S]) continue; int j = __builtin_popcountll(S);
    T[j] += g[S]; V[j]++; if (g[full ^ S]){ C[j] += g[S]; W[j]++; } }
  for (int j = 0; j <= N; j++) printf("%d %d %llu %llu %llu %llu\n", N, j, T[j], V[j], C[j], W[j]);
}
