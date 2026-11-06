/* map1.c N mode [G]: over the whole pair triangle (any parity), map in (u/N, u'/N).
   mode 0: which old region (B, b = B2, D, d = D0, W) or '.';
   mode 1..5: '#' where the PF candidate holds, '_' old region, '.' neither:
     1 Z (u',u) w1=(1,1); 2 Z (u',u) (2,1); 3 X0 (u',u) (1,1); 4 X0 (u',u) (2,1); 5 Z (u',u) (3,2). */
#include "../residual/parok.h"
static int cand(ll N, ll u, ll up, int o, int f, ll p, ll q) {
  ll x = o ? up : u, y = o ? u : up;
  if (f > 0 && y < 3) return 0;
  ll K, R, al, be, smax, amin;
  comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
  buildCons(K, x, R, al, be, smax, amin);
  return parOKdir(p, q);
}
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int mode = atoi(argv[2]);
  int G = argc > 3 ? atoi(argv[3]) : 60;
  static char mp[300][300];
  for (int i = 0; i < 300; i++) for (int j = 0; j < 300; j++) mp[i][j] = ' ';
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      int i = u * G / N, j = up * G / N;
      char ch;
      if (mode == 0) {
        ch = regB(N,u,up)?'B':regB2(N,u,up)?'b':regD(N,u,up)?'D':regD0(N,u,up)?'d':regW(N,u,up)?'W':'.';
      } else {
        static const int o_[6] = {0,1,1,1,1,1}, f_[6] = {0,0,0,1,1,0};
        static const ll p_[6] = {0,1,2,1,2,3}, q_[6] = {0,1,1,1,1,2};
        ch = cand(N,u,up,o_[mode],f_[mode],p_[mode],q_[mode])?'#':(provenOld(N,u,up)?'_':'.');
      }
      if (mp[i][j] == ' ' || ch == '.') mp[i][j] = ch;
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) putchar(mp[i][j]);
    printf("\n");
  }
  return 0;
}
