/* Explicit enumeration of all semi-symmetric sequences of length N (N <= ~17) and checks of
   the swap-involution congruences.
   For a position i (0-based) let sw_i(x) = x with entries i, i+1 exchanged, "possible" iff
   x[i], x[i+1] are mutually outside each other's windows (iff sw_i(x) is again valid).
   For i with image i' = N-2-i (reversal), tau_i = sw_i o sw_i' (each applied when possible;
   i = i' only for the middle pair of even N).
   Checks, for every i <= i' with |i-i'| >= 2 or i == i':
     #Y_i  ==  #(Y_i cap Fix RM) + #(Y_i cap Fix tau_i RM)   (mod 8),
   Y_i = {x : tau_i x != x}.
   Also the "rigid" formula for E = <tau_i : i in P>, P = {n-1, n-3, ...} (even N) or
   {n-2, n-4, ...} (odd N, N = 2n+1):  a == #Z + #T1 (mod 8) where Z = {x: all tau_i, i in
   P, trivial}, T1 = {x : exactly one tau_j active, and x = RM x or x = tau_j RM x}.
   usage: enum N */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int N; static int x[64]; static int used[64]; static int rad[64];
static long long A=0;
static long long Y[64],YF[64],YT[64];
static long long Zc=0,T1=0,Zsd=0;
static int P[64],np=0;
static int inwin(int a,int b){ /* a in W(b) */ int d=a>b?a-b:b-a; return d>=1&&d<=rad[b]; }
static int canswap(const int*s,int i){ return !inwin(s[i],s[i+1]) && !inwin(s[i+1],s[i]); }
static void tau(const int*s,int*t,int i){ int j=N-2-i; memcpy(t,s,sizeof(int)*N);
  if(canswap(s,i)){int u=t[i];t[i]=t[i+1];t[i+1]=u;}
  if(j!=i && canswap(s,j)){int u=t[j];t[j]=t[j+1];t[j+1]=u;} }
static void rm(const int*s,int*t){ for(int k=0;k<N;k++) t[k]=N+1-s[N-1-k]; }
static int eq(const int*s,const int*t){ return memcmp(s,t,sizeof(int)*N)==0; }
static void leaf(void){
  A++; int r[64],t[64],u[64];
  rm(x,r); int sd=eq(r,x);
  for(int i=0;i<=N-2;i++){ int j=N-2-i; if(i>j) break; if(i!=j && j-i<2) continue;
    tau(x,t,i); if(eq(t,x)) continue; Y[i]++; if(sd) YF[i]++;
    tau(r,u,i); if(eq(u,x)) YT[i]++; }
  int act=0,last=-1; for(int k=0;k<np;k++){ tau(x,t,P[k]); if(!eq(t,x)){act++;last=P[k];} }
  if(act==0){Zc++; if(sd)Zsd++;}
  else if(act==1){ if(sd) T1++; else { tau(r,u,last); if(eq(u,x)) T1++; } }
}
static void dfs(int k){
  if(k==N){leaf();return;}
  for(int m=1;m<=N;m++) if(!used[m]){
    int l=0,rr=0; for(int d=1;d<=rad[m];d++){ l+=used[m-d]; rr+=used[m+d]; }
    if(l!=rr) continue; used[m]=1; x[k]=m; dfs(k+1); used[m]=0; }
}
int main(int argc,char**argv){
  N=atoi(argv[1]); for(int m=1;m<=N;m++) rad[m]=m-1<N-m?m-1:N-m;
  int n=N/2;
  if(N%2==0){ for(int i=n-1;i>=0;i-=2) P[np++]=i; }
  else { for(int i=n-2;i>=0;i-=2) P[np++]=i; }
  dfs(0);
  printf("N=%d a=%lld a%%8=%lld\n",N,A,A%8);
  for(int i=0;i<=N-2;i++){ int j=N-2-i; if(i>j) break; if(i!=j && j-i<2) continue;
    long long rhs=YF[i]+YT[i];
    printf("  pair %d/%d: Y=%lld FixRM=%lld FixTauRM=%lld  Y%%8=%lld rhs%%8=%lld %s\n",i,j,Y[i],YF[i],YT[i],
      Y[i]%8,rhs%8,(Y[i]-rhs)%8==0?"ok":"FAIL"); }
  printf("  rigid: Z=%lld (Z/a=%.4f, sd %lld) T1=%lld  (Z+T1)%%8=%lld %s\n",Zc,(double)Zc/A,Zsd,T1,(Zc+T1)%8,
    (A-Zc-T1)%8==0?"ok":"FAIL");
  return 0;
}
