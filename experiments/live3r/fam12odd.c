/* fam12odd.c NMAX: check the closed-form near copy for {1, 2, c}, N = 1 (mod 4), c odd:
   phi(1) = 1, phi(2) = 2, phi(y) = 2y - 1 (3 <= y <= p), p = (N+1)/2;
   (1) every panel j != 2 is regular (window relation preserved around phi(j) for all y);
   (2) 4 is a valid step after B = phi([p]) and B + {4} pulls no panel to the left
       (I(m) >= 0 for all m outside, Theorem G with the centre 1/2);
   (3) for which odd c is {1, 2, (c+1)/2} valid and not dead in [p]. */
#include <stdio.h>
#include <stdlib.h>
static int reachn(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
static int rel(int n,int j,int y){int r=reachn(n,j); if(j-r<=y&&y<j)return 1; if(j<y&&y<=j+r)return -1; return 0;}
int main(int argc,char**argv){ int nmax=atoi(argv[1]);
  for(int N=9;N<=nmax;N+=4){ int p=(N+1)/2; int phi[300]; for(int y=1;y<=p;y++)phi[y]=(y==2)?2:2*y-1;
    int ok1=1; for(int j=1;j<=p;j++){ if(j==2)continue; for(int y=1;y<=p;y++) if(rel(N,phi[j],phi[y])!=rel(p,j,y)) ok1=0; }
    char in[300]={0}; for(int y=1;y<=p;y++)in[phi[y]]=1;
    int I4=0; { int r=reachn(N,4); for(int d=1;d<=r;d++){ if(in[4-d])I4++; if(in[4+d])I4--; } }
    in[4]=1; int ok2=(I4==0)&&!(in[4]&&0);
    for(int m=1;m<=N;m++){ if(in[m])continue; int r=reachn(N,m),I=0; for(int d=1;d<=r;d++){ if(in[m-d])I++; if(in[m+d])I--; } if(I<0)ok2=0; }
    printf("N=%d p=%d regular=%d step4+inward=%d\n",N,p,ok1,ok2); }
  return 0;}
