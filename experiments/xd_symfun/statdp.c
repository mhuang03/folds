/* Subset DP for statistic generating polynomials over semi-symmetric fold sequences.
   Extends experiments/arith/polydp.c to every statistic that is computable from
   (S, m) (the set S of panels placed before, the panel m placed now, k = |S|), or from
   (S, last, m).  a = fold sequence (a_k = panel at step k), t = time word (t_m = step of m).

   usage: statdp N mode
   modes with state S:
     inv     inversions (the same for a and t)          inc = #{x in S : x > m}
     a_exc   excedances of a (a_k > k)                   inc = [m > k+1]
     a_fix   fixed points (the same for a and t)         inc = [m == k+1]
     a_lrmax left-to-right maxima of a                   inc = [m > max S]
     t_des   descents of t (= inverse descents of a)     inc = [m+1 in S]
     t_maj   major index of t                            inc = m [m+1 in S]
     t_exc   excedances of t (t_m > m)                   inc = [k+1 > m]
     t_lrmax left-to-right maxima of t                   inc = [{1..m-1} subset S]
     t_pk    interior peaks of t (t_{m-1} < t_m > t_{m+1}) inc = [m-1, m+1 in S]
   modes with state (S, last):
     a_des   descents of a
     a_maj   major index of a                            inc = k [last > m]
     a_deslast  joint (descents, last panel): prints one line per last panel
   mode with state (S, last, up):
     a_pk    interior peaks of a
   prints "N mode c_0 c_1 ... " (coefficient of q^i). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc,char**argv){
  int N=atoi(argv[1]); const char*mode=argv[2];
  u64 full=(1ULL<<N)-1, L[64],R[64];
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=r;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  enum {INV,AEXC,AFIX,ALRMAX,TDES,TMAJ,TEXC,TLRMAX,TPK,ADES,AMAJ,ADESLAST,APK} md;
  const char*names[]={"inv","a_exc","a_fix","a_lrmax","t_des","t_maj","t_exc","t_lrmax","t_pk","a_des","a_maj","a_deslast","a_pk"};
  int found=-1; for(int i=0;i<13;i++) if(!strcmp(mode,names[i])) found=i;
  if(found<0){fprintf(stderr,"unknown mode\n");return 1;} md=found;
  int D = (md==INV||md==TMAJ||md==AMAJ) ? N*(N-1)/2+1 : N+1;
  if(md<=TPK){
    u64 *g=calloc((full+1)*(u64)D,8); if(!g){fprintf(stderr,"oom\n");return 1;}
    g[0]=1;
    for(u64 S=0;S<full;S++){ u64*src=g+S*D; int hi=-1; for(int i=D-1;i>=0;i--)if(src[i]){hi=i;break;} if(hi<0)continue;
      int k=__builtin_popcountll(S); int top=S?64-__builtin_clzll(S):0;
      for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
        int inc=0;
        switch(md){
          case INV: inc=__builtin_popcountll(S>>m); break;
          case AEXC: inc=(m>k+1); break;
          case AFIX: inc=(m==k+1); break;
          case ALRMAX: inc=(m>top); break;
          case TDES: inc=(m<N && (S>>m&1)); break;
          case TMAJ: inc=(m<N && (S>>m&1))?m:0; break;
          case TEXC: inc=(k+1>m); break;
          case TLRMAX: inc=((S&(b-1))==(b-1)); break;
          case TPK: inc=(m>1&&m<N&&(S>>m&1)&&(S>>(m-2)&1)); break;
          default: break; }
        u64*dst=g+(S|b)*D; for(int i=0;i<=hi;i++) dst[i+inc]+=src[i]; } }
    printf("%d %s",N,mode); for(int i=0;i<D;i++)printf(" %llu",(unsigned long long)g[full*D+i]); printf("\n");
  } else if(md!=APK){
    u64 *g=calloc((full+1)*N*(u64)D,8); if(!g){fprintf(stderr,"oom\n");return 1;}
    for(int m=1;m<=N;m++) g[((1ULL<<(m-1))*N+(m-1))*D]=1;
    for(u64 S=1;S<full;S++){ int k=__builtin_popcountll(S);
      for(int l=0;l<N;l++){ if(!(S>>l&1))continue;
      u64*src=g+(S*N+l)*D; int hi=-1; for(int i=D-1;i>=0;i--)if(src[i]){hi=i;break;} if(hi<0)continue;
      for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
        int inc=(l+1>m); if(md==AMAJ) inc*=k;
        u64*dst=g+((S|b)*N+(m-1))*D; for(int i=0;i<=hi;i++) dst[i+inc]+=src[i]; } } }
    if(md==ADESLAST){
      for(int l=0;l<N;l++){ printf("%d a_deslast %d",N,l+1); for(int i=0;i<D;i++)printf(" %llu",(unsigned long long)g[(full*N+l)*D+i]); printf("\n"); }
    } else {
      u64 *res=calloc(D,8);
      for(int l=0;l<N;l++) for(int i=0;i<D;i++) res[i]+=g[(full*N+l)*D+i];
      printf("%d %s",N,mode); for(int i=0;i<D;i++)printf(" %llu",(unsigned long long)res[i]); printf("\n");
    }
  } else {
    u64 *g=calloc((full+1)*N*2*(u64)D,8); if(!g){fprintf(stderr,"oom\n");return 1;}
    for(int m=1;m<=N;m++) g[(((1ULL<<(m-1))*N+(m-1))*2)*D]=1;
    for(u64 S=1;S<full;S++) for(int l=0;l<N;l++){ if(!(S>>l&1))continue;
      for(int up=0;up<2;up++){
      u64*src=g+((S*N+l)*2+up)*D; int hi=-1; for(int i=D-1;i>=0;i--)if(src[i]){hi=i;break;} if(hi<0)continue;
      for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
        int desc=(l+1>m); int inc=(up&&desc);
        u64*dst=g+((((S|b)*N+(m-1))*2)+(desc?0:1))*D; for(int i=0;i<=hi;i++) dst[i+inc]+=src[i]; } } }
    u64 *res=calloc(D,8);
    for(int l=0;l<N;l++) for(int up=0;up<2;up++) for(int i=0;i<D;i++) res[i]+=g[((full*N+l)*2+up)*D+i];
    printf("%d %s",N,mode); for(int i=0;i<D;i++)printf(" %llu",(unsigned long long)res[i]); printf("\n");
  }
  return 0;
}
