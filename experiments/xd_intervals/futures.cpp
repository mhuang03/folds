// How many catalytic parameters does an insertion / deletion scheme need?
//
// A scheme is a deletion map D : S_N -> S_{N-s} (delete s fixed panels and standardise the
// times).  It turns the set of all time words into a generating tree: every word of size N
// has exactly one parent of size N-s.  A node is "accepting" if it is a valid
// (semi-symmetric) sequence of its own size.  a(N) = number of accepting nodes of size N.
//
// A generating-tree rewriting rule (ECO system) with labels exists iff the labels refine the
// COUNTING BISIMULATION: two nodes of the same size are equivalent iff they are both
// accepting or both not, and their children can be matched class by class.  We compute this
// equivalence on the tree truncated at size Tmax, bottom up (nodes without accepting
// descendants of size <= Tmax, and which are not accepting themselves, are dropped: they form
// one dead class).  The number of classes at size N for look-ahead Tmax is a LOWER bound for
// the number of labels of any ECO system for this scheme (it increases with Tmax).
//
// usage: futures scheme Tmax        scheme in: ends mid2 mid1 last last2
//   ends : delete panels 1 and N                 (step 2)
//   mid2 : delete panels ceil(N/2), ceil(N/2)+1  (step 2)
//   mid1 : delete panel floor(N/2)+1             (step 1)
//   last : delete panel N                        (step 1)
//   last2: delete panels N-1, N                  (step 2)
// output per size N: live nodes, accepting nodes (= a(N)), classes, classes among accepting,
//   distinct numbers of accepting children (the coarsest one-step statistic).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <string>
using namespace std;
typedef uint64_t u64;
typedef unsigned __int128 u128;
static int Ncur; static u64 Lm[20],Rm[20]; static vector<u64>*outv; static int tt[20];
static void dfs(u64 S,int k){
  if(k==Ncur){ u64 c=0; for(int m=0;m<Ncur;m++)c|=(u64)tt[m]<<(4*m); outv->push_back(c); return; }
  for(int m=0;m<Ncur;m++){ u64 b=1ULL<<m; if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])){ tt[m]=k; dfs(S|b,k+1);} }
}
static void enumValid(int N,vector<u64>&v){
  Ncur=N; outv=&v; v.clear();
  for(int m=1;m<=N;m++){ int r=min(m-1,N-m); Lm[m-1]=Rm[m-1]=0;
    for(int d=1;d<=r;d++){ Lm[m-1]|=1ULL<<(m-d-1); Rm[m-1]|=1ULL<<(m+d-1);} }
  dfs(0,0); sort(v.begin(),v.end());
}
static string scheme;
static int step(){ return (scheme=="mid1"||scheme=="last")?1:2; }
static u64 parent(u64 c,int N){
  int del[2]; int nd=step();
  if(scheme=="ends"){del[0]=0;del[1]=N-1;}
  else if(scheme=="mid2"){del[0]=(N+1)/2-1;del[1]=(N+1)/2;}
  else if(scheme=="mid1"){del[0]=N/2;}
  else if(scheme=="last"){del[0]=N-1;}
  else if(scheme=="last2"){del[0]=N-2;del[1]=N-1;}
  else { fprintf(stderr,"bad scheme\n"); exit(1); }
  int t[16]; for(int m=0;m<N;m++)t[m]=(c>>(4*m))&15;
  int td[2]; for(int i=0;i<nd;i++)td[i]=t[del[i]];
  u64 o=0; int j=0;
  for(int m=0;m<N;m++){ bool isd=false; for(int i=0;i<nd;i++) if(m==del[i])isd=true; if(isd)continue;
    int x=t[m]; int y=x; for(int i=0;i<nd;i++) if(td[i]<x)y--;
    o|=(u64)y<<(4*j); j++; }
  return o;
}
static inline u128 mix(u128 h,u64 x){ h^=x; h*=(((u128)0x9E3779B97F4A7C15ULL)<<64|0xC2B2AE3D27D4EB4FULL); h^=h>>67; return h; }
struct Pair{ u64 par; uint32_t cls; uint8_t acc; };
int main(int argc,char**argv){
  scheme=argv[1]; int Tmax=atoi(argv[2]); int s=step();
  vector<u64> nodes; vector<uint32_t> cls; vector<uint8_t> nacc;   // current level (sorted codes)
  printf("# scheme %s  Tmax %d\n# N  live  accepting  classes  classes(accepting)  distinct#acc.children\n",scheme.c_str(),Tmax);
  for(int N=Tmax;N>=1;N-=s){
    vector<u64> valid; enumValid(N,valid);
    // children info: pairs (parent, class) from the level N+s
    vector<Pair> pr; pr.reserve(nodes.size());
    if(N<Tmax) for(size_t i=0;i<nodes.size();i++) pr.push_back({parent(nodes[i],N+s),cls[i],nacc[i]});
    sort(pr.begin(),pr.end(),[](const Pair&a,const Pair&b){return a.par<b.par||(a.par==b.par&&a.cls<b.cls);});
    vector<u64> nn; nn.reserve(pr.size()/2+valid.size());
    { size_t i=0,j=0; while(i<pr.size()||j<valid.size()){ u64 x;
        if(j>=valid.size()||(i<pr.size()&&pr[i].par<=valid[j])) x=pr[i].par; else x=valid[j];
        nn.push_back(x); while(i<pr.size()&&pr[i].par==x)i++; if(j<valid.size()&&valid[j]==x)j++; } }
    vector<u128> sig(nn.size()); vector<uint8_t> acc(nn.size()); vector<uint32_t> nchild(nn.size());
    { size_t i=0,j=0; for(size_t q=0;q<nn.size();q++){ u64 x=nn[q]; u128 h=0x1234567;
        bool a=(j<valid.size()&&valid[j]==x); if(a)j++; acc[q]=a; h=mix(h,a?77:99);
        uint32_t ac=0;
        while(i<pr.size()&&pr[i].par==x){ h=mix(h,pr[i].cls+1000); ac+=pr[i].acc; i++; }
        sig[q]=h; nchild[q]=ac; } }
    // class ids
    vector<pair<u128,size_t>> o(nn.size()); for(size_t q=0;q<nn.size();q++)o[q]={sig[q],q};
    sort(o.begin(),o.end());
    vector<uint32_t> nc(nn.size()); uint32_t id=0; size_t accCls=0;
    for(size_t q=0;q<o.size();q++){ if(q&&o[q].first!=o[q-1].first)id++; nc[o[q].second]=id; }
    size_t ncls=nn.empty()?0:id+1;
    { vector<uint32_t> a; for(size_t q=0;q<nn.size();q++) if(acc[q])a.push_back(nc[q]); sort(a.begin(),a.end()); accCls=unique(a.begin(),a.end())-a.begin(); }
    size_t dch; { vector<uint32_t> a; for(size_t q=0;q<nn.size();q++) if(acc[q])a.push_back(nchild[q]); sort(a.begin(),a.end()); dch=unique(a.begin(),a.end())-a.begin(); }
    printf("%d %zu %zu %zu %zu %zu\n",N,nn.size(),valid.size(),ncls,accCls,dch); fflush(stdout);
    nodes.swap(nn); cls.swap(nc); nacc.swap(acc);
  }
  return 0;
}
