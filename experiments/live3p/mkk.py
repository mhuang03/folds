# generate live3k.c (Theorem G after up to k extra valid steps) from live3.c
src = open('live3.c').read()
src = src.replace("static int isdead", "static int gk(u64 S,int k){ if(inwardG(S))return 1; if(!k)return 0; for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0&&gk(S|1ull<<(m-1),k-1))return 1;} return 0;}\nstatic int isdead")
src = src.replace('int w=witness(B);', 'int kk=-1; for(int k=1;k<=3;k++) if(gk(B,k)){kk=k;break;} hist[kk+1]++; if(verbose>0&&kk<0)printf("noGk %d %d %d %d\\n",N,a,b,c);\n      int w=witness(B);')
src = src.replace('static unsigned char seen', 'static int hist[10];\nstatic unsigned char seen')
i = src.rindex("  return 0;\n}\n"); src = src[:i] + '  printf("hist none=%d k1=%d k2=%d k3=%d\\n",hist[0],hist[2],hist[3],hist[4]);\n  return 0;\n}\n'
src = src.replace('if(verbose)printf("nonG', 'if(verbose>1)printf("nonG')
open('live3k.c', 'w').write(src)
