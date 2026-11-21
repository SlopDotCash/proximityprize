// 4-cycle pattern: Q0 (a = b-1 points), two disjoint b-sets A, C in the complement R with L_A(x)/L_C(x) constant on Q0.
// D = R \ (A u C) has |R| - 2b points.  key_x(S) = L_S(x0)/L_S(x).  key(A)=key(C) => key_x(R)/key_x(D) is a square.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>
typedef uint64_t u64;
static int N,A_,DS; const int NQ=16;
static uint8_t chi[NQ][64][64];
static u64 rotl(u64 m,int r){u64 Mk=(N==64)?~0ull:((1ull<<N)-1); r%=N; if(!r)return m; return ((m<<r)|(m>>(N-r)))&Mk;}
static u64 rev(u64 m){u64 r=0;for(int i=0;i<N;i++) if(m>>i&1) r|=1ull<<((N-i)%N);return r;}
static bool canon(u64 m){u64 v=rev(m);for(int r=0;r<N;r++){if(rotl(m,r)<m||rotl(v,r)<m)return false;}return true;}
static bool isprime(int n){if(n<2)return false;for(int d=2;(long)d*d<=n;d++)if(n%d==0)return false;return true;}
static long pw(long a,long e,long q){long r=1;a%=q;while(e){if(e&1)r=r*a%q;a=a*a%q;e>>=1;}return r;}
std::mutex mu; std::atomic<long> cnt(0);
struct W{ u64 v0[64],v1[64]; int R[64],nr; u64 T;
  void dfs(int start,int left,u64 a0,u64 a1,u64 Dm){
    if(left==0){ if(a0|a1)return; cnt++; std::lock_guard<std::mutex> l(mu); printf("CAND B=%016llx D=%016llx\n",(unsigned long long)T,(unsigned long long)Dm); return;}
    for(int i=start;i<=nr-left;i++) dfs(i+1,left-1,a0^v0[i],a1^v1[i],Dm|(1ull<<R[i]));
  }
  void run(u64 Tm){ T=Tm; int t[64],nt=0; nr=0; for(int i=0;i<N;i++){ if(Tm>>i&1)t[nt++]=i; else R[nr++]=i; }
    u64 b0=0,b1=0; for(int r=0;r<nr;r++){v0[r]=v1[r]=0;}
    for(int i=0;i<NQ;i++)for(int j=1;j<nt;j++){ u64 pos=1ull<<((i%8)*(nt-1)+j-1); int bit=0;
        for(int r=0;r<nr;r++){ int c=chi[i][t[0]][R[r]]^chi[i][t[j]][R[r]]; bit^=c; if(c){ if(i<8)v0[r]|=pos; else v1[r]|=pos; } }
        if(bit){ if(i<8)b0|=pos; else b1|=pos; } }
    dfs(0,DS,b0,b1,0);
  }
};
int main(int argc,char**argv){
  N=atoi(argv[1]); int b=N/4; A_=b-1; int nth=atoi(argv[2]); DS=N-A_-2*b;
  int q=1; for(int i=0;i<NQ;i++){ do{q+=N;}while(!isprime(q));
    int g=2; for(;;g++){bool ok=true; int m=q-1; for(int d=2;d<=m;d++) if(m%d==0){ if(pw(g,(q-1)/d,q)==1){ok=false;break;} while(m%d==0)m/=d; } if(ok)break;}
    std::vector<int> ind(q); long v=1; for(int e=0;e<q-1;e++){ind[v]=e;v=v*g%q;}
    long z=pw(g,(q-1)/N,q); std::vector<long> zp(N); zp[0]=1; for(int a=1;a<N;a++)zp[a]=zp[a-1]*z%q;
    for(int a=0;a<N;a++) for(int c=0;c<N;c++) chi[i][a][c]= a==c?0: ind[((zp[a]-zp[c])%q+q)%q]&1; }
  std::vector<u64> Ts; { int M=A_; std::vector<int> idx(M); for(int i=0;i<M;i++)idx[i]=i;
    while(true){ u64 m=0; for(int i:idx)m|=1ull<<i; if(canon(m))Ts.push_back(m);
      int i=M-1; while(i>=1&&idx[i]==N-M+i)i--; if(i<1)break; idx[i]++; for(int j=i+1;j<M;j++)idx[j]=idx[j-1]+1; } }
  fprintf(stderr,"N=%d |Q0|=%d |D|=%d canonical Q0: %zu\n",N,A_,DS,Ts.size());
  std::atomic<size_t> next(0); std::vector<std::thread> th;
  for(int w=0;w<nth;w++) th.emplace_back([&]{ W wk; for(;;){ size_t i=next++; if(i>=Ts.size())break; wk.run(Ts[i]); }});
  for(auto&x:th)x.join();
  printf("DONE N=%d Q0-orbits=%zu candidates=%ld\n",N,Ts.size(),cnt.load());
}
