// Three-split pencils on mu_N in characteristic zero (necessary condition via quadratic characters).
// Monic A,B,C of degree m, pairwise coprime, roots in mu_N, A - lam*B = (1-lam)*C.  D = mu_N \ roots(ABC).
// At each root beta of B:  L_C(beta)^2 (1-lam) L_D(beta) L_B'(beta) beta = N, so
// L_D(beta) L_B'(beta) beta has constant quadratic character over beta in B, modulo every prime q = 1 mod N.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>
typedef uint64_t u64;
static int N,M,DS; const int NQ=16;
static uint8_t chi[NQ][64][64], chiz[NQ][64];
static u64 rotl(u64 m,int r){u64 Mk=(N==64)?~0ull:((1ull<<N)-1); r%=N; if(!r)return m; return ((m<<r)|(m>>(N-r)))&Mk;}
static u64 rev(u64 m){u64 r=0;for(int i=0;i<N;i++) if(m>>i&1) r|=1ull<<((N-i)%N);return r;}
static bool canon(u64 m){u64 v=rev(m);for(int r=0;r<N;r++){if(rotl(m,r)<m||rotl(v,r)<m)return false;}return true;}
static bool isprime(int n){if(n<2)return false;for(int d=2;(long)d*d<=n;d++)if(n%d==0)return false;return true;}
static long pw(long a,long e,long q){long r=1;a%=q;while(e){if(e&1)r=r*a%q;a=a*a%q;e>>=1;}return r;}
std::mutex mu; std::atomic<long> cnt(0);
struct W{ u64 v0[64],v1[64]; int R[64],nr; u64 b0,b1,mask0[8],mask1[8]; u64 B;
  void dfs(int start,int left,u64 a0,u64 a1,u64 Dm){
    if(left==0){ for(int i=0;i<8;i++){u64 x=a0&mask0[i]; if(x&&x!=mask0[i])return; x=a1&mask1[i]; if(x&&x!=mask1[i])return;}
      cnt++; std::lock_guard<std::mutex> l(mu); printf("CAND B=%016llx D=%016llx\n",(unsigned long long)B,(unsigned long long)Dm); fflush(stdout); return;}
    for(int i=start;i<=nr-left;i++) dfs(i+1,left-1,a0^v0[i],a1^v1[i],Dm|(1ull<<R[i]));
  }
  void run(u64 Bm){ B=Bm; int b[64],nb=0; nr=0; for(int i=0;i<N;i++){ if(Bm>>i&1)b[nb++]=i; else R[nr++]=i; }
    b0=b1=0; for(int i=0;i<8;i++){mask0[i]=((1ull<<M)-1)<<(i*M); mask1[i]=mask0[i];}
    for(int r=0;r<nr;r++){v0[r]=v1[r]=0;}
    for(int i=0;i<NQ;i++)for(int j=0;j<M;j++){ int bit=chiz[i][b[j]]; for(int j2=0;j2<M;j2++) if(j2!=j) bit^=chi[i][b[j]][b[j2]];
        u64 pos=1ull<<((i%8)*M+j); if(bit){ if(i<8)b0|=pos; else b1|=pos; }
        for(int r=0;r<nr;r++) if(chi[i][b[j]][R[r]]){ if(i<8)v0[r]|=pos; else v1[r]|=pos; } }
    dfs(0,DS,b0,b1,0);
  }
};
int main(int argc,char**argv){
  N=atoi(argv[1]); M=atoi(argv[2]); int nth=atoi(argv[3]); DS=N-3*M;
  int q=1; for(int i=0;i<NQ;i++){ do{q+=N;}while(!isprime(q));
    int g=2; for(;;g++){bool ok=true; int m=q-1; for(int d=2;d<=m;d++) if(m%d==0){ if(pw(g,(q-1)/d,q)==1){ok=false;break;} while(m%d==0)m/=d; } if(ok)break;}
    std::vector<int> ind(q); long v=1; for(int e=0;e<q-1;e++){ind[v]=e;v=v*g%q;}
    long z=pw(g,(q-1)/N,q); std::vector<long> zp(N); zp[0]=1; for(int a=1;a<N;a++)zp[a]=zp[a-1]*z%q;
    for(int a=0;a<N;a++){ chiz[i][a]=ind[zp[a]]&1; for(int b=0;b<N;b++) chi[i][a][b]= a==b?0: ind[((zp[a]-zp[b])%q+q)%q]&1; } }
  std::vector<u64> Bs; { std::vector<int> idx(M); for(int i=0;i<M;i++)idx[i]=i;
    while(true){ u64 m=0; for(int i:idx)m|=1ull<<i; if(canon(m))Bs.push_back(m);
      int i=M-1; while(i>=1&&idx[i]==N-M+i)i--; if(i<1)break; idx[i]++; for(int j=i+1;j<M;j++)idx[j]=idx[j-1]+1; } }
  fprintf(stderr,"N=%d m=%d |D|=%d canonical B: %zu\n",N,M,DS,Bs.size());
  std::atomic<size_t> next(0); std::vector<std::thread> th;
  for(int w=0;w<nth;w++) th.emplace_back([&]{ W wk; for(;;){ size_t i=next++; if(i>=Bs.size())break; wk.run(Bs[i]); }});
  for(auto&x:th)x.join();
  printf("DONE N=%d m=%d B-orbits=%zu candidates=%ld\n",N,M,Bs.size(),cnt.load());
}
