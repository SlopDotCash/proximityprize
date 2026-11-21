// Exact count of three-split pencils of degree m on mu_N over a small prime field F_p (p = 1 mod N),
// using full discrete logarithms modulo M = p-1 as additive keys.
// For each dihedral-canonical B (|B| = m) and each D (|D| = N-3m) in the complement R:
//   key_j(A) = key_j(C) forces  2*key_j(A) = key_j(R) - key_j(D)  (mod M)  for j = 1..m-1,
// where key_j(S) = sum_{s in S} [ell(b_j - s) - ell(b_0 - s)].  Parity filter, then meet in the middle over R \ D.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <thread>
#include <mutex>
#include <atomic>
typedef uint64_t u64;
static int N,Mdeg,DS; static u64 MOD; static u64 ell[64][64];
static u64 rotl(u64 m,int r){u64 Mk=(N==64)?~0ull:((1ull<<N)-1); r%=N; if(!r)return m; return ((m<<r)|(m>>(N-r)))&Mk;}
static u64 rev(u64 m){u64 r=0;for(int i=0;i<N;i++) if(m>>i&1) r|=1ull<<((N-i)%N);return r;}
static bool canon(u64 m){u64 v=rev(m);for(int r=0;r<N;r++){if(rotl(m,r)<m||rotl(v,r)<m)return false;}return true;}
std::mutex mu; std::atomic<long> cnt(0), surv(0);
struct W{ int R[64],b[64],nr; u64 d[16][64]; u64 tot[16]; uint32_t par[64]; uint32_t ptot; u64 B;
  int Dsel[64];
  void check(u64 Dmask){ // exact: find A in S=R\D, |A|=Mdeg, with 2*key_j(A) = tot_j - key_j(D) for all j
    int S[64],ns=0; u64 s[16]; for(int j=1;j<Mdeg;j++)s[j]=tot[j];
    for(int r=0;r<nr;r++){ if(Dmask>>r&1){ for(int j=1;j<Mdeg;j++) s[j]=(s[j]+MOD-d[j][r])%MOD; } else S[ns++]=r; }
    int h1=ns/2,h2=ns-h1;
    // enumerate halves on coordinate 1, verify the rest
    static thread_local std::vector<std::unordered_multimap<u64,uint32_t>> tabs; tabs.assign(h1+1,{});
    for(uint32_t m=0;m<(1u<<h1);m++){ u64 k=0; for(int i=0;i<h1;i++) if(m>>i&1) k+=d[1][S[i]]; tabs[__builtin_popcount(m)].emplace(k%MOD,m); }
    for(int c=0;c<2;c++){ if(s[1]&1) return; u64 target=(s[1]/2+c*(MOD/2))%MOD;
      for(uint32_t m2=0;m2<(1u<<h2);m2++){ int sz=__builtin_popcount(m2); if(sz>Mdeg||Mdeg-sz>h1) continue; u64 k=0; for(int i=0;i<h2;i++) if(m2>>i&1) k+=d[1][S[h1+i]]; k%=MOD;
        u64 need=(target+MOD-k)%MOD; auto rg=tabs[Mdeg-sz].equal_range(need);
        for(auto it=rg.first;it!=rg.second;++it){ uint32_t m1=it->second; bool ok=true; uint32_t am=0;
          // A must contain S[0] to count unordered {A,C} once
          if(!(m1&1)) continue;
          for(int j=2;j<Mdeg&&ok;j++){ u64 kk=0; for(int i=0;i<h1;i++) if(m1>>i&1) kk+=d[j][S[i]]; for(int i=0;i<h2;i++) if(m2>>i&1) kk+=d[j][S[h1+i]]; kk%=MOD; ok=((2*kk)%MOD==s[j]); (void)am; }
          if(ok){ cnt++; u64 A=0,C=0; for(int i=0;i<h1;i++){ if(m1>>i&1)A|=1ull<<R[S[i]]; else C|=1ull<<R[S[i]]; } for(int i=0;i<h2;i++){ if(m2>>i&1)A|=1ull<<R[S[h1+i]]; else C|=1ull<<R[S[h1+i]]; }
            std::lock_guard<std::mutex> l(mu); printf("PENCIL B=%016llx A=%016llx C=%016llx\n",(unsigned long long)B,(unsigned long long)A,(unsigned long long)C); fflush(stdout);} } } }
  }
  void dfs(int start,int left,uint32_t p,u64 Dmask){
    if(left==0){ if(p==0){ surv++; check(Dmask);} return; }
    for(int i=start;i<=nr-left;i++) dfs(i+1,left-1,p^par[i],Dmask|(1ull<<i));
  }
  void run(u64 Bm){ B=Bm; int nb=0; nr=0; for(int i=0;i<N;i++){ if(Bm>>i&1)b[nb++]=i; else R[nr++]=i; }
    ptot=0; for(int r=0;r<nr;r++)par[r]=0;
    for(int j=1;j<Mdeg;j++){ tot[j]=0; for(int r=0;r<nr;r++){ d[j][r]=(ell[b[j]][R[r]]+MOD-ell[b[0]][R[r]])%MOD; tot[j]=(tot[j]+d[j][r])%MOD; if(d[j][r]&1) par[r]|=1u<<j; } if(tot[j]&1) ptot|=1u<<j; }
    dfs(0,DS,ptot,0);
  }
};
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); unsigned long long md; if(fscanf(f,"%d %llu",&N,&md)!=2)return 1; MOD=md;
  for(int a=0;a<N;a++)for(int c=0;c<N;c++){unsigned long long x; if(fscanf(f,"%llu",&x)!=1)return 1; ell[a][c]=x;}
  Mdeg=atoi(argv[2]); int nth=atoi(argv[3]); DS=N-3*Mdeg;
  std::vector<u64> Bs; { std::vector<int> idx(Mdeg); for(int i=0;i<Mdeg;i++)idx[i]=i;
    while(true){ u64 m=0; for(int i:idx)m|=1ull<<i; if(canon(m))Bs.push_back(m);
      int i=Mdeg-1; while(i>=1&&idx[i]==N-Mdeg+i)i--; if(i<1)break; idx[i]++; for(int j=i+1;j<Mdeg;j++)idx[j]=idx[j-1]+1; } }
  std::atomic<size_t> next(0); std::vector<std::thread> th;
  for(int w=0;w<nth;w++) th.emplace_back([&]{ W wk; for(;;){ size_t i=next++; if(i>=Bs.size())break; wk.run(Bs[i]); }});
  for(auto&x:th)x.join();
  printf("DONE N=%d m=%d p=%llu B-orbits=%zu parity-survivors=%ld pencils=%ld\n",N,Mdeg,(unsigned long long)(MOD+1),Bs.size(),surv.load(),cnt.load());
}
