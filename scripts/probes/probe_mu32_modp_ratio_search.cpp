// Exact search modulo a fixed prime p on mu_N via additive fingerprints ell(zeta^a - zeta^b) in Z/2^64
// (discrete logarithm in the 2-Sylow subgroup of F_p^*, table from the companion Python script).
// For every dihedral-canonical T (|T| = tsz) and every pair of disjoint subsets A, C of the complement with |A|=|C|=ssz:
// L_A(x)/L_C(x) constant on T  ==>  sum_{a in A} d_j[a] = sum_{c in C} d_j[c] for all j, d_j[r] = ell(t_j - r) - ell(t_0 - r).
// Prints every pair passing all tsz-1 fingerprint equalities (to be verified exactly in F_p).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <thread>
#include <mutex>
#include <atomic>
typedef uint64_t u64; typedef unsigned __int128 u128; static u128 MASK;
static int N,TS,SS; static u128 ell[64][64];
static u64 rotl(u64 m,int r){u64 Mk=(N==64)?~0ull:((1ull<<N)-1); r%=N; if(!r)return m; return ((m<<r)|(m>>(N-r)))&Mk;}
static u64 rev(u64 m){u64 r=0;for(int i=0;i<N;i++) if(m>>i&1) r|=1ull<<((N-i)%N);return r;}
static bool canon(u64 m){u64 v=rev(m);for(int r=0;r<N;r++){if(rotl(m,r)<m||rotl(v,r)<m)return false;}return true;}
struct E{u128 k1; u64 k2; uint32_t m; bool operator<(const E&o)const{return k1!=o.k1?k1<o.k1:(k2!=o.k2?k2<o.k2:m<o.m);}};
std::mutex mu; std::atomic<long> cnt(0),done(0);
struct W{ std::vector<E> v; int R[64],t[64],nr,nt; u128 d[16][64]; u64 T;
  void dfs(int start,int left,u128 a,u128 b,uint32_t mask){
    if(left==0){v.push_back({a&MASK,(u64)(b&MASK)^(u64)((b&MASK)>>64),mask});return;}
    for(int i=start;i<=nr-left;i++) dfs(i+1,left-1,a+d[1][i],b+d[2][i],mask|(1u<<i));
  }
  void run(u64 Tm){ T=Tm; nr=nt=0; for(int i=0;i<N;i++){ if(Tm>>i&1)t[nt++]=i; else R[nr++]=i; }
    for(int j=1;j<nt;j++)for(int r=0;r<nr;r++) d[j][r]=(ell[t[j]][R[r]]-ell[t[0]][R[r]])&MASK;
    v.clear(); dfs(0,SS,0,0,0); std::sort(v.begin(),v.end());
    for(size_t i=0;i<v.size();){ size_t j=i+1; while(j<v.size()&&v[j].k1==v[i].k1&&v[j].k2==v[i].k2)j++;
      for(size_t a=i;a<j;a++)for(size_t b=a+1;b<j;b++) if(!(v[a].m&v[b].m)){
        bool ok=true; for(int q=3;q<nt&&ok;q++){u128 s1=0,s2=0; for(int r=0;r<nr;r++){ if(v[a].m>>r&1)s1+=d[q][r]; if(v[b].m>>r&1)s2+=d[q][r]; } ok=((s1&MASK)==(s2&MASK));}
        if(ok){ cnt++; u64 A=0,C=0; for(int r=0;r<nr;r++){ if(v[a].m>>r&1)A|=1ull<<R[r]; if(v[b].m>>r&1)C|=1ull<<R[r]; }
          std::lock_guard<std::mutex> l(mu); printf("HIT T=%016llx A=%016llx C=%016llx\n",(unsigned long long)T,(unsigned long long)A,(unsigned long long)C); fflush(stdout);} }
      i=j; }
  }
};
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int eb; if(fscanf(f,"%d %d",&N,&eb)!=2)return 1; MASK=(eb>=128)?~(u128)0:(((u128)1<<eb)-1); for(int a=0;a<N;a++)for(int b=0;b<N;b++){char buf[64]; if(fscanf(f,"%63s",buf)!=1)return 1; u128 x=0; for(char*q=buf;*q;q++)x=x*10+(*q-'0'); ell[a][b]=x;}
  TS=atoi(argv[2]); SS=atoi(argv[3]); int nth=atoi(argv[4]);
  std::vector<u64> Ts; { std::vector<int> idx(TS); for(int i=0;i<TS;i++)idx[i]=i;
    while(true){ u64 m=0; for(int i:idx)m|=1ull<<i; if(canon(m))Ts.push_back(m);
      int i=TS-1; while(i>=1&&idx[i]==N-TS+i)i--; if(i<1)break; idx[i]++; for(int j=i+1;j<TS;j++)idx[j]=idx[j-1]+1; } }
  fprintf(stderr,"N=%d |T|=%d subset size %d canonical T: %zu\n",N,TS,SS,Ts.size());
  std::atomic<size_t> next(0); std::vector<std::thread> th;
  for(int w=0;w<nth;w++) th.emplace_back([&]{ W wk; for(;;){ size_t i=next++; if(i>=Ts.size())break; wk.run(Ts[i]); long dd=++done; if(dd%5000==0){fprintf(stderr,"progress %ld/%zu hits %ld\n",dd,Ts.size(),cnt.load());} }});
  for(auto&x:th)x.join();
  printf("DONE N=%d |T|=%d size=%d T-orbits=%zu hits=%ld\n",N,TS,SS,Ts.size(),cnt.load());
}
