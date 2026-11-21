// Characteristic-zero necessary condition for star 4-lists on mu_N:
// kappa^3 = prod_{e in R} r_x(e) * prod_{p in shared triple} r_x(p), r_x(e)=(x0-e)/(x-e), must be a cube in Q(zeta_N).
// Tested modulo NQ primes q = 1 mod lcm(N,3) via cubic residue characters.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>
typedef uint64_t u64;
static int N,H; const int NQ=14;
static uint8_t chi[NQ][64][64]; // cubic character class (0,1,2) of zeta^a - zeta^b mod q
static u64 rotl(u64 m,int r){u64 M=(N==64)?~0ull:((1ull<<N)-1); r%=N; if(!r)return m; return ((m<<r)|(m>>(N-r)))&M;}
static u64 rev(u64 m){u64 r=0;for(int i=0;i<N;i++) if(m>>i&1) r|=1ull<<((N-i)%N);return r;}
static bool canon(u64 m){u64 v=rev(m);for(int r=0;r<N;r++){if(rotl(m,r)<m||rotl(v,r)<m)return false;}return true;}
static bool isprime(int n){if(n<2)return false;for(int d=2;(long)d*d<=n;d++)if(n%d==0)return false;return true;}
static long pw(long a,long e,long q){long r=1;a%=q;while(e){if(e&1)r=r*a%q;a=a*a%q;e>>=1;}return r;}
std::mutex mu; std::atomic<long> cnt(0), nT(0);
int main(int argc,char**argv){
  N=atoi(argv[1]); H=N/4; int nth=atoi(argv[2]);
  int step=(N%3==0)?N:3*N; int q=1;
  for(int i=0;i<NQ;i++){ do{q+=step;}while(!isprime(q));
    int g=2; for(;;g++){bool ok=true; int m=q-1; for(int d=2;d<=m;d++) if(m%d==0){ if(pw(g,(q-1)/d,q)==1){ok=false;break;} while(m%d==0)m/=d; } if(ok)break;}
    std::vector<int> ind(q); long v=1; for(int e=0;e<q-1;e++){ind[v]=e;v=v*g%q;}
    long z=pw(g,(q-1)/N,q); std::vector<long> zp(N); zp[0]=1; for(int a=1;a<N;a++)zp[a]=zp[a-1]*z%q;
    for(int a=0;a<N;a++)for(int b=0;b<N;b++) chi[i][a][b]= a==b?0: ind[((zp[a]-zp[b])%q+q)%q]%3;
    fprintf(stderr,"q=%d ",q);
  }
  fprintf(stderr,"\n");
  std::vector<u64> Ts; { std::vector<int> idx(H); for(int i=0;i<H;i++)idx[i]=i;
    while(true){ u64 m=0; for(int i:idx)m|=1ull<<i; if(canon(m))Ts.push_back(m);
      int i=H-1; while(i>=1&&idx[i]==N-H+i)i--; if(i<1)break; idx[i]++; for(int j=i+1;j<H;j++)idx[j]=idx[j-1]+1; } }
  fprintf(stderr,"N=%d canonical T: %zu\n",N,Ts.size());
  std::atomic<size_t> next(0);
  std::vector<std::thread> th;
  for(int w=0;w<nth;w++) th.emplace_back([&]{
    for(;;){ size_t ti=next++; if(ti>=Ts.size())break; u64 T=Ts[ti];
      int t[64],R[64],nt=0,nr=0; for(int i=0;i<N;i++){ if(T>>i&1)t[nt++]=i; else R[nr++]=i; }
      // per q: per p in R: trit vector over x in T\{x0}, packed 2 bits per x into u64 (nt-1 <= 15 -> 30 bits)
      // we use plain arrays for clarity
      static thread_local std::vector<uint8_t> d; d.assign((size_t)NQ*nr*(nt-1),0);
      uint8_t base[NQ][16];
      for(int i=0;i<NQ;i++) for(int xi=1;xi<nt;xi++){ int s=0; for(int r=0;r<nr;r++){ int v=(chi[i][t[0]][R[r]]+3-chi[i][t[xi]][R[r]])%3; d[((size_t)i*nr+r)*(nt-1)+xi-1]=v; s+=v;} base[i][xi-1]=s%3; }
      for(int a=0;a<nr;a++)for(int b=a+1;b<nr;b++)for(int c=b+1;c<nr;c++){
        bool ok=true;
        for(int i=0;i<NQ&&ok;i++){ const uint8_t*da=&d[((size_t)i*nr+a)*(nt-1)],*db=&d[((size_t)i*nr+b)*(nt-1)],*dc=&d[((size_t)i*nr+c)*(nt-1)];
          for(int xi=0;xi<nt-1;xi++) if((base[i][xi]+da[xi]+db[xi]+dc[xi])%3){ok=false;break;} }
        if(ok){ cnt++; std::lock_guard<std::mutex> l(mu); printf("CAND T=%016llx shared=%d,%d,%d\n",(unsigned long long)T,R[a],R[b],R[c]); fflush(stdout);} }
      nT++;
    }});
  for(auto&x:th)x.join();
  printf("DONE N=%d T=%zu candidates=%ld\n",N,Ts.size(),cnt.load());
}
