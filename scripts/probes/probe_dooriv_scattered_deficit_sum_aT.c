#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef long long ll;
ll mulmod(ll a, ll b, ll m){ return (ll)((__int128)a*b % m); }
ll powmod(ll a, ll e, ll m){ ll r=1%m; a%=m; while(e){ if(e&1) r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1;} return r;}
int isprime(ll n){ if(n<2)return 0; for(ll i=2;i*i<=n;i++) if(n%i==0)return 0; return 1;}
ll find_prime(ll n,double beta){ ll t=(ll)pow((double)n,beta); ll p=t-(t%n)+1; if(p<t)p+=n; while(!isprime(p))p+=n; return p;}
ll prim_root(ll p){ ll phi=p-1; ll fac[64]; int nf=0; ll m=phi;
  for(ll d=2;d*d<=m;d++){ if(m%d==0){fac[nf++]=d; while(m%d==0)m/=d;} } if(m>1)fac[nf++]=m;
  for(ll g=2;g<p;g++){ int ok=1; for(int i=0;i<nf;i++) if(powmod(g,phi/fac[i],p)==1){ok=0;break;} if(ok)return g;} return -1;}
int main(int argc,char**argv){
  int a=atoi(argv[1]); double beta=atof(argv[2]);
  ll n=1LL<<a; ll p=find_prime(n,beta); ll g=prim_root(p);
  ll h=powmod(g,(p-1)/n,p); ll *S=malloc(n*sizeof(ll)); ll x=1;
  for(ll i=0;i<n;i++){S[i]=x; x=mulmod(x,h,p);}
  char *seen=calloc(p,1); double best=-1; ll bb=1;
  for(ll b=1;b<p;b++){ if(seen[b])continue;
    for(ll c=0;c<n;c++) seen[mulmod(b,S[c],p)]=1;
    double cr=0,ci=0;
    for(ll c=0;c<n;c++){ double t=2*M_PI*((double)mulmod(b,S[c],p))/p; cr+=cos(t); ci+=sin(t);}
    double v=cr*cr+ci*ci; if(v>best){best=v; bb=b;}
  }
  free(seen);
  int T=0;
  for(int k=0;k<a;k++){ ll order=1LL<<(a-k); if(order<2)break;
    ll hh=powmod(g,(p-1)/order,p); ll half=order/2; (void)half;
    double c0r=0,c0i=0,c1r=0,c1i=0; ll y=1;
    for(ll i=0;i<order;i++){ double t=2*M_PI*((double)mulmod(bb,y,p))/p;
      if(i%2==0){c0r+=cos(t);c0i+=sin(t);} else {c1r+=cos(t);c1i+=sin(t);}
      y=mulmod(y,hh,p);
    }
    double P0=hypot(c0r,c0i),P1=hypot(c1r,c1i),den=P0+P1;
    double rho = den>1e-12 ? hypot(c0r+c1r,c0i+c1i)/den : 1.0;
    if(1.0-rho<=1e-9) T++; else break;
  }
  printf("a=%d n=%lld beta=%.1f p=%lld bstar=%lld T=%d a-T=%d sup=%.4f sup_over_sqrtn=%.4f\n",
         a,n,beta,p,bb,T,a-T,sqrt(best),sqrt(best)/sqrt((double)n));
  return 0;
}
