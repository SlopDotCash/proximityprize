// Fast exact floor-bad scanner via vanishing-polynomial reduction (#466 lane W3).
//
// Same predicate as floor_scan_exact.c (KB bad-prime-localization):
//   p in B(n) iff some adjacent 7th-type pattern A is realizable over F_p:
//     rank[M_A] == rank[M_A | b_A],
//     M_A = [x^0 .. x^{n/2-1} | -x^{n/2}]_{x in A},  b_A = x^{3n/4}.
//
// EQUIVALENT POLYNOMIAL TEST (the speedup):
//   Solutions (c_0..c_{n/2-1}, c) of M_A c = b_A correspond exactly to polynomials
//     F(x) = x^{3n/4} + c*x^{n/2} - sum_{k<n/2} c_k x^k
//   vanishing on all of A. Since the points of A are DISTINCT (powers of an element of
//   exact order n, p == 1 mod n), F vanishes on A iff V_A | F where
//   V_A(x) = prod_{a in A}(x-a), monic of degree |A|.
//   Let r(x) = x^{3n/4} mod V_A  (deg r <= |A|-1).  The free coefficient c kills the
//   x^{n/2} coefficient of r, and coefficients below n/2 are absorbed by the c_k.
//   =>  A realizable  <=>  r_k = 0 for all k in [n/2+1, |A|-1].
//   (|A| = 5n/8, so that is n/8 - 1 conditions: n=16 -> 1, n=32 -> 3, n=64 -> 7.)
//
// Validation contract: must reproduce floor_scan_exact.c EXACTLY:
//   n=16: p=17 -> 160 realizable of 2304, p in {97,113,193,241,257} -> 0.
//   n=32: p=97 -> BAD, all other primes == 1 mod 32 up to 1249 -> 0 of 15,366,400.
//
// Modes:
//   full   n p              full enumeration, exact realizable count
//   sc     n p maxpat       short-circuit enumeration (stop at first hit), budgeted
//   sample n p N seed       N uniform random patterns, count realizable
//   dump   n p              full enumeration, print every realizable pattern
//   anneal n p evals seed   greedy random-restart local search on E = #violated
//                           conditions (0 => realizable found => p is floor-BAD)
//   testfile n p file       test explicit patterns (lines of |A| space-sep indices)
//   mitm n p astart aend rr EXACT full decision via meet-in-the-middle:
//                           enumerate MINORITY side only; majority side is decided by
//                           agreement-decoding (see below). rr=1: rotation-reduce
//                           (c0=0 + diagonal-shift canonical pairs; valid for decision
//                           because A -> g0*A rescales columns of M_A and b_A, so
//                           realizability is rotation invariant). rr=0: enumerate all
//                           c0 and all pairs (calibration mode; prints every hit).
//
// MITM REDUCTION (exact, no heuristic):
//   Realizable <=> exists monic Q deg n/8 with V_A*Q = x^{3n/4} + c x^{n/2} + L.
//   Divide x^{3n/4} = V_min*q + r1 (q monic, deg 3n/8). Then
//     V_min*(V_maj*Q - q) = c x^{n/2} + L + r1, RHS deg <= n/2,
//   forces deg(V_maj*Q - q) <= n/8. Writing g := q - V_maj*Q (deg <= n/8):
//   at the majority points V_maj = 0, so g = q there; conversely g deg <= n/8
//   agreeing with q on all majority points gives Q := (q-g)/V_maj monic deg n/8.
//   =>  A realizable <=> q agrees with SOME poly of degree <= n/8 on all chosen
//       majority points (n/8 per majority class).
//   Decoding sweep (complete): with K = n/8, m = n/4 per class domain:
//     case (i)  |S0|>=K+1: g determined by a (K+1)-subset T of class mj0 domain;
//     case (ii) |S0|=K: g determined by the K-subset + 1 point of mj1.
//   Enumerate all C(m,K+1) + C(m,K)*m interpolants, count agreements per class,
//   hit iff >=K in each. Covers every realizable majority profile.
//
// Pattern space (same as floor_scan_exact.c): m = n/4 classes mod 4; two adjacent
// minority classes contribute agr_min = m - m/4 points each, two majority classes
// agr_maj = m - m/2 points each; 4 rotations c0.
// Count = 4 * C(m,agr_min)^2 * C(m,agr_maj)^2.
//   n=16: 4*4^2*6^2 = 2304    n=32: 4*28^2*70^2 = 15,366,400
//   n=64: 4*1820^2*12870^2 = 2,194,657,046,760,000 (~2.19e15)  <- full scan INFEASIBLE
//
// All primes used are < 2^20, so products < 2^40 accumulate safely in uint64
// across <= 64 terms before a single final reduction.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long u64;
typedef long long ll;
static u64 P;

static u64 pw(u64 a, u64 e){ a%=P; u64 r=1; while(e){ if(e&1) r=r*a%P; a=a*a%P; e>>=1;} return r; }

static int isprime(u64 n){ if(n<2)return 0; for(u64 d=2;d*d<=n;d++) if(n%d==0) return 0; return 1; }
static u64 generator(u64 p){
    u64 m=p-1, fac[64]; int nf=0; u64 mm=m;
    for(u64 d=2; d*d<=mm; d++){ if(mm%d==0){ fac[nf++]=d; while(mm%d==0)mm/=d; } }
    if(mm>1) fac[nf++]=mm;
    for(u64 h=2; h<p; h++){ int ok=1; for(int i=0;i<nf;i++){ if(pw(h,(p-1)/fac[i])==1){ok=0;break;} } if(ok) return h; }
    return 0;
}

// ---- combinations ----
static ll binom(int n,int k){ ll r=1; for(int i=0;i<k;i++){ r=r*(n-i)/(i+1);} return r; }
static int build_combos(int setsize, int k, int *combos /* cnt x k */){
    int idx[16]; for(int i=0;i<k;i++) idx[i]=i; int cnt=0;
    while(1){
        for(int i=0;i<k;i++) combos[cnt*k+i]=idx[i];
        cnt++;
        int i=k-1; while(i>=0 && idx[i]==setsize-k+i) i--;
        if(i<0) break;
        idx[i]++; for(int j=i+1;j<k;j++) idx[j]=idx[j-1]+1;
    }
    return cnt;
}

// ---- poly ops mod P (coeff arrays, low-to-high, all coeffs < P < 2^20) ----
// dst (deg da+db) = a (deg da) * b (deg db); lazy accumulation, one mod at end.
static void pmul(const u64*a,int da,const u64*b,int db,u64*dst){
    for(int i=0;i<=da+db;i++) dst[i]=0;
    for(int i=0;i<=da;i++){ u64 ai=a[i]; if(!ai) continue;
        for(int j=0;j<=db;j++) dst[i+j]+=ai*b[j]; }
    for(int i=0;i<=da+db;i++) dst[i]%=P;
}

// global geometry
static int N_, m_, half_, deg34_, agrmin_, agrmaj_, Asz_, ncond_;
static u64 *Xpow;               // Xpow[j] = g0^j, j=0..n-1
static int cls[4][16];          // class member domain indices
static int *cmin, *cmaj;        // combo tables
static int nmin_, nmaj_;
static u64 *BminP, *BmajP;      // block polys: BminP[(c*nmin+a)*(agrmin+1)+k]

static void build_blocks(void){
    // block poly for class c, combo t: prod over chosen j in class c of (x - Xpow[j])
    for(int c=0;c<4;c++){
        for(int t=0;t<nmin_;t++){
            u64 *B=&BminP[((u64)(c*nmin_+t))*(agrmin_+1)];
            B[0]=1; int deg=0;
            for(int i=0;i<agrmin_;i++){
                u64 root=Xpow[cls[c][cmin[t*agrmin_+i]]];
                // multiply by (x - root)
                B[deg+1]=B[deg];
                for(int k=deg;k>=1;k--) B[k]=(B[k-1]+ (P-root)*B[k])%P;
                B[0]=(P-root)*B[0]%P;
                deg++;
            }
        }
        for(int t=0;t<nmaj_;t++){
            u64 *B=&BmajP[((u64)(c*nmaj_+t))*(agrmaj_+1)];
            B[0]=1; int deg=0;
            for(int i=0;i<agrmaj_;i++){
                u64 root=Xpow[cls[c][cmaj[t*agrmaj_+i]]];
                B[deg+1]=B[deg];
                for(int k=deg;k>=1;k--) B[k]=(B[k-1]+ (P-root)*B[k])%P;
                B[0]=(P-root)*B[0]%P;
                deg++;
            }
        }
    }
}

// realizability test given monic V (deg Asz_): r = x^{deg34_} mod V; realizable iff
// r_k == 0 for k in [half_+1, Asz_-1].
static u64 rbuf[80];
static int test_V(const u64 *V){
    int D=Asz_;
    // r = x^D mod V = -(V - x^D) lower part
    for(int k=0;k<D;k++) rbuf[k]=(P-V[k])%P;
    // multiply by x, reduce, (deg34_ - D) times
    for(int s=0;s<deg34_-D;s++){
        u64 top=rbuf[D-1];
        for(int k=D-1;k>=1;k--){
            u64 v=(rbuf[k-1]+(P-top)*V[k])%P;
            rbuf[k]=v;
        }
        rbuf[0]=(P-top)*V[0]%P;
    }
    for(int k=half_+1;k<D;k++) if(rbuf[k]) return 0;
    return 1;
}

static void print_pattern(int c0,int a,int b,int d,int e){
    int mn0=c0, mn1=(c0+1)%4, mj0=(c0+2)%4, mj1=(c0+3)%4;
    printf("REALIZABLE c0=%d A={",c0);
    for(int i=0;i<agrmin_;i++) printf("%d,",cls[mn0][cmin[a*agrmin_+i]]);
    for(int i=0;i<agrmin_;i++) printf("%d,",cls[mn1][cmin[b*agrmin_+i]]);
    for(int i=0;i<agrmaj_;i++) printf("%d,",cls[mj0][cmaj[d*agrmaj_+i]]);
    for(int i=0;i<agrmaj_;i++) printf("%d%s",cls[mj1][cmaj[e*agrmaj_+i]], i==agrmaj_-1?"":",");
    printf("} idx=(%d,%d,%d,%d)\n",a,b,d,e);
}

static void setup(u64 p, int n){
    P=p; N_=n; m_=n/4; half_=n/2; deg34_=3*n/4;
    agrmin_=m_-m_/4; agrmaj_=m_-m_/2;
    Asz_=2*agrmin_+2*agrmaj_; ncond_=Asz_-1-half_;
    u64 g0=pw(generator(p),(p-1)/n);
    Xpow=malloc(sizeof(u64)*n);
    u64 x=1; for(int j=0;j<n;j++){ Xpow[j]=x; x=x*g0%P; }
    for(int c=0;c<4;c++){ int t=0; for(int j=0;j<n;j++) if(j%4==c) cls[c][t++]=j; }
    nmin_=(int)binom(m_,agrmin_); nmaj_=(int)binom(m_,agrmaj_);
    cmin=malloc(sizeof(int)*nmin_*agrmin_); cmaj=malloc(sizeof(int)*nmaj_*agrmaj_);
    build_combos(m_,agrmin_,cmin); build_combos(m_,agrmaj_,cmaj);
    BminP=malloc(sizeof(u64)*4*nmin_*(agrmin_+1));
    BmajP=malloc(sizeof(u64)*4*nmaj_*(agrmaj_+1));
    build_blocks();
    fprintf(stderr,"[setup] p=%llu n=%d |A|=%d conds=%d nmin=%d nmaj=%d total=%.6g\n",
        p,n,Asz_,ncond_,nmin_,nmaj_, 4.0*nmin_*nmin_*(double)nmaj_*nmaj_);
}

// enumeration (full / short-circuit / dump)
static u64 enumerate(int shortcircuit,int dump,u64 maxpat){
    int dmin=agrmin_, dmaj=agrmaj_;
    u64 *P1,*P12,*P123,*V;
    P12 =malloc(sizeof(u64)*(2*dmin+1));
    P123=malloc(sizeof(u64)*(2*dmin+dmaj+1));
    V   =malloc(sizeof(u64)*(Asz_+1));
    u64 count=0, total=0;
    for(int c0=0;c0<4;c0++){
        int mn0=c0, mn1=(c0+1)%4, mj0=(c0+2)%4, mj1=(c0+3)%4;
        for(int a=0;a<nmin_;a++){
            P1=&BminP[((u64)(mn0*nmin_+a))*(dmin+1)];
            for(int b=0;b<nmin_;b++){
                pmul(P1,dmin,&BminP[((u64)(mn1*nmin_+b))*(dmin+1)],dmin,P12);
                for(int d=0;d<nmaj_;d++){
                    pmul(P12,2*dmin,&BmajP[((u64)(mj0*nmaj_+d))*(dmaj+1)],dmaj,P123);
                    for(int e=0;e<nmaj_;e++){
                        pmul(P123,2*dmin+dmaj,&BmajP[((u64)(mj1*nmaj_+e))*(dmaj+1)],dmaj,V);
                        total++;
                        if(test_V(V)){
                            count++;
                            if(dump) print_pattern(c0,a,b,d,e);
                            if(shortcircuit){ printf("SHORTCIRCUIT hit at pattern %llu\n",total);
                                print_pattern(c0,a,b,d,e); return count; }
                        }
                        if(maxpat && total>=maxpat){
                            fprintf(stderr,"[budget] stopped at %llu patterns, %llu realizable\n",total,count);
                            return count; }
                    }
                }
            }
        }
    }
    fprintf(stderr,"[enum] total=%llu realizable=%llu\n",total,count);
    free(P12);free(P123);free(V);
    return count;
}

// splitmix64
static u64 sm_state;
static u64 sm_next(void){ u64 z=(sm_state+=0x9E3779B97f4A7C15ULL);
    z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL; z=(z^(z>>27))*0x94D049BB133111EBULL; return z^(z>>31); }

static u64 sample(u64 Nsamp, u64 seed){
    int dmin=agrmin_, dmaj=agrmaj_;
    u64 *P12 =malloc(sizeof(u64)*(2*dmin+1));
    u64 *P123=malloc(sizeof(u64)*(2*dmin+dmaj+1));
    u64 *V   =malloc(sizeof(u64)*(Asz_+1));
    sm_state=seed;
    u64 count=0;
    for(u64 t=0;t<Nsamp;t++){
        int c0=(int)(sm_next()%4);
        int a=(int)(sm_next()%nmin_), b=(int)(sm_next()%nmin_);
        int d=(int)(sm_next()%nmaj_), e=(int)(sm_next()%nmaj_);
        int mn0=c0, mn1=(c0+1)%4, mj0=(c0+2)%4, mj1=(c0+3)%4;
        pmul(&BminP[((u64)(mn0*nmin_+a))*(dmin+1)],dmin,
             &BminP[((u64)(mn1*nmin_+b))*(dmin+1)],dmin,P12);
        pmul(P12,2*dmin,&BmajP[((u64)(mj0*nmaj_+d))*(dmaj+1)],dmaj,P123);
        pmul(P123,2*dmin+dmaj,&BmajP[((u64)(mj1*nmaj_+e))*(dmaj+1)],dmaj,V);
        if(test_V(V)){ count++; print_pattern(c0,a,b,d,e); }
        if((t&0xFFFFFF)==0xFFFFFF) fprintf(stderr,"[sample] %llu/%llu hits=%llu\n",t+1,Nsamp,count);
    }
    fprintf(stderr,"[sample] done N=%llu hits=%llu\n",Nsamp,count);
    return count;
}

// energy = number of violated conditions (0..ncond_); builds V from the root list.
static u64 Vtmp[84];
static int energy_of(const int *Aidx){
    // V = prod (x - X[A[i]])
    Vtmp[0]=1; int deg=0;
    for(int i=0;i<Asz_;i++){
        u64 root=Xpow[Aidx[i]];
        Vtmp[deg+1]=Vtmp[deg];
        for(int k=deg;k>=1;k--) Vtmp[k]=(Vtmp[k-1]+(P-root)*Vtmp[k])%P;
        Vtmp[0]=(P-root)*Vtmp[0]%P;
        deg++;
    }
    int D=Asz_;
    for(int k=0;k<D;k++) rbuf[k]=(P-Vtmp[k])%P;
    for(int s=0;s<deg34_-D;s++){
        u64 top=rbuf[D-1];
        for(int k=D-1;k>=1;k--) rbuf[k]=(rbuf[k-1]+(P-top)*Vtmp[k])%P;
        rbuf[0]=(P-top)*Vtmp[0]%P;
    }
    int E=0;
    for(int k=half_+1;k<D;k++) if(rbuf[k]) E++;
    return E;
}

// greedy random-restart local search. State: per class, chosen positions.
static u64 anneal(u64 evals, u64 seed){
    sm_state=seed;
    int agr[4], A[80], chosen[4][16], nch[4];
    u64 done=0, restarts=0; int bestE=999;
    while(done<evals){
        // random restart
        int c0=(int)(sm_next()%4);
        for(int c=0;c<4;c++){
            int is_min = (c==c0)||(c==(c0+1)%4);
            agr[c]= is_min?agrmin_:agrmaj_;
            // random subset of size agr[c] from m_ positions (partial Fisher-Yates)
            int perm[16]; for(int t=0;t<m_;t++) perm[t]=t;
            for(int t=0;t<agr[c];t++){ int u=t+(int)(sm_next()%(m_-t)); int tmp=perm[t];perm[t]=perm[u];perm[u]=tmp; }
            nch[c]=agr[c]; for(int t=0;t<agr[c];t++) chosen[c][t]=perm[t];
        }
        restarts++;
        int build=0;
        for(int c=0;c<4;c++) for(int t=0;t<nch[c];t++) A[build++]=4*chosen[c][t]+c;
        int E=energy_of(A); done++;
        u64 stagn=0;
        while(stagn<4000 && done<evals){
            // propose swap in random class
            int c=(int)(sm_next()%4);
            int ic=(int)(sm_next()%nch[c]);
            int old=chosen[c][ic];
            // pick a missing position in class c
            int missing[16], nm=0;
            for(int t=0;t<m_;t++){ int used=0; for(int u=0;u<nch[c];u++) if(chosen[c][u]==t){used=1;break;} if(!used) missing[nm++]=t; }
            int nw=missing[sm_next()%nm];
            chosen[c][ic]=nw;
            build=0; for(int cc=0;cc<4;cc++) for(int t=0;t<nch[cc];t++) A[build++]=4*chosen[cc][t]+cc;
            int E2=energy_of(A); done++;
            if(E2<=E){ if(E2<E) stagn=0; else stagn++; E=E2; }
            else { chosen[c][ic]=old; stagn++; }
            if(E<bestE){ bestE=E; fprintf(stderr,"[anneal] best E=%d after %llu evals (%llu restarts)\n",bestE,done,restarts); }
            if(E==0){
                printf("HIT E=0 (REALIZABLE) after %llu evals:\nA={",done);
                for(int i=0;i<Asz_;i++) printf("%d%s",A[i],i==Asz_-1?"}\n":",");
                return 0;
            }
        }
    }
    fprintf(stderr,"[anneal] done evals=%llu restarts=%llu bestE=%d (no hit)\n",done,restarts,bestE);
    return bestE;
}

static void testfile(const char*path){
    FILE*f=fopen(path,"r");
    if(!f){fprintf(stderr,"cannot open %s\n",path);exit(1);}
    char line[4096]; int A[80];
    while(fgets(line,sizeof line,f)){
        int cnt=0; char*s=line;
        while(*s && cnt<Asz_){
            while(*s && (*s<'0'||*s>'9')) s++;
            if(!*s) break;
            A[cnt++]=(int)strtol(s,&s,10);
        }
        if(cnt!=Asz_) continue;
        int E=energy_of(A);
        printf("pattern E=%d %s:",E,E==0?"REALIZABLE":"no");
        for(int i=0;i<cnt;i++) printf(" %d",A[i]);
        printf("\n");
    }
    fclose(f);
}

int main(int argc,char**argv){
    if(argc<4){ fprintf(stderr,
        "usage: %s full n p | sc n p maxpat | sample n p N seed | dump n p\n",argv[0]); return 1; }
    const char*mode=argv[1];
    int n=atoi(argv[2]); u64 p=strtoull(argv[3],0,10);
    if(!isprime(p)||((p-1)%n)){ fprintf(stderr,"p must be prime == 1 mod n\n"); return 1; }
    setup(p,n);
    if(!strcmp(mode,"full")){ u64 c=enumerate(0,0,0);
        printf("n=%d p=%llu realizable=%llu -> %s\n",n,p,c,c?"BAD":"good"); }
    else if(!strcmp(mode,"sc")){ u64 maxpat=argc>4?strtoull(argv[4],0,10):0;
        u64 c=enumerate(1,0,maxpat);
        printf("n=%d p=%llu sc-result=%llu -> %s\n",n,p,c,c?"BAD (>=1 realizable)":"no hit in budget"); }
    else if(!strcmp(mode,"sample")){ u64 Ns=strtoull(argv[4],0,10); u64 seed=argc>5?strtoull(argv[5],0,10):12345;
        u64 c=sample(Ns,seed);
        printf("n=%d p=%llu sampled=%llu hits=%llu\n",n,p,Ns,c); }
    else if(!strcmp(mode,"dump")){ u64 c=enumerate(0,1,0);
        printf("n=%d p=%llu realizable=%llu (dumped)\n",n,p,c); }
    else if(!strcmp(mode,"anneal")){ u64 ev=strtoull(argv[4],0,10); u64 seed=argc>5?strtoull(argv[5],0,10):777;
        u64 best=anneal(ev,seed);
        printf("n=%d p=%llu anneal bestE=%llu -> %s\n",n,p,best,best==0?"BAD":"no realizable found (inconclusive)"); }
    else if(!strcmp(mode,"testfile")){ testfile(argv[4]); }
    else { fprintf(stderr,"unknown mode\n"); return 1; }
    return 0;
}
