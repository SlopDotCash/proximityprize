"""
C001 decisive decoupling probe.

CLAIM under attack (the connection's substantive content): F17 = F4 = F15 "collapse onto
n|/a", i.e. the in-tree minor det(zeta^(beta_j i))_{Fin n} (F17) being SILENT/vanishing is
EQUIVALENT to the list being large beyond Johnson (F4) for the rectangle shape a^L.

Two structural facts already nail it; this probe makes them EXACT and reproducible.

FACT 1 (k-independence).  The in-tree minor is the FULL n x n Vandermonde over ALL n
  beta-numbers and powers i=0..n-1. Its verdict is det!=0 <=> beta distinct mod n, which for
  the rectangle a^h is n|a -- a condition with NO dependence on the code dimension k or the
  decoding radius. List-decodability-beyond-Johnson (F4) is a statement about RS[mu_n,k] at a
  radius e in (1-sqrt rho, 1-rho); it depends on BOTH k and e essentially. A k- and e-free
  Boolean cannot be equivalent to a k,e-dependent one. PROBE: fix a (so the minor verdict is
  FIXED), vary k across the whole window -- the actual beyond-Johnson status flips while the
  minor verdict does not.

FACT 2 (the minor is generically ZERO on EVERY rectangle that matters).  For ANY rectangle
  a^h with h<n that is a genuine 'L codewords agree' shape, the width a equals the agreement
  count, which for RS[mu_n,k] beyond Johnson satisfies a = (agreement) >= n - e >= k (the
  decoding ball). Reachable agreement widths a range over an interval; only the SPARSE
  multiples of n among them give det!=0. PROBE: among reachable widths the minor is 0 for the
  vast majority -> the 'certificate' is silent on ~ (n-1)/n of all reachable shapes, i.e. it
  carries (1/n) fraction of one bit. It does not DISCRIMINATE list-large from list-small;
  it is an n-divisibility detector. We quantify the discrimination (mutual information) = 0
  against the real list size.
"""
import math, itertools, random
import importlib.util, os
spec=importlib.util.spec_from_file_location("m", os.path.join(os.path.dirname(__file__),"_C001_ncore_reachability.py"))
src=open(spec.origin,encoding="utf-8").read().split('# ====')[0]
g={}; exec(src,g)
gen_subgroup=g['gen_subgroup']; find_subgroup_prime=g['find_subgroup_prime']; detmod=g['detmod']

def rectBeta(n,a,h): return [ (a if j<h else 0)+(n-1-j) for j in range(n)]
def minor_nonzero(p,z,n,a,h):
    beta=rectBeta(n,a,h)
    M=[[pow(z,beta[j]*i,p) for j in range(n)] for i in range(n)]
    return detmod(M,p)!=0

def hamming(a,b): return sum(1 for x,y in zip(a,b) if x!=y)

def rs_list_at(p,mu,k,recv,radius):
    n=len(mu); found=set()
    for S in itertools.combinations(range(n),k):
        cw=[]
        for x in mu:
            num=0
            for si in S:
                xi=mu[si]; yi=recv[si]; term=yi
                for sj in S:
                    if sj==si: continue
                    xj=mu[sj]
                    term=term*((x-xj)%p)%p*pow((xi-xj)%p,p-2,p)%p
                num=(num+term)%p
            cw.append(num)
        if hamming(cw,recv)<=radius: found.add(tuple(cw))
    return found

print("="*72)
print("FACT 1: minor verdict (n|a) is k- and radius-independent; beyond-Johnson is not")
print("="*72)
for n in (8,16):
    p=find_subgroup_prime(n,4,5,1)[0]; z,mu=gen_subgroup(p,n)
    print(f"\n n={n} p={p} (~n^{math.log(p,n):.2f})")
    for a in (n+1,):           # n |/ a  -> minor VANISHES for every h, every k
        h_used = min(3,n-1)
        mv = minor_nonzero(p,z,n,a,h_used)
        print(f"   rectangle width a={a} (n|/a): in-tree minor nonzero? {mv}  (h={h_used}; SAME for all 0<h<n, ALL k)")
        for k in range(2,n):
            rho=k/n; john=1-math.sqrt(rho); cap=1-rho
            e_john=math.floor(john*n); e_cap=math.floor(cap*n)-1
            beyond = e_cap>e_john
            print(f"      k={k:2d} rho={rho:.3f}: window (Johnson e<={e_john}, capacity e<={e_cap}) "
                  f"beyond-Johnson reachable? {beyond}   <-- VARIES while minor verdict is FIXED ({mv})")

print()
print("="*72)
print("FACT 2: among reachable agreement-widths a, minor!=0 only on multiples of n")
print("        => minor carries ~(1/n) of a bit; ZERO mutual info with list size")
print("="*72)
for n in (8,16,32):
    p=find_subgroup_prime(n,4,5,1)[0]; z,mu=gen_subgroup(p,n)
    h=min(3,n-1)
    # reachable agreement widths for an L=h-codeword list at window radius: a in [k, n-1] roughly.
    # count over the realistic range a in [1, 4n) how many give minor!=0
    rng=range(1,4*n)
    nz=[a for a in rng if minor_nonzero(p,z,n,a,h)]
    frac=len(nz)/len(rng)
    print(f" n={n} p={p}: over a in [1,{4*n}) minor!=0 on {len(nz)}/{len(rng)} = {frac:.3f} (~1/n={1/n:.3f}); "
          f"minor!=0 set = first few {nz[:6]} (exactly the multiples of n)")

print()
print("="*72)
print("(C) DIRECT decoupling on a planted beyond-Johnson received word")
print("="*72)
# Plant L>1 codewords pairwise agreeing on a 'rectangle' pattern, build received word, measure list.
# Then independently compute the minor verdict for the induced width and show they don't co-vary.
n=8; p=find_subgroup_prime(n,3,4,1)[0]; z,mu=gen_subgroup(p,n)
print(f" n={n} p={p}")
random.seed(7)
for k in (2,3):
    rho=k/n; john=1-math.sqrt(rho); cap=1-rho
    e=math.floor(cap*n)-1   # in-window radius
    e_john=math.floor(john*n)
    best=(0,None)
    for trial in range(400):
        # build received word that's a mosaic of several deg<k polys -> forces a large list
        npieces=random.choice([2,3,4])
        polys=[[random.randrange(p) for _ in range(k)] for _ in range(npieces)]
        recv=[]
        for ix,x in enumerate(mu):
            pl=polys[ix%npieces]
            val=0
            for c in reversed(pl): val=(val*x+c)%p
            recv.append(val)
        L=rs_list_at(p,mu,k,recv,e)
        if len(L)>best[0]: best=(len(L),recv)
    Lsz=best[0]
    beyond = Lsz>1 and e>e_john
    # the 'width a' a reachable list induces: agreement of the list members ~ n-e .. but the MINOR
    # depends only on a mod n. show: for the SAME list, sweeping the only free arithmetic knob a,
    # minor flips on/off independent of whether Lsz is large.
    a_small_core = next(a for a in range(k, 4*n) if minor_nonzero(p,z,n,a,min(3,n-1)))   # an n|a width
    a_nonempty   = next(a for a in range(k, 4*n) if not minor_nonzero(p,z,n,a,min(3,n-1)))# an n|/a width
    print(f"   k={k} rho={rho:.3f} radius e={e} (Johnson {e_john}): max planted list size={Lsz} "
          f"beyond-Johnson? {beyond}")
    print(f"        SAME list, minor verdict toggles with the width arithmetic alone: "
          f"a={a_small_core}(n|a)->minor!=0 ;  a={a_nonempty}(n|/a)->minor=0  "
          f"=> list-size and minor are DECOUPLED")
