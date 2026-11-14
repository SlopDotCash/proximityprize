"""
Probe the max-vs-mean wall of the per-orbit same-arc coincidence sum in the arc program (#466).

Object (from G80V honest scope): for a multiplicative subgroup H = mu_n < F_p^*, |H|=n,
and window count K, define for each dilation b in F_p^*:

    S(b) = sum_{d in H} #{ y in H : arcIndex(b*d*y) = arcIndex(b*y) }
         = same-arc pair count of the coset b*H
         = #{ (x,y) in H^2 : arcIndex(b x) = arcIndex(b y) }

where arcIndex(v) = floor(K * (val v) / p), val v in {0..p-1} the canonical lift.

The b-averaged form is a THEOREM: (1/(p-1)) sum_b S(b) = (|H|/(p-1)) * sum_{d in H} R(d),
R(d) = #{v != 0 : arcIndex(d v)=arcIndex(v)}, and this equals ~ n + n^2/K (near-uniform).

OPEN: sup_b S(b). Prize needs S(b) <= n + n^2*(2/K)*O(1) + n*polylog  for EVERY b.
Wall hypothesis: does max_b S(b) stay within O(1)*mean, or can it blow up (subgroup anomaly)?

We measure, per cell (p, n, K):
  - mean S, max S, min S over all b (b ranges over coset reps; S is constant on cosets b*H
    so we take one b per coset: p-1)/n cosets).
  - the "excess" e(b) = S(b) - n (diagonal), and e/(n^2/K) normalized.
  - max/mean ratio.
  - which b achieves the max (is it structured? b in a subgroup? b=1?).
Saddle window: K ~ round(sqrt(2*pi*n/log q)), q = p here (single instance). Also sweep K.
"""
import math

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    # find generator of F_p^*
    if p == 2: return 1
    fac = []
    phi = p-1
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d += 1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    return None

def subgroup_mu_n(p, n):
    # H = unique subgroup of order n in F_p^* (requires n | p-1)
    assert (p-1) % n == 0
    g = primitive_root(p)
    gen = pow(g, (p-1)//n, p)
    H = []
    x = 1
    for _ in range(n):
        H.append(x)
        x = (x*gen) % p
    assert len(set(H)) == n
    return H

def arcIndex(K, v, p):
    return (K * v) // p   # v in 0..p-1

def probe_cell(p, n, K):
    H = subgroup_mu_n(p, n)
    Hset = set(H)
    # cosets: b ranges over reps of F_p^* / H. S constant on b*H.
    # We iterate all b in 1..p-1, compute S(b), dedup by coset later or just take all (cheap enough).
    # For speed compute S(b) for all b but note it's constant on cosets.
    results = {}
    seen_coset = {}
    # coset id: normalize by dividing by min element? Just compute for all b, group.
    Ssum = 0
    Scount = 0
    Smax = -1; bmax=None
    Smin = 10**9; bmin=None
    perb = {}
    for b in range(1, p):
        # S(b) = #{(x,y) in H^2 : arc(b x)=arc(b y)}
        # = sum over arc buckets of (count in bucket)^2
        buckets = {}
        for h in H:
            a = arcIndex(K, (b*h) % p, p)
            buckets[a] = buckets.get(a,0)+1
        S = sum(c*c for c in buckets.values())
        perb[b] = S
        Ssum += S; Scount += 1
        if S > Smax: Smax=S; bmax=b
        if S < Smin: Smin=S; bmin=b
    mean = Ssum/Scount
    # is bmax in H (subgroup element)?
    bmax_in_H = bmax in Hset
    # distinct coset values
    return dict(p=p,n=n,K=K, mean=round(mean,3), Smax=Smax, Smin=Smin,
               ratio=round(Smax/mean,3), bmax=bmax, bmax_in_H=bmax_in_H,
               diag=n, excess_max=Smax-n, n2overK=round(n*n/K,2),
               excess_norm=round((Smax-n)/(n*n/K),3) if K>0 and n*n/K>0 else None)

# cells with n | p-1, saddle K
cells = []
# choose p prime with n | p-1, n a 2-power (thin subgroup, adversarial)
candidates = [
    (n, ) for n in [4,8,16,32]
]
tested = []
for n in [4,8,16,32]:
    # find a prime p ~ a few hundred to few thousand with n | p-1
    found=0
    pp = None
    # want p reasonably larger than n^2 so window meaningful
    start = max(2*n*n, 200)
    for p in range(start, start+20000):
        if is_prime(p) and (p-1)%n==0:
            pp=p; break
    if pp is None: continue
    q = pp
    Ksaddle = max(2, round(math.sqrt(2*math.pi*n/math.log(q))))
    for K in sorted(set([Ksaddle, max(2,Ksaddle//2), Ksaddle*2, int(math.isqrt(pp))//2 if pp>4 else 2])):
        if K<1: continue
        r = probe_cell(pp, n, K)
        r['Ksaddle']=Ksaddle
        tested.append(r)

for r in tested:
    print(r)

print("\n=== SUMMARY: max/mean ratio across cells ===")
for r in tested:
    tag = "SADDLE" if r['K']==r['Ksaddle'] else ""
    print(f"p={r['p']:6d} n={r['n']:3d} K={r['K']:3d} {tag:6s} mean={r['mean']:8.2f} max={r['Smax']:6d} ratio={r['ratio']:.3f} bmax_in_H={r['bmax_in_H']} excess_norm={r['excess_norm']}")
