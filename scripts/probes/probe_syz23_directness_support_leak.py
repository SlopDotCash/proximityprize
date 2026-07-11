# Corrected-accounting LP for SYZ23 directness lower bound.
# span_dim >= sum_i (s_i - k) - sum_i max(0, o_i - k)
# where o_i = |C_i ∩ union_{j<i} C_j|, with pairwise |C_i∩C_j| <= k-1.
# Adversary maximizes total yield subject to span_dim <= (n-k-1)  [single-copy]
#   (or 2(n-k)-1 doubled; equivalent boundary).
# Key adversarial move: nest a core inside the existing union (spread across
#   >= s/(k-1) previous cores, each sharing <= k-1). Then o_i = s, cost = 0.
#
# We compute the LEAST forced span (adversary-favorable lower bound value)
# for a family that yields Y bad scalars, and check if Y can exceed budget B=n
# while span stays <= n-k-1. If yes => LP leaks (lower bound can't close strip).

def yieldS(n,t,s):
    return (n-s) if t<=s else (n-s)//(t-s)

def analyze(n,k,t,B):
    # cores of size s, s in [k+1, n]. incremental cost adversary can drive to 0
    # once the union has enough "capacity" to host a nested core: need union size
    # large enough and >= ceil(s/(k-1)) previous cores.
    # Phase 1 (seed): build union with real-cost cores until it can host nested s.
    # Phase 2: add unlimited nested cores at cost 0, each yielding yieldS.
    # If phase-2 yield alone can exceed B with total span <= n-k-1 => LEAK.
    # cheapest seed: to host a nested core of size s spread over prev cores each
    # sharing <= k-1, we need union >= s and #prev >= ceil(s/(k-1)).
    # Each seed core of size s costs (s-k) span first time (o=0 or small).
    best_leak=None
    for s in range(k+1, n+1):
        y=yieldS(n,t,s)
        if y==0: continue
        need_cores = -(-s//(k-1))          # ceil
        # seed: place need_cores cores; their pairwise overlaps <=k-1.
        # minimal span used by seed: union grows; use sunflower-ish.
        # Upper-bound seed span cost by need_cores*(s-k) (crude; adversary does better)
        # but for LEAK demonstration we want: can nested phase exceed B under span<=n-k-1?
        # nested cores cost 0 span, so we can add arbitrarily many => yield unbounded
        # PROVIDED the seed fits in span budget n-k-1 and union has room (union<=n).
        # union after seed at least s (to host). union<=n always ok if s<=n.
        # seed span (lower bound forced): even one seed core forces s-k>0.
        # As long as s-k <= n-k-1 i.e. s<=n-1, seed fits; nested unbounded => LEAK.
        if s<=n-1 and need_cores>=1:
            best_leak=(s,y,need_cores)
            break
    return best_leak

for (n,k) in [(32,16),(64,32)]:
    B=n
    print(f"n={n} k={k} B={B}")
    for t in range(k+1, n):
        d=(n-t)/n
        leak=analyze(n,k,t,B)
        tag="LEAK(nested cost-0)" if leak else "no-yield"
        print(f"  t={t} delta={d:.3f} {tag} {leak}")
    print()
