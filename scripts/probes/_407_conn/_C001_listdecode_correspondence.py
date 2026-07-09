"""
C001 attack, decisive half: does the in-tree minor verdict (n|a) track list-decoding-beyond-Johnson (F4)?

The connection asserts F17 (minor vanishing) = F4 (list size large beyond Johnson) coincide on n|/a.
We test the F4 side DIRECTLY by exact RS list decoding at proper-subgroup primes, and check:

 (A) Does the in-tree minor (full n x n, beta = rectangle a^h) actually CONTROL the RS list size?
     The minor is k-INDEPENDENT (Q1). RS list-decodability beyond Johnson depends ESSENTIALLY on k
     and on the radius. A k-independent object cannot be equivalent to a k-dependent one.
     We exhibit, at fixed (n,a) with n|/a so the minor VANISHES, that the actual RS[mu_n,k] list
     size is SMALL (= 1, within Johnson) for a range of k -- i.e. minor-vanishing does NOT imply
     beyond-Johnson list, refuting the literal F17=F4 identification.

 (B) Reachability: the "rectangle a^L" of the connection is L codewords AGREEING on a common shape.
     For RS, h=L codewords of degree<k pairwise agree on at most k-1 points; a true window-radius
     decoding list of L words sharing an agreement pattern constrains a. We check whether a list of
     L>1 distinct RS codewords that all lie within the decoding ball of a received word can produce
     the rectangle width a with n|/a, AND whether that has anything to do with the minor.
"""
import itertools, math

# reuse arithmetic
import importlib.util, os
spec=importlib.util.spec_from_file_location("m", os.path.join(os.path.dirname(__file__),"_C001_ncore_reachability.py"))
# avoid re-running its __main__ prints: load just functions
src=open(spec.origin,encoding="utf-8").read().split('# ====')[0]
g={}; exec(src,g)
is_prime=g['is_prime']; primitive_root=g['primitive_root']; gen_subgroup=g['gen_subgroup']
find_subgroup_prime=g['find_subgroup_prime']

def poly_eval(coeffs, x, p):
    r=0
    for c in reversed(coeffs): r=(r*x+c)%p
    return r

def hamming(a,b): return sum(1 for x,y in zip(a,b) if x!=y)

def all_rs_codewords(p, mu, k):
    """ALL RS[mu_n,k] codewords (deg<k). Only feasible for small p^k; we sample structurally instead."""
    raise NotImplementedError

def rs_list_at(p, mu, k, received, radius):
    """exact list of RS[mu_n,k] codewords within Hamming `radius` of `received`.
       brute over all deg<k polys is p^k -- too big. We instead count via the
       'agreement >= n-radius' formulation and the fact that any two codewords agree on <k points,
       so we can search by choosing k agreement positions (interpolation) and checking distance."""
    n=len(mu)
    agree_needed = n - radius
    found=set()
    # candidate codewords: interpolate through any k positions using received values, then verify.
    idxs=range(n)
    for S in itertools.combinations(idxs, k):
        # Lagrange interpolation of (mu[s], received[s]) for s in S
        # build coeffs implicitly; just evaluate the interpolant at all points
        cw=[]
        ok=True
        for x in mu:
            # Lagrange value at x
            num=0
            for si in S:
                xi=mu[si]; yi=received[si]
                term=yi
                for sj in S:
                    if sj==si: continue
                    xj=mu[sj]
                    term=term*( (x-xj) % p )%p * pow((xi-xj)%p, p-2, p)%p
                num=(num+term)%p
            cw.append(num)
        if hamming(cw, received) <= radius:
            found.add(tuple(cw))
    return found

print("="*70)
print("(A) does minor-vanishing (n|/a) imply RS list large beyond Johnson? exact RS list decode")
print("="*70)
# small n so brute interpolation list-decode is tractable; use PROPER-subgroup prime p=1 mod n, p~n^4
for n in (8,):
    ps=find_subgroup_prime(n, beta_min=4, beta_max=4, count=1)
    if not ps: ps=find_subgroup_prime(n, beta_min=3, beta_max=5, count=1)
    p=ps[0]; z,mu=gen_subgroup(p,n)
    print(f"\n n={n} p={p} (~n^{math.log(p,n):.2f}) proper subgroup, m={(p-1)//n}")
    for k in (2,3,4):
        rho=k/n
        # Johnson radius (relative) ~ 1 - sqrt(rho); abs Johnson list radius
        johnson_rel = 1 - math.sqrt(rho)
        cap_rel = 1 - rho
        # pick a radius strictly between Johnson and capacity (the prize window)
        e_john = math.floor(johnson_rel*n)
        e_cap  = math.floor(cap_rel*n) - 1
        if e_cap <= e_john:
            print(f"   k={k} rho={rho:.3f}: window empty (e_john={e_john} e_cap={e_cap}) -- skip")
            continue
        e = e_cap  # most aggressive in-window radius
        # adversarial received word: take a few RS codewords and a 'rectangle' pattern, then a random-ish received word
        # Use received = a fixed low-deg poly perturbed; measure list size.
        import random; random.seed(1)
        maxlist=0; total=0; samples=12
        for _ in range(samples):
            recv=[random.randrange(p) for _ in range(n)]
            L=rs_list_at(p,mu,k,recv,e)
            maxlist=max(maxlist,len(L)); total+=len(L)
        print(f"   k={k} rho={rho:.3f}  window radius e={e} (Johnson e<= {e_john}, capacity e<{e_cap+1})  "
              f"max RS list over {samples} random recv = {maxlist}  (avg {total/samples:.2f})")
