"""
probe_444_angleD_structmap.py  (#444 Angle D -- is there an actual STRUCTURAL descent map
  bad(r,n) -> bad(r-1, n/2) with bounded fibers?)

A rigorous recursion needs a concrete map Phi: {bad (r+1)-subsets at depth r on line L_n}
  -> {bad r-subsets at depth r-1 on some line L_{n/2}} with fiber size <= c (constant), giving
  #bad(r,n) <= c * #bad(r-1,n/2). We test several candidate Phi on the ACTUAL bad subsets:

Candidate maps (S subset Z_n, |S|=r+1):
 (P1) "squaring": s -> 2s mod n (z -> z^2 sends mu_n -> mu_{n/2}). Image multiset in Z_{n/2}.
      If the r+1 exponents have <= ... distinct squares. Check if image (as set) is bad at (r-1,n/2).
 (P2) "delete-min + project": remove the smallest exponent, reduce rest mod n/2.
 (P3) "antipodal collapse": pair up s, s+n/2; replace each pair by its square; singletons by square.

For each candidate, on the n=16 maximizer bad set at depth r, we map every bad S, look at the
multiset of images, count how many land in the depth-(r-1) bad set at n/2 on the matched line, and
report the max fiber (how many S map to one image). A bounded max-fiber + full landing = a viable
structural recursion. Anything with unbounded/large fiber or low landing = NOT viable.

We need the bad-SUBSET lists (not just counts), so we call measure(..., want_orbits_of_subsets=True).
"""
import itertools, sys
from math import comb, gcd
from collections import Counter, defaultdict
sys.path.insert(0, "C:/Users/Administrator/arklib/scripts/probes")
from probe_444_angleD_recursion import measure, w_of_order, P, LINES

def bad_subset_set(n, e, f, r):
    res = measure(n, e, f, r, want_orbits_of_subsets=True)
    if res is None: return None, None
    return set(res['bad_subsets']), res

if __name__ == "__main__":
    # Test at n=16 (parent) vs n=8 (child). Maximizer families.
    print("=== structural descent map candidates: bad(r,16) -> bad(r-1,8) ===", flush=True)
    for r in [4]:
        n = 16
        e, f = LINES[r](n)
        parent_set, pres = bad_subset_set(n, e, f, r)
        # child line: use the named family at n/2 for depth r-1
        e2, f2 = LINES[r-1](n//2)
        child_set, cres = bad_subset_set(n//2, e2, f2, r-1)
        if parent_set is None or child_set is None:
            print(f"  r={r}: SKIP (neg deg somewhere)", flush=True); continue
        print(f"  parent (r={r},n={n}) line(x^{e},x^{f}): #bad_subsets={len(parent_set)}", flush=True)
        print(f"  child  (r-1={r-1},n/2={n//2}) line(x^{e2},x^{f2}): #bad_subsets={len(child_set)}", flush=True)
        h = n//2
        for name, phi in [
            ("P1_square(2s mod n/2)", lambda S: tuple(sorted(set((2*s) % (n//2) for s in S)))),
            ("P2_delmin_modh", lambda S: tuple(sorted(set((s % (n//2)) for s in sorted(S)[1:])))),
            ("P3_modh_dedup", lambda S: tuple(sorted(set((s % (n//2)) for s in S)))),
        ]:
            images = Counter()
            land = 0; total = 0; sizes = Counter()
            for S in parent_set:
                img = phi(S)
                sizes[len(img)] += 1
                images[img] += 1
                total += 1
            # how many distinct images have the right size (=r for depth r-1 subset) AND are in child_set
            right_size_imgs = [im for im in images if len(im) == r]   # depth r-1 -> a0=r elements
            in_child = sum(1 for im in right_size_imgs if im in child_set)
            maxfiber = max(images.values()) if images else 0
            print(f"    {name}: distinct_images={len(images)} maxfiber={maxfiber} "
                  f"img_size_dist={dict(sizes)} #right-size-imgs={len(right_size_imgs)} "
                  f"in_child={in_child}", flush=True)
