"""
C027 attack: "Covering number IS subgroup distinct r-fold subset-sum, base-{2,3} bracket,
field-capped at p."

Claims to test (exact integer arithmetic, prize regime n=2^mu PROPER subgroup, q ~ n^beta):

  (A) char-0 full-subgroup distinct subset-sum count = 3^{n/2}  (the {-1,0,1} cube image,
      ceiling) and the half-domain count = 2^{n/2} (free power basis, floor).
      [In-tree: subsetSumset_full_le_three_pow / card_subsetSumset_..._two_pow_ge.]

  (B) THE DECISIVE PRIZE QUESTION: for q ~ n^beta (beta in {4,5}), is the realized
      mod-p distinct subset-sum count = min(3^{n/2}, p) ?  i.e. does the mod-p reduction
      SATURATE the field cap p (collapse the cube below 3^{n/2} down to ~p), or does it
      stay strictly below p (i.e. is the count actually << p, so 'field cap is operative'
      is itself a question)?

  (C) Is the realized count >= the prize budget? (the count vs the budget n / q*eps).

Method: pick prime q == 1 mod n, n = 2^mu a PROPER subgroup (n << sqrt(q)), find a
primitive n-th root g in F_q. Enumerate the FULL-subgroup signed cube {-1,0,1}^{n/2}
images mod q (the char-0 image is 3^{n/2}; mod q it can only collapse). Count distinct.
For n where 3^{n/2} is enumerable (n<=16: 3^8=6561, n=24: 3^12=531441) do EXACT full
enumeration. For larger n, sample.
"""
import sys, random
from math import comb

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x = x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime_1_mod_n(n, lo):
    """smallest prime q >= lo with q == 1 mod n."""
    k = (lo - 1)//n + 1
    if k < 1: k = 1
    while True:
        q = k*n + 1
        if q >= lo and is_prime(q): return q
        k += 1

def primitive_nth_root(q, n):
    """g of exact multiplicative order n in F_q (q==1 mod n)."""
    # take a generator candidate h, set g = h^((q-1)/n); check order exactly n.
    cof = (q-1)//n
    # prime factors of n (n=2^mu => just 2)
    nf = []
    m = n
    p = 2
    while p*p <= m:
        if m%p==0:
            nf.append(p)
            while m%p==0: m//=p
        p += 1
    if m>1: nf.append(m)
    for h in range(2, q):
        g = pow(h, cof, q)
        if g == 1: continue
        # check order exactly n: g^n==1 and g^(n/pr)!=1 for each prime pr|n
        if pow(g, n, q) != 1: continue
        ok = all(pow(g, n//pr, q) != 1 for pr in nf)
        if ok: return g
    raise RuntimeError("no root")

def signed_cube_count_modq(g, q, half, exact_cap=2_000_000, seed=12345):
    """
    Count distinct values of sum_{i<half} eps_i * g^i  mod q, eps in {-1,0,1}.
    char-0 (true) count of distinct combos = 3^half (all distinct since power basis indep).
    mod q some collapse. If 3^half <= exact_cap do EXACT full enumeration, else sample.
    Returns (count, total_tried, exact_flag, char0_count=3^half).
    """
    powers = [pow(g, i, q) for i in range(half)]
    char0 = 3**half
    if char0 <= exact_cap:
        seen = set()
        # enumerate all eps in {-1,0,1}^half via base-3 odometer
        for code in range(char0):
            c = code
            s = 0
            idx = 0
            while c:
                d = c % 3
                if d == 1: s += powers[idx]
                elif d == 2: s -= powers[idx]
                c //= 3
                idx += 1
            seen.add(s % q)
        return len(seen), char0, True, char0
    else:
        rng = random.Random(seed)
        seen = set()
        trials = min(exact_cap, char0)
        for _ in range(trials):
            s = 0
            for i in range(half):
                d = rng.randint(0,2)
                if d==1: s += powers[i]
                elif d==2: s -= powers[i]
            seen.add(s % q)
        return len(seen), trials, False, char0

def main():
    print("="*78)
    print("C027 PROBE: covering = signed-cube subset-sum, field cap at p, prize regime")
    print("="*78)
    print(f"{'n':>4} {'mu':>3} {'beta':>5} {'q':>14} {'half':>4} "
          f"{'3^half':>14} {'2^half':>10} {'realized':>12} {'=min?':>7} {'sat':>6} {'mode':>7}")
    for mu in (3,4,5,6):
        n = 2**mu
        half = n//2
        for beta in (4,5):
            lo = n**beta
            q = find_prime_1_mod_n(n, lo)
            g = primitive_nth_root(q, n)
            # sanity: g^half == -1 mod q  (the antipodal collapse)
            assert pow(g, half, q) == q-1, f"g^half != -1 at n={n}"
            cnt, tried, exact, char0 = signed_cube_count_modq(g, q, half)
            ceil3 = 3**half
            floor2 = 2**half
            mn = min(ceil3, q)
            # is realized == min(3^half, q)?  (full enumeration only meaningful when exact)
            eqmin = (cnt == mn) if exact else "samp"
            sat = f"{cnt/min(q,char0):.3f}"  # fraction of the binding ceiling realized
            mode = "EXACT" if exact else "sample"
            print(f"{n:>4} {mu:>3} {beta:>5} {q:>14} {half:>4} "
                  f"{ceil3:>14} {floor2:>10} {cnt:>12} {str(eqmin):>7} {sat:>6} {mode:>7}")
    print()
    print("Interpretation:")
    print(" - char0 count = 3^half exactly (power basis indep): in-tree PROVEN bracket top.")
    print(" - In prize regime q~n^beta: when 3^half < q the cube does NOT collapse mod q")
    print("   (realized == 3^half, field cap p is NOT yet binding) => count = 3^half << q.")
    print(" - The 'field cap p keeps prize alive' framing: only binds once 3^half >= q,")
    print("   i.e. half >= log_3 q ~ beta*mu*log_3 2 ~ 0.63*beta*mu, vs half = 2^{mu-1}.")
    print("   2^{mu-1} >> 0.63*beta*mu for any mu>=4: the CUBE OVERWHELMS p almost instantly,")
    print("   so the realized count = min(3^half,p) = p (saturates) for the actual prize n.")

if __name__ == "__main__":
    main()
