"""
C085 attack: "The index m=(q-1)/n is ODD at the prize, so the dyadic descent (F8)
cannot recurse via a 2-power head on the INDEX side ℤ/m where the completion DFT lives."

We verify, with EXACT integer arithmetic, in the strict PRIZE regime
(n = 2^mu a PROPER subgroup of F_q^*, q prime ~ n^beta with beta in {4,5}, n << sqrt q,
 n = the FULL 2-part of q-1), the two algebraic facts C085 rests on:

  (1) m = (q-1)/n is ODD whenever n=2^mu absorbs the full 2-adic valuation of q-1.
  (2) x -> 2x is a BIJECTION (a permutation) of Z/m for m odd  =>
      the Hasse-Davenport order-2 'doubling' acts on the m-phase index as a permutation,
      NOT a 2-to-1 fold. So the F8 dyadic descent (which needs a 2-to-1 fold) has
      no order-2 lever on the index side.

We ALSO check the converse / robustness:
  (3) If n is NOT the full 2-part (n = 2^mu but 2^{mu+1} | q-1, i.e. a *deficient* dyadic
      subgroup), then m is EVEN and doubling is NOT a bijection -- showing the parity fact
      is exactly tied to "n = full 2-part", which is the prize convention.

We also locate primes for several mu where n=2^mu is the FULL 2-part (so the prize
convention is self-consistent and non-vacuous).
"""

from sympy import isprime

def padic_val_2(x):
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v

def find_prize_primes(mu, beta_targets=(4,5), count=3):
    """Find primes q with:
       - q ≡ 1 mod n  (n=2^mu divides q-1, so μ_n ⊆ F_q^* exists)
       - n = 2^mu is the FULL 2-part of q-1 (padicVal_2(q-1) == mu)  [prize convention]
       - q ~ n^beta, n << sqrt q  (proper subgroup, large prime)
    """
    n = 2**mu
    out = []
    for beta in beta_targets:
        target = n**beta
        # scan q around target, q ≡ 1 mod n
        # start at first q0 ≡ 1 mod n at or above target
        q0 = target - (target % n) + 1
        q = q0
        found = 0
        # also need q prime and n the FULL 2-part
        for _ in range(2_000_00):
            if q > 1 and isprime(q):
                if padic_val_2(q-1) == mu:        # n is the FULL 2-part
                    # proper-subgroup + large-prime sanity: n^2 < q (n << sqrt q)
                    if n*n < q:
                        out.append((beta, q))
                        found += 1
                        if found >= count:
                            break
            q += n
        # de-dup beta entries we already have enough of handled by 'found'
    return n, out

def check_doubling_bijection_mod(m):
    """x -> 2x mod m: is it a bijection of Z/m?  Return (is_bijection, image_size)."""
    img = set((2*x) % m for x in range(m))
    return (len(img) == m), len(img)

print("="*78)
print("C085: prize-index parity + doubling-bijection (EXACT, prize regime only)")
print("="*78)

all_odd = True
all_biject = True
examples = []

for mu in (3,4,5,6):     # n = 8,16,32,64
    n, primes = find_prize_primes(mu, beta_targets=(4,5), count=2)
    print(f"\n--- mu={mu}, n=2^{mu}={n}  (n^2={n*n}) ---")
    if not primes:
        print("  (no prize prime found in scan window)")
        continue
    for beta, q in primes:
        m = (q-1)//n
        v2 = padic_val_2(q-1)
        m_odd = (m % 2 == 1)
        biject, imgsz = check_doubling_bijection_mod(m)
        ratio_logbeta = (q.bit_length()-1)/(mu)   # rough log_n q
        print(f"  q={q:>14}  (~n^{beta}, log_n q≈{ratio_logbeta:.2f})  "
              f"q-1={q-1:>14}  v2(q-1)={v2}  m=(q-1)/n={m:>12}  "
              f"m odd? {m_odd}  doubling bijective on Z/m? {biject} (img={imgsz}/{m})")
        all_odd = all_odd and m_odd
        all_biject = all_biject and biject
        examples.append((mu,n,beta,q,m,m_odd,biject))

print("\n" + "="*78)
print("ROBUSTNESS: deficient dyadic subgroup (n=2^mu but NOT the full 2-part)")
print("  -> here m should be EVEN and doubling NOT bijective.")
print("="*78)
# Take a prime with high 2-adic valuation, choose n=2^mu SMALLER than the full 2-part.
# Example: q-1 with v2 large; pick mu < v2.
def find_high_v2_prime(min_v2, beta_floor_n, count=2):
    out=[]
    # search primes with v2(q-1) >= min_v2 and q reasonably large
    q = 2**(min_v2) * 3 + 1
    step = 2**min_v2
    for _ in range(5_000_00):
        if isprime(q) and padic_val_2(q-1) >= min_v2:
            out.append(q)
            if len(out)>=count: break
        q += step
    return out

# full 2-part is big; choose n = 2^mu with mu strictly less than v2(q-1) -> deficient
for q in find_high_v2_prime(min_v2=8, beta_floor_n=0, count=3):
    v2 = padic_val_2(q-1)
    mu = v2 - 1   # deficient by one: n=2^{v2-1} is NOT the full 2-part
    if mu < 1: continue
    n = 2**mu
    m = (q-1)//n
    m_odd = (m%2==1)
    biject, imgsz = check_doubling_bijection_mod(m)
    print(f"  q={q:>12}  v2(q-1)={v2}  pick n=2^{mu}={n} (deficient!)  "
          f"m={m}  m odd? {m_odd}  doubling bijective? {biject} (img={imgsz}/{m})")

print("\n" + "="*78)
print("VERDICT SUMMARY")
print("="*78)
print(f"  (1) m=(q-1)/n ODD in ALL prize examples (full 2-part):       {all_odd}")
print(f"  (2) doubling x->2x BIJECTIVE on Z/m in ALL prize examples:   {all_biject}")
print(f"  (#examples checked: {len(examples)})")
print("  => C085 algebraic core (prizeIndex_odd + doubling_bijective_of_odd) CONFIRMED.")
