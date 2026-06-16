"""
C068 probe: verify the claimed RING-THEORETIC dichotomy in the PRIZE REGIME.

Claim C068 (three sub-claims):
  (i)  mu_{2^mu} subset F_q*  <=>  2^mu | q-1  <=>  q == 1 mod 2^mu.   (FFT-domain existence)
  (ii) q splits COMPLETELY in Q(zeta_m)  <=>  q == 1 mod m.            (cyclotomic splitting)
  (iii) Therefore for m=2^mu: existence of FFT subgroup  <=>  q fully splits in Q(zeta_{2^mu}),
        and in the split case every prime P|q has residue degree 1, N(P)=q  ("the open Pan-Xu case").
  (iv) q !== 1 mod 2^mu  =>  no order-2^mu subgroup  =>  cannot host a smooth (FFT) RS code.

We check (i),(ii),(iii) EXACTLY in the prize regime: n=2^mu a PROPER subgroup, q prime ~ n^beta
(beta 4-5), q==1 mod n, large prime, and we confirm:
  - the FFT subgroup exists iff q==1 mod n  (cyclic group order = q-1, has order-n elt iff n|q-1);
  - the residue/inertia degree f of q in Z[zeta_n] equals ord_n(q) (multiplicative order of q mod n)
    [standard: in Z[zeta_n], q (q coprime to n) splits into phi(n)/f primes each of residue degree
     f = ord of q in (Z/n)^*]. Full split <=> f=1 <=> q==1 mod n.
  - so on the SAME congruence q==1 mod n: FFT exists AND q fully splits AND f=1 (N(P)=q).

We use exact integer arithmetic + sympy for primality / factorization sanity. No floats.
"""
from sympy import isprime, totient, factorint, primitive_root, nextprime
import random

def ord_mod(q, n):
    """multiplicative order of q modulo n (q coprime to n)."""
    assert __import__('math').gcd(q, n) == 1
    o = 1
    cur = q % n
    while cur != 1:
        cur = (cur * q) % n
        o += 1
    return o

def has_order_n_subgroup(q, n):
    """F_q* is cyclic of order q-1; it has a (unique) subgroup of order n iff n | q-1."""
    return (q - 1) % n == 0

def find_primes_in_regime(mu, beta, count, rng):
    """Find primes q ~ n^beta with q == 1 mod n (split) and a matched set NOT == 1 mod n."""
    n = 2**mu
    target = n**beta
    split = []
    nonsplit = []
    # split primes: search q = 1 + k*n near target
    k0 = max(2, target // n)
    k = k0
    while len(split) < count and k < k0 + 5_000_000:
        q = 1 + k*n
        if isprime(q):
            split.append(q)
        k += 1
    # non-split primes near target: any prime with q % n in {3,5,7,...} for mu>=3
    q = nextprime(target)
    while len(nonsplit) < count and q < target * 4:
        if (q - 1) % n != 0:
            nonsplit.append(q)
        q = nextprime(q)
    return n, split, nonsplit

def main():
    rng = random.Random(407)
    print("="*78)
    print("C068 dichotomy check  (n=2^mu PROPER subgroup, q~n^beta, prize regime)")
    print("="*78)
    for (mu, beta) in [(3,5),(4,5),(5,4),(6,4)]:
        n = 2**mu
        n_, split, nonsplit = find_primes_in_regime(mu, beta, 4, rng)
        phi = int(totient(n))  # = n/2 for n=2^mu, mu>=1
        print(f"\n--- mu={mu}  n=2^{mu}={n}  beta={beta}  target~{n}^{beta}={n**beta}  phi(n)={phi} ---")
        print(f"    (n/2 = {n//2}, phi(n)={phi}: equal? {phi==n//2})")
        print("  SPLIT candidates (q == 1 mod n):")
        for q in split:
            assert isprime(q)
            cong = (q-1) % n == 0
            fft  = has_order_n_subgroup(q, n)
            f    = ord_mod(q, n)         # residue degree of q in Z[zeta_n]
            ngp  = phi // f              # number of primes above q
            fully_split = (f == 1)
            # N(P) = q^f ; fully split => N(P)=q (Pan-Xu open case)
            NP_is_q = (f == 1)
            ok = (cong and fft and fully_split and NP_is_q and ngp == phi)
            print(f"    q={q:>12}  q-1 factor 2-adic v2={(q-1 & -(q-1)).bit_length()-1:>3}"
                  f"  cong(q==1 mod n)={cong}  FFT-exists={fft}  f=ord_n(q)={f}"
                  f"  #primes={ngp}  fully_split={fully_split}  N(P)=q?={NP_is_q}  [DICHOTOMY OK={ok}]")
            assert ok, f"DICHOTOMY BROKE (split side) q={q}"
        print("  NON-SPLIT candidates (q !== 1 mod n):")
        for q in nonsplit[:4]:
            assert isprime(q)
            cong = (q-1) % n == 0
            fft  = has_order_n_subgroup(q, n)
            import math
            if math.gcd(q, n) != 1:
                print(f"    q={q} divides n? skip"); continue
            f    = ord_mod(q, n)
            ngp  = phi // f
            fully_split = (f == 1)
            # KEY dichotomy assertion: no FFT subgroup AND not fully split (f>1, residue deg>1)
            ok = (not cong) and (not fft) and (not fully_split) and (f > 1)
            print(f"    q={q:>12}  q mod n={q%n:>4}  cong={cong}  FFT-exists={fft}"
                  f"  f=ord_n(q)={f}  #primes={ngp}  fully_split={fully_split}  [DICHOTOMY OK={ok}]")
            assert ok, f"DICHOTOMY BROKE (nonsplit side) q={q}"
    print("\n" + "="*78)
    print("RESULT: in EVERY prize-regime instance tested,")
    print("  FFT subgroup mu_n exists  <=>  q == 1 mod n  <=>  q fully splits in Q(zeta_n) (f=1, N(P)=q).")
    print("  q !== 1 mod n  =>  no FFT subgroup AND q NOT fully split (residue degree f>1).")
    print("  => the dichotomy (i)-(iv) holds exactly. SAME congruence governs both.")
    print("="*78)

if __name__ == "__main__":
    main()
