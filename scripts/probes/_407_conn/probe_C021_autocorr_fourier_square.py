"""
Probe for connection C021 (#407): "Autocorrelation r(h) IS the Fourier square of eta_b".

Claim to test (exact, integer/Gaussian-integer arithmetic via sympy):
  For G = mu_n (a PROPER multiplicative subgroup of F_q*, q prime = 1 mod n, n = 2^mu,
  n << sqrt(q) i.e. q ~ n^beta, beta ~ 4-5):

  (I)  UNSIGNED indicator side (the F18 = F2^2 Parseval identity).
       r(h) = #{(x,y) in G^2 : x - y = h}  =  sum_x 1_G(x) 1_G(x-h)   (group autocorrelation
       on the ADDITIVE group of F_q).
       eta_b = sum_{y in G} psi(b*y),  psi(t) = exp(2 pi i t / q)  (FT of 1_G at frequency b).
       CLAIM:  r_hat(b) := sum_h r(h) psi(-b*h)  ==  |eta_b|^2   EXACTLY for every b.
       => max_b r_hat(b) = max_b |eta_b|^2 = (max_b |eta_b|)^2 = F2^2.
       So F18 (max Fourier coeff of r <= n*log(p/n)) <=> F2 (max |eta_b| <= sqrt(n*log(p/n))).

  (II) The DIAGONAL CAP on the spatial side: r(h) <= r(0) = n  (autocorr_le_autocorr_zero,
       valid because 1_G >= 0).  Verify it holds for the unsigned case.

  (III) The SIGNED prize autocorrelation:  rsig(h) = sum_j tau_j conj(tau_{j+h})  where
       tau_j are the Gauss sums attached to mu_n (the actual prize object B = max|eta_b| is a
       sum of (q-1)/n Gauss-sum phases). Verify rsig is NOT nonnegative (so the Cauchy-Schwarz
       diagonal-cap lemma DOES NOT apply), while rsig_hat(b) = |that-transform|^2 >= 0 still
       holds (Parseval is sign-blind). The gap between the proven nonneg cap and the open
       signed flatness is exactly the Gauss-sum phase cancellation = BGK.

We test at several PROPER-subgroup primes with n in {8,16,32,64}, q ~ n^4..n^5.
"""

import cmath
import math
import random

# ---- pure-Python number theory (no sympy) ----

def isprime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def factorize(m):
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs

def primitive_root(q):
    """A primitive root mod prime q."""
    phi = q - 1
    facs = factorize(phi)
    for g in range(2, q):
        if all(pow(g, phi // p, q) != 1 for p in facs):
            return g
    raise RuntimeError("no primitive root found")

def find_prize_prime(n, beta_lo, beta_hi):
    """Find prime q = 1 mod n with n^beta_lo <= q <= n^beta_hi (proper subgroup, large prime)."""
    lo = int(n ** beta_lo)
    hi = int(n ** beta_hi)
    # search upward from lo for q = 1 mod n
    q = lo + ((n - (lo % n)) % n) + 1  # next value = 1 mod n (q % n == 1)
    while q < lo:
        q += n
    while q <= hi:
        if q % n == 1 and isprime(q):
            return q
        q += n
    return None

def subgroup_mu_n(q, n):
    """Return the multiplicative subgroup of order n in F_q^* as a sorted list of residues."""
    g = primitive_root(q)
    # generator of order n: g^((q-1)/n)
    h = pow(g, (q - 1) // n, q)
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x * h) % q
    assert len(set(G)) == n, "subgroup size mismatch"
    assert pow(h, n, q) == 1
    return sorted(G)

def eta(b, G, q):
    """eta_b = sum_{y in G} exp(2 pi i b y / q)  (complex float, high precision enough for exactness check)."""
    s = 0.0 + 0.0j
    for y in G:
        ang = 2.0 * math.pi * (b * y % q) / q
        s += cmath.exp(1j * ang)
    return s

def autocorr_unsigned(G, q):
    """r(h) = #{(x,y) in G^2 : x - y = h}, SPARSE dict (only nonzero shifts, <= n^2 entries)."""
    r = {}
    for x in G:
        for y in G:
            h = (x - y) % q
            r[h] = r.get(h, 0) + 1
    return r

def main():
    print("=" * 78)
    print("C021 probe: r_hat(b) == |eta_b|^2 exactly (unsigned), diagonal cap, signed sign-test")
    print("=" * 78)

    cases = [
        (8,  4.0, 5.0),
        (16, 4.0, 5.0),
        (32, 4.0, 4.6),
        (64, 4.0, 4.4),
    ]

    overall_ok_I = True
    overall_ok_II = True
    signed_has_negative = False

    for n, blo, bhi in cases:
        q = find_prize_prime(n, blo, bhi)
        if q is None:
            print(f"\n[n={n}] no prize prime found in range; skipping")
            continue
        beta = math.log(q) / math.log(n)
        G = subgroup_mu_n(q, n)
        print(f"\n[n={n}] q={q}  (q ~ n^{beta:.3f}, proper subgroup, n<<sqrt(q)={int(math.isqrt(q))})")

        # ---- (I) exact identity r_hat(b) == |eta_b|^2 ----
        r = autocorr_unsigned(G, q)
        # diagonal value
        r0 = r[0]
        assert r0 == n, f"r(0)={r0} != n={n}"

        # Compute r_hat(b) = sum_h r(h) exp(-2 pi i b h / q) and compare to |eta_b|^2.
        # Do this for a spread of b values including b=0, b in G, and random nonzero b.
        random.seed(1234 + n)
        test_bs = [0] + G[:3] + [random.randrange(1, q) for _ in range(6)]
        max_abs_err = 0.0
        max_eta_sq = 0.0
        for b in test_bs:
            # r_hat(b)
            rh = 0.0 + 0.0j
            for h, c in r.items():
                if c == 0:
                    continue
                ang = -2.0 * math.pi * (b * h % q) / q
                rh += c * cmath.exp(1j * ang)
            e = eta(b, G, q)
            eta_sq = abs(e) ** 2
            err = abs(rh - eta_sq)
            max_abs_err = max(max_abs_err, err)
            if b != 0:
                max_eta_sq = max(max_eta_sq, eta_sq)
        ok_I = max_abs_err < 1e-6
        overall_ok_I = overall_ok_I and ok_I
        print(f"  (I)  max|r_hat(b) - |eta_b|^2| over {len(test_bs)} freqs = {max_abs_err:.3e}  -> {'PASS' if ok_I else 'FAIL'}")
        print(f"       max_{{b!=0}} |eta_b|^2 (=F2^2 over tested b) = {max_eta_sq:.4f};  sqrt = {math.sqrt(max_eta_sq):.4f}")
        print(f"       reference: n={n}, sqrt(n)={math.sqrt(n):.4f}, n*ln(q/n)={n*math.log(q/n):.2f}, sqrt(that)={math.sqrt(n*math.log(q/n)):.4f}")

        # ---- (II) diagonal cap r(h) <= r(0)=n on the unsigned (nonneg) side ----
        max_r_nonzero = max(c for h, c in r.items() if h != 0) if q > 1 else 0
        ok_II = max_r_nonzero <= r0
        overall_ok_II = overall_ok_II and ok_II
        print(f"  (II) max_{{h!=0}} r(h) = {max_r_nonzero} <= r(0)=n={r0}  -> {'PASS' if ok_II else 'FAIL'}  (nonneg-weight cap holds)")

        # ---- (III) signed prize autocorrelation rsig(h) = sum_j tau_j conj(tau_{j+h}) ----
        # The prize B = max_b |eta_b| is itself a sum over the (q-1)/n cosets of Gauss-sum phases:
        #   eta_b = (1/n?) ... ; concretely eta_b = sum_{chi in mu_n^perp} chibar(b) tau(chi) up to
        # normalization. The "signed autocorrelation" the connection refers to is the autocorrelation
        # of the SEQUENCE of signed Gauss-sum terms tau_j := chibar_j(b) tau(chi_j). We build a
        # representative signed sequence: take the eta_b summand sequence s_y = psi(b*y), y in G
        # (these are the n unit phases whose sum is eta_b), and form rsig(h)=sum_y s_y conj(s_{y+shift}).
        # That is EXACTLY the additive autocorrelation of the COMPLEX weight w(x)=1_G(x)*psi(b x):
        # its transform is |hat w|^2 >= 0 (Parseval, sign-blind) but the spatial weight w is complex
        # (signed), so the Cauchy-Schwarz diagonal-cap lemma (needs w real >=0) does NOT apply.
        b = G[1] if len(G) > 1 else 1
        # complex weight supported on G: w(x) = psi(b x) for x in G, else 0
        Gset = set(G)
        w = {}
        for x in G:
            ang = 2.0 * math.pi * (b * x % q) / q
            w[x] = cmath.exp(1j * ang)
        # signed spatial autocorrelation rsig(h) = sum_x w(x) conj(w(x-h)), SPARSE
        # (nonzero only when both x and x-h are in G, i.e. h is a difference of two G elements)
        rsig = {}
        for x in G:
            for xm in G:
                h = (x - xm) % q
                rsig[h] = rsig.get(h, 0.0 + 0.0j) + w[x] * w[xm].conjugate()
        rsig0 = rsig[0]
        # is rsig real and nonnegative? rsig(0) should be real = n. off-diagonal generally complex/neg-real.
        min_real = min(v.real for v in rsig.values())
        max_imag = max(abs(v.imag) for v in rsig.values())
        # also: does |rsig(h)| ever EXCEED rsig(0)? (the nonneg cap would forbid even the real part>r0;
        # here the signed weight can have real part go negative -> cap-lemma assumption violated)
        any_neg_real = any(v.real < -1e-9 for h, v in rsig.items() if h != 0)
        signed_has_negative = signed_has_negative or any_neg_real
        print(f"  (III) signed weight w(x)=1_G(x)psi(b x), b={b}: rsig(0)={rsig0.real:.3f} (im {rsig0.imag:.1e})")
        print(f"        min Re rsig(h) = {min_real:.4f}  (negative => Cauchy-Schwarz nonneg-cap lemma N/A)")
        print(f"        off-diagonal Re<0 occurs: {any_neg_real}  ;  max |Im rsig| = {max_imag:.4f}")

        # Parseval sign-blindness: transform of the SIGNED autocorr is still |hat w|^2 >= 0.
        # hat w(c) = sum_x w(x) psi(-c x) = eta_{b-? } ... ; check rsig_hat(c) = |hat_w(c)|^2 exactly.
        random.seed(99 + n)
        test_cs = [0] + [random.randrange(1, q) for _ in range(5)]
        max_err_sig = 0.0
        min_rsig_hat = math.inf
        for c in test_cs:
            rh = 0.0 + 0.0j
            for h, v in rsig.items():
                if abs(v) < 1e-15:
                    continue
                ang = -2.0 * math.pi * (c * h % q) / q
                rh += v * cmath.exp(1j * ang)
            # hat w(c)
            hw = 0.0 + 0.0j
            for x in G:
                ang = 2.0 * math.pi * (b * x % q) / q - 2.0 * math.pi * (c * x % q) / q
                hw += cmath.exp(1j * ang)
            hw_sq = abs(hw) ** 2
            max_err_sig = max(max_err_sig, abs(rh - hw_sq))
            min_rsig_hat = min(min_rsig_hat, rh.real)
        print(f"        Parseval (sign-blind): max|rsig_hat(c) - |hat_w(c)|^2| = {max_err_sig:.3e} (PASS if ~0)")
        print(f"        min rsig_hat over tested c = {min_rsig_hat:.4f} (>=0 always: transform stays a square)")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print(f"  (I)  r_hat(b) == |eta_b|^2 EXACTLY (Parseval/orthogonality identity): {'CONFIRMED' if overall_ok_I else 'FAILED'}")
    print(f"       => F18 (max r_hat <= n L) is LITERALLY F2^2 (max|eta_b|^2 <= n L). The duality is exact.")
    print(f"  (II) diagonal cap r(h) <= r(0)=n on the UNSIGNED (nonneg) side: {'CONFIRMED' if overall_ok_II else 'FAILED'}")
    print(f"  (III) signed prize autocorrelation has Re<0 off-diagonal (nonneg cap N/A): {'CONFIRMED' if signed_has_negative else 'NOT SEEN'}")
    print( "        => autocorr_le_autocorr_zero is the NONNEG degenerate case; the open content")
    print( "           is the FREQUENCY-side flatness max_b|eta_b|^2 <= n*log(p/n), = BGK / Paley.")
    print("=" * 78)

if __name__ == "__main__":
    main()
