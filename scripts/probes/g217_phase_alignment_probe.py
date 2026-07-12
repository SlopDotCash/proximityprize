#!/usr/bin/env python3
# G217 opus-core CORE probe: the phase-alignment hypothesis for the signed simultaneous covariance.
#
# CONTEXT (frontier tip 0ef0e6689f). The magnitude/support tower is maximally pinned
# (G182/G206/G209/G210/G213/G215). The SOLE live CORE object is the SIGNED simultaneous
# late-Newton covariance, in G56's exact quotient-Mellin/Jacobi coordinates (G216):
#
#   A_r = ((p*W_G(0)-n^2)(p*R_r(0)-M_r))/(p-1)
#         + p/(p-1) * Sum_{chi != 1, chi|G = 1} What(chi) * conj(Rhat(chi)),
#   What(chi) = Sum_{t!=0} W_G(t) chibar(t),  Rhat(chi) = Sum_{t!=0} R_r(t) chibar(t),
#   M_r = C(n,r) C(n,r-1),  W_G(t) = #{y in G : 2y - t in G}.
#
# CLOSED (do NOT re-run): bounded-ORDER Jacobi truncation (G216 g56 — >99.5% mass above
# order 8); top-k dyadic CONDUCTOR-SHELL truncation, magnitude AND sign (Fable 00:35 —
# top-2 band overshoots signed total 2.007x => cancellation-controlled, sign-blind);
# zero-cell as sign source (collapses to 0-5.7% at Fermat scale); all magnitude floors
# (G206/G209/G210/G215 sign-blind n-2 residual); single-depth / same-sign / ratio / DC
# cross-depth reductions (G214, Fable 22:20 — all refuted).
#
# THE ONE UNTESTED SIGNED ROUTE (Fable's explicit handoff, 00:35 MDT): a TRUNCATION-FREE
# signed bound requires a UNIFORM CONDUCTOR-INDEPENDENT PHASE ALIGNMENT between What(chi)
# and Rhat(chi). If the per-mode signed contribution's PHASE
#       theta_r(chi) = arg( What(chi) * conj(Rhat(chi)) )
# concentrated in a fixed half-plane (Re >= 0 for a controlling mass fraction, uniformly
# across ALL conductor shells and BOTH ranks, stably as m grows), then
#       A_r = zero_cell + (p/(p-1)) Sum_chi |What||Rhat| cos(theta_r(chi))
# would admit a signed lower bound with NO truncation: every mode would add coherently.
#
# HYPOTHESES.
#   H_align  : theta_r(chi) is half-plane concentrated (aligned mass fraction f -> 1 or a
#              stable f > 1/2 with bounded anti-aligned magnitude), uniformly in conductor,
#              for BOTH r=5 and r=6  => truncation-free signed lower bound exists.
#   H_random : theta_r(chi) is NOT half-plane concentrated; aligned/anti-aligned magnitude
#              masses are near-balanced (the signed sum is a small residual of massive
#              cancellation), the balance is conductor-uniform (no shell is coherent), and
#              it does NOT improve as m grows  => the coherent-phase route is dead; A_r is
#              an unavoidable cancellation residual = the BGK phase-correlation wall, in the
#              STRONGEST possible sense (no coordinate, no shell, no phase gate thins it).
#
# METHOD. Exact integer W_G, exact integer R_r (subset-sum DP over the difference conv),
# exact integer A_r. Mellin modes via exact discrete-log indexing + complex accumulation,
# cross-checked: full reconstruction must match exact A_r. For each quotient character
# chi != 1 we record |What(chi)|, |Rhat(chi)|, the signed real part
#   s(chi) = Re(What(chi) conj(Rhat(chi))),
# and its conductor order. We then measure, per rank and overall AND per conductor shell:
#   - aligned magnitude mass  Sum_{s>0} s   vs anti-aligned  Sum_{s<0} (-s)
#   - the "coherence ratio"   R_coh = |Sum s| / Sum |s|   (1 = perfectly coherent, 0 = full
#     cancellation). A truncation-free signed bound needs R_coh bounded below uniformly.
#   - the half-plane fraction f+ = (# modes with s>0)/(#modes) and the mass-weighted
#     aligned fraction  w+ = Sum_{s>0} s / Sum |s|.
# We sweep n in {8,16,32,64}, r in {5,6}, over the largest exact cells reachable, to test
# the m-scaling of R_coh (does coherence survive the limit, or collapse ~ 1/sqrt(#modes)?).

import itertools, math, cmath
from collections import Counter
from sympy import primitive_root as pr, isprime

def build_group(p, n):
    assert (p - 1) % n == 0
    g = pr(p)
    m = (p - 1) // n
    G = sorted({pow(g, (m * k) % (p - 1), p) for k in range(n)})
    assert len(G) == n
    return set(G), g, m

def W_G_exact(p, G):
    W = [0] * p
    Gs = set(G)
    for t in range(p):
        c = 0
        for y in G:
            if (2 * y - t) % p in Gs:
                c += 1
        W[t] = c
    return W

def R_r_exact(p, G, r):
    Gl = sorted(G)
    sumsA = Counter(sum(A) % p for A in itertools.combinations(Gl, r))
    sumsB = Counter(sum(B) % p for B in itertools.combinations(Gl, r - 1))
    R = [0] * p
    for sa, ca in sumsA.items():
        for sb, cb in sumsB.items():
            R[(sa - sb) % p] += ca * cb
    return R

def discrete_log_table(p, g):
    dlog = [0] * p
    val = 1
    for e in range(p - 1):
        dlog[val] = e
        val = (val * g) % p
    return dlog

def analyze(p, n, r, verbose=True):
    G, g, m = build_group(p, n)
    W = W_G_exact(p, G)
    R = R_r_exact(p, G, r)
    p1 = p - 1
    dlog = discrete_log_table(p, g)
    Mr = math.comb(n, r) * math.comb(n, r - 1)

    # exact integer A_r
    C12 = sum(W[t] * R[t] for t in range(p))
    A_exact = p * C12 - n * n * Mr

    # zero cell
    zero_term = ((p * W[0] - n * n) * (p * R[0] - Mr)) / p1

    # Mellin modes over quotient characters chi trivial on G: a = n*j mod (p-1), j=0..m-1
    modes = []  # (order, s_signed, absW, absR)
    full_signed = 0.0
    for j in range(m):
        a = (n * j) % p1
        if a == 0:
            continue  # trivial char handled by zero_term convention (chi=1 excluded from sum)
        order = p1 // math.gcd(a, p1)
        What = 0j
        Rhat = 0j
        for t in range(1, p):
            ph = cmath.exp(-2j * math.pi * a * dlog[t] / p1)
            What += W[t] * ph
            Rhat += R[t] * ph
        prod = What * Rhat.conjugate()
        contrib = (p / p1) * prod
        full_signed += contrib.real
        modes.append((order, contrib.real, abs(What), abs(Rhat)))

    recon = zero_term + full_signed
    err = abs(A_exact - recon)

    # coherence statistics on the SIGNED per-mode contributions
    pos = [s for (_, s, _, _) in modes if s > 0]
    neg = [-s for (_, s, _, _) in modes if s < 0]
    L1 = sum(abs(s) for (_, s, _, _) in modes)
    signed = sum(s for (_, s, _, _) in modes)
    R_coh = abs(signed) / L1 if L1 > 0 else float('nan')
    f_plus = (len(pos) / len(modes)) if modes else float('nan')
    w_plus = (sum(pos) / L1) if L1 > 0 else float('nan')

    # per-conductor-shell coherence: is ANY shell internally coherent?
    shells = {}
    for (o, s, _, _) in modes:
        shells.setdefault(o, []).append(s)
    shell_rows = []
    for o in sorted(shells):
        ss = shells[o]
        sl1 = sum(abs(x) for x in ss)
        ssig = sum(ss)
        rc = abs(ssig) / sl1 if sl1 > 0 else float('nan')
        shell_rows.append((o, len(ss), rc, ssig))

    if verbose:
        print(f"=== p={p} n={n} r={r} m={m} #modes={len(modes)} ===")
        print(f"  A_exact={A_exact}  recon={recon:.3f}  err={err:.3e}  (recon must match A_exact)")
        print(f"  zero_term={zero_term:.2f}  full_signed={full_signed:.2f}")
        print(f"  aligned_mass(pos)={sum(pos):.3e}  anti_mass(neg)={sum(neg):.3e}  L1={L1:.3e}")
        print(f"  R_coh=|signed|/L1={R_coh:.4f}   f+ (#modes s>0)={f_plus:.4f}   w+ (mass s>0)={w_plus:.4f}")
        # show the most coherent shell (best case for H_align)
        best = max(shell_rows, key=lambda z: z[2]) if shell_rows else None
        if best:
            print(f"  most-coherent shell: order={best[0]} nmodes={best[1]} R_coh_shell={best[2]:.4f} signed={best[3]:.3e}")
        # 1/sqrt(N) random-phase benchmark
        rand_bench = 1.0 / math.sqrt(len(modes)) if modes else float('nan')
        print(f"  1/sqrt(#modes) random-phase benchmark = {rand_bench:.4f}")
        print()
    return {
        "p": p, "n": n, "r": r, "m": m, "nmodes": len(modes),
        "A_exact": A_exact, "err": err, "R_coh": R_coh, "f_plus": f_plus,
        "w_plus": w_plus, "signed": signed, "L1": L1,
        "rand_bench": 1.0 / math.sqrt(len(modes)) if modes else float('nan'),
    }

def main():
    # exact cells; keep r-subset enumeration tractable (C(n,r) blows up for large n,r)
    cells = [
        (41, 8, 5), (41, 8, 6),
        (89, 8, 5), (89, 8, 6),
        (97, 16, 5), (97, 16, 6),
        (113, 16, 5), (113, 16, 6),
        (257, 16, 5), (257, 16, 6),
        (257, 32, 5), (257, 32, 6),
        (353, 32, 5), (353, 32, 6),
        (449, 64, 5), (449, 64, 6),
    ]
    rows = []
    for (p, n, r) in cells:
        if not isprime(p):
            continue
        if (p - 1) % n != 0:
            continue
        try:
            rows.append(analyze(p, n, r))
        except Exception as e:
            print(f"  SKIP p={p} n={n} r={r}: {e}")
    # m-scaling summary: does R_coh track 1/sqrt(#modes) (random phase) or stay bounded below?
    print("=== R_coh vs random-phase benchmark (m-scaling of coherence) ===")
    print(f"{'p':>5} {'n':>3} {'r':>2} {'#modes':>7} {'R_coh':>8} {'rand':>8} {'R/rand':>8} {'w+':>7}")
    for x in rows:
        ratio = x["R_coh"] / x["rand_bench"] if x["rand_bench"] else float('nan')
        print(f"{x['p']:>5} {x['n']:>3} {x['r']:>2} {x['nmodes']:>7} "
              f"{x['R_coh']:>8.4f} {x['rand_bench']:>8.4f} {ratio:>8.3f} {x['w_plus']:>7.4f}")

if __name__ == "__main__":
    main()
