"""
ADVERSARIAL independent verification of claim `identity-gausssum-dft`.

Claim under test (verbatim from task):
    eta_b = (1/m) * [ -1 + sum_{j=1}^{m-1} conj(chi_j)(b) * tau(chi_j) ]

We DERIVE the identity from scratch (do not trust the stated form) and check:
  (A) direct eta_b  ==  Gauss-sum formula, for ALL b != 0, to < 1e-8
  (B) |tau(chi_j)| == sqrt(p) for every NON-principal chi_j (j != 0), to < 1e-8
      and tau(chi_0) = -1.

Definitions:
    p prime, n | p-1, mu_n = order-n subgroup of F_p^*.
    Q = F_p^*/mu_n cyclic of order m = (p-1)/n.
    Characters of F_p^* trivial on mu_n are chi_{n*l}(g^k) = exp(2 pi i (n*l) k/(p-1)),
        l = 0..m-1  (chi_0 principal). There are exactly m of them.
    tau(chi) = sum_{t in F_p^*} chi(t) e_p(t).
    eta_b = sum_{x in mu_n} e_p(b x).
    e_p(u) = exp(2 pi i u / p).

Vectorized with numpy so the prize-regime (large m, large p) cases finish.
Fresh code. Reuse only is_prime/primitive_root/odd_part number helpers.
"""
import sys, math
import numpy as np
sys.path.insert(0, 'C:/Users/Administrator/arklib/scripts/probes')
from probe_constant_additive_vs_mult import is_prime, primitive_root, odd_part


def run(p, n, label=""):
    assert is_prime(p), f"{p} not prime"
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    g = primitive_root(p)
    m = (p - 1) // n
    op = odd_part((p - 1) // n)

    # --- discrete-log table: powg[k] = g^k mod p (k=0..p-2); dlog inverse ---
    powg = np.empty(p - 1, dtype=np.int64)
    cur = 1
    for k in range(p - 1):
        powg[k] = cur
        cur = (cur * g) % p
    dlog = np.empty(p, dtype=np.int64)          # dlog[t] for t in 1..p-1
    dlog[powg] = np.arange(p - 1, dtype=np.int64)

    # --- mu_n = <g^{(p-1)/n}> : the elements with dlog divisible by m ---
    # g^k in mu_n  <=>  (g^k)^n = 1  <=>  n*k ≡ 0 (mod p-1)  <=>  m | k.
    sub_klogs = np.arange(0, p - 1, m)          # k = 0, m, 2m, ..., (n-1)m
    assert sub_klogs.size == n
    sub = powg[sub_klogs]                        # the n subgroup elements as residues
    assert len(set(sub.tolist())) == n
    # closure sanity: every element to the n-th power is 1
    assert all(pow(int(x), n, p) == 1 for x in sub)

    # --- additive character values e_p(t) for t = 0..p-1 ---
    ep = np.exp(2j * np.pi * np.arange(p) / p)   # ep[t] = e_p(t)

    # --- direct Gauss periods eta_b for ALL b = 1..p-1 ---
    # eta_b = sum_{x in mu_n} e_p(b x).  Compute (b*x mod p) matrix then index ep.
    bs = np.arange(1, p, dtype=np.int64)                 # shape (p-1,)
    bx = (bs[:, None] * sub[None, :]) % p                # (p-1, n)
    eta_direct = ep[bx].sum(axis=1)                      # (p-1,)  complex

    # --- characters chi_{n*l}, l=0..m-1, as value tables over t=1..p-1 ---
    # chi_{n*l}(t) = exp(2 pi i * (n*l) * dlog[t] / (p-1)).
    # Build chi_vals[l, t-1] for t=1..p-1.
    klog_t = dlog[1:p]                                   # dlog of t=1..p-1, shape (p-1,)
    ls = np.arange(m, dtype=np.int64)                    # l = 0..m-1
    # exponent (n*l*klog) mod (p-1), as float angle
    expo = (np.outer(ls * n, klog_t)) % (p - 1)          # (m, p-1)
    chi_vals = np.exp(2j * np.pi * expo / (p - 1))       # (m, p-1)

    # verify each chi is trivial on mu_n (mu_n elements as t-values -> column index t-1)
    sub_cols = sub - 1
    triv_err = np.max(np.abs(chi_vals[:, sub_cols] - 1.0))
    assert triv_err < 1e-9, f"some chi not trivial on mu_n, err={triv_err:.2e}"

    # --- Gauss sums tau_l = sum_t chi_l(t) e_p(t) ---
    ep_nonzero = ep[1:p]                                 # e_p(t), t=1..p-1
    taus = chi_vals @ ep_nonzero                         # (m,) complex

    # (B) |tau| checks
    sqrtp = math.sqrt(p)
    tau_abs = np.abs(taus)
    tau_err_nonprinc = float(np.max(np.abs(tau_abs[1:] - sqrtp))) if m > 1 else 0.0
    tau0_err = float(abs(taus[0] - (-1.0)))

    # (A) identity:  formula_full(b) = (1/m) sum_l conj(chi_l(b)) tau_l
    #     stated form drops l=0 and adds explicit -1 (== conj(1)*tau_0 only if tau_0=-1)
    # chi_l(b): b ranges 1..p-1, column index b-1.
    chi_b = chi_vals[:, bs - 1]                          # (m, p-1) = chi_l(b)
    formula_full = (np.conj(chi_b) * taus[:, None]).sum(axis=0) / m     # (p-1,)
    # stated: -1 + sum_{l=1}^{m-1} conj(chi_l(b)) tau_l, all over m
    bracket_stated = -1.0 + (np.conj(chi_b[1:]) * taus[1:, None]).sum(axis=0)
    formula_stated = bracket_stated / m

    err_full = float(np.max(np.abs(eta_direct - formula_full)))
    err_stated = float(np.max(np.abs(eta_direct - formula_stated)))
    worst_b = int(bs[int(np.argmax(np.abs(eta_direct - formula_stated)))])

    # B and Parseval
    eta_abs = np.abs(eta_direct)
    Bval = float(np.max(eta_abs))
    rms = float(math.sqrt(np.mean(eta_abs ** 2)))

    print(f"=== {label} p={p} n={n} m={m} (odd_part((p-1)/n)={op}) ===", flush=True)
    print(f"  primitive root g={g} ; |mu_n|={len(sub)} (expect {n})", flush=True)
    print(f"  (B) max||tau_j|-sqrt(p)| over j>=1 : {tau_err_nonprinc:.3e}  "
          f"[sqrt(p)={sqrtp:.8f}, |tau_1|={tau_abs[1]:.8f}]", flush=True)
    print(f"      tau_0={taus[0].real:+.6f}{taus[0].imag:+.6f}j (expect -1) ; "
          f"|tau0-(-1)|={tau0_err:.3e}", flush=True)
    print(f"  (A) max|eta_direct - formula_STATED|  : {err_stated:.3e}  (worst b={worst_b})", flush=True)
    print(f"  (A) max|eta_direct - formula_FULLSUM| : {err_full:.3e}", flush=True)
    print(f"  B=max|eta_b|={Bval:.6f} ; ParsevalRMS={rms:.6f} (sqrt(n)={math.sqrt(n):.6f})", flush=True)
    print(flush=True)
    return dict(p=p, n=n, m=m, odd_part=op, tau_err=tau_err_nonprinc, tau0_err=tau0_err,
                err_stated=err_stated, err_full=err_full, B=Bval, rms=rms)


def find_primes(n, beta_target, count=1, cap=300000):
    target = int(round(n ** beta_target))
    out = []
    k = max(1, target // n)
    k0 = k
    while len(out) < count and k < k0 + cap:
        p = 1 + k * n
        if is_prime(p) and odd_part((p - 1) // n) > 1 and p != 65537:
            out.append(p)
        k += 1
    return out


if __name__ == "__main__":
    results = []

    # MAIN: task spec — n=16, p~16^3=4096, proper subgroup
    n = 16
    primes = find_primes(n, 3.0, count=3)
    print(f"MAIN primes (n=16, p~4096, proper): {primes}\n", flush=True)
    for p in primes:
        results.append(run(p, n, "MAIN"))

    # XCHECK: vary n and regime to confirm structural, not coincidental.
    # Keep p modest so numpy stays fast (p<~6000 -> (p-1,n) and (m,p-1) arrays small).
    for nn, bt in [(8, 3.0), (32, 2.4), (16, 3.5)]:
        ps = find_primes(nn, bt, count=1)
        if ps and ps[0] < 12000:
            results.append(run(ps[0], nn, "XCHECK"))
        elif ps:
            print(f"(skipping XCHECK n={nn} p={ps[0]}: too large for quick run)\n", flush=True)

    worst_A = max(max(r['err_stated'], r['err_full']) for r in results)
    worst_B = max(r['tau_err'] for r in results)
    worst_tau0 = max(r['tau0_err'] for r in results)
    print("================ SUMMARY ================", flush=True)
    print(f"cases run: {len(results)}", flush=True)
    print(f"WORST identity error (A)            : {worst_A:.3e}", flush=True)
    print(f"WORST |tau|=sqrt(p) error (B, j>=1)  : {worst_B:.3e}", flush=True)
    print(f"WORST |tau_0 - (-1)| error          : {worst_tau0:.3e}", flush=True)
    print(f"Identity holds < 1e-8     : {worst_A < 1e-8}", flush=True)
    print(f"|tau|=sqrt(p) holds < 1e-8 : {worst_B < 1e-8}", flush=True)
