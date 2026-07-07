#!/usr/bin/env python3
"""
probe_466_d4_scanner.py -- LANE R7 (round-1 P6 followup 3): the D4(n) bad-prime scanner.

Object: E_4(mu_n, p) = #{(x1..x4, y1..y4) in mu_n^8 : x1+x2+x3+x4 = y1+y2+y3+y4 in F_p},
mu_n = the order-n subgroup of F_p^x (p == 1 mod n), n dyadic (8, 16, 32).

Char-0 comparator: E_4^{(0)}(n) = #solutions over the complex n-th roots of unity, computed
EXACTLY by negacyclic dict convolution in Z[X]/(X^{n/2}+1) (Phi_{2^k} = X^{n/2}+1; the
representation of a sum of roots in the power basis 1..zeta^{n/2-1} is unique over Z).
Cross-checked against the in-tree closed form (_CharZeroEnergyClosedForm.lean):
    E_2^{(0)} = 3n^2 - 3n
    E_3^{(0)} = 15n^3 - 45n^2 + 40n      (_AvL_T3ClosedForm)
    E_4^{(0)} = 105n^4 - 630n^3 + 1435n^2 - 1155n

Wraparound excess: W_r = E_r(p) - E_r^{(0)}  (integer, provably >= 0: every char-0 vanishing
sum of roots reduces mod any split prime to a char-p solution; the tuple map is injective).
DC term: n^{2r}/p.  DC-subtracted: A_4 = E_4(p) - n^8/p.
Verdicts: EXACT-BAD iff W_4 > 0;  K-BAD iff A_4 > K * E_4^{(0)} with K = 1.05.

Norm-height provable cutoffs (depth r): a wraparound event needs alpha != 0 in Z[zeta_n],
alpha = (sum of r roots) - (sum of r roots), alpha == 0 mod a prime above p; every conjugate
|sigma(alpha)| <= 2r, so p | N(alpha), |N(alpha)| <= (2r)^{phi(n)}.  Hence
    D_r(n) subset of {p <= (2r)^{n/2}}   -- D4(n) is FINITE for every n, unconditionally.
For n=8: D4(8) subset {p < 4096 = n^4} (8^4 = 4096, equality impossible for odd p).
For n=16: D2(16) subset {p <= 65536} => W_2(65537) = 0 provably; D4 cutoff 8^8 = 16.7M.

MANDATORY cross-check: n=16, p=65537 must give W_4 = +4480 (dossier v3 / DISPROOF_LOG).

Scan plan:
  n=8 : ALL p == 1 mod 8  in [17, 4*8^4  = 16384]   (exhaustive, includes window [4096,16384])
  n=16: ALL p == 1 mod 16 in [17, 4*16^4 = 262144]  (exhaustive, includes window [65536,262144])
  n=32: ALL p == 1 mod 32 in [97, 70000]            (exhaustive small-p incl. Fermat 65537)
        + window [32^4, 4*32^4] = [1048576, 4194304] SAMPLE: first 12 + last 4 + 8 spread
        + ALL high-v2 (v2(p-1) >= 13) primes in the window (structured suspects).

Regime flags: p < n^4 rows are beta<4 (out-of-regime; scanned only for bad-set finiteness);
p = n+1 (full group mu_n = F_p^x) flagged FULLGROUP and excluded from regime conclusions.
"""

import sys
import time
from collections import Counter

import numpy as np

T0 = time.time()
K_THRESH = 1.05


def log(msg=""):
    print(msg, flush=True)


# ---------------------------------------------------------------- sieve
SIEVE_LIMIT = 4 * 32**4 + 64


def sieve_upto(limit):
    is_p = np.ones(limit + 1, dtype=bool)
    is_p[:2] = False
    for q in range(2, int(limit**0.5) + 1):
        if is_p[q]:
            is_p[q * q :: q] = False
    return is_p


IS_PRIME = sieve_upto(SIEVE_LIMIT)
PRIMES = np.nonzero(IS_PRIME)[0]


def primes_1modn(n, lo, hi):
    ps = PRIMES[(PRIMES >= lo) & (PRIMES <= hi)]
    return [int(p) for p in ps if p % n == 1]


def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2
        k += 1
    return k


# ------------------------------------------- char-0 exact energies (negacyclic dict)
def char0_energies(n):
    """Exact ordered-tuple energies E_2^0, E_3^0, E_4^0 for the complex n-th roots, n = 2^k.
    zeta^j -> +e_j (j < d) / -e_{j-d} (j >= d), d = n/2 (reduction mod X^{n/2}+1).
    Encoding: a depth-k signed vector v is keyed as sum_e (v_e + k) * 9^e; digits stay in
    [0, 2k] subset [0, 8] so key addition == vector addition, uniquely decodable per depth."""
    d = n // 2
    pw = [9**e for e in range(d)]
    ones = sum(pw)  # +1 in every digit = one depth-level offset bump
    enc1 = []
    for j in range(n):
        v = ones
        if j < d:
            v += pw[j]
        else:
            v -= pw[j - d]
        enc1.append(v)
    T2 = Counter()
    for a in enc1:
        for b in enc1:
            T2[a + b] += 1
    E2 = sum(c * c for c in T2.values())
    T3 = Counter()
    for k2, c2 in T2.items():
        for a in enc1:
            T3[k2 + a] += c2
    E3 = sum(c * c for c in T3.values())
    T4 = Counter()
    items = list(T2.items())
    for k2, c2 in items:
        for k2b, c2b in items:
            T4[k2 + k2b] += c2 * c2b
    E4 = sum(c * c for c in T4.values())
    assert sum(T2.values()) == n**2
    assert sum(T3.values()) == n**3
    assert sum(T4.values()) == n**4
    return E2, E3, E4


def E2_closed(n):
    return 3 * n**2 - 3 * n


def E3_closed(n):
    return 15 * n**3 - 45 * n**2 + 40 * n


def E4_closed(n):
    return 105 * n**4 - 630 * n**3 + 1435 * n**2 - 1155 * n


# ------------------------------------------- char-p exact energies (histogram convolution)
def mu_subgroup(p, n):
    q = (p - 1) // n
    for a in range(2, p):
        h = pow(a, q, p)
        if h != 1 and pow(h, n // 2, p) == p - 1:  # order exactly n (n a 2-power)
            break
    else:
        raise RuntimeError("no order-n element found for p=%d n=%d" % (p, n))
    xs = np.empty(n, dtype=np.int64)
    cur = 1
    for i in range(n):
        xs[i] = cur
        cur = (cur * h) % p
    assert len(set(xs.tolist())) == n
    return xs


def _group_counts(sums, weights):
    """Exact histogram of weighted sums: returns int64 bin totals of `weights`
    grouped by equal values of `sums`.  weights are integer-valued float64 with
    all bin totals < 2^53, so float64 accumulation is exact."""
    _, inv = np.unique(sums, return_inverse=True)
    return np.rint(np.bincount(inv, weights=weights)).astype(np.int64)


def energies_char_p(p, n, xs):
    """Exact integer E_2, E_3, E_4 via r-fold autocorrelation: E_r = sum_t N_r(t)^2.
    N2 kept on its support (<= n^2 points, the sumset mu_n + mu_n); N3 = N2 * ind and
    N4 = N2 * N2 by sparse grouping of the support-pair sums (no length-p arrays;
    float64 partial sums are exact: all bin values <= n^3 < 2^53)."""
    s2 = (xs[:, None] + xs[None, :]) % p
    vals, cnts = np.unique(s2.ravel(), return_counts=True)
    cnts = cnts.astype(np.int64)
    E2 = int(np.dot(cnts, cnts))
    # depth 3
    s3 = ((vals[:, None] + xs[None, :]) % p).ravel()
    w3 = np.repeat(cnts, n).astype(np.float64)
    N3i = _group_counts(s3, w3)
    assert int(N3i.sum()) == n**3
    E3 = int(np.dot(N3i, N3i))
    # depth 4
    s4 = ((vals[:, None] + vals[None, :]) % p).ravel()
    w4 = (cnts[:, None] * cnts[None, :]).astype(np.float64).ravel()
    N4i = _group_counts(s4, w4)
    assert int(N4i.sum()) == n**4
    E4 = int(np.dot(N4i, N4i))
    return E2, E3, E4


def energies_char_p_dense(p, n, xs):
    """Dense length-p int64 cross-check of E_4 (np.add.at, exact); small p only."""
    N2 = np.zeros(p, dtype=np.int64)
    np.add.at(N2, ((xs[:, None] + xs[None, :]) % p).ravel(), 1)
    idx = np.nonzero(N2)[0]
    N4 = np.zeros(p, dtype=np.int64)
    np.add.at(
        N4,
        ((idx[:, None] + idx[None, :]) % p).ravel(),
        (N2[idx][:, None] * N2[idx][None, :]).ravel(),
    )
    assert int(N4.sum()) == n**4
    return int(np.dot(N4, N4))


# ---------------------------------------------------------------- scan driver
def scan_n(n, prime_tags, E0):
    """prime_tags: list of (p, tag) with tag in {'exh','smp'}. Returns records list."""
    E2_0, E3_0, E4_0 = E0
    recs = []
    t_s = time.time()
    for i, (p, tag) in enumerate(prime_tags):
        if len(prime_tags) > 600 and (i + 1) % 1000 == 0:
            log("    ... n=%d: %d/%d primes (%.0fs)" % (n, i + 1, len(prime_tags), time.time() - t_s))
        xs = mu_subgroup(p, n)
        E2p, E3p, E4p = energies_char_p(p, n, xs)
        W2, W3, W4 = E2p - E2_0, E3p - E3_0, E4p - E4_0
        # one-sided inflation is a theorem; a violation means the code is wrong
        assert W2 >= 0 and W3 >= 0 and W4 >= 0, (n, p, W2, W3, W4)
        dc4 = n**8 / p
        A4 = E4p - dc4
        recs.append(
            dict(
                p=p,
                tag=tag,
                v2=v2(p - 1),
                beta=np.log(p) / np.log(n),
                E2p=E2p,
                E3p=E3p,
                E4p=E4p,
                W2=W2,
                W3=W3,
                W4=W4,
                dc4=dc4,
                A4=A4,
                kbad=A4 > K_THRESH * E4_0,
                xbad=W4 > 0,
                fullgroup=(p == n + 1),
            )
        )
    return recs


def fmt_row(r, n, E4_0):
    flags = []
    if r["fullgroup"]:
        flags.append("FULLGROUP(n=p-1)")
    if r["p"] < n**4:
        flags.append("beta<4")
    if r["v2"] >= 8:
        flags.append("v2=%d" % r["v2"])
    if r["p"] - 1 == 2 ** r["v2"]:
        flags.append("FERMAT")
    return (
        "  p=%-9d beta=%.2f  E4(p)=%-13d E4^0=%-11d DC=%-11.1f "
        "W4=%-10d A4=%-13.1f A4/E4^0=%-8.4f %s%s  [%s]"
        % (
            r["p"],
            r["beta"],
            r["E4p"],
            E4_0,
            r["dc4"],
            r["W4"],
            r["A4"],
            r["A4"] / E4_0,
            "EXACT-BAD " if r["xbad"] else "clean ",
            "K-BAD" if r["kbad"] else "k-ok",
            " ".join(flags) if flags else "-",
        )
    )


def summarize(n, recs, E0, window_total=None):
    E2_0, E3_0, E4_0 = E0
    lo4, hi4 = n**4, 4 * n**4
    log("")
    log("=" * 100)
    log("n = %d   (window [n^4, 4n^4] = [%d, %d];  K = %.2f)" % (n, lo4, hi4, K_THRESH))
    log("=" * 100)
    log(
        "char-0 (dict, exact): E2^0=%d E3^0=%d E4^0=%d | closed forms: %d %d %d | match: %s %s %s"
        % (
            E2_0,
            E3_0,
            E4_0,
            E2_closed(n),
            E3_closed(n),
            E4_closed(n),
            E2_0 == E2_closed(n),
            E3_0 == E3_closed(n),
            E4_0 == E4_closed(n),
        )
    )
    log(
        "norm-height provable cutoffs: D2(n) in p<=%g, D3(n) in p<=%g, D4(n) in p<=%g"
        % (4.0 ** (n // 2), 6.0 ** (n // 2), 8.0 ** (n // 2))
    )
    bad2 = sorted(r["p"] for r in recs if r["W2"] > 0)
    bad3 = sorted(r["p"] for r in recs if r["W3"] > 0)
    bad4 = sorted(r["p"] for r in recs if r["W4"] > 0)
    kbad = sorted(r["p"] for r in recs if r["kbad"])
    exh_hi = max(r["p"] for r in recs if r["tag"] == "exh")

    def show(name, lst):
        s = ", ".join(str(x) for x in lst[:44]) + (" ..." if len(lst) > 44 else "")
        log("%s (%d primes): {%s}" % (name, len(lst), s))

    show("D2(%d) exact-bad set (W2>0) in scan" % n, bad2)
    show("D3(%d) exact-bad set (W3>0) in scan" % n, bad3)
    show("D4(%d) exact-bad set (W4>0) in scan" % n, bad4)
    show("K-BAD set (A4 > %.2f*E4^0) in scan" % K_THRESH, kbad)
    log(
        "largest exact-bad prime in scan: D2 %s | D3 %s | D4 %s   (exhaustive up to %d)"
        % (
            max(bad2) if bad2 else "-",
            max(bad3) if bad3 else "-",
            max(bad4) if bad4 else "-",
            exh_hi,
        )
    )
    # least proper prime
    proper = [r for r in recs if not r["fullgroup"]]
    least = min(proper, key=lambda r: r["p"])
    log(
        "least prime == 1 mod %d with mu_%d PROPER: p=%d -> W4=%d (%s)%s"
        % (
            n,
            n,
            least["p"],
            least["W4"],
            "EXACT-BAD" if least["xbad"] else "clean",
            "  [K-BAD]" if least["kbad"] else "",
        )
    )
    fg = [r for r in recs if r["fullgroup"]]
    if fg:
        r = fg[0]
        log(
            "  (excluded from regime: p=%d is FULL GROUP n=p-1; W4=%d %s)"
            % (r["p"], r["W4"], "EXACT-BAD" if r["xbad"] else "clean")
        )
    # bands
    log("band statistics (W4):")
    bands = [
        ("p <  n^2", 2, n**2),
        ("n^2 <= p < n^3", n**2, n**3),
        ("n^3 <= p < n^4", n**3, n**4),
        ("WINDOW [n^4, 4n^4]", n**4, 4 * n**4 + 1),
    ]
    for name, blo, bhi in bands:
        rs = [r for r in recs if blo <= r["p"] < bhi]
        if not rs:
            continue
        nb = sum(1 for r in rs if r["xbad"])
        nk = sum(1 for r in rs if r["kbad"])
        mx = max(r["W4"] for r in rs)
        note = ""
        if name.startswith("WINDOW") and window_total is not None:
            note = "  [SAMPLED %d of %d window primes]" % (len(rs), window_total)
        log(
            "  %-20s scanned=%-5d exact-bad=%-4d K-bad=%-3d max W4=%-12d max A4/E4^0=%.4f%s"
            % (name, len(rs), nb, nk, mx, max(r["A4"] for r in rs) / E4_0, note)
        )
    # print all bad rows + interesting rows
    log("all EXACT-BAD rows (W4 > 0):")
    shown = 0
    for r in sorted(recs, key=lambda r: r["p"]):
        if r["xbad"]:
            log(fmt_row(r, n, E4_0))
            shown += 1
            if shown >= 60:
                log("  ... (%d more)" % (sum(1 for x in recs if x["xbad"]) - shown))
                break
    if shown == 0:
        log("  (none)")
    wrows = [r for r in recs if r["p"] >= n**4]
    if wrows:
        log("window sample rows (first 3 / high-v2 / last 2):")
        wsort = sorted(wrows, key=lambda r: r["p"])
        pick = wsort[:3] + [r for r in wsort if r["v2"] >= 13] + wsort[-2:]
        seen = set()
        for r in pick:
            if r["p"] in seen:
                continue
            seen.add(r["p"])
            log(fmt_row(r, n, E4_0))
    return bad2, bad3, bad4, kbad


# ================================================================ main
log("probe_466_d4_scanner.py -- D4(n) bad-prime scanner (depth-4 wraparound excess)")
log("sieve limit %d, %d primes total" % (SIEVE_LIMIT, len(PRIMES)))
log("")
log("Definitions: E_r(p) = #{x_1+..+x_r = y_1+..+y_r in mu_n subset F_p} (ordered tuples);")
log("W_r = E_r(p) - E_r^{(0)} >= 0 (wraparound excess); A_4 = E_4(p) - n^8/p (DC-subtracted);")
log("EXACT-BAD iff W_4 > 0; K-BAD iff A_4 > %.2f * E_4^{(0)}." % K_THRESH)

# -------- front-loaded validation: the pipeline must reproduce the dossier anchor
# W_4(65537) = +4480 (n=16) and agree with the dense int64 convolution, BEFORE the
# long scans; a silent convolution bug would otherwise waste the whole run.
log("")
log("[VALIDATION]")
for vn, vp in ((8, 12289), (16, 65537), (16, 65617), (32, 65537)):
    vxs = mu_subgroup(vp, vn)
    e4s = energies_char_p(vp, vn, vxs)[2]
    e4d = energies_char_p_dense(vp, vn, vxs)
    log("  sparse-vs-dense E4: n=%d p=%d -> %d / %d  %s" % (vn, vp, e4s, e4d, "OK" if e4s == e4d else "FAIL"))
    assert e4s == e4d
w4_anchor = energies_char_p(65537, 16, mu_subgroup(65537, 16))[2] - E4_closed(16)
log("  ANCHOR n=16 p=65537: W4 = %+d (dossier requires +4480) %s" % (w4_anchor, "PASS" if w4_anchor == 4480 else "FAIL"))
assert w4_anchor == 4480, "anchor mismatch -- convolution wrong, aborting before scan"

results = {}
for n in (8, 16, 32):
    t_n = time.time()
    E0 = char0_energies(n)
    # EXHAUSTIVE for every n: all p == 1 mod n in [2, 4n^4] (the sparse-support
    # method needs no length-p arrays, so the full n=32 window is feasible).
    plist = [(p, "exh") for p in primes_1modn(n, 2, 4 * n**4)]
    window_total = None
    recs = scan_n(n, plist, E0)
    results[n] = (recs, E0, window_total)
    log("")
    log(
        "[n=%d] scanned %d primes in %.1fs (exhaustive: %d, window-sample: %d)"
        % (
            n,
            len(recs),
            time.time() - t_n,
            sum(1 for r in recs if r["tag"] == "exh"),
            sum(1 for r in recs if r["tag"] == "smp"),
        )
    )

# mandatory cross-check BEFORE any reporting
recs16, E0_16, _ = results[16]
r65537 = [r for r in recs16 if r["p"] == 65537]
assert r65537, "65537 missing from the n=16 scan"
w4_fermat = r65537[0]["W4"]
log("")
log(
    "MANDATORY CROSS-CHECK n=16 p=65537: E4(p)=%d, E4^0=%d, W4=%d (dossier: +4480) -> %s"
    % (r65537[0]["E4p"], E0_16[2], w4_fermat, "PASS" if w4_fermat == 4480 else "FAIL")
)
if w4_fermat != 4480:
    log("FATAL: convolution does not reproduce the dossier value; aborting.")
    sys.exit(1)

badsets = {}
for n in (8, 16, 32):
    recs, E0, wt = results[n]
    badsets[n] = summarize(n, recs, E0, window_total=wt)

# ---------------------------------------------------------------- decision block
log("")
log("=" * 100)
log("DECISION BLOCK: good-prime supply for the D4-conditional n^{7/8} bound")
log("=" * 100)
for n in (8, 16, 32):
    recs, E0, wt = results[n]
    lo4, hi4 = n**4, 4 * n**4
    win_all = primes_1modn(n, lo4, hi4)
    wrecs = [r for r in recs if lo4 <= r["p"] <= hi4]
    nb = sum(1 for r in wrecs if r["xbad"])
    nk = sum(1 for r in wrecs if r["kbad"])
    mode = "exhaustive" if wt is None else ("sample %d/%d" % (len(wrecs), wt))
    log(
        "n=%-3d window primes==1 mod n: %-5d | scanned %-16s | exact-bad: %d | K-bad: %d"
        % (n, len(win_all), mode, nb, nk)
    )
log("")
log("K-BAD margin at beta>=4: K-badness needs W4 > 0.05*E4^0 + n^8/p ~ (5.25+1)*n^4;")
for n in (8, 16, 32):
    recs, E0, wt = results[n]
    wrecs = [r for r in recs if r["p"] >= n**4]
    mx = max((r["W4"] for r in wrecs), default=0)
    log(
        "  n=%-3d max in-window W4 = %-8d vs K-margin %.0f  (ratio %.2e)"
        % (n, mx, 0.05 * E0[2] + n**4, mx / (0.05 * E0[2] + n**4))
    )
log("")
log("total elapsed %.1fs" % (time.time() - T0))
