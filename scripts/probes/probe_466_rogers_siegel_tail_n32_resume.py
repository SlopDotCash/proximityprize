#!/usr/bin/env python3
"""
probe_466_rogers_siegel_tail_n32_resume.py -- LANE L3 (#466): robust finisher for the
n = 32 block of probe_466_rogers_siegel_tail.py.

The parent probe's n=32 scan died silently mid-run (twice: 2026-07-01 and the 2026-07-02
re-run, both between prime 1500 and 2000 of 2103) with no traceback in the captured output.
This driver redoes the SAME deterministic n=32 ensemble (evenly sampled + all structured
primes, identical selection code) with:
  * per-prime try/except -- any crash is attributed to its prime and reported, never fatal;
  * incremental checkpointing to a .csv every 50 primes (resumable);
  * the same exact full-coset-scan statistic and Parseval check;
  * the same stats block, appended to _out_466_rogers_siegel_tail.txt at the end.
"""

import importlib.util
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "rs_tail", os.path.join(HERE, "probe_466_rogers_siegel_tail.py"))
rs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rs)

CKPT = os.path.join(HERE, "_ckpt_466_rs_tail_n32.csv")
OUT = os.path.join(HERE, "_out_466_rogers_siegel_tail.txt")
EULER_GAMMA = 0.5772156649015329


def main():
    n = 32
    sample_target = 2000
    limit = 4 * 32 ** 4 + 10
    isprime = rs.sieve(limit)
    small_primes = [i for i in range(2, 3000) if isprime[i]]

    lo, hi = n ** 4, 4 * n ** 4
    allp = [p for p in range(lo + 1, hi + 1, n) if isprime[p]]
    structured = [p for p in allp if rs.gf_level(p) > 0 or rs.v2(p - 1) >= 12]
    step = len(allp) / sample_target
    chosen = sorted(set([allp[int(i * step)] for i in range(sample_target)] + structured))
    print(f"n=32 ensemble rebuilt: {len(allp)} primes total, {len(chosen)} chosen, "
          f"{len(structured)} structured", flush=True)

    done = {}
    if os.path.exists(CKPT):
        for line in open(CKPT):
            f = line.strip().split(",")
            if len(f) == 8:
                done[int(f[0])] = tuple(float(x) if "." in x or "e" in x else int(x)
                                        for x in f)
        print(f"checkpoint: {len(done)} primes already done", flush=True)

    ck = open(CKPT, "a")
    failures = []
    t0 = time.time()
    todo = [p for p in chosen if p not in done]
    for k, p in enumerate(todo):
        try:
            g = rs.find_generator(p, small_primes)
            M, m, parseval = rs.exact_M(p, n, g)
            rel = abs(parseval - (p - n)) / (p - n)
            if rel >= 1e-6:
                failures.append((p, f"PARSEVAL rel={rel:.3e}"))
                continue
            sigma = math.sqrt((p - n) / m)
            x = M / math.sqrt(n * math.log(p / n))
            loc, scale = rs.gumbel_loc_scale(m, sigma)
            z = (M - loc) / scale
            row = (p, m, M, x, z, rs.v2(p - 1), rs.gf_level(p),
                   rs.least_prime_factor(m, small_primes))
            done[p] = row
            ck.write(",".join(repr(v) for v in row) + "\n")
            if (k + 1) % 50 == 0:
                ck.flush()
            if (k + 1) % 250 == 0:
                print(f"  ... {k + 1}/{len(todo)} new primes, {time.time() - t0:.0f}s",
                      flush=True)
        except Exception as e:  # noqa: BLE001 -- attribute the crash, keep going
            failures.append((p, f"{type(e).__name__}: {e}"))
            print(f"  !! FAILURE at p={p}: {type(e).__name__}: {e}", flush=True)
    ck.close()
    print(f"scan complete: {len(done)} ok, {len(failures)} failures, "
          f"{time.time() - t0:.0f}s", flush=True)

    rows = [done[p] for p in sorted(done)]
    dt = np.dtype([("p", np.int64), ("m", np.int64), ("M", np.float64),
                   ("x", np.float64), ("z", np.float64), ("v2", np.int64),
                   ("gf", np.int64), ("lpf", np.int64)])
    arr = np.array(rows, dtype=dt)

    lines = []

    def out(s=""):
        print(s, flush=True)
        lines.append(s)

    out("")
    out("(n = 32 block completed by probe_466_rogers_siegel_tail_n32_resume.py -- the")
    out(" in-place n=32 scan of the parent probe died silently mid-run twice; this")
    out(" driver redid the identical deterministic ensemble with per-prime trapping.)")
    if failures:
        out(f"PER-PRIME FAILURES ({len(failures)}):")
        for p, msg in failures:
            out(f"   p={p}: {msg}")
    else:
        out("per-prime failures: NONE (every prime computed exactly; Parseval <1e-6 all)")

    def stats(tag, a):
        x = a["x"]
        z = a["z"]
        qs = np.percentile(x, [0, 1, 5, 10, 25, 50, 75, 90, 95, 99, 100])
        out(f"\n-- {tag}  (N = {len(a)}) --")
        out(f"x = M/sqrt(n log(p/n)):  mean {x.mean():.4f}  std {x.std():.4f}  "
            f"skew {float(((x - x.mean()) ** 3).mean() / x.std() ** 3):+.3f}")
        out("x quantiles  min/1/5/10/25/50/75/90/95/99/max:")
        out("   " + "  ".join(f"{q:.3f}" for q in qs))
        out(f"lower tail:  P(x<1.0) = {np.mean(x < 1.0):.5f}   "
            f"P(x<0.9) = {np.mean(x < 0.9):.5f}   "
            f"P(x<1.1) = {np.mean(x < 1.1):.5f}   P(x<1.2) = {np.mean(x < 1.2):.5f}")
        out(f"upper tail:  P(x>1.8) = {np.mean(x > 1.8):.5f}   "
            f"P(x>2.0) = {np.mean(x > 2.0):.5f}   P(x>2.5) = {np.mean(x > 2.5):.5f}")
        out(f"Gumbel-standardized z (iid benchmark: mean {EULER_GAMMA:.4f}, "
            f"std {math.pi / math.sqrt(6):.4f}):")
        out(f"   observed mean {z.mean():.4f}  std {z.std():.4f}")
        out(f"   P(z<-1) obs {np.mean(z < -1):.5f} vs Gumbel {math.exp(-math.e):.5f}   "
            f"P(z<-2) obs {np.mean(z < -2):.6f} vs Gumbel {math.exp(-math.e ** 2):.6f}")

    stats("ALL primes", arr)
    non_gf = arr[arr["gf"] == 0]
    if len(non_gf) < len(arr):
        stats("NON-GF primes only (regime discipline)", non_gf)
        gf = arr[arr["gf"] > 0]
        out(f"\n-- GF primes p = b^(2^s)+1 in window: {len(gf)} --")
        for r in gf:
            out(f"   p={r['p']}  s={r['gf']}  v2={r['v2']}  x={r['x']:.4f}  z={r['z']:+.3f}")

    order = np.argsort(arr["x"])
    out("\n-- 15 SMALLEST-x primes (the lower tail; anomaly-class scan) --")
    out("   p        m       v2  GF  lpf(m)     x       z")
    for i in order[:15]:
        r = arr[i]
        out(f"   {r['p']:<8} {r['m']:<7} {r['v2']:<3} {r['gf']:<3} {r['lpf']:<9} "
            f"{r['x']:.4f}  {r['z']:+.3f}")
    out("-- 10 LARGEST-x primes (upper tail) --")
    for i in order[-10:][::-1]:
        r = arr[i]
        out(f"   {r['p']:<8} {r['m']:<7} {r['v2']:<3} {r['gf']:<3} {r['lpf']:<9} "
            f"{r['x']:.4f}  {r['z']:+.3f}")

    out("\n-- mean x by v2(p-1) --")
    for v in sorted(set(arr["v2"].tolist())):
        sel = arr[arr["v2"] == v]
        out(f"   v2={v:<3} N={len(sel):<5} mean x = {sel['x'].mean():.4f}  "
            f"min x = {sel['x'].min():.4f}")
    med = np.median(arr["x"])
    tail = arr[arr["x"] < 0.85 * med]
    out(f"\nprimes with x < 0.85 * median ({0.85 * med:.3f}): {len(tail)} "
        f"({len(tail) / len(arr):.5f} of ensemble)")

    out("")
    out("CONCENTRATION TEST (n=32 vs the n=16 block above):")
    an = arr[arr["gf"] == 0]
    out(f"  n=32: std(x) all = {arr['x'].std():.4f}, non-GF = {an['x'].std():.4f}, "
        f"median = {np.median(arr['x']):.4f}, mean log m = "
        f"{np.mean(np.log(arr['m'].astype(float))):.2f}")
    pred = np.mean(math.pi / math.sqrt(6) /
                   np.sqrt(2 * np.log(2 * arr["m"].astype(float))
                           * np.log(arr["p"].astype(float) / n)))
    out(f"  n=32: Gumbel-predicted std(x) = {pred:.4f}")
    out(f"  (n=16 reference, from the block above: std 0.0193, median 1.1470)")

    with open(OUT, "a", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    print(f"\nappended n=32 block to {OUT}", flush=True)


if __name__ == "__main__":
    main()
