"""
probe_444_r6_fast.py  (#444 deep-band demand census, r=6, numpy-vectorized)

FAST kernel using the barycentric top-2-coefficient identity (verified vs full Gaussian-elim
interpolation, 0 mismatch in /tmp/verify_dd.py):
  For a node set S of size a0=r+1 (so deg<=r interpolant), with barycentric weights
    w_i = 1 / prod_{j!=i}(x_i - x_j),  E1 = sum_i x_i,
  the top-2 interpolant coefficients of values y on S are
    c_r     = sum_i  y_i * w_i
    c_{r-1} = -sum_i y_i * (E1 - x_i) * w_i.
  A line (x^e, x^f) is BAD on S with scalar gamma iff the 2x2 band matrix
    [[c_r(e),  c_r(f) ],
     [c_{rm1}(e), c_{rm1}(f)]]
  is singular AND nondegenerate (not both rows zero across the two witnesses), with the SAME gamma
  pinned by both rows.  gamma = -c_r(e)/c_r(f) (or via the c_{r-1} row when c_r(f)=0), and we require
  the two band degrees to agree (exactly the validated interpolation condition).

  #bad   = distinct nonzero pinned gamma  (+ [gamma=0 reachable]).
  O_P    = #distinct nonzero gamma orbits under multiply-by w^{e-f} (dilation eigenvector).

LARGE prime p = BabyBear = 2013265921 (2^27 | p-1) => char-0 worst case.
"""
import numpy as np
import itertools, sys, time, os
from math import comb, gcd

P = 2013265921

def w_of_order(n):
    e = (P - 1) // n
    for c in range(2, 500):
        h = pow(c, e, P)
        if pow(h, n, P) == 1 and pow(h, n // 2, P) != 1:
            return h
    raise RuntimeError("no w of order %d" % n)

def inv_mod_arr(a):
    """vectorized modular inverse via Fermat (a^(P-2) mod P), a: int64 numpy array, 0 -> 0."""
    # use Python pow per element is slow; do square-and-multiply vectorized.
    exp = P - 2
    result = np.ones_like(a, dtype=object)  # fallback path not used; see fast version below
    raise NotImplementedError

# We avoid array exponentiation entirely. The only modular inverses needed are the barycentric
# weights' denominators (one per (i,S)) and the final gamma ratios (few). We batch the weight
# denominators with a single big Fermat exponentiation using numpy int64 + repeated squaring on
# the WHOLE array at once.

def batch_inv(arr):
    """Modular inverse of every entry of int64 numpy array arr mod P (Fermat). 0 stays 0."""
    a = (arr % P).astype(np.int64)
    res = np.ones_like(a)
    base = a.copy()
    e = P - 2
    while e > 0:
        if e & 1:
            res = (res * base) % P
        base = (base * base) % P
        e >>= 1
    res[a == 0] = 0
    return res

def _process_chunk(X, e, f, a0):
    """X: (C,a0) int64 node values. Return (cr_e,crm1_e,cr_f,crm1_f) band coeffs per subset."""
    ncomb = X.shape[0]
    diff = (X[:, :, None] - X[:, None, :]) % P     # (C, a0, a0): x_i - x_j
    idx = np.arange(a0)
    diff[:, idx, idx] = 1
    denom = np.ones((ncomb, a0), dtype=np.int64)
    for j in range(a0):
        denom = (denom * diff[:, :, j]) % P
    del diff
    wts = batch_inv(denom)                         # (C, a0)
    E1 = X.sum(axis=1) % P
    coef_em1 = (E1[:, None] - X) % P

    def band_coeffs(ex):
        Y = np.ones((ncomb, a0), dtype=np.int64)
        base = X.copy()
        ee = ex
        while ee > 0:
            if ee & 1:
                Y = (Y * base) % P
            base = (base * base) % P
            ee >>= 1
        yw = (Y * wts) % P
        c_r = yw.sum(axis=1) % P
        c_rm1 = (P - (yw * coef_em1 % P).sum(axis=1) % P) % P
        return c_r, c_rm1

    cr_e, crm1_e = band_coeffs(e)
    cr_f, crm1_f = band_coeffs(f)
    return cr_e, crm1_e, cr_f, crm1_f

def census_line(n, r, e, f, mu_np, w, chunk=400000):
    """Vectorized census for one line. mu_np: int64 array of mu_n. Returns stats dict.
    Subsets processed in chunks of `chunk` to bound memory (n=32 a0=7 -> 3.36M subsets)."""
    a0 = r + 1
    badset = set()
    zero_bad = False
    comb_iter = itertools.combinations(range(n), a0)
    while True:
        block = list(itertools.islice(comb_iter, chunk))
        if not block:
            break
        combs = np.array(block, dtype=np.int64)        # (c, a0)
        X = mu_np[combs]
        cr_e, crm1_e, cr_f, crm1_f = _process_chunk(X, e, f, a0)
        det = (cr_e * crm1_f - cr_f * crm1_e) % P
        nondeg = ~((cr_e == 0) & (crm1_e == 0) & (cr_f == 0) & (crm1_f == 0))
        cand = (det == 0) & nondeg
        ci = np.nonzero(cand)[0]
        if ci.size == 0:
            continue
        # Split candidates: dominant branch cr_f != 0 -> gamma = -cr_e/cr_f (singularity guarantees
        # the crm1 band agrees). Rare branch cr_f == 0 handled in Python (exact interpolation logic).
        crf = cr_f[ci]; cre = cr_e[ci]
        mask_main = (crf != 0)
        # main branch: vectorized gamma = -cre/crf
        if mask_main.any():
            cf = crf[mask_main]; ce = cre[mask_main]
            inv = batch_inv(cf.astype(np.int64))
            gam_main = ((P - ce) % P * inv) % P
            for g in gam_main.tolist():
                if g == 0:
                    zero_bad = True
                else:
                    badset.add(int(g))
        # rare branch cr_f == 0: replicate exact two-band logic in Python
        rare = ci[~mask_main]
        for t in rare.tolist():
            x0r, x1r = int(cr_e[t]), int(cr_f[t])   # x1r == 0 here
            x0m, x1m = int(crm1_e[t]), int(crm1_f[t])
            gam = None; ok = True; nd = False
            for (x0, x1) in ((x0m, x1m), (x0r, x1r)):
                if x0 or x1:
                    nd = True
                if x1 == 0:
                    if x0:
                        ok = False; break
                else:
                    g = (-x0 * pow(x1, P - 2, P)) % P
                    if gam is None:
                        gam = g
                    elif gam != g:
                        ok = False; break
            if ok and nd and gam is not None:
                if gam == 0:
                    zero_bad = True
                else:
                    badset.add(gam)
    # O_P: orbits under multiply by w^{e-f}
    d = gcd((e - f) % n, n)
    mult = pow(w, (e - f) % n, P)
    rem = set(badset); orbs = 0
    while rem:
        x0 = next(iter(rem)); cur = x0; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % P
        orbs += 1; rem -= o
    K = (1 << r) * comb(n // 2, r)
    return dict(nbad=len(badset), zero=int(zero_bad), OP=orbs, d=d, K=K,
                ratio=(len(badset) / K if K else 0.0))

def full_sweep_allexp(n, r, chunk=300000):
    """Compute #bad and O_P for ALL lines (e>f) at once. Precompute node-set quantities and the
    per-exponent band coeffs (c_r[ex], c_{r-1}[ex]) once per subset-chunk, accumulating per-line
    bad-gamma sets. Returns {(e,f): dict(nbad,zero,OP,d)}.  This is the node-weight-reuse speedup."""
    a0 = r + 1
    w = w_of_order(n)
    mu = np.array([pow(w, i, P) for i in range(n)], dtype=np.int64)
    exps = list(range(0, n))
    # per-line accumulators: set of nonzero gamma, and zero-reachable flag
    badsets = {(e, f): set() for e in range(1, n) for f in range(0, e)}
    zeroflag = {(e, f): False for e in range(1, n) for f in range(0, e)}
    comb_iter = itertools.combinations(range(n), a0)
    nproc = 0
    while True:
        block = list(itertools.islice(comb_iter, chunk))
        if not block:
            break
        combs = np.array(block, dtype=np.int64)
        X = mu[combs]
        c = X.shape[0]; nproc += c
        # node-set quantities (line-independent)
        diff = (X[:, :, None] - X[:, None, :]) % P
        idx = np.arange(a0); diff[:, idx, idx] = 1
        denom = np.ones((c, a0), dtype=np.int64)
        for j in range(a0):
            denom = (denom * diff[:, :, j]) % P
        del diff
        wts = batch_inv(denom)
        E1 = X.sum(axis=1) % P
        coef_em1 = (E1[:, None] - X) % P
        # per-exponent band coeffs
        CR = np.empty((n, c), dtype=np.int64)     # c_r[ex]
        CM = np.empty((n, c), dtype=np.int64)     # c_{r-1}[ex]
        # x_i^ex incrementally: ex from 0..n-1
        Y = np.ones((c, a0), dtype=np.int64)
        for ex in range(n):
            yw = (Y * wts) % P
            CR[ex] = yw.sum(axis=1) % P
            CM[ex] = (P - (yw * coef_em1 % P).sum(axis=1) % P) % P
            Y = (Y * X) % P
        # per line: singular & nondeg & pin gamma. Fully vectorized via np.unique on gamma arrays.
        for e in range(1, n):
            cre = CR[e]; crm1e = CM[e]
            for f in range(0, e):
                crf = CR[f]; crm1f = CM[f]
                det = (cre * crm1f - crf * crm1e) % P
                nondeg = ~((cre == 0) & (crm1e == 0) & (crf == 0) & (crm1f == 0))
                cand = (det == 0) & nondeg
                ci = np.nonzero(cand)[0]
                if ci.size == 0:
                    continue
                crf_c = crf[ci]; cre_c = cre[ci]; crm1f_c = crm1f[ci]; crm1e_c = crm1e[ci]
                # gamma: where crf!=0 -> -cre/crf ; else (crf==0, det=0 => crm1e=0 too) use crm1 row:
                #   if crm1f!=0 -> -crm1e/crm1f ; else both rows have x1=0 -> only bad if x0=0 (then
                #   degenerate, excluded by nondeg already on the union) -> no gamma pinned.
                gam = np.full(ci.size, -1, dtype=np.int64)
                m1 = (crf_c != 0)
                if m1.any():
                    inv = batch_inv(crf_c[m1])
                    gam[m1] = ((P - cre_c[m1]) % P * inv) % P
                m2 = (~m1) & (crm1f_c != 0)
                if m2.any():
                    inv2 = batch_inv(crm1f_c[m2])
                    gam[m2] = ((P - crm1e_c[m2]) % P * inv2) % P
                # remaining (crf==0 and crm1f==0): cre and crm1e must be 0 by det/nondeg logic;
                # these pin no gamma (skip, gam stays -1).
                gv = gam[gam >= 0]
                if gv.size == 0:
                    continue
                uniq = np.unique(gv)
                if (uniq == 0).any():
                    zeroflag[(e, f)] = True
                nz = uniq[uniq != 0]
                if nz.size:
                    badsets[(e, f)].update(nz.tolist())
    # finalize: O_P per line
    out = {}
    for (e, f), bs in badsets.items():
        d = gcd((e - f) % n, n); mult = pow(w, (e - f) % n, P)
        rem = set(bs); orbs = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; o = set()
            for _ in range(n):
                o.add(cur); cur = cur * mult % P
            orbs += 1; rem -= o
        out[(e, f)] = dict(nbad=len(bs), zero=int(zeroflag[(e, f)]), OP=orbs, d=d)
    return out

def calibrate_fast():
    print("=== FAST CALIBRATION (barycentric kernel) ===")
    ok = True
    # r=3 known closed form
    for n in [16, 32]:
        w = w_of_order(n); mu = np.array([pow(w, i, P) for i in range(n)], dtype=np.int64)
        st = census_line(n, 3, n // 2, n // 2 - 1, mu, w)
        exp_OP = comb(n // 4, 2); exp_incl = n * comb(n // 4, 2) + 1
        incl = st['nbad'] + st['zero']
        good = (st['OP'] == exp_OP) and (incl == exp_incl)
        ok = ok and good
        print(f"  r=3 n={n} (x^{n//2},x^{n//2-1}): O_P={st['OP']}(exp{exp_OP}) "
              f"#bad+zero={incl}(exp{exp_incl}) -> {'OK' if good else 'MISMATCH'}")
    # r=4 reference lines
    for (n, e, f, eb, eo) in [(16, 8, 5, 145, 9), (32, 16, 13, 577, 18)]:
        w = w_of_order(n); mu = np.array([pow(w, i, P) for i in range(n)], dtype=np.int64)
        st = census_line(n, 4, e, f, mu, w)
        incl = st['nbad'] + st['zero']
        good = (incl == eb) and (st['OP'] == eo)
        ok = ok and good
        print(f"  r=4 n={n} (x^{e},x^{f}): #bad+zero={incl}(ref{eb}) O_P={st['OP']}(ref{eo}) "
              f"-> {'OK' if good else 'MISMATCH'}")
    # r=6 n=16 known winners from the slow sweep: (10,8)->#bad112,zero1,O_P14
    w = w_of_order(16); mu = np.array([pow(w, i, P) for i in range(16)], dtype=np.int64)
    st = census_line(16, 6, 10, 8, mu, w)
    good = (st['nbad'] == 112) and (st['zero'] == 1) and (st['OP'] == 14)
    ok = ok and good
    print(f"  r=6 n=16 (x^10,x^8): #bad={st['nbad']}(exp112) zero={st['zero']} O_P={st['OP']}(exp14) "
          f"-> {'OK' if good else 'MISMATCH'}")
    print(f"  FAST CALIBRATION {'PASSED' if ok else 'FAILED'}")
    return ok

def sweep(n, r, lines, label, topk=20):
    w = w_of_order(n); mu = np.array([pow(w, i, P) for i in range(n)], dtype=np.int64)
    K = (1 << r) * comb(n // 2, r)
    res = []
    for (e, f) in lines:
        st = census_line(n, r, e, f, mu, w)
        res.append(((e, f), st))
    res.sort(key=lambda kv: (kv[1]['nbad'], kv[1]['OP']), reverse=True)
    print(f"=== r={r} {label} n={n} (K=2^{r}*C({n//2},{r})={K}); top {topk} by #bad ===")
    for (e, f), st in res[:topk]:
        print(f"  line(x^{e:>2},x^{f:>2}) d={st['d']:>2}: #bad={st['nbad']:>6} +zero={st['zero']} "
              f"O_P={st['OP']:>5} bad/K={st['ratio']:.4f}")
    return res

if __name__ == "__main__":
    t0 = time.time()
    calibrate_fast()
    print(f"  [calibration took {time.time()-t0:.1f}s]")
    print()
    mode = sys.argv[1] if len(sys.argv) > 1 else "n16full"
    if mode == "n16full":
        t1 = time.time()
        lines = [(e, f) for e in range(1, 16) for f in range(0, e)]
        sweep(16, 6, lines, "FULL SWEEP", topk=20)
        print(f"  [n=16 r=6 full sweep ({len(lines)} lines) took {time.time()-t1:.1f}s]")
    elif mode == "n32":
        # n=32 r=6: C(32,7)=3.36M subsets/line. Sweep a curated candidate set first (small gaps),
        # then expand around the winner. Each line is heavy (~minutes), so report incrementally.
        t1 = time.time()
        cands = []
        for e in range(2, 32):
            for g in (1, 2, 3, 4, 5, 6):
                f = e - g
                if f >= 0:
                    cands.append((e, f))
        cands = sorted(set(cands))
        print(f"  [n=32 r=6: {len(cands)} candidate lines, ~minutes each]")
        sweep(32, 6, cands, "CANDIDATE SWEEP", topk=25)
        print(f"  [n=32 r=6 candidate sweep took {time.time()-t1:.1f}s]")
    elif mode == "n32lines":
        # explicit line list from argv: pairs e,f e,f ...
        lines = []
        toks = sys.argv[2:]
        for i in range(0, len(toks), 2):
            lines.append((int(toks[i]), int(toks[i + 1])))
        sweep(32, 6, lines, "EXPLICIT LINES", topk=len(lines))
    elif mode == "n32full":
        # FULL e>f sweep at n=32 r=6, RESUMABLE via a checkpoint file. Each completed line is
        # appended as "e f nbad zero OP d" so reruns skip done lines. Run in 10-min chunks.
        import json
        n, r = 32, 6
        ckpt = sys.argv[2] if len(sys.argv) > 2 else r"C:\Users\Administrator\arklib\scripts\probes\n32_r6_ckpt.txt"
        w = w_of_order(n); mu = np.array([pow(w, i, P) for i in range(n)], dtype=np.int64)
        K = (1 << r) * comb(n // 2, r)
        lines = [(e, f) for e in range(1, n) for f in range(0, e)]
        lines.sort(key=lambda ef: (abs(ef[0] - ef[1]), ef[0]))
        done = {}
        if os.path.exists(ckpt):
            with open(ckpt) as fh:
                for ln in fh:
                    a = ln.split()
                    if len(a) == 6:
                        done[(int(a[0]), int(a[1]))] = tuple(int(x) for x in a[2:])
        todo = [ef for ef in lines if ef not in done]
        print(f"=== n=32 r=6 RESUMABLE sweep: {len(done)} done, {len(todo)} todo ===", flush=True)
        t1 = time.time()
        deadline = float(os.environ.get("SWEEP_DEADLINE_S", "9999999"))  # default: run to completion
        with open(ckpt, "a") as fh:
            for (e, f) in todo:
                if time.time() - t1 > deadline:
                    print(f"  [time cap hit, {len([1 for _ in done])} done; rerun to continue]", flush=True)
                    break
                st = census_line(n, r, e, f, mu, w)
                fh.write(f"{e} {f} {st['nbad']} {st['zero']} {st['OP']} {st['d']}\n"); fh.flush()
                done[(e, f)] = (st['nbad'], st['zero'], st['OP'], st['d'])
                print(f"  done(x^{e},x^{f}) #bad={st['nbad']} O_P={st['OP']} [{time.time()-t1:.0f}s, {len(done)}/{len(lines)}]", flush=True)
        if len(done) == len(lines):
            print(f"=== n=32 r=6 COMPLETE: TOP 25 ===", flush=True)
            res = sorted(done.items(), key=lambda kv: (kv[1][0], kv[1][2]), reverse=True)
            for (e, f), (nb, z, op, d) in res[:25]:
                print(f"  line(x^{e:>2},x^{f:>2}) d={d:>2}: #bad={nb:>7} +zero={z} O_P={op:>6} bad/K={nb/K:.5f}", flush=True)
