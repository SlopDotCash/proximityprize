#!/usr/bin/env python3
"""G94 supplement: (a) verify value-factoring exactly (cocycle metrics constant on pairs with
equal eta up to fp error); (b) anatomy of the domination-forcing pairs for cocycle metrics
(are they lone-spike shaped: large |Delta eta| at tiny cocycle distance?); (c) exact-value
degeneracy check (distinct cosets, equal eta)."""
import numpy as np, math
import importlib.util
spec = importlib.util.spec_from_file_location("probe", "probe_g94_jacobi_cocycle_metric.py")
P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)

for (p, n) in [(761, 8), (6529, 16)]:
    m = (p-1)//n
    eta, coset_of, reps = P.gauss_periods(p, n)
    w = np.full(m, 1.0/m)
    a, b, V = P.stieltjes(eta, w, min(m-1, 48))
    K = max(2, int(math.ceil(math.log(p))))
    A = P.transfer_products(a, b, K, eta.astype(complex))
    F = np.real(A).reshape(m, 4)
    Dtm = P.pdist_from_features(F)
    Dval = np.abs(eta[:, None] - eta[None, :])
    iu = np.triu_indices(m, 1)
    # (a) value-factoring: pairs with near-equal eta must have near-zero d_tm
    close = Dval[iu] < 1e-8
    print(f"n={n} p={p}: pairs with |Deta|<1e-8: {int(close.sum())}, "
          f"max d_tm on those: {Dtm[iu][close].max() if close.any() else float('nan'):.3g} "
          f"(value-factoring: should be ~0)")
    # near-duplicate eta values (spectrum degeneracy across cosets)
    se = np.sort(eta)
    mind = np.min(np.diff(se))
    print(f"   min spacing of eta values: {mind:.3e} (near-degenerate pairs are where any "
          f"injective-in-b metric hope dies: cocycle data identical, frequencies distinct)")
    # (b) anatomy: top-5 pairs by Deta/dtm ratio
    r = Dval[iu]/np.maximum(Dtm[iu], 1e-300)
    top = np.argsort(r)[-5:][::-1]
    print("   top domination-forcing pairs for d_tm (Deta, d_tm, eta_i, eta_j):")
    for t in top:
        i, j = iu[0][t], iu[1][t]
        print(f"     Deta={Dval[i,j]:8.4f} d_tm={Dtm[i,j]:10.4g} "
              f"eta=({eta[i]:8.4f},{eta[j]:8.4f}) ratio={r[t]:9.3g}")
    # (c) where is the sup pair in cocycle gauge?
    imax = int(np.argmax(np.abs(eta)))
    inear = int(np.argmin(np.abs(eta - np.median(eta))))
    print(f"   sup coset eta={eta[imax]:.4f} vs bulk eta={eta[inear]:.4f}: "
          f"Deta={abs(eta[imax]-eta[inear]):.4f}, d_tm={Dtm[imax,inear]:.4g}, "
          f"d_val={Dval[imax,inear]:.4f}")
