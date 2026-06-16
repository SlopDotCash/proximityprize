"""
probe_444_hypocycloid_anisotropy.py  (lens [hypocycloid-support], part C, issue #444)

Last form of the lead worth testing: even if the hull RADIUS = house = sqrt(n log m) (the wall),
maybe the support is ANISOTROPIC -- a hypocycloid is a thin curved region, not a disk. If the
period cloud were confined to a sqrt(n)-THIN annulus/curve (one direction sqrt(n log m), the
transverse direction only sqrt(n)), a directional bound could still help (e.g. project onto the
thin axis). We measure the cloud's anisotropy: principal-axis spread (SVD of the centered
point set), the min-width over directions (the support 'thickness'), and whether the hull is a
genuine 2D blob (radius ~ width, isotropic disk) or a thin hypocycloid curve.

If min-width ~ sqrt(n) << house ~ sqrt(n log m): thin support, possible directional handle.
If min-width ~ house (isotropic disk): support is a full disk of radius sqrt(n log m) = pure wall.
"""
import math, cmath
import numpy as np
from sympy import isprime, primitive_root


def order_subgroup(p, n):
    g0 = int(primitive_root(p))
    g = pow(g0, (p - 1) // n, p)
    s, x = [], 1
    for _ in range(n):
        s.append(x); x = (x * g) % p
    return s, g0


def period_points(p, n):
    S, g0 = order_subgroup(p, n)
    m = (p - 1) // n
    reps = [pow(g0, j, p) for j in range(m)]
    w = 2 * math.pi / p
    pts = []
    for b in reps:
        s = 0j
        for x in S:
            s += cmath.exp(1j * w * ((b * x) % p))
        pts.append(s)
    return np.array([[z.real, z.imag] for z in pts]), m


def min_width(P):
    """min over directions u of (max - min) of P.u  = support thickness (rotating-calipers-ish)."""
    best = float('inf')
    for k in range(180):
        th = math.pi * k / 180
        u = np.array([math.cos(th), math.sin(th)])
        proj = P @ u
        w = proj.max() - proj.min()
        if w < best:
            best = w
    return best


def main():
    print("=" * 100)
    print("[hypocycloid-support] part C: anisotropy of the period cloud (thin curve vs isotropic disk)")
    print("=" * 100)
    cases = []
    for n in [8, 16, 32, 64]:
        for kk in [2.0, 3.0, 4.0]:
            target = int(n ** kk)
            p = None
            for cand in range(target - target % n + 1, target * 4, n):
                if cand > n + 1 and isprime(cand):
                    p = cand; break
            if p:
                cases.append((p, n))
    print(f"{'p':>9} {'n':>4} {'m':>7} {'house':>8} {'maxwidth':>9} {'minwidth':>9} "
          f"{'aniso=mx/mn':>11} {'minw/sqrtn':>10} {'house/sqrtn':>11}")
    for p, n in cases:
        m = (p - 1) // n
        if m > 40000:
            continue
        P, m = period_points(p, n)
        C = P - P.mean(axis=0)
        house = np.max(np.sqrt((P ** 2).sum(axis=1)))
        # max width over directions
        mxw = 0.0
        for k in range(180):
            th = math.pi * k / 180
            u = np.array([math.cos(th), math.sin(th)])
            proj = C @ u
            w = proj.max() - proj.min()
            if w > mxw: mxw = w
        mnw = min_width(C)
        aniso = mxw / mnw if mnw > 0 else float('inf')
        print(f"{p:>9} {n:>4} {m:>7} {house:>8.2f} {mxw:>9.2f} {mnw:>9.2f} "
              f"{aniso:>11.3f} {mnw/math.sqrt(n):>10.3f} {house/math.sqrt(n):>11.3f}")
    print("-" * 100)
    print("READING:")
    print(" * aniso ~ 1 and minw/sqrtn GROWS with m  => isotropic disk of radius sqrt(n log m):")
    print("   support = full wall disk, NO thin direction. Lead REFUTED / reduces-to-wall.")
    print(" * minw/sqrtn FLAT (O(1)) while house/sqrtn grows => genuine thin sqrt(n) axis: SURVIVES")
    print("   (a directional/projection handle would then exist).")


if __name__ == "__main__":
    main()
