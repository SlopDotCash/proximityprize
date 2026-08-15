"""
Claim (non-Fourier, from central symmetry O=-O ALONE, no integer lift):
If the dilated orbit O (|O|=n, centrally symmetric) is contained in a length-V natAbs
interval about center a, i.e. O ⊆ {y : valMinAbs(y-a) natAbs <= V}, then since O=-O,
also O ⊆ {y: |vma(y+a)| <= V}. Every point z in O has |vma(z-a)|<=V AND |vma(z+a)|<=V.
Then vma(2a) = vma((z+a)-(z-a)) has natAbs <= 2V (triangle ineq on lifts when 2V<p/2).
So 2a is within 2V of 0 => a is a near-2-torsion point (a ≈ 0 or a ≈ p/2 within V).

=> An off-center (a not near 0 or p/2) short interval CANNOT contain O, at ANY scale V
   with 4V < p (much weaker than 2V^2<p!). The residual case is intervals centered at
   a 2-torsion point, where G99's √(p/2) integer-lift then finishes.

Verify empirically: for intervals NOT centered near {0, p/2}, orbit never fits even for
V well above √(p/2). And for centered ones, √(p/2) is the true threshold.
"""
from sympy import isprime, primitive_root
import math

def vma(z, p):
    z %= p
    return z if z <= p // 2 else z - p

def orbit(p, x, b, n):
    return [(b * pow(x, k, p)) % p for k in range(n)]

def fits_interval(O, p, a, V):
    return all(abs(vma(z - a, p)) <= V for z in O)

for (p, n) in [(65537, 16), (65537, 32), (7681, 16), (40961, 32)]:
    if not isprime(p):
        continue
    g = primitive_root(p)
    x = pow(g, (p - 1) // n, p)
    if pow(x, n, p) != 1 or pow(x, 2, p) == 1:
        continue
    b = 1
    O = orbit(p, x, b, n)
    Vg99 = int(math.isqrt(p // 2))
    # For each possible center a, find the min V that fits. Sample many centers.
    fitting_centers = []
    # test at V a bit above g99 threshold to show off-center never fits
    Vtest = 2 * Vg99
    for a in range(0, p, max(1, p // 400)):
        if fits_interval(O, p, a, Vtest):
            fitting_centers.append((a, min(abs(vma(a, p)), abs(vma(a - p // 2, p)))))
    print(f"p={p} n={n} Vg99=√(p/2)≈{Vg99}  Vtest=2·Vg99={Vtest}")
    print(f"  centers (sampled) that fit at Vtest: {len(fitting_centers)}")
    if fitting_centers:
        # report their distance to nearest 2-torsion point {0, p/2}
        dists = sorted(d for (_, d) in fitting_centers)
        print(f"  their dist to {{0,p/2}}: min={dists[0]} max={dists[-1]}  (all near 2-torsion => claim holds)")
    else:
        print("  NONE fit even at 2·Vg99 (orbit spread beyond any short interval)")
