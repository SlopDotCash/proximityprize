#!/usr/bin/env python3
"""Check the optimized Corvaja–Zannier parameters, subdegrees and branch signatures."""
from fractions import Fraction
from math import ceil


def finite_stabilizer(degree):
    # The off-diagonal pullback of W(z)=z^3+z+1 by z=x^degree has equation
    # x^(2d)+x^d*y^d+y^(2d)+1=0. Its smooth projective model is a conic or quartic.
    p = 17
    exponents = [(2*degree, 0), (degree, degree), (0, 2*degree)]
    stabilizer = [(a, b) for a in range(1, p) for b in range(1, p)
                  if all(pow(a, i, p)*pow(b, j, p) % p == 1 for i, j in exponents)]
    assert len(stabilizer) == 2*degree**2
    assert sum(a == 1 for a, b in stabilizer) == degree
    assert Fraction((p-1)*2*degree, len(stabilizer)) == (p-1)//degree


def main():
    n, degree = 2**30, 2**28-2
    lam = Fraction(78*degree-14*n, 325)
    assert 6*Fraction(degree, 89) < lam
    candidates = []
    for h in range(1, 45):
        for k in range(1, 45):
            dimension = h*k+h+k
            if dimension <= 89:
                ratio = Fraction(h+3*k, dimension)
                candidates.append((2*(3*degree-n*ratio)/(dimension-1), h, k))
    candidates.sort(reverse=True)
    assert candidates[0] == (lam, 8, 2)
    assert candidates[1][0] < lam
    subdegree = ceil(lam/2)
    assert subdegree == 9_085_508 and degree//subdegree == 29
    assert 4 * 108*n**2 < (3*degree)**3
    print(f"{len(candidates)} admissible parameter pairs below dimension 90; unique optimum (8, 2).")
    print(f"Nontrivial subdegree >= {subdegree}, at most {degree//subdegree} such suborbits.")
    for t, h, threshold, gmin in [
        (19_173_961, 1, 1_801_168, 174_205_119_066_280),
        (38_347_922, 2, 620_967, 87_102_540_359_181),
        (134_217_727, 1, 145_214, 1_219_435_887_976_983),
        (268_435_454, 2, 70_063, 609_717_809_770_766),
    ]:
        m = t//h
        excess = 2*(lam-4*h)/(2*(t+h)-lam)
        assert threshold < excess*1_000_000 < threshold+1
        assert ceil(1+(m-1)*(lam/h-4)/2) == gmin
        assert excess/(degree//t) > Fraction(70_063, 1_000_000)
        print(f"prefix {t}, source degree {h}: E >= {excess}, pair genus >= {gmin}")
    for h in (1, 2):
        finite_stabilizer(h)
    print("Two finite-field scaling stabilizers and their projection kernels verified.")


if __name__ == "__main__":
    main()
