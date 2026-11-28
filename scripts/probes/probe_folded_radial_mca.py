#!/usr/bin/env python3
"""Verify folded first-derivative interpolation and its two-polar degree prices."""
from itertools import combinations
from math import comb


N = 2**30
BOARDS = (
    # Rate denominator, errors, order, derivative cap, plane cap, reserved weight, surplus.
    (2, 314_491_699, 19, 6, 99, False, 4_128_454_092),
    (4, 536_870_913, 11, 5, 63, False, 17_888),
    (2, 314_491_699, 15, 2, 292, False, 1_603_007_627),
    (4, 536_870_913, 9, 2, 167, False, 1_610_623_611),
    (2, 314_491_699, 73, 24, 359, True, 459_712_885_250),
    (4, 536_870_913, 55, 26, 269, True, 729_614_679_390),
    (2, 314_491_699, 57, 15, 453, True, 193_772_302_476),
    (4, 536_870_913, 44, 17, 333, True, 285_082_020_609),
)


def board(rate, errors, order, v, s, reserve):
    d, t = N//rate - 1, N-errors
    delta = N - 1 - d if reserve else 0
    w = order*t - delta
    # Enumerate scalar powers individually in the local count.
    rows = 0
    for b in range(order):
        for m in range(min(s, b+v)+1):
            slots = len(range(max(0, m-b), min(v, m)+1))
            rows += sum(min(order-b, slots) for _ in range(s-m+1))
    cols = sum((s+1-j-k)*max(0, w-j*d-k*(d-1))
               for k in range(v+1) for j in range(s-k+1))
    if reserve:
        assert delta >= t-(d-1)
    return cols - N*rows, (w+v-1)//d


def local_control():
    # Each block is a consecutive Pascal minor; compare with its ground-field rank.
    p = 101
    for r in range(1, 9):
        for b in range(r):
            for v in range(7):
                for m in range(b+v+1):
                    ks = range(max(0, m-b), min(v, m)+1)
                    matrix = [[comb(k, h) % p for k in ks] for h in range(r-b)]
                    rank = 0
                    for c in range(len(ks)):
                        q = next((j for j in range(rank, len(matrix)) if matrix[j][c]), None)
                        if q is None:
                            continue
                        matrix[rank], matrix[q] = matrix[q], matrix[rank]
                        inv = pow(matrix[rank][c], -1, p)
                        for j in range(rank+1, len(matrix)):
                            scale = matrix[j][c]*inv % p
                            matrix[j] = [(x-scale*y)%p for x, y in zip(matrix[j], matrix[rank])]
                        rank += 1
                    assert rank == min(len(ks), r-b)


def half_integral_families():
    d, errors, plane, cutoff = N//2-1, 314_491_699, 4386, 30_000
    t = N-errors
    core = t-errors//cutoff
    assert 3*core > N+2*d
    nonlinear = (plane*(N-d)+t-d-1)//(t-d)
    charges = []
    for heads in range(plane+1):
        rich = heads*(errors+1)
        if heads >= 3:
            denominator = core+(heads-1)*d
            union = (heads*core*core+denominator-1)//denominator
            rich = min(rich, heads*N-(heads-1)*union)
        charges.append(rich+(plane-heads)*cutoff+nonlinear)
    maximum = max(charges)
    assert (maximum, charges.index(maximum)) == (1_649_087_237, 1323)
    assert 2_115_451_893-maximum == 466_364_656
    quadratic = 2*plane+(8*N*plane+t-d-1)//(t-d)
    assert (quadratic, 466_364_656-quadratic) == (178_192, 466_186_464)
    print("Half rate: at least 466,186,464 labels on fixed surfaces or regular "
          "nonintegrable projected curves of ordinate degree at least three in any overrun.")


def quadratic_branch_control():
    # The quartics P(X,Z)=(X²+Z+h)²+Z(Z−1) are squares at Z=0,1.
    # Directly compute their Sylvester rank and compare determinants with
    # 256(u²+v)v², u=Z+h and v=Z(Z−1), on the full small field.
    prime = 101
    for shift in (0, 2):
        for z in range(prime):
            u, v = z+shift, z*(z-1)
            f = [1, 0, 2*u, 0, u*u+v]
            derivative = [4, 0, 4*u, 0]
            rows = [[0]*i+f+[0]*(2-i) for i in range(3)]
            rows += [[0]*i+derivative+[0]*(3-i) for i in range(4)]
            rank, leading = 0, 1
            for col in range(7):
                pivot = next((i for i in range(rank, 7) if rows[i][col] % prime), None)
                if pivot is None:
                    continue
                if pivot != rank:
                    leading = -leading
                    rows[rank], rows[pivot] = rows[pivot], rows[rank]
                entry = rows[rank][col] % prime
                leading = leading*entry % prime
                for i in range(rank+1,7):
                    scale = rows[i][col]*pow(entry,-1,prime) % prime
                    rows[i] = [(a-scale*b)%prime for a,b in zip(rows[i],rows[rank])]
                rank += 1
            determinant = leading if rank == 7 else 0
            assert (determinant-256*(u*u+v)*v*v) % prime == 0
            if z in (0,1):
                assert 7-rank >= 2


def cubic_resolvent_control():
    prime = 31
    cubes = {pow(a,3,prime) for a in range(prime)}
    radical = next(a for a in range(prime) if a*a % prime == prime-3)
    for roots in combinations(range(prime),3):
        first, second, third = roots
        b = -sum(roots)
        c = first*second+first*third+second*third
        d = -first*second*third
        u = b*b-3*c
        v = 2*b**3-9*b*c+27*d
        sqrt_discriminant = (first-second)*(first-third)*(second-third)
        for sign in (-1,1):
            radicand = ((-v+sign*3*radical*sqrt_discriminant)
                        *pow(2,-1,prime)) % prime
            assert radicand in cubes
            if radicand:
                j = next(a for a in range(1,prime) if pow(a,3,prime)==radicand)
                value = (j+u*pow(j,-1,prime)) % prime
                assert (value**3-3*u*value+v)%prime == 0


if __name__ == "__main__":
    local_control()
    half_integral_families()
    quadratic_branch_control()
    cubic_resolvent_control()
    for rate, errors, order, v, s, reserve, expected in BOARDS:
        actual, m = board(rate, errors, order, v, s, reserve)
        assert actual == expected
        print(f"1/{rate}, {errors:,} errors, (r,v,s)=({order},{v},{s}), "
              f"reserved={reserve}, surplus={actual:,}.")
        if s in (359, 269):
            retained = 2*N+1-s**3
            curves = (2*s*v-v*v)//4
            assert (retained, curves) == ((2_101_215_370, 4164) if rate == 2
                                          else (2_128_018_540, 3328))
            print(f"  At least {retained:,} bad labels on scalar-varying singular components "
                  "if the pair exceeds budget.")
            low_s, low_v = (99, 6) if rate == 2 else (63, 5)
            mixed = low_s*v+s*low_v-low_v*v
            exceptional = low_s*s*s+mixed*mixed+low_s*s
            concentrated = 2*N+1-exceptional
            assert (mixed, concentrated) == ((4386, 2_115_451_893) if rate == 2
                                             else (2853, 2_134_768_350))
            print(f"  At least {concentrated:,} labels on fixed surfaces of derivative "
                  f"degree at most two or on differential lifts of total plane degree ≤ {mixed:,}.")
        if v == 2:
            assert m == (21 if rate == 2 else 18)
        if s in (453, 333):
            plane, ordinate = (2*v-1)*s, (2*v-1)*m
            cap = 2*plane*ordinate
            assert cap == (60_193_734 if rate==2 else 61_648_290) < 2*N
            print(f"  Coprime projected certificate: degrees ({plane},{ordinate}), "
                  f"at most {cap:,} bad labels.")
