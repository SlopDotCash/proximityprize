"""Closed-form fit for O_P(4) given data points. Plug in the n=64 value when available."""
from math import comb
from fractions import Fraction

def fit(data):
    # data: dict n -> O_P. m=n/4.
    pts = sorted(data.items())
    print("Data:", {n: v for n, v in pts}, " m=n/4:", {n // 4: v for n, v in pts})
    ms = [n // 4 for n, _ in pts]
    vs = [v for _, v in pts]
    # candidate closed forms
    cands = {
        'C(n/4,2)': lambda m: comb(m, 2),
        'C(n/4,3)': lambda m: comb(m, 3),
        'C(n/4,2)+C(n/4,3)': lambda m: comb(m, 2) + comb(m, 3),
        'C(n/2,3)=C(2m,3)': lambda m: comb(2 * m, 3),
        'C(n/2,2)=C(2m,2)': lambda m: comb(2 * m, 2),
        '(n/4)^2-(n/4)+1': lambda m: m * m - m + 1,
        '2C(m,2)+m-1': lambda m: 2 * comb(m, 2) + m - 1,
        'C(m,3)+C(m,2)-1': lambda m: comb(m, 3) + comb(m, 2) - 1,
        'C(m+1,3)': lambda m: comb(m + 1, 3),
        'm^2-m+? : m(m-1)+1': lambda m: m * (m - 1) + 1,
        'C(2m-1,2)': lambda m: comb(2 * m - 1, 2),
        'C(2m,2)-m': lambda m: comb(2 * m, 2) - m,
        'C(2m,2)-2m+1': lambda m: comb(2 * m, 2) - 2 * m + 1,
        '(2m-1)(m-1)/1?': lambda m: (2 * m - 1) * (m - 1),
        'C(2m-2,2)+? = (m-1)(2m-3)+?': lambda m: comb(2 * m - 2, 2),
        '3C(m,2)+? ': lambda m: 3 * comb(m, 2),
    }
    print("\nForm                          " + "  ".join(f"m={m}->" for m in ms))
    for name, fn in cands.items():
        vals = [fn(m) for m in ms]
        hit = all(vals[i] == vs[i] for i in range(len(vs)))
        mark = "  <== MATCH" if hit else ""
        print(f"  {name:28s} " + "  ".join(f"{v}" for v in vals) + mark)
    # quadratic / cubic exact fit in m
    print("\n--- exact polynomial in m through the points ---")
    if len(ms) == 3:
        # quadratic a m^2 + b m + c
        m0, m1, m2 = ms; y0, y1, y2 = [Fraction(v) for v in vs]
        # solve
        import itertools
        A = [[Fraction(m ** 2), Fraction(m), Fraction(1)] for m in ms]
        # Cramer
        def det3(M):
            return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                    - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                    + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
        D = det3(A)
        ys = [y0, y1, y2]
        coef = []
        for col in range(3):
            M = [row[:] for row in A]
            for r in range(3):
                M[r][col] = ys[r]
            coef.append(det3(M) / D)
        a, b, c = coef
        print(f"  quadratic in m: {a} m^2 + {b} m + {c}")
        # also cubic in m needs 4 pts; with 3 we can fit a cubic with leading from C(m,3) guess
    # fit in n directly (cubic) requires more pts

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        v64 = int(sys.argv[1])
        fit({16: 9, 32: 97, 64: v64})
    else:
        fit({16: 9, 32: 97})
