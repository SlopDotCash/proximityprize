#!/usr/bin/env python3
"""Compare every stored sign and every Fourier frequency to direct calculations."""
import argparse
import cmath
import math
import struct
import subprocess
import tempfile
from pathlib import Path

CASES = (
    ("positive-control", 17318209, pow(7, (17318209 - 1) // 64, 17318209), 64, 64),
    ("primitive-control", 17, 3, 16, 16),
    ("sextic-control", 97, 8, 16, 16),
    ("first", 365375409332725729550921208179070755120141565953,
     303645430271030343624574566109998498685964493478, 2**30, 1024),
    ("second", 730750818665451459101842416358141509841924915201,
     192152681249815148642741928588691886362054863855, 2**30, 256),
)


def require(test, detail):
    if not test:
        raise ArithmeticError(detail)


def labels(line):
    return dict(word.split("=", 1) for word in line.split())


def check_projective(field, p, g, n, norm):
    character = [pow(x, (p - 1) // 2, p) for x in range(p)]
    character = [-1 if x == p - 1 else x for x in character]
    infinity = p
    points = range(p + 1)

    def entry(x, y):
        if infinity in (x, y):
            return int(x != y)
        return character[(x - y) % p]

    rows = [[entry(x, y) for y in points] for x in points]
    for x in points:
        for y in points:
            dot = sum(a*b for a, b in zip(rows[x], rows[y]))
            require(dot == (p if x == y else 0), (field, "conference", x, y))

    subgroup = {pow(g, j, p) for j in range(n)}
    nonsquare = character.index(-1)
    for a, b, c, d in ((1, 1, 0, 1), (0, 1, 1, -1), (nonsquare, 0, 0, 1)):
        images = []
        signs = []
        for x in points:
            u, v = (a, c) if x == infinity else ((a*x + b) % p, (c*x + d) % p)
            images.append(u * pow(v, -1, p) % p if v else infinity)
            signs.append(character[v or u])
        require(len(set(images)) == p + 1, (field, "projective bijection"))
        det = character[(a*d - b*c) % p]
        for x in points:
            for y in points:
                require(rows[images[x]][images[y]] == det*signs[x]*signs[y]*rows[x][y],
                        (field, "projective signs", x, y))

        # Pack two disjoint squares, one in H and one in its projective image.
        second = {images[x] for x in subgroup} - subgroup
        support = subgroup | second
        discrepancy = abs(sum(rows[x][y] for x in support for y in support))
        certified_deficit = sum(max(0, len(s)**2 - norm*len(s)) for s in (subgroup, second))
        require(len(support)**2 - discrepancy >= certified_deficit,
                (field, "rectangle bound"))


def run(signs_bin, fft_bin):
    count = 0
    with tempfile.TemporaryDirectory() as temp:
        for field, p, generator, order, n in CASES:
            g = pow(generator, order // n, p)
            row = [pow(1 - pow(g, j, p), (p - 1) // 2, p) for j in range(n)]
            row = [-1 if s == p - 1 else s for s in row]
            require(row[0] == 0 and all(abs(s) == 1 for s in row[1:]), field)
            roots = [cmath.exp(2j * math.pi * j / n) for j in range(n)]
            direct = [sum(s * roots[k*j % n] for j, s in enumerate(row)) for k in range(n)]
            require(abs(sum(abs(z)**2 for z in direct) - n*(n-1)) < 1e-6, field)
            path = Path(temp, "signs.bin")
            report = labels(subprocess.check_output([signs_bin, field, path, "2", str(n)], text=True))
            require(int(report["row"]) == sum(row), field)
            words = [w[0] for w in struct.iter_unpack("=Q", path.read_bytes())]
            require(all(((words[j//64] >> (j % 64)) & 1) == (s < 0) for j, s in enumerate(row)), field)
            for blocks in sorted({2, 8, n//2}):
                out = subprocess.check_output([fft_bin, field, path, str(blocks), "2", str(n)], text=True)
                lines = out.splitlines()
                data = labels(lines[0])
                require(len(lines) == n + 1 and int(data["row_sum"]) == sum(row), field)
                for j, line in enumerate(lines[1:]):
                    idx, re, im = map(int, line.split())
                    estimated = complex(re, im)/2**30
                    require(idx == j and abs(estimated - direct[j]) <= int(data["error"]), (field, j))
                actual_peak = max(map(abs, direct))
                require(int(data["lower"]) <= actual_peak <= int(data["upper"]), field)
                count += n
            if p in (17, 97):
                check_projective(field, p, g, n, int(data["upper"]))
    print(f"{len(CASES)} independently enumerated rows, {count} individual frequencies checked")
    print("Projective signs, conference identities and packed rectangles checked over F_17 and F_97")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("signs", type=Path)
    parser.add_argument("full", type=Path)
    args = parser.parse_args()
    run(args.signs.resolve(), args.full.resolve())
