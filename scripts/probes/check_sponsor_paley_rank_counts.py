#!/usr/bin/env python3
"""Check every cyclic correlation and every four-site determinant on small boards."""
import argparse
from itertools import combinations, permutations
from fractions import Fraction
from math import comb, prod
from pathlib import Path
import struct
import subprocess
import tempfile

from check_sponsor_paley_full_spectrum import CASES, require


def check_receipts(paths):
    for (field, p, _, n, _), path, chebyshev, lower_z, side in zip(
        CASES[-2:], paths, (Fraction(7, 10**18), Fraction(51, 10**11)),
        (379693158, 44480), (1, -1),
    ):
        head = path.read_text().splitlines()[0]
        data = dict(word.split("=", 1) for word in head.split())
        require(data["field"] == field and int(data["n"]) == n, (path, "input"))
        count, energy = int(data["singular"]), int(data["energy"])
        blocks = comb(n, 4)
        require(int(data["four_subsets"]) == blocks and
                energy == n*int(data["sum_squares"]) and
                energy == n*(n-1)*(2*n-3) + 8*(4*count-blocks), (path, "count"))
        v = p+1
        theta = Fraction(p-5, 4*(p-2))
        variance = theta*(1-theta)*blocks*Fraction(comb(v-n, 4), comb(v-4, 4))
        delta = count-theta*blocks
        require(side*delta > 0 and variance/delta**2 < chebyshev, (path, "Chebyshev"))
        require(lower_z**2 < delta**2/variance < (lower_z+1)**2, (path, "deviation"))
        print(f"{field}: exact rank identity, deviation and Chebyshev bound verified")


def check(rank_bin):
    checks = correlations = determinants = 0
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "row.bits")
        for name, p, generator, order, _ in (*CASES, ("asymmetric-control", 113, 35, 16, 16)):
            n = min(16, order)
            sites = [pow(generator, (order//n)*i, p) for i in range(n)]

            def chi(x):
                k = pow(x, (p-1)//2, p)
                return -1 if k == p-1 else k

            row = [chi(1-x) for x in sites]
            path.write_bytes(struct.pack("=Q", sum((x < 0) << j for j, x in enumerate(row))))
            corr = [sum(row[j]*row[(j+h) % n] for j in range(n)) for h in range(n)]
            if name == "asymmetric-control":
                require(chi(sites[1]) == -1 and [corr[2], corr[4], corr[6]] == [-2, 6, -10],
                        (name, "distinct twisted even offsets"))
            matrix = [[chi(x-y) for y in sites] for x in sites]
            signed_perms = [(perm, (-1)**sum(perm[i] > perm[j] for i, j in combinations(range(4), 2)))
                            for perm in permutations(range(4))]
            singular = 0
            for t in combinations(range(n), 4):
                det = sum(sign*prod(matrix[t[i]][t[j]] for i, j in enumerate(perm))
                          for perm, sign in signed_perms)
                singular += int(det % 3 == 0)
                determinants += 1
            for blocks in (2, 4, 8):
                out = subprocess.check_output([rank_bin, name, path, str(blocks), "2", str(n)], text=True)
                head, *detail = out.splitlines()
                fields = dict(word.split("=", 1) for word in head.split())
                require(len(detail) == n and [list(map(int, line.split())) for line in detail]
                        == [[h, x] for h, x in enumerate(corr)], (name, blocks, "correlations"))
                expected = dict(n=n, gamma=chi(sites[1]), row_sum=sum(row),
                                sum_correlations=sum(corr), sum_squares=sum(x*x for x in corr),
                                max_offdiag=max(map(abs, corr[1:])), energy=n*sum(x*x for x in corr),
                                singular=singular, four_subsets=comb(n, 4))
                require(all(int(fields[key]) == val for key, val in expected.items()),
                        (name, blocks, fields, expected))
                correlations += n
                checks += 1
    print(f"{checks} transform controls, {correlations} cyclic correlations, "
          f"{determinants} independently expanded four-site determinants")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rank_bin", type=Path)
    parser.add_argument("--receipts", nargs=2, type=Path, metavar=("FIRST", "SECOND"))
    args = parser.parse_args()
    check(args.rank_bin.resolve())
    if args.receipts:
        check_receipts(args.receipts)
