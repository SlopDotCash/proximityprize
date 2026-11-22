#!/usr/bin/env python3
"""Exact least-squares bounds from two sets of full classes in a split pencil."""
import argparse
from fractions import Fraction
from itertools import combinations
from math import gcd

from probe_mu64_unit_lattice import require
from probe_split_pencil_six_blocks import SITES, comparison_rows, first_triples


def squared_norms(equations, reverse):
    """Orthogonalize integer equations, with one column per right-hand side."""
    if reverse:
        equations = equations[::-1]
    size = len(equations[0][1])
    norms = [Fraction(0) for _ in range(size)]
    impossible = [False]*size
    basis = []
    for left, right in equations:
        for row, values, length in basis:
            dot = sum(x*y for x,y in zip(left,row))
            if not dot:
                continue
            common = gcd(dot,length)
            scale, subtract = length//common,dot//common
            left = [scale*x-subtract*y for x,y in zip(left,row)]
            right = [scale*x-subtract*y for x,y in zip(right,values)]
            common = gcd(*left,*right)
            if common > 1:
                left = [x//common for x in left]
                right = [x//common for x in right]
        length = sum(x*x for x in left)
        if length:
            basis.append((left,right,length))
            for j,value in enumerate(right):
                norms[j] += Fraction(value*value,length)
        else:
            for j,value in enumerate(right):
                impossible[j] |= value != 0
    return [None if fail else value for fail,value in zip(impossible,norms)]


def coefficients(free, i, j, h):
    width = len(free)
    row = [0]*(3*width)
    for k, site in enumerate(free):
        row[i*width+k] = h[site]
        row[j*width+k] = -h[site]
    return row


def mass_rows(width, totals, size):
    out = []
    for i,total in enumerate(totals):
        row = [0]*(3*width)
        row[i*width:(i+1)*width] = [1]*width
        out.append((row,[total]*size))
    return out


def three_three(first, second, reverse):
    """Minimum mass of the three normalized rows on the ten remaining sites."""
    free = sorted(SITES.difference(first,second))
    equations = mass_rows(len(free),(1,1,4),1)
    for centers,positive,i in ((first,second,1),(second,first,0)):
        for h in comparison_rows(centers):
            row = coefficients(free,i,2,h)
            equations.append((row,[-sum(h[j] for j in positive)]))
    return squared_norms(equations, reverse)


def three_two(first, second, reverse):
    """Compare to the ideal seven-block layout for every pair of unassigned blocks."""
    free = sorted(SITES.difference(first,second))
    pairs = list(combinations(free,2))
    equations = mass_rows(len(free),(0,0,0),len(pairs))
    for centers,positive,i in ((first,second,1),(second,first,0)):
        for h in comparison_rows(centers):
            row = coefficients(free,i,2,h)
            rhs = []
            for pair in pairs:
                unused = SITES.difference(first,second,pair)
                offset = (len(pair)-len(positive))*sum(h[j] for j in unused)
                offset += 9*(sum(h[j] for j in positive)-sum(h[j] for j in pair))
                rhs.append(-offset)
            equations.append((row,rhs))
    return [v/81 if v is not None else None for v in squared_norms(equations,reverse)]


def check(size, reverse):
    total = possible = 0
    minimum = None
    for first in first_triples(False):
        for second in combinations(sorted(SITES.difference(first)),size):
            values = (three_three if size == 3 else three_two)(first,second,reverse)
            total += len(values)
            for value in values:
                if value is not None:
                    possible += 1
                    minimum = value if minimum is None else min(minimum,value)
    if size == 3:
        require((total,possible,minimum) == (2574,2341,Fraction(11,5)),
                "three-three bound or coverage")
    else:
        require((total,possible) == (38610,37290) and minimum == Fraction(68585,462186),
                "three-two bound or coverage")
    print(f"(3,{size}) {total} layouts, {possible} consistent, "
          f"minimum squared norm {minimum}", flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse', action='store_true', help='eliminate equations in reverse order')
    flags = parser.parse_args()
    for size in (3,2):
        check(size,flags.reverse)
