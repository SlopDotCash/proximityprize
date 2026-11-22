#!/usr/bin/env python3
"""Verify all balanced weight-two vanisher comparisons on the order-128 grids."""
import argparse
import json
import subprocess
from functools import partial
from math import isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from probe_dyadic_antipodal_blocks import verified_source
from probe_mu128_unit_ellipsoid import PRIMES, exponent_rows
from probe_mu64_balanced_weight import balanced_shifts, check_witness
from probe_mu64_unit_lattice import lattice_coordinates, require

HERE = Path(__file__).resolve().parent


def enclosure_parameters(mu, lengths, radius, affine):
    """Integer outer bounds and overflow checks for a centered or translated lattice."""
    dimension = len(lengths)
    scale, resolution = 2**15, 2**25
    budget = resolution*scale**2
    coefficients = [[round(scale*x) for x in row] for row in mu]
    weights = [resolution*x.numerator//(x.denominator*radius) for x in lengths]
    require(min(weights) > 0, "fixed-point resolution too low")
    bounds = [0]*dimension
    for i in reversed(range(dimension)):
        error = sum(bounds[i+1:]) + (dimension+1 if affine else 0)
        offset = sum(abs(coefficients[j][i])*bounds[j] for j in range(i+1,dimension))
        if affine:
            offset += (scale+sum(abs(coefficients[j][i]) for j in range(i+1,dimension)))//2+1
        reach = isqrt(budget//weights[i])+error
        bounds[i] = (reach+offset)//scale
        require(4*(reach+offset+scale*bounds[i]+scale) < 2**63 and
                max(budget,weights[i],*map(abs,coefficients[i])) < 2**63,
                "fixed-point word overflow")
    payload = [f"{dimension} {scale} {budget}"]
    payload.extend(' '.join(map(str,[weights[i]]+coefficients[i][:i])) for i in range(dimension))
    return scale, coefficients, payload


def enclosed_coordinates(binary, mu, lengths, radius):
    """Enumerate an integer outer approximation, then test the original Gram form."""
    dimension = len(lengths)
    _, _, payload = enclosure_parameters(mu,lengths,radius,False)
    gram = []
    for i in range(dimension):
        row = []
        for j in range(i+1):
            dot = sum(mu[i][k]*mu[j][k]*lengths[k] for k in range(j))
            dot += (mu[i][j] if i > j else 1)*lengths[j]
            require(dot.denominator == 1, "original Gram form must be integral")
            row.append(int(dot))
        gram.append(row)

    result = subprocess.run([binary],input='\n'.join(payload)+'\n',text=True,capture_output=True,check=True)
    for line in result.stdout.splitlines():
        v = tuple(map(int,line.split()))
        require(len(v) == dimension, "bad native leaf")
        norm = sum(v[i]*(gram[i][i]*v[i]+2*sum(gram[i][j]*v[j] for j in range(i) if v[j]))
                   for i in range(dimension) if v[i])
        if norm <= radius:
            yield v


def verify(enumerate_coordinates, reverse, selected, shifts):
    data = json.loads((HERE/'mu128_unit_logs.json').read_text())
    tables = json.loads((HERE/'mu128_balanced_weight_two_certificates.json').read_text())
    require(tuple(c['prime'] for c in data) == PRIMES and len(tables) == 2, "named fields missing")
    for i in selected:
        p,g,z,logs = verified_source(data[i])
        table = tables[i]
        require(table['bound'] == 2, "unexpected weight bound")
        value = check_witness(table,z,p,exponent_rows(128))
        total, used = balanced_shifts(p,g,z,logs,2,table['separators'],shifts,reverse,enumerate_coordinates)
        if len(shifts) == 64:
            require((total,used) == ((216604,75),(107204,36))[i], "unexpected lattice census")
        print(f"p{i+1}  shifts {len(shifts)}  lattice points {total}  separating rows {used}  "
              f"weight-3 witness equal value {value}",flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rational',action='store_true',help='use exact rational branches throughout')
    parser.add_argument('--reverse-basis',action='store_true')
    parser.add_argument('--field',type=int,choices=(1,2))
    parser.add_argument('--shifts',nargs='+',type=int,choices=range(1,65))
    args = parser.parse_args()
    selected = [args.field-1] if args.field else [0,1]
    shifts = sorted(set(args.shifts)) if args.shifts else range(1,65)
    if args.rational:
        verify(lattice_coordinates,args.reverse_basis,selected,shifts)
    else:
        with TemporaryDirectory() as folder:
            binary = Path(folder)/'lattice-enclosure'
            subprocess.run(['c++','-O3','-std=c++17',HERE/'probe_lattice_enclosure.cpp','-o',binary],
                           check=True)
            verify(partial(enclosed_coordinates,binary),args.reverse_basis,selected,shifts)
