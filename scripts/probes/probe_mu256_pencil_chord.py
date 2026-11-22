#!/usr/bin/env python3
"""Check inhomogeneous chord targets on the order-128 quotient of a split pencil."""
import argparse
import json
import subprocess
from fractions import Fraction
from math import prod
from pathlib import Path
from tempfile import TemporaryDirectory

from flint import fmpz_mat

from probe_dyadic_antipodal_blocks import verified_source
from probe_mu128_balanced_weight import enclosure_parameters
from probe_mu128_unit_ellipsoid import PRIMES, bezout, check_ellipsoid, exponent_rows, kernel_basis
from probe_mu64_unit_lattice import orthogonal_lengths, require

HERE = Path(__file__).resolve().parent


def absolute_chord_logs(cert, p, g, quotient_root):
    root,logs = cert['root'],cert['logs']
    require((cert['prime'],cert['generator']) == (p,g) and root*root % p == quotient_root and
            pow(root,128,p) == p-1 and root == pow(g,(p-1)//256,p), "mismatched lifted root")
    units = [(1-pow(root,j,p)) % p for j in range(1,128,2)]
    require(len(logs) == 64 and all(pow(g,a,p) == u for a,u in zip(logs,units)), "order-256 logs")
    phase = {pow(root,j,p):j for j in range(256)}
    rows = exponent_rows(256)
    absolute = {}
    for j in range(1,129):
        value = (1-pow(root,j,p)) % p
        monomial = prod(pow(u,row[j],p) for u,row in zip(units,rows)) % p
        twist = phase[value*pow(monomial,-1,p) % p]
        unit_log = sum(a*row[j] for a,row in zip(logs,rows))+twist*((p-1)//256)
        absolute[j] = (2*unit_log+(p-1)//2-j*((p-1)//256)) % (p-1)
        require(pow(g,absolute[j],p) == value*(1-pow(root,-j,p)) % p, "bad chord-square logarithm")
    return absolute


def targets(absolute, modulus):
    result = {}
    for a in range(1,129):
        for b in range(1,a):
            if a % 2 == b % 2 == 0:
                continue
            value = (2*(absolute[a]-absolute[b])) % modulus
            residue = min(value,(-value) % modulus)
            require(residue not in result, "non-distinct normalized chord targets")
            result[residue] = (a,b) if value == residue else (b,a)
    require(len(result) == 6112, "incomplete parity or sign coverage")
    return result


def kernel_coordinates(logs, modulus, basis):
    """A rational coordinate representative for a generator of the quotient by the kernel."""
    divisor = modulus
    witness = [0]*len(logs)
    for j,log in enumerate(logs):
        divisor,x,y = bezout(divisor,log)
        witness = [x*a for a in witness]
        witness[j] = y
    require(sum(a*b for a,b in zip(witness,logs)) % modulus == divisor, "wrong Bezout row")
    numerator,denominator = (fmpz_mat([witness])*basis.inv()).numer_denom()
    require(numerator*basis == denominator*fmpz_mat([witness]), "bad affine coordinates")
    return divisor,list(map(int,numerator.tolist()[0])),int(denominator)


def check(data, source, index, duals, binary, reverse):
    p,g,z,logs = verified_source(data)
    modulus = p-1
    beta = [(2*a+modulus//2-r*(modulus//128)) % modulus for a,r in zip(logs,range(1,64,2))]
    require(all(pow(g,a,p) == (1-pow(z,r,p))*(1-pow(z,-r,p)) % p
                for a,r in zip(beta,range(1,64,2))), "bad order-128 phase logarithm")
    table = targets(absolute_chord_logs(source,p,g,z),modulus)
    rows = exponent_rows(128)
    matrix = fmpz_mat([r[1:] for r in rows])
    require(check_ellipsoid(matrix,beta,modulus,384,reverse,"homogeneous chord case") == 1,
            "loss of homogeneous transfer")
    sums = fmpz_mat([[sum(row)] for row in matrix.tolist()])
    covariance = 127*matrix*matrix.transpose()-sums*sums.transpose()
    metric,scale = covariance.inv().numer_denom()
    require(covariance*metric == scale*fmpz_mat([[int(i == j) for j in range(32)] for i in range(32)]) and scale > 0, "bad covariance")
    metric *= 127
    radius = 252*int(scale)
    initial = kernel_basis(beta,modulus)
    if reverse:
        initial = fmpz_mat(list(reversed(initial.tolist())))
    reduced,change = (initial*metric*initial.transpose()).lll(transform=True,rep='gram',gram='exact')
    basis = change*initial
    require(abs(int(change.det())) == 1 and basis*metric*basis.transpose() == reduced, "bad basis")
    dimension = 32
    gram = [[int(x) for x in row] for row in reduced.tolist()]
    mu,lengths = orthogonal_lengths(gram)
    rounding,coefficients,payload = enclosure_parameters(mu,lengths,radius,True)
    divisor,coords,den = kernel_coordinates(beta,modulus,basis)
    require(all(t % divisor == 0 for t in table), "unexpected empty congruence fiber")
    representatives = []
    residues = list(table)
    payload.append(f"{len(table)} {dimension+1}")
    for t in residues:
        r = [(t//divisor*c+den//2) % den-den//2 for c in coords]
        representatives.append(r)
        offsets = [round(Fraction(rounding*r[i]+sum(coefficients[j][i]*r[j]
                                                        for j in range(i+1,dimension)),den))
                   for i in range(dimension)]
        payload.append(' '.join(map(str,offsets)))
    result = subprocess.run([binary,'--affine'],input='\n'.join(payload)+'\n',text=True,
                            capture_output=True,check=True)
    count = 0
    for line in result.stdout.splitlines():
        block,*v = map(int,line.split())
        require(0 <= block < len(table) and len(v) == dimension, "bad affine leaf")
        c = [x*den+y for x,y in zip(v,representatives[block])]
        norm = sum(c[i]*(gram[i][i]*c[i]+2*sum(gram[i][j]*c[j] for j in range(i)))
                   for i in range(dimension))
        if norm > radius*den**2:
            continue
        numerator = (fmpz_mat([c])*basis).tolist()[0]
        require(all(x % den == 0 for x in numerator), "nonintegral congruence representative")
        e = [int(x//den) for x in numerator]
        require(sum(a*b for a,b in zip(e,beta)) % modulus == residues[block], "target mismatch")
        dual = duals.get(tuple(e))
        require(dual is not None and len(dual) == dimension+1, "missing separating row")
        left = sum(a*b for a,b in zip(dual,e))
        right = sum(abs(dual[-1]+sum(dual[i]*row[j] for i,row in enumerate(rows))) for j in range(1,128))
        require(left > 2*right, "target can meet the population cap")
        count += 1
    require(count == (2,5)[index], "unexpected inhomogeneous point count")
    print(f"p{index+1}  targets {len(table)}  ellipsoid points {count}  bounded solutions 0",flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-basis',action='store_true')
    args = parser.parse_args()
    fields = json.loads((HERE/'mu128_unit_logs.json').read_text())
    lifted = json.loads((HERE/'mu256_unit_logs.json').read_text())
    data = json.loads((HERE/'mu256_pencil_chord_certificates.json').read_text())
    require(tuple(c['prime'] for c in fields) == PRIMES and len(lifted) == len(data) == 2,
            "named fields missing")
    with TemporaryDirectory() as folder:
        binary = Path(folder)/'lattice-enclosure'
        subprocess.run(['c++','-O3','-std=c++17',HERE/'probe_lattice_enclosure.cpp','-o',binary],check=True)
        for i in range(2):
            check(fields[i],lifted[i],i,{tuple(e):y for e,y in data[i]},binary,args.reverse_basis)
