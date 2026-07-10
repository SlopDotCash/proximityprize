#!/usr/bin/env python3
"""Bit-vector SAT backend for the source-seven signature extremal query.

The two finite sets of each signature are represented as 7- and 9-bit
vectors.  Five-bit popcount circuits encode every cardinality exactly.  The
resulting QF_BV instance can be solved by Boolector with any of its bundled
SAT engines and dumped as SMT-LIB for independent replay.
"""

from argparse import ArgumentParser
from pathlib import Path
import subprocess

from z3 import (And, BitVec, BitVecVal, Concat, Extract, If, Implies, Not,
                Or, Solver, ULE, ULT, ZeroExt)


SOURCE_SIZE = 7
COMPLEMENT_SIZE = 9
COUNT_WIDTH = 5


def bit(vector, index):
    return Extract(index, index, vector) == BitVecVal(1, 1)


def popcount(vector):
    total = BitVecVal(0, COUNT_WIDTH)
    for i in range(vector.size()):
        total = total + ZeroExt(COUNT_WIDTH - 1, Extract(i, i, vector))
    return total


def bool_count(predicates):
    total = BitVecVal(0, COUNT_WIDTH)
    for predicate in predicates:
        total = total + If(predicate, BitVecVal(1, COUNT_WIDTH),
                           BitVecVal(0, COUNT_WIDTH))
    return total


def build(signatures=13, maximum=2, regular_only=False,
          regular_balance_only=False, regular_count=None):
    solver = Solver()
    root = [BitVec(f"root_{s}", SOURCE_SIZE) for s in range(signatures)]
    missed = [BitVec(f"missed_{s}", COMPLEMENT_SIZE)
              for s in range(signatures)]
    root_card = [popcount(row) for row in root]
    missed_card = [popcount(row) for row in missed]
    three = BitVecVal(3, COUNT_WIDTH)

    for s in range(signatures):
        solver.add(ULE(missed_card[s], root_card[s]))
        solver.add(ULE(root_card[s], three))
        if regular_only:
            solver.add(root_card[s] == three, missed_card[s] == three)

    # Canonical first signature and ordered remaining labels.
    for i in range(SOURCE_SIZE - 1):
        solver.add(Implies(bit(root[0], i + 1), bit(root[0], i)))
    for i in range(COMPLEMENT_SIZE - 1):
        solver.add(Implies(bit(missed[0], i + 1), bit(missed[0], i)))
    for s in range(1, signatures - 1):
        solver.add(ULT(Concat(missed[s], root[s]),
                       Concat(missed[s + 1], root[s + 1])))

    for a in range(signatures):
        for b in range(a + 1, signatures):
            solver.add(ULE(
                BitVecVal(2, COUNT_WIDTH) + popcount(root[a] & root[b]),
                popcount(missed[a] | missed[b])))

    regular = [And(root_card[s] == three, missed_card[s] == three)
               for s in range(signatures)]
    if regular_count is not None:
        solver.add(bool_count(regular) ==
                   BitVecVal(regular_count, COUNT_WIDTH))
    from itertools import combinations
    for a, b, c, d in combinations(range(signatures), 4):
        solver.add(Not(And(
            regular[a], regular[b], regular[c], regular[d],
            root[a] == root[b], root[a] == root[c], root[a] == root[d])))

    balance = {}
    for a, b, c in combinations(range(signatures), 3):
        predicate = ULE(
            BitVecVal(4, COUNT_WIDTH) +
                popcount(missed[a] | missed[b] | missed[c]),
            BitVecVal(9, COUNT_WIDTH) +
                popcount(root[a] & root[b] & root[c]))
        if regular_balance_only:
            predicate = And(predicate, regular[a], regular[b], regular[c])
        balance[(a, b, c)] = predicate

    for a, b in combinations(range(signatures), 2):
        witnesses = [balance[tuple(sorted((a, b, c)))]
                     for c in range(signatures) if c not in (a, b)]
        solver.add(ULE(bool_count(witnesses),
                       BitVecVal(maximum, COUNT_WIDTH)))
    return solver


def smt2_instance(signatures, maximum, regular_only,
                  regular_balance_only, regular_count):
    solver = build(signatures, maximum, regular_only, regular_balance_only,
                   regular_count)
    return "(set-logic QF_BV)\n" + solver.to_smt2()


def run(args):
    instance = smt2_instance(
        args.signatures, args.max_balanced_witnesses,
        args.regular_only, args.regular_balance_only, args.regular_count)
    if args.output:
        Path(args.output).write_text(instance)
    command = ["boolector", "--smt2", "-SE", args.sat_engine,
               "-E", args.engine, "-t", str(args.timeout)]
    if args.model:
        command.append("-m")
    result = subprocess.run(
        command, input=instance, text=True, capture_output=True,
        check=False)
    print({
        "returncode": result.returncode,
        "signatures": args.signatures,
        "maximum": args.max_balanced_witnesses,
        "regular_only": args.regular_only,
        "regular_balance_only": args.regular_balance_only,
        "regular_count": args.regular_count,
        "engine": args.engine,
        "sat_engine": args.sat_engine,
        "smt2_bytes": len(instance),
    })
    print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="")
    return result.returncode


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--signatures", type=int, default=13)
    parser.add_argument("--max-balanced-witnesses", type=int, default=2)
    parser.add_argument("--regular-only", action="store_true")
    parser.add_argument("--regular-balance-only", action="store_true")
    parser.add_argument("--engine", choices=("fun", "prop", "aigprop", "sls"),
                        default="fun")
    parser.add_argument("--sat-engine", choices=(
        "cadical", "cms", "lingeling", "minisat", "picosat"),
        default="cadical")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--model", action="store_true")
    parser.add_argument("--output")
    parser.add_argument("--regular-count", type=int)
    arguments = parser.parse_args()
    raise SystemExit(run(arguments))
