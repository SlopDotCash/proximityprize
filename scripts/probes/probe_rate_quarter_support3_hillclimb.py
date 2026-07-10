#!/usr/bin/env python3
"""Adversarial exact search for safe support-three [16,4] affine lines over F17."""

import argparse
import itertools
import random

import numpy as np


P = 17
N = 16
K = 4
A = 9
SUPPORT = np.array([13, 14, 15])
ZERO = np.array(list(range(13)))


def codewords():
    # 3 generates F17*, hence the full dyadic order-16 domain.
    domain = np.array([pow(3, i, P) for i in range(N)], dtype=np.int16)
    coeffs = np.array(list(itertools.product(range(P), repeat=K)), dtype=np.int16)
    vand = np.array([[pow(int(x), j, P) for j in range(K)] for x in domain], dtype=np.int16)
    return (coeffs @ vand.T) % P


WORDS = codewords()
INV = np.array([0] + [pow(x, P - 2, P) for x in range(1, P)], dtype=np.int16)


def score(u0, direction, support=SUPPORT):
    support = np.array(support)
    zero = np.array([i for i in range(N) if i not in set(map(int, support))])
    zero_hits = np.sum(WORDS[:, zero] == u0[zero], axis=1)
    if int(np.max(zero_hits)) >= A:
        return -1, (), None
    votes = ((WORDS[:, support] - u0[support]) % P) * INV[direction] % P
    eligible = zero_hits >= A - 3
    eligible_rows = np.flatnonzero(eligible)
    evotes = votes[eligible]
    ehits = zero_hits[eligible]
    bad_list = []
    witness = {}
    for gamma in range(P):
        moving = np.sum(evotes == gamma, axis=1)
        winning = np.flatnonzero(ehits + moving >= A)
        if len(winning):
            j = int(winning[0])
            row = int(eligible_rows[j])
            bad_list.append(gamma)
            witness[gamma] = (row, int(ehits[j]), int(moving[j]))
    bad = tuple(bad_list)
    return len(bad), bad, witness


def run(restarts, steps, seed):
    rng = random.Random(seed)
    global_best = (-1, None)
    for restart in range(restarts):
        u0 = np.array([rng.randrange(P) for _ in range(N)], dtype=np.int16)
        direction = np.array([rng.randrange(1, P) for _ in range(3)], dtype=np.int16)
        current = score(u0, direction)
        for _ in range(steps):
            v0 = u0.copy()
            vd = direction.copy()
            if rng.randrange(5):
                i = rng.randrange(N)
                v0[i] = rng.randrange(P)
            else:
                i = rng.randrange(3)
                vd[i] = rng.randrange(1, P)
            candidate = score(v0, vd)
            if candidate[0] >= current[0] or rng.random() < 0.002:
                u0, direction, current = v0, vd, candidate
            if current[0] > global_best[0]:
                global_best = (current[0], (u0.copy(), direction.copy(), current))
                print(
                    f"best={current[0]} restart={restart} bad={current[1]} "
                    f"u0={u0.tolist()} direction={direction.tolist()}"
                )
    print(f"final_best={global_best[0]} data={global_best[1]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--restarts", type=int, default=20)
    parser.add_argument("--steps", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=400)
    args = parser.parse_args()
    run(args.restarts, args.steps, args.seed)
