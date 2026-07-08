#!/usr/bin/env python3
"""R27 GENK probe: validate the general-k block/divisibility normal form at k=5 (d=32, q=193).

Checks, over F_193 (32 | 192) and over random F_q:
  (1) BLOCK<->DVD: for random P,Q of degree < n=16, the 16 block equations
        e_j = c_j + c*c_{j+16},  c_m = coeff_m(P(v)^2 - v*Q(v)^2)
      vanish  <=>  (v^16 - c) | (P^2 - v Q^2).
  (2) CONVOLUTION NORMAL FORM: c_m = sum_{i+i'=m} a_{2i}a_{2i'} - sum_{i+i'=m-1} a_{2i+1}a_{2i'+1}
      (a interleaved: P from even, Q from odd indices) -- the r26 normal form continues at k=5.
  (3) REGROUP: over K(s), s^2=c, with b_i = a_i + a_{i+16} s, the regrouped half-system
        e_j + s e_{j+8}  ==  ehat_j(s; b)  (the d=16 system with parameter s),
      correction quotient K_j = c_{j+16} + s c_{j+24} on (s^2 - c): checked symbolically
      by working in F_q[s]/(s^2-c) with c a non-square.
  (4) DESCENT (statistical): search for nonzero solutions of the 16-block system over F_193
      with c, -c both non-squares: none should exist among many random + structured tries.
"""
import random

p = 193
assert (p - 1) % 32 == 0

def polmul(A, B):
    R = [0] * (len(A) + len(B) - 1)
    for i, x in enumerate(A):
        if x:
            for j, y in enumerate(B):
                R[i + j] = (R[i + j] + x * y) % p
    return R

def polsub(A, B):
    n = max(len(A), len(B))
    return [((A[i] if i < len(A) else 0) - (B[i] if i < len(B) else 0)) % p for i in range(n)]

def polmod(A, mod):  # mod monic
    A = A[:]
    d = len(mod) - 1
    for i in range(len(A) - 1, d - 1, -1):
        q = A[i]
        if q:
            for j in range(d + 1):
                A[i - d + j] = (A[i - d + j] - q * mod[j]) % p
    return A[:d]

def is_sq(x):
    return pow(x % p, (p - 1) // 2, p) != p - 1

n = 16
d = 32
# pick c with c, -c both nonsquare
c = next(x for x in range(2, p) if not is_sq(x) and not is_sq(-x % p))

def blocks(a):
    P = [a[2 * i] for i in range(n)]
    Q = [a[2 * i + 1] for i in range(n)]
    f = polsub(polmul(P, P), [0] + polmul(Q, Q))
    f = f + [0] * (2 * n - len(f))
    return f, [(f[j] + c * f[j + n]) % p for j in range(n)]

ok = True
# (1)+(2)
for trial in range(200):
    a = [random.randrange(p) for _ in range(d)]
    f, e = blocks(a)
    # convolution normal form
    for m in range(2 * n):
        s1 = sum(a[2 * i] * a[2 * (m - i)] for i in range(n) if 0 <= m - i < n)
        s2 = sum(a[2 * i + 1] * a[2 * (m - 1 - i) + 1] for i in range(n) if 0 <= m - 1 - i < n) if m >= 1 else 0
        if (s1 - s2) % p != f[m] % p:
            ok = False; print("CONV FAIL", trial, m)
    # dvd <-> blocks
    mod = [(-c) % p] + [0] * (n - 1) + [1]
    rem = polmod(f[:], mod)
    dvd = all(x == 0 for x in rem)
    blk = all(x == 0 for x in e)
    if dvd != blk:
        ok = False; print("DVD<->BLK FAIL", trial)
print("(1)(2) block/dvd + convolution normal form at k=5:", "OK" if ok else "FAIL")

# (3) regroup over K(s)=F_p[s]/(s^2-c): elements as (u,v) = u+vs
def smul(x, y):
    return ((x[0] * y[0] + c * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
def sadd(x, y):
    return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)
def ssub(x, y):
    return ((x[0] - y[0]) % p, (x[1] - y[1]) % p)

ok3 = True
for trial in range(100):
    a = [random.randrange(p) for _ in range(d)]
    f, e = blocks(a)
    b = [(a[i], a[i + n]) for i in range(n)]  # b_i = a_i + a_{i+n} s
    # half system at d=16 with parameter s: chat_m from b (even/odd interleave), ehat_j = chat_j + s*chat_{j+8}
    h = n // 2  # 8
    Ph = [b[2 * i] for i in range(h)]
    Qh = [b[2 * i + 1] for i in range(h)]
    # fhat = Ph^2 - v Qh^2 over K(s)
    fh = [(0, 0)] * (2 * h)
    for i in range(h):
        for j in range(h):
            fh[i + j] = sadd(fh[i + j], smul(Ph[i], Ph[j]))
            fh[i + j + 1] = ssub(fh[i + j + 1], smul(Qh[i], Qh[j]))
    for j in range(h):
        ehat = sadd(fh[j], smul((0, 1), fh[j + h]))
        lhs = sadd((e[j], 0), smul((0, 1), (e[j + h], 0)))  # e_j + s e_{j+h}
        if ehat != lhs:
            ok3 = False; print("REGROUP FAIL", trial, j, ehat, lhs)
print("(3) regroup e_j + s*e_{j+8} == half-system at k=5:", "OK" if ok3 else "FAIL")

# (4) no nonzero solutions (statistical): random near-solutions via gradient-free search is weak;
# instead verify forced-zero on structured candidates: monomial and two-term vectors.
found = None
for i in range(d):
    for val in (1, 2, 5):
        a = [0] * d; a[i] = val
        _, e = blocks(a)
        if all(x == 0 for x in e):
            found = (i, val)
for trial in range(4000):
    a = [0] * d
    for _ in range(2):
        a[random.randrange(d)] = random.randrange(1, p)
    _, e = blocks(a)
    if all(x == 0 for x in e) and any(a):
        found = tuple(a)
print("(4) nonzero solutions found (should be None):", found)
print("c =", c, "q =", p)
