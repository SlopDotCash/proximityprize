#!/usr/bin/env python3
"""
G299 probe: the production prize depth lies INSIDE the palindrome census window,
refuting G296's "r > n / escapes the window / certificate at depth r >= n" prose.

Pure integer. Hard SystemExit(1) on any failure. No floats in the acceptance checks.

Production parameters (from the repo, CumulantOrderThreshold.lean / BadPrimeNormBound.lean):
    field scale   q = 2^158
    subgroup order n = 2^30
    cumulant/EVT threshold log_n q ~= 5.27 ; deep sup-control ledger depth r* ~= 89.

Window (G296): W(n) = Icc 2 (n-1) = { r : 2 <= r <= n-1 }.
Reflection (G295/G296): sigma(n, r) = n + 1 - r.
"""
import sys

def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)

# --- production constants (exact integers) ---
n = 2 ** 30            # subgroup order
q = 2 ** 158           # prize field scale
rstar = 89             # ledger deep sup-control / EVT depth r* (report value)

def window_lo(): return 2
def window_hi(nn): return nn - 1
def in_window(nn, r): return window_lo() <= r <= window_hi(nn)
def sigma(nn, r): return nn + 1 - r

# --- (1) the ledger prize depth r*=89 is deep inside the window, NOT r > n ---
if not in_window(n, rstar):
    fail(f"r*={rstar} not in window [2, {n-1}]")
if not (rstar < n):
    fail(f"expected r* < n but r*={rstar}, n={n}")
# G296's prose claimed r > n so n+1-r < 2 (escapes). Show that is FALSE:
if sigma(n, rstar) < 2:
    fail("sigma(n,r*) < 2 would mean escape; must NOT hold at production")
if not in_window(n, sigma(n, rstar)):
    fail(f"reflection sigma(n,r*)={sigma(n,rstar)} not in window")
assert sigma(n, rstar) == n + 1 - 89 == 2**30 - 88
print(f"[1] r*={rstar} in W, reflection sigma={sigma(n,rstar)}=2^30-88 in W. r*<n by margin {n-rstar}.")

# --- (2) general r-uniform integer content: Nat.log_n q <= n for all q <= n^n ---
# The prize rank r ~ log_n q is bounded by floor(log_n q); we show floor(log_n q) < n
# with astronomical margin because q = 2^158 << n^n = (2^30)^(2^30) = 2^(30*2^30).
def nat_log(base, x):
    # Lean Nat.log semantics: greatest k with base^k <= x (base>=2, x>=1)
    if base < 2 or x < 1:
        return 0
    k = 0
    while base ** (k + 1) <= x:
        k += 1
    return k

# base-2 shortcut: n = 2^30, q = 2^158, so log_n q = floor(158/30) = 5 (NO huge ints)
lnq = 158 // 30              # floor(log_n q) for n=2^30, q=2^158
if not (lnq < n):
    fail(f"Nat.log n q = {lnq} not < n")
if lnq != 5:
    fail(f"expected Nat.log (2^30) (2^158) = 5, got {lnq}")
# n^n dominates q via EXPONENT comparison only (never materialize n^n):
# log2(q)=158, log2(n^n)=30*2^30. Compare exponents.
log2_q = 158
log2_nn = 30 * (2 ** 30)     # log2 of n^n = 30 * 2^30
if not (log2_q < log2_nn):
    fail("log2 q < log2 n^n failed (q < n^n)")
print(f"[2] Nat.log_n q = {lnq} < n = 2^30. q=2^158 < n^n = 2^{log2_nn}. margin log2 = {log2_nn-158}.")

# --- (3) monotone/eventual: for ANY prize prime p with 2 <= p <= n^n, log_n p <= n ---
# Spot-check the boundary and several scales; the Lean theorem proves it in general.
for e in [1, 8, 128, 158, 256, 1000, 3000, 30720]:
    p = 2 ** e
    lp = nat_log(n, p)
    if not (lp <= n):
        fail(f"log_n(2^{e}) = {lp} > n")
    # log_n(2^e) = floor(e/30)
    if lp != e // 30:
        fail(f"log_n(2^{e}) expected {e//30}, got {lp}")
print("[3] log_n(2^e) = floor(e/30) <= n verified across scales up to e=30720.")

# --- (4) contrapositive sanity: escape (r > n) would require q >= n^(n+1), impossible at prize ---
# If the prize rank exceeded n, we would need log_n q > n, i.e. q > n^n = 2^(30*2^30).
# q = 2^158 is nowhere near. Confirm the threshold.
escape_needs_exp = 30 * (2 ** 30)      # q would need > 2^escape_needs_exp
if 158 >= escape_needs_exp:
    fail("158 >= escape threshold?! impossible")
print(f"[4] Escape (r>n) needs q > 2^{escape_needs_exp}; prize q=2^158. Escape FALSE by 2^{escape_needs_exp-158}.")

print("ALL G299 CHECKS PASS: production prize depth is INSIDE the palindrome window; G296 escape-prose refuted.")
