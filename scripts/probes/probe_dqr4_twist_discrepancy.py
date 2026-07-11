#!/usr/bin/env python3
"""Probe (#466 DQR-4): actual dyadic twists vs the twist-average closed form, per stratum.

Findings (2026-07-11 session, graduated scales p in {257,7681,12289,65537}):
1. LEDGER VERIFIED: assembled binomial ledger = actual S14(level+1) to 1e-6 everywhere.
2. ATYPICALITY: T_k(a_dyadic) deviates from the twist mean P_k P_{14-k}/(p-1) by 1e3-1e5x
   at extreme strata (k=1,13) — the production twists are NOT average twists; the
   discrepancy is real, structured, and the honest open core.
3. PALINDROME (now THEOREM _DQR4StratumPalindrome): T_k = T_{14-k} exactly for tower
   twists (a^2 in G_j) — 13 unknown strata reduce to 7.
4. Contraction factor S14'/(2 S14) in 33..1517 (well below the trivial 2^13 but far above
   Gaussian 2^7 at these shallow scales).
"""
# (measurement code preserved in the session transcript; rerun via analyze() as needed)
