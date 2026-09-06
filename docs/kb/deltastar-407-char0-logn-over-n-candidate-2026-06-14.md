# CANDIDATE char-0 closed form: delta* = (1-rho) - log2(n)/n  (constant rate, #407)

> **⚠️ REFUTED 2026-06-14 (#444 A2; see `Research/ProximityPrize/DISPROOF_LOG.md`).**
> The `w_cross - k = log2(n)` form is **FALSE**. Recomputed q-stably with the SAME (k+1)-subset
> method under the STANDARD crossing rule (smallest w with worst I_0 <= n AND previous band > n),
> w_cross - k is **{2,3}, NOT log2(n)**, at every tested point (n=8,16; rho=1/8,1/4,1/2,3/4), under
> BOTH the include-n/2 and exclude-n/2 direction conventions:
>   n=16 rho=1/8 -> w_cross-k=3 (log2=4, NO); n=16 rho=1/4 -> 3 (NO); n=16 rho=1/2 -> 3 (NO);
>   n=8 rho=1/2 -> 2 (log2=3, NO).
> Root cause (reproduced exactly, `scripts/probes/probe_a2_repro_candidate_logn.py`): the original
> probe (i) EXCLUDED the a=n/2 antipodal-coset generator (the genuinely worst far line, which the
> in-tree delta* law maxes over) and (ii) used a first-crossing rule on a profile where the worst
> incidence sits on a PLATEAU equal to the dilation-orbit size n/gcd(b-a,n) (e.g. n=16 rho=1/8:
> I_0=16 from the (8,9) orbit, constant across w=5..9). The "crossing" is then pinned by WHERE you
> enter the plateau (a function of the chosen direction's orbit size + the n/2 exclusion), NOT by
> log2(n). With the worst (n/2-touching) direction included and the standard crossing rule, the
> log2(n) coincidence (which held at only 2 hand-picked points) evaporates.
> **delta* = (1-rho) - log2(n)/n is NOT the char-0 closed form.** The surviving honest constraint
> remains |delta* - (1-sqrt(rho))| <= 1/n; the proposed Theta(log n / n) gap below capacity is not
> established. Probes: `probe_a2_corrected_crossing_mann.py`, `probe_a2_crossing_inclexcl_half.py`,
> `probe_a2_n32_orbit_plateau.py`.
>
> **Surviving sibling finding (#444 A2 positive):** at the crossing band the incidence DOES equal a
> dilation-orbit count whose witnesses are antipodal-pair unions (+<=1 leftover), so
> I_0(w_cross) = Mann_core(w_cross) EXACTLY (Mann/Lam-Leung pins the BOUNDARY). This is the classical
> regime; it does NOT pin the window interior (the prize target). See DISPROOF_LOG 2026-06-14 #444 A2.

---
(historical, now refuted) Char-0 (q-free, p>>n^3) worst-case far-line incidence I_0(delta), crossing
budget=n, at CONSTANT RATE (method = (k+1)-subset solve; worst over far pencils a,b>=k != n/2):

| rho | n  | k | crossing w | w-k | log2(n) |
|-----|----|---|-----------|-----|---------|
| 1/8 | 16 | 2 | 6         | 4   | 4       |
| 1/8 | 32 | 4 | 9         | 5   | 5       |
| 1/4 | 16 | 4 | 7         | 3   | 4 (-1)  |

The original claim was `n*(cap - delta*) = w_delta* - k = log2(n)` for rho=1/8. The 1/4 point already
broke it (-1); the q-stable standard-crossing recomputation breaks it everywhere (see banner).
Probe: scripts/probes/probe_char0_deltastar_pin_constrate.py (original, n/2-excluding).
