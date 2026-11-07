# Beating di Benedetto via the 2-power Sidon-floor energies — VERIFIED linchpin, exponent 0.989→0.958 (#444)

> **Correction (2026-10-28 audit, T48).** This note correctly flags its modular substitution as
> unverified (Phase 2). That gate stands, and so does its later Phase-1 threshold refinement: the
> general expression's nontriviality point is `p^{40/191}`, not `p^{1/4}`. Note, though, that this
> point, like `p^{1/7}`, lies below the published theorem's window `p^{1/4} < H`. The claimed
> **all-prime** energy invariance does not hold.
> "E_3 is p-INVARIANT" and "T_2, T_3 EXACT ... incl extreme structured primes" describe the primes
> sampled. At the recorded thin cell `n = 64`, `p = 17318209` (`p > n⁴`; T91), the exact pair count
> gives `E_2 = 13632`, not `3n² − 3n = 12096`, so the claimed universal `T_2` identity already fails
> there. The selected finite measurements may well be correct as measurements. The published
> Theorem 3.1 also assumes `p^{1/4} < H < p^{1/2}`, so the `p^{1/7}` "nontriviality" lies outside
> its proven range (see `dibenedetto-beat-CONFIRMED-2026-06-15.md` and R-260).

GOAL: beat di Benedetto et al (arXiv:2003.06165, char-sum exponent 1-31/2880~0.9892, vanishes at |H|=p^{1/4})
for CLOSENESS to the prize, by any margin. Phase-1 deep-read+slack-audit (4 verified agents) + linchpin
computation. **A genuine improvement is identified, with its linchpin machine-verified; one validity check
remains (Phase 2).**

## The barrier origin (4-agent consensus, verified against the paper)
The |H|>p^{1/4} requirement comes ENTIRELY from the p^{1/4} prefactor of the Petridis-Shparlinski trilinear
estimate (Lemma 4.1) — the ONLY place p enters the Thm 3.1 argument. The exponent is MODULAR in the energy
inputs: saving s=(Hexp-4)/72, Hexp=(6-t3)+(6-t3)+(1/2)(4-t2), where T_2<<H^{t2}, T_3<<H^{t3}.
- di Benedetto (general subgroups): t2=49/20, t3=4 => Hexp=4.775 => s=31/2880. [REPRODUCED EXACTLY — corroborates
  the audit's reading of the modular structure.]

## The 2-power lever + VERIFIED linchpin
mu_n additive energies are at the SIDON FLOOR (minimal), MUCH better than the general worst-case:
- T_2(mu_n)=3n^2-3n EXACTLY (t2=2). [proven Sidon floor]
- T_3(mu_n)=15n^3-45n^2+40n=O(n^3) (t3=3). [LINCHPIN]
**VERIFIED by exact F_p computation (probe_dibenedetto_energy_inputs.py):** E_2/(3n^2-3n)=1.00000 and
E_3/(15n^3-45n^2+40n)=1.00000 for n=8,16,32 across primes incl EXTREME structured ones (v2(p-1) up to 25,
e.g. n=32 p=167772161). E_3 is p-INVARIANT (unlike E_4 which fails at structured primes). So T_3=O(n^3) char-p
holds in the prize regime — SOLID.

Plugging t2=2, t3=3 into the modular formula: Hexp=14-2(3)-2/2=7 => s=(7-4)/72=1/24~0.0417.
=> char-sum exponent 1 - 1/24 = 23/24 ~ 0.958 (BEATS 0.9892), and (per audit) nontriviality extends to
H>p^{1/7} ~ p^{0.143}, COVERING the prize regime H~q^{1/4..1/5}=p^{0.2..0.25} where di Benedetto VANISHES.

## Status: beats di Benedetto for CLOSENESS *if* the substitution is valid in the actual argument
- VERIFIED (solid): the linchpin T_2,T_3 = Sidon-floor, p-invariant to extreme structured primes.
- CORROBORATED: the modular formula reproduces 31/2880 exactly.
- OPEN (Phase 2): confirm di Benedetto's Lemma 4.2/4.3 take T_2(mu_n)/T_3(mu_n) as modular inputs (not a coupled
  sumset object), so the substitution is valid; pin the EXACT improved exponent + threshold; check whether
  combining with a 2-power-specific trilinear prefactor (Lemma 4.1) pushes closer still.
- HONEST: this is an improvement for CLOSENESS (0.989->0.958, into the prize regime) — exactly the GOAL — NOT a
  prize closure (0.958 >> 1/2). The half-power wall stands; this is genuine forward progress on the SOTA exponent.

## Phase-1 REFINEMENTS (verified line-by-line, /tmp/diben.txt)
- True di Benedetto threshold = p^{40/191}=p^{0.2094} (just above prize floor p^{0.20}), NOT exactly p^{1/4}.
- T3 (Lemma 4.3) used TWICE (X,Y legs); T2 (Lemma 4.2) used ONCE (Z leg, |Z|^{7/8} in trilinear).
- t3:4->3 alone: Hexp=271/40, exponent 0.9615, threshold p^{1/6.78}. Both Sidon-floor (t3=3,t2=2): Hexp=7, exponent 0.9583, threshold p^{1/7}=p^{0.143} (covers prize q^{1/4..1/5}). t2->2 alone: exponent 0.9861, threshold p^{1/5}.
- UPGRADE: T2,T3 are EXACT (diff=0) for all tested n<=64 incl extreme structured primes => t3=3 is a VERIFIED IDENTITY for tested n, only 'persists for all n' (No-Excess) remains to prove.
- The p^{1/4} prefactor (Lemma 4.1) is the ONLY route toward 1/2 and is open (Target for further push); the energy substitution does NOT need it for the closeness/regime gain.
