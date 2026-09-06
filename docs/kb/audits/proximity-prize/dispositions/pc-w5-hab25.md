STATUS: PARTIAL — Hab25 Lemma 1 (the [AHIV17/BKS18] collinearity→correlated-agreement counting bound) PORTED & PROVEN (kernel-clean, axioms = [propext, Classical.choice, Quot.sound]); main theorem (MCA up to 1−√ρ) decomposed with the GS-bivariate nodes classified DEEP/NEEDS-INFRA. New file: Research/ProximityPrize/Hab25Core.lean.

# Hab25 port — scout + first core lemma

Source: Ulrich Haböck, "A note on mutual correlated agreement for Reed–Solomon codes",
ePrint 2025/2110, Nov 17 2025. Fulltext: research/proximity-prize/artifacts/2025-2110-fulltext.txt (369 lines).
Worktree: /home/shaw/arklib-prize (branch proximity-prize-l217). Compile: single-file `lake env lean`.

## In-tree discharge targets (unchanged; statements left as-is, no sorry faked)
- mca_johnson_bound_CONJECTURE — ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:263 (BStar=√ρ).
- rs_epsMCA_johnson_range_bchks25 — Research/ProximityPrize/CapacityBounds.lean:273
  (ABF26 Thm 4.12; the note there already records "ABF26 cites [Hab25] alongside [BCHKS25]" — Hab25 IS the
  cleaner Johnson-radius proof of this exact bound).

## PHASE A — Theorem dependency tree (Hab25)

MAIN THM (Definition 1, paper l.43–54; = rs_epsMCA_johnson_range): RS[F_q,D,k] satisfies mutual
correlated agreement up to the Johnson radius γ = 1 − √(1−δ) = 1 − √ρ_plus, with |E| ≤ poly(m)/|F|·n²-ish.
Reduces (l.236) to:

  Theorem 2 (l.124–146): |E| ≤ (ℓ⁷/3)·(ρn)², ℓ=(m+½)/√ρ.  [= [BCIKS20] Thm 5.1 generalized to F(Z)]
  └─ via E = ⋃_{i,j} E_{i,j}, #(i,j) ≤ D_Y < ℓ, and:
     Claim 1 (l.238–243): |E_{i,j}| ≤ (ℓ⁶/3)·(ρn)².  [proof l.246–311]
       ├─ NODE-GS-INTERP: Guruswami–Sudan interpolating polynomial Q(X,Y,Z) of f₀+Z·f₁ over K=F_q(Z),
       │    factored Q = C·∏ Ri(X,Y^{p^{fi}},Z)^{ei}, Ri irreducible/separable (l.158–168).
       │    Degree bounds (l.169–177): D_Y<ℓ, D_X<ℓ·ρn, D_{YZ}≤(ℓ³/6)·ρn  [[BCIKS20] Claim 5.4].   → DEEP
       ├─ NODE-DISCRIMINANT: deg_X disc_Y(Q) < ℓ²·ρn ⇒ ∃ x₀ with disc_Y Ri(x₀,Y,Z)≠0 ∀i, for |F|>ℓ²ρn
       │    (else Thm 2 trivial). Starting pt for the Hensel lift.  [[BCIKS20] §5.2.3]               → DEEP
       ├─ NODE-HENSEL/STEPS5-7: Hensel lift + [BCIKS20] Step5–Step7 (+ App.C inseparable fi>0) on the
       │    "useful factor" R=Ri w/ irreducible H=Hi,j of Ri(x₀,Y,Z); |S_{x₀,R,H}| > 2·D_Y²·D_X·D_{YZ}
       │    ⇒ Ri(X,Y^{p^{fi}},Z) = (Y−(a(X)+Z·b(X)))^{p^{fi}}, hence pz(X)=a(X)+z·b(X) UNIQUE.
       │    [[BCIKS20] Claim 5.7, Steps 5–7, App. C]                                                  → DEEP
       └─ ENDGAME (l.302–310): once pz=a+z·b is unique, every z∈E_{i,j} must "improve agreement
            beyond A°={x:(a(x),b(x))=(f₀(x),f₁(x))}", and **"from the proof of Lemma 1"** the number of
            such z is ≤ |D\A°| ≤ n; then (m+½)⁶/(3ρ)·n² > n gives the contradiction.
            ⇒ **directly reuses Lemma 1's per-coordinate counting**.                    → IN-TREE-PROVABLE
                                                                                          (this is what I built)

  Lemma 1 ([AHIV17,BKS18], §2, l.94–114): general linear code C; f₀,f₁:D→F; p₀,p₁∈C with
    Δ(p₀+z p₁, f₀+z f₁) ≤ γ ∀ z∈S. If |S| > ⌈γn⌉+1 then Δ([p₀,p₁],[f₀,f₁]) ≤ γ.
    Proof = double count over S×E': each z matches ≥1 pt of E' (size e+1), each pt of E matches
    ≤1 z (the gap (p₀−f₀)(x)+z(p₁−f₁)(x) is a nontrivial affine functional). ⇒ |S|≤e+1, contra.
                                                                                  → IN-TREE-PROVABLE-NOW ✔ DONE

### Per-node classification & in-tree asset map
| Node | Class | In-tree asset / gap |
|---|---|---|
| Lemma 1 (counting) | IN-TREE-PROVABLE-NOW | **PROVEN here** (Hab25Core.lean). Generalizes the l=0 case of WeightedAgreement.badCoord_match_card_le; GSCounting.exists_heavy_coordinate is the dual averaging primitive. |
| Claim-1 ENDGAME | IN-TREE-PROVABLE (next) | reuses Lemma 1 (affine_match_card_le_one) summed over D\A°; the only extra input is uniqueness of pz, which is the DEEP GS output. |
| NODE-GS-INTERP (degrees) | NEEDS-NAMED-INFRA | partial: BCKHS25/Interpolation.lean has BW interpolant exists_BW_pair / exists_modified_guruswami_interpolant / exists_joint_proximate (multiplicity-coded), and BCIKS20/ListDecoding/{Guruswami,Extraction,RootClearing} exist. Missing: the X/Y/YZ degree bookkeeping of Claim 5.4 over F(Z). |
| NODE-DISCRIMINANT | DEEP | no disc_Y / resultant-over-K machinery in tree; needs algebraic-function-field discriminant API. |
| NODE-HENSEL/STEPS5-7 | DEEP | BCIKS20/HenselNumerator.lean is a stub-name only; Steps 5–7 + App.C (inseparable p^{fi}) not formalized. This is the genuine crux and is the same wall LineDecoding.lean documents. |
| List/Johnson inputs | NEEDS-NAMED-INFRA | JohnsonBound/{Basic,Family,Lemmas}.lean (Family.lean is 96KB, substantial), ListDecodability.lean, ListDecoding/Bounds.lean present; GuruswamiSudan/GuruswamiSudan.lean present. Connect-up not done. |

### Cross-check vs the existing in-tree wall (important)
ArkLib/.../ProximityGap/LineDecoding.lean (lineDecodable_imp_epsMCA_le, ABF26 Thm 4.21 = GG25) already
documents — with a kernel-checked counterexample (LineDecodingCounting.double_coverage_counterexample) —
that the *elementary* multi-γ "double-coverage" reduction is mathematically FALSE, and that the genuine
proof MUST route through the GS bivariate interpolation over F(Z). Hab25 is precisely that GS route.
So Hab25's Lemma 1 is the shared elementary bedrock both traditions reuse; the GS interpolation nodes
above are the real content that the in-tree `sorry` (LineDecoding.lean:235, CapacityBounds.lean:289)
is blocked on. My port closes the bedrock node honestly and pins the DEEP nodes precisely.

## PHASE B — What was proven (Research/ProximityPrize/Hab25Core.lean)

All compile single-file (lake env lean, lean4 v4.29.0), zero warnings, no sorry/admit/native_decide/bv_decide/axiom.
In-file `#print axioms` (run, then removed per protocol) on ALL THREE:
  depends on axioms: [propext, Classical.choice, Quot.sound]   ← standard Mathlib only, no sorryAx.

1. `affine_root_subsingleton {d₀ d₁ : F} (hne : d₀ ≠ 0 ∨ d₁ ≠ 0) : {z | d₀ + z*d₁ = 0}.Subsingleton`
   — the per-coordinate pivot of Lemma 1 (paper l.108–112): a non-trivial affine functional in z has
   ≤1 root. Case split on d₁=0 (no root, since d₀≠0) vs d₁≠0 (unique root via mul_right_cancel₀).

2. `affine_match_card_le_one (d₀ d₁ : F) (hne) (S : Finset F) :
       (S.filter (fun z => d₀ + z*d₁ = 0)).card ≤ 1`
   — Finset form: the exact quantity double-counted in Lemma 1 ("each disagreement point has ≤1
   matching z"). This is what Claim-1's endgame reuses.

3. `hab25_lemma1_counting (d₀ d₁ : ι → F) (S : Finset F) (e : ℕ)
       (hagree : ∀ z ∈ S, |{x : d₀x + z·d₁x ≠ 0}| ≤ e) (hS : e+1 < S.card) :
       |{x : d₀x ≠ 0 ∨ d₁x ≠ 0}| ≤ e`
   — **the full Lemma 1**, sharp integer form (e = ⌈γn⌉; d₀=p₀−f₀, d₁=p₁−f₁; working with differences
   removes the linear-code hypothesis, WLOG). Proof is the paper's exact S×E' double count:
   exists_subset_card_eq pulls E' of size e+1 from the (assumed >e) disagreement set; each z∈S matches
   ≥1 pt of E' (else hagree z violated); Fubini (Finset.sum_comm') swaps to per-coordinate sums; each
   x∈E' contributes ≤1 via affine_match_card_le_one; ⇒ |S| ≤ e+1, contra hS via omega.
   Supporting defs: `affineGap d₀ d₁ z x := d₀ x + z*d₁ x`, `disagreeSet d₀ d₁ := filter (d₀≠0 ∨ d₁≠0)`.

## Staged entry points (next, in dependency order)
- E1 (IN-TREE-PROVABLE next): Claim-1 ENDGAME as a standalone lemma — given a UNIQUE affine pair
  (a,b) and the per-z "improves agreement beyond A°" hypothesis, conclude |E_{i,j}| ≤ n by summing
  affine_match_card_le_one over D\A°. Depends only on Hab25Core + a uniqueness hypothesis (the GS output
  taken as an explicit hypothesis, NOT proven). This is a faithful, honest intermediate.
- E2 (NEEDS-NAMED-INFRA): Theorem-2 assembly E=⋃E_{i,j}, #(i,j)<ℓ — pure union-card bookkeeping over
  Claim 1; needs the D_Y<ℓ degree bound (NODE-GS-INTERP) as hypothesis.
- E3..E5 (DEEP): NODE-GS-INTERP degree bounds (partial via BCKHS25/Interpolation), NODE-DISCRIMINANT,
  NODE-HENSEL/STEPS5-7. These are the same GS-over-F(Z) crux flagged by LineDecoding.lean's WALL note;
  not reachable without algebraic-function-field discriminant + Hensel-lift infrastructure (no mathlib API).

## Honesty stance
No existing statement was edited or fake-proved. The MCA conjecture statement in Whir/MutualCorrAgreement.lean
and the two `sorry`-bearing in-tree theorems remain exactly as found. New work is a NEW self-contained file
proving the one genuinely-reachable shared node (Lemma 1), with the DEEP nodes named precisely and left open.
