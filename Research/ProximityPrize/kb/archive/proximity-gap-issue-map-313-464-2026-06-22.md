# Proximity-gap issue map: #313 (Binius) ↔ #464 (δ*) — one substrate, two ends

*Cross-issue orientation note. Honesty contract (cone §6): this note CLOSES nothing. It is a
`docs/kb` map — bold in exploration, strict in claims. Its central "tie-it-together" claim was run
through the apophenia gate (`/lewis-brain`) and the over-unification half was REFUSED; see §3.*

---

## 1. The two open issues sit at opposite ends of the same object

Both open ArkLib issues are *proximity testing* in the same SNARK stack — they are the **applied
end** and the **theoretical frontier** of a single coding-theory object, the proximity gap.

| | **#313 Binius** | **#464 δ\*** |
|---|---|---|
| Object | FRI-Binius / Binary Basefold soundness over binary tower fields | optimal proximity-gap list-decoding threshold for smooth-domain RS codes |
| Cone | `ArkLib/ProofSystem/Binius/**` | `ArkLib/Data/CodingTheory/ProximityGap/**` |
| Nature | **engineering** — a half-propagated `Fin.rev` index refactor | **open research** — `$1M`, genuinely unsolved |
| State (cold, 2026-06-22) | build RED, 30 errors (`Steps/Fold.lean` 12 + `BinaryBasefold/QueryPhase.lean` 18), author-grade migration | floor open at the Paley/BGK wall; ceiling + exact value + lower bound settled |
| Load-bearing file | `QueryPhase.lean` `rbrKnowledgeSoundness` (the soundness bound) | `MCAThresholdLedger.lean` `mcaDeltaStar` (the threshold) |

The genuine link: Binius soundness (the `rbrKnowledgeSoundness` obligation in QueryPhase) ultimately
rests on **proximity-gap arguments**, and δ\* is exactly *where the optimal proximity gap sits*.
Same subfield, same `ProximityGap/` math, one stack.

## 2. The δ* frontier, named precisely (the arxiv tie)

The δ\* floor reduces — machine-checked, axiom-clean — to the **Paley Graph Conjecture**:

- `B = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|` is the non-principal eigenvalue of the generalized Paley graph
  `Cay(F_q, μ_n)` (Liu–Zhou Thm 115). `B ≤ 2√n ⟺ Ramanujan ⟺` the conjecture.
- **Proven:** BGK `n^{1−o(1)}`. **SOTA:** di Benedetto `n^{0.98924}` (arXiv 2003.06165, `≈1%`
  sub-trivial). **Conjectured:** `n^{1/2+o(1)}` — a full **half-power** open.
- **Ceiling RESOLVED** (Kambiré, arXiv 2604.09724 / eprint 2026/782): on the smooth `μ_n` domain
  proximity gaps provably FAIL at `(1−ρ)−Θ(1/log n)` — purely algebraic (coset-vanishing + root
  count + Linnik), so the `−Θ(1/log n)` term is structurally necessary.
- **Exact value pinned** (campaign): `M ≈ √(2 n log p)`, `C = √2` (antipodal-pair CLT; kurtosis
  `3 − 3/n`); proven lower bound `M ≥ √3·√n`.
- Substrate papers: [ABF26] 2026/680, [KKH26] 2026/782, [Jo26] 2026/891, [GG25] 2025/2054.
  Full inventory: `deltastar-444-CAMPAIGN-CAPSTONE-2026-06-21.md` (~57 angles / ~257 papers).

## 3. The apophenia gate (/lewis-brain verdict on "tie it together")

The instinct to "surface everything and tie it together" is itself the thing to test. The campaign
already names why a unifying frame fails: **K=1 extremality** — `μ_n·μ_n = μ_n` (perfect
multiplicative closure, zero doubling slack) makes *every* structural method (Green–Ruzsa,
sum-product, Burgess, decoupling, SOS, ergodic, …) structurally vacuous. A frame general enough to
"tie everything together" constrains nothing — no-free-lunch. This matches the prior witnessed
verdict on the string-theory+QM universal-solver framing (memory `issue-464-delta-star-apophenia-refused`).

Decomposed verdict:

- ✅ **Real (load-bearing, two witnesses):** #313 and #464 share the proximity-gap substrate; the
  δ\* floor = Paley/BGK; the ceiling is closed. The campaign's 57-angle exhaustion and the
  literature's 257-paper SOTA independently converge on the same wall.
- ❌ **Apophenia (refused):** that "tying them together" *unlocks* either. It does not. The Binius
  Fold bug is `Fin.rev` index wiring closeable by hand; δ\* is a half-power gap no current
  mathematics crosses. "Same subfield" ≠ "one solution."

## 4. Net — a map, not a master key

One proximity-gap substrate, two ends: one an author-grade engineering migration (closeable with
focused effort — see `issue-313-binius-cone-cold-census` memory for the live error map), one a
recognized open prize (closeable only by new mathematics on the Paley wall). The honest deliverable
is the map plus the refusal to let the map fabricate progress on the open core.

*Pointers:* `issue-313-binius-cone-cold-census`, `issue-464-delta-star-apophenia-refused` (memory) ·
`deltastar-444-CAMPAIGN-CAPSTONE-2026-06-21.md` · `ProximityGap/CLAUDE.md` §3.5/§5.
