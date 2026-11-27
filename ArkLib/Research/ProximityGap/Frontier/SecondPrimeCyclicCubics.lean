/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Six cyclic Lagrange cubics lower the second-prime half-rate MCA bound to 380,283,564

Six cyclic 4-vertex Lagrange cubic heads over the 8-element quotient `μ_8` of the second
production domain (`PrizeShapePrimeP30Second`, `N = 2^30`) sit at the exact extremal
zero-face-collinearity threshold (`D = 3, V = 6, H = 6`): every 5-vertex face contains at
most two blocks, so all 5/5 foreign directions at the two non-vertex quotient classes and all
2/2 foreign directions at the six vertex quotient classes are pairwise distinct.

Allocating `134,217,726` common roots and `134,217,730` owned non-vertex sites across the
32 quarter-fibers (`S32 = 2^25`) with zero off-head sites yields:
- defining core sizes `[693,458,259, 693,458,259, 693,458,260, 693,458,260, 693,458,260, 693,458,260]`,
- strict MCA failure at `380,283,564` errors (`-7,456,540` errors below `SecondPrimeTetrahedron`'s
  `387,740,104`), and
- `2,281,701,386` simultaneous bad scalars (`+134,217,738` above the `2^31` budget `P / 2^128`).

This module is 100% kernel-checked via `PlanarQuartetMass.mass` with standard axioms only.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCyclicCubics

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed (F N dom)
open PrizeShapePrimeP30Second (P prime_P orderOf_g)

local instance : Fact P.Prime := ⟨prime_P⟩

private abbrev S32 : ℕ := 33554432
private abbrev D8 : ℕ := 134217728
private def z8 : F := 684944486517762849622048856798491974355853664681

/-- Residue class modulo 32, followed by a position in its quarter-fiber of size `2^25`. -/
private abbrev Grid := Σ _ : Fin 32, Fin S32

/-- Enumeration of `Fin (2^30)` in 32-fiber order. -/
private noncomputable def index : Grid ≃ Fin N :=
  (Equiv.sigmaEquivProd _ _).trans
    (((Equiv.prodComm _ _).trans finProdFinEquiv).trans (finCongr (by decide : S32 * 32 = N)))

/-- The `D8`-th power map on `dom` factors through the 8th-root quotient `z8^(r % 8)`. -/
private theorem power8 (u : Grid) : (dom (index u)) ^ D8 = z8 ^ (u.1.val % 8) := by
  change (PrizeShapePrimeP30Second.g ^ (u.1.val + 32 * u.2.val)) ^ D8 = _
  have hg : PrizeShapePrimeP30Second.g ^ N = 1 := by
    simpa only [orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30Second.g
  have hr : (PrizeShapePrimeP30Second.g ^ (32 * u.2.val)) ^ D8 = 1 := by
    have h : 32 * u.2.val * D8 = N * (4 * u.2.val) := by
      change 32 * u.2.val * 134217728 = 1073741824 * (4 * u.2.val)
      ring
    rw [← pow_mul, h, pow_mul, hg, one_pow]
  have hz : PrizeShapePrimeP30Second.g ^ D8 = z8 := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
    decide +kernel
  have hz8 : z8 ^ 8 = 1 := by decide +kernel
  rw [pow_add, mul_pow, hr, mul_one, ← pow_mul, Nat.mul_comm, pow_mul, hz]
  calc
    z8 ^ u.1.val = z8 ^ (u.1.val % 8 + 8 * (u.1.val / 8)) :=
      congrArg (z8 ^ ·) (Nat.mod_add_div _ _).symm
    _ = z8 ^ (u.1.val % 8) := by rw [pow_add, pow_mul, hz8, one_pow, mul_one]

/-- First coordinates of the six cyclic Lagrange cubic heads, in ascending degree order. -/
def first : Fin 6 → Fin 4 → F :=
  ![![147258167331296645351292812204347133489395348276,
      532694058966416233080148854295695578621662617045,
      537686319186466204270756044594144840866458316408,
      243863091846723835501487121622095466706333548674],
    ![147258167331296645351292812204347133489395348277,
      191400412738968597767550641664513581560534699005,
      534358145706432890143684584395178666036594516833,
      490215900298760937727426754935012217965455166100],
    ![147258167331296645351292812204347133489395348278,
      629992090804694345163659865150088804657266746261,
      193064499478985254831086371763996668975466598793,
      441081394671039014120561735176396507649520116006],
    ![487726183693447671002974243244190933412667097352,
      679952226297712878431441666500042712111057965320,
      243024634972003788098868173113950576429257817852,
      50798592367738580670400749858098797730866949879],
    ![242199005106707178437951391522612379291401648891,
      481069836733381042748831322846258583752939498200,
      488551813558744280663891024835529130550523266313,
      249680981932070416353011093511882926088985416999],
    ![481069836733381042748831322846258583752939498205,
      242199005106707178437951391522612379291401648886,
      94940837775410533086658579318265245802006300613,
      643291957715404163930243539029146810837502382699]]

/-- Second coordinates of the six cyclic Lagrange cubic heads, in ascending degree order. -/
def second : Fin 6 → Fin 4 → F :=
  ![![2211844510998453527550184464627982775188026599,
      377247980477481990138777471748626312376798009982,
      642611677401976679738629004509308611158056015748,
      439430134940445794798728171993720113373807778074],
    ![296728179173591744230135808873322249753978723152,
      511754038669050613187501064439060335046213848618,
      677727554777290987162189315118608036196650376868,
      462701695281832118204824059552869950904415251377],
    ![591244513836185034932721433282016516732769419707,
      112753235038329831236861188159267275095330463111,
      129646320513964339585716482546678064743810379424,
      608137599311819543281576727669427306381249335995],
    ![479444231021634698910402093497195575755666284001,
      234413502168182251842585028473535144437778714900,
      251306587643816760191440322860945934086258631213,
      496337316497269207259257387884606365404146200289],
    ![233891398416047330861974907942003635355961711827,
      687510217443865250933317767605194623332134644449,
      496859420249404128239867508416137874485963203387,
      43240601221586208168524648752946886509790270740],
    ![449465015682487996283354617872886616008452964126,
      471936600177424585511938057674311642679643392150,
      28775883537832805591426218187980456574125489707,
      511324137933157530816965938981104304421627984420]]

private def valPoly (A : Fin 4 → F) (t : F) : F :=
  A 3 * t ^ 3 + A 2 * t ^ 2 + A 1 * t ^ 1 + A 0

private def fPoly (A : Fin 4 → F) : F[X] :=
  C (A 3) * Polynomial.X ^ 3 + C (A 2) * Polynomial.X ^ 2 + C (A 1) * Polynomial.X ^ 1 + C (A 0)

private def lift (A : Fin 4 → F) : F[X] := (fPoly A).comp (Polynomial.X ^ D8)

private theorem deg (A : Fin 4 → F) : (lift A).natDegree ≤ 3 * D8 := by
  have h : (fPoly A).natDegree ≤ 3 := by
    unfold fPoly
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le ..)
          ((natDegree_C_mul_X_pow_le ..).trans (by decide))
      · exact (natDegree_C_mul_X_pow_le ..).trans (by decide)
    · simp only [natDegree_C, Nat.zero_le]
  exact natDegree_comp_le.trans (Nat.mul_le_mul h (natDegree_X_pow_le D8))

private theorem lifted (A : Fin 4 → F) (u : Grid) :
    (lift A).eval (dom (index u)) = valPoly A (z8 ^ (u.1.val % 8)) := by
  rw [lift, eval_comp, eval_pow, eval_X, power8]
  simp [fPoly, valPoly]

private def U8 (i : Fin 6) (q : Fin 8) : F := valPoly (first i) (z8 ^ q.val)
private def V8 (i : Fin 6) (q : Fin 8) : F := valPoly (second i) (z8 ^ q.val)

private def UVal : Fin 6 → Fin 8 → F :=
  ![![1, 2, 3, 4,
      639138154370074240142255297238842438869782414166,
      687301680580630428618901288334619954589451493286,
      680645333620563800364758367936687604929723894135,
      632481807410007611888112376840910089210054815013],
    ![632481807410007611888112376840910089210054815014,
      2, 3, 4, 5,
      639138154370074240142255297238842438869782414167,
      687301680580630428618901288334619954589451493287,
      680645333620563800364758367936687604929723894136],
    ![680645333620563800364758367936687604929723894137,
      632481807410007611888112376840910089210054815015,
      3, 4, 5, 6,
      639138154370074240142255297238842438869782414168,
      687301680580630428618901288334619954589451493288],
    ![1,
      434583224272264949077423228766770848587421880727,
      669300252553608889600314918300112681081239761503,
      4, 5, 6,
      550853663554730335309739638318509542727503712698,
      54819873170622816730788911493709865379396678269],
    ![1, 2,
      674279685764235423049219941681755250186815899005,
      674279685764235423049219941681755250186815899008,
      5, 6,
      294516334662593290702585624408694266978790696553,
      294516334662593290702585624408694266978790696548],
    ![1, 2, 3,
      662643905593542261346171997902180331421512162356,
      421270530352131692569137387970906149267966682434,
      6,
      41507179250489560222503070697845166059941479980,
      530884622674530450547310877124712493748320915255]]

private def VVal : Fin 6 → Fin 8 → F :=
  ![![1, 4, 9, 16,
      558896225160498807430515961589731678024563169492,
      55650343627695034203617659914613047461528451589,
      180701971548946465781527192626921762918113852095,
      683947853081750239008425494302040393481148569988],
    ![487409830570862544580965415267577552217408369613,
      4, 9, 16, 25,
      375670896569744369511341723351133536080278167423,
      699502886123504432339577820225711446798506522961,
      80491001459171148307359095784013953093711809964],
    ![711030850034847289935033415299247653111234683036,
      290871808059974850153505336233114710953668169240,
      9, 16, 25, 36,
      192445567978989931592167485112535394135993165356,
      612604609953862371373695564178668336293559679134],
    ![1,
      636676878017292876657022306097291081451558344952,
      665105554229730878169060349103459603213166901521,
      16, 25, 36,
      521920551191356458370705608527181189967573319256,
      550349227403794459882743651533349711729181875799],
    ![1, 4,
      525334563907760272906802252259968183860174403051,
      145571212806118140560167934986907200652149200616,
      25, 36,
      410231029756429050541097379508046357563672444231,
      59243562192619723785889280422965830929772731451],
    ![1, 4, 9,
      586962812680027987065366882383373127746284502525,
      225730979775190144647719255763592635323231992464,
      36,
      110627445623858922282014383011670809026730033628,
      480146431384472538966209172750031826445602438738]]

private theorem U8_eq_UVal : ∀ i q, U8 i q = UVal i q := by decide +kernel
private theorem V8_eq_VVal : ∀ i q, V8 i q = VVal i q := by decide +kernel

private def vertexGroup : Fin 6 → Finset (Fin 6) :=
  ![{0, 3, 4, 5}, {0, 1, 4, 5}, {0, 1, 2, 5}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4, 5}]

private def own : Fin 32 → Fin 6 :=
  ![0, 1, 2, 3, 4, 5, 0, 4,
    0, 1, 2, 3, 4, 5, 1, 5,
    0, 1, 2, 3, 4, 5, 2, 0,
    0, 1, 2, 3, 4, 5, 3, 0]

private def group (r : Fin 32) : Finset (Fin 6) :=
  if h : r.val % 8 < 6 then vertexGroup ⟨r.val % 8, h⟩ else {own r}

private def cut : Fin 32 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 11184811, 11184810,
    0, 0, 0, 0, 0, 0, 11184811, 11184810,
    0, 0, 0, 0, 0, 0, 11184810, 33554432,
    0, 0, 0, 0, 0, 0, 11184810, 33554432]

private theorem cut_le : ∀ r : Fin 32, cut r ≤ S32 := by decide +kernel

/-- Zero face collinearity at the six vertex quotient classes (`q = 0..5`) and the two
non-vertex quotient classes (`q = 6, 7`): every foreign head misses in `V` and every pair
of distinct foreign heads produces a nonzero 2x2 determinant against the owner. -/
theorem zero_face_collinearity :
    (∀ (v : Fin 6) (i : Fin 6), i ∈ vertexGroup v →
      U8 i ⟨v.val, by omega⟩ = U8 v ⟨v.val, by omega⟩ ∧
      V8 i ⟨v.val, by omega⟩ = V8 v ⟨v.val, by omega⟩) ∧
    (∀ (v : Fin 6) (i : Fin 6), i ∉ vertexGroup v →
      V8 i ⟨v.val, by omega⟩ ≠ V8 v ⟨v.val, by omega⟩) ∧
    (∀ (v : Fin 6) (i j : Fin 6), i ∉ vertexGroup v → j ∉ vertexGroup v → i ≠ j →
      (U8 v ⟨v.val, by omega⟩ - U8 i ⟨v.val, by omega⟩) *
        (V8 j ⟨v.val, by omega⟩ - V8 v ⟨v.val, by omega⟩) ≠
      (U8 v ⟨v.val, by omega⟩ - U8 j ⟨v.val, by omega⟩) *
        (V8 i ⟨v.val, by omega⟩ - V8 v ⟨v.val, by omega⟩)) ∧
    (∀ (q : Fin 8), 6 ≤ q.val → ∀ (ow i : Fin 6), i ≠ ow → V8 i q ≠ V8 ow q) ∧
    (∀ (q : Fin 8), 6 ≤ q.val → ∀ (ow i j : Fin 6), i ≠ ow → j ≠ ow → i ≠ j →
      (U8 ow q - U8 i q) * (V8 j q - V8 ow q) ≠
      (U8 ow q - U8 j q) * (V8 i q - V8 ow q)) := by
  simp only [U8_eq_UVal, V8_eq_VVal]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

private theorem own_vertex (r : Fin 32) (h : r.val % 8 < 6) :
    (own r).val = r.val % 8 := by
  revert r h; decide +kernel

private theorem agrees (r : Fin 32) (i : Fin 6) (hi : i ∈ group r) :
    U8 i ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ = U8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ ∧
    V8 i ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ = V8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ := by
  unfold group at hi
  split_ifs at hi with h
  · have how : own r = ⟨r.val % 8, h⟩ := Fin.ext (own_vertex r h)
    rw [how]
    exact zero_face_collinearity.1 ⟨r.val % 8, h⟩ i hi
  · rw [Finset.mem_singleton.mp hi]
    exact ⟨rfl, rfl⟩

private theorem misses (r : Fin 32) (i : Fin 6) (hi : i ∉ group r) :
    V8 i ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ ≠ V8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ := by
  unfold group at hi
  split_ifs at hi with h
  · have how : own r = ⟨r.val % 8, h⟩ := Fin.ext (own_vertex r h)
    rw [how]
    exact zero_face_collinearity.2.1 ⟨r.val % 8, h⟩ i hi
  · exact zero_face_collinearity.2.2.2.1 ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
      (own r) i (Finset.mem_singleton.not.mp hi)

private theorem determinant (r : Fin 32) (i j : Fin 6) (hi : i ∉ group r) (hj : j ∉ group r)
    (hne : i ≠ j) :
    (U8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ - U8 i ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩) *
      (V8 j ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ - V8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩) ≠
    (U8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ - U8 j ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩) *
      (V8 i ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ - V8 (own r) ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩) := by
  unfold group at hi hj
  split_ifs at hi hj with h
  · have how : own r = ⟨r.val % 8, h⟩ := Fin.ext (own_vertex r h)
    rw [how]
    exact zero_face_collinearity.2.2.1 ⟨r.val % 8, h⟩ i j hi hj hne
  · exact zero_face_collinearity.2.2.2.2 ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
      (own r) i j (Finset.mem_singleton.not.mp hi) (Finset.mem_singleton.not.mp hj) hne

private noncomputable def lower (r : Fin 32) : Finset (Fin S32) :=
  univ.filter (fun s => s.val < cut r)

private theorem card_lower (r : Fin 32) : (lower r).card = cut r := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le r)]

private abbrev Selection := Fin 32 → Bool → Bool

private noncomputable def row (take : Selection) (r : Fin 32) : Finset (Fin S32) :=
  (if take r false then lower r else ∅) ∪ (if take r true then (lower r)ᶜ else ∅)

private noncomputable def selected (take : Selection) : Finset (Fin N) :=
  (univ.sigma (row take)).map index.toEmbedding

private theorem card_selected (take : Selection) :
    (selected take).card =
      ∑ r : Fin 32, ((if take r false then cut r else 0) + (if take r true then S32 - cut r else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro r _
  cases h1 : take r false <;> cases h2 : take r true <;>
    simp [row, h1, h2, card_lower, card_compl, Nat.add_sub_of_le (cut_le r)]

private theorem mem_selected (take : Selection) (u : Grid) :
    index u ∈ selected take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) := by
  classical
  change index.toEmbedding u ∈ (univ.sigma (row take)).map index.toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]

private def roots : Finset (Fin N) := selected (fun _ high => !high)
private def core (i : Fin 6) : Finset (Fin N) := selected (fun r high => !high || decide (i ∈ group r))
private def owner (x : Fin N) : Fin 6 := own (index.symm x).1

private theorem root_count : roots.card = 134217726 := by
  rw [roots, card_selected]
  decide +kernel

private theorem core_count (i : Fin 6) :
    (core i).card = (![693458259, 693458259, 693458260, 693458260, 693458260, 693458260] : Fin 6 → ℕ) i := by
  rw [core, card_selected]
  fin_cases i <;> decide +kernel

private theorem roots_subset_core (i : Fin 6) : roots ⊆ core i := by
  intro x hx
  obtain ⟨u, rfl⟩ := index.surjective x
  rw [roots, mem_selected] at hx
  rw [core, mem_selected]
  simp [hx]

/-- Exact integer optimality of the smallest active core for any 6-cubic cyclic allocation:
no allocation of `r ≤ 134,217,726` roots and `a ≤ 805,306,368` vertex sites can push the
minimum core above `693,458,259` (corresponding to `380,283,564` errors). -/
theorem allocation_limit {r a o c : ℕ} (hr : r ≤ 134217726) (ha : a ≤ 805306368)
    (hsum : r + a + o ≤ 1073741824) (hcores : 6 * c ≤ 6 * r + 4 * a + o) :
    c ≤ 693458259 := by
  omega

/-- Simultaneous bad-scalar lower bound at `380,283,564` errors for every dimension
`536,870,912 ≤ k ≤ 693,458,259` and every positive interleaving width. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 693458259) (width : ℕ) [NeZero width] :
    (2281701386 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (380283564 / 1073741824) := by
  have counts : (∑ i : Fin 6, (core i)ᶜ.card) = 2281701386 := by
    simp only [card_compl, core_count, Fintype.card_fin, Fin.sum_univ_succ]
    decide
  have least (i : Fin 6) : 693458259 ≤ (core i).card := by
    rw [core_count]
    fin_cases i <;> decide
  rw [epsMCA_interleaved_eq]
  have hm := PlanarQuartetMass.mass dom k (3 * D8) (380283564 / 1073741824)
    (fun i => lift (first i)) (fun i => lift (second i)) roots owner core
    (by rw [root_count]; dsimp [D8]; omega)
    (fun i => deg _) (fun i => deg _)
    roots_subset_core
    (by
      intro i x hx hr
      obtain ⟨u, rfl⟩ := index.surjective x
      rw [core, mem_selected] at hx
      rw [roots, mem_selected] at hr
      have hhi : decide (cut u.1 ≤ u.2.val) = true := by
        cases h : decide (cut u.1 ≤ u.2.val) <;> simp_all
      have hi : i ∈ group u.1 := by simpa [hhi] using hx
      have hres := agrees u.1 i hi
      simpa only [lifted, owner, Equiv.symm_apply_apply, U8, V8] using hres)
    (by
      intro i x hx
      obtain ⟨u, rfl⟩ := index.surjective x
      rw [core, mem_selected] at hx
      have hi : i ∉ group u.1 := by
        intro hmem
        exact hx (by simp [hmem])
      have hres := misses u.1 i hi
      simpa only [lifted, owner, Equiv.symm_apply_apply, V8] using hres)
    (by
      intro x i j hi hj hne
      obtain ⟨u, rfl⟩ := index.surjective x
      rw [core, mem_selected] at hi hj
      have hi' : i ∉ group u.1 := fun hmem => hi (by simp [hmem])
      have hj' : j ∉ group u.1 := fun hmem => hj (by simp [hmem])
      have hres := determinant u.1 i j hi' hj' hne
      simpa only [lifted, owner, Equiv.symm_apply_apply, U8, V8] using hres)
    (fun i => hc.trans (least i))
    (by
      intro i
      rw [Fintype.card_fin]
      apply le_trans (b := ((693458259 + 1 : ℕ) : ℝ≥0))
      · rw [tsub_mul, one_mul]
        norm_num [N, tsub_le_iff_right]
      · exact_mod_cast Nat.add_le_add_right (least i) 1)
    (by rw [counts, Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right]; decide +kernel)
  rw [counts, ZMod.card] at hm
  simpa only [Nat.cast_ofNat] using hm

/-- At half rate on the second production prime, MCA strictly exceeds `2^(-128)` at
`380,283,564` errors (`-7,456,540` errors below `SecondPrimeTetrahedron.half`). -/
theorem half (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 536870912 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1 / (2 : ℝ≥0∞) ^ 128
    tol < epsMCA (F := F) code (380283564 / 1073741824) ∧
      mcaDeltaStar (F := F) code tol ≤ 380283564 / 1073741824 := by
  dsimp only
  have hb : 1 / (2 : ℝ≥0∞) ^ 128 < (2281701386 : ℝ≥0∞) / (P : ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0 < 2 ^ 128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h :
        ((2281701386 : ℕ) : ℝ≥0∞) / P ≤ 1 / ((2 ^ 128 : ℕ) : ℝ≥0∞))
    exact (by decide +kernel : ¬ 2281701386 ≤ P / 2 ^ 128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad, mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms zero_face_collinearity
#print axioms allocation_limit
#print axioms label_mass
#print axioms half

end ArkLib.ProximityGap.Frontier.SecondPrimeCyclicCubics
