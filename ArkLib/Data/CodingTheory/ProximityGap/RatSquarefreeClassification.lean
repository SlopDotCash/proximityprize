/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralPacketCombination
import ArkLib.Data.CodingTheory.ProximityGap.CoprimePacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefreeExp

/-!
# Issue #232 — THE GENERAL SQUAREFREE ℚ-CLASSIFICATION: the arity induction (O109)

The O109 gate executed: for EVERY squarefree modulus `n` (any number of prime
factors) and `ζ` a primitive `n`-th root in characteristic zero,

    `∑_{e<n} w_e·ζ^e = 0   ⟺   ∃ A : ℕ → ℕ → ℚ, ∀ e < n,
        w e = ∑_{p ∈ primeFactors n} A p (e % (n/p))`

— the de Bruijn–Schoenberg LINEAR theory of vanishing weighted root-of-unity
sums, at arbitrary arity, subsuming the proved `k = 2` (O102) and `k = 3` (O107)
instances.  Strong induction on `n`, peeling `p = minFac n`:

* CRT transport `e ↔ (e % p, e % m)` (`m = n/p`, coprime by squarefreeness) with
  the explicit section `(e₁·i + e₂·f) % n` — the O102 forward at general
  composite cofactor (the coordinate-root primitivity argument generalizes:
  `Coprime e₂ m` falls out of `e₂ ≡ 1 [MOD m]` by one `gcd_rec`);
* the `p`-fiber coefficients live in `K = ℚ⟮η'⟯` (the cofactor root is adjoined
  DIRECTLY — no composite-base generator juggling), and the O106 gate at
  `(m, p)` feeds `slice_of_packet_minpoly`: all `p`-fibers are equal;
* fiber differences vanish at level `m` ⟹ the inductive hypothesis components;
* decode: `A p y := W(0, y)` and, for `q ∣ m`,
  `A q y := B_{y % p} q (y % (m/q))` — well-defined by `p ∣ n/q`,
  `(m/q) ∣ n/q`, `(m/q) ∣ m` and `Nat.mod_mod_of_dvd`;
* converse: O109a `rat_packet_combination_vanishes` (every modulus).

With this, the ℚ-linear half of the general de Bruijn program is COMPLETE at all
squarefree moduli; the remaining ℕ-content is Lam–Leung's positivity induction
(boundary pinned ℤ-yes/ℕ-no by O108/O105 at three primes).
-/

namespace RatSquarefreeClassification

open Polynomial Finset IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- **THE GENERAL SQUAREFREE ℚ-CLASSIFICATION** (arbitrary arity): a ℚ-weighted
power sum at a primitive `n`-th root (`n` squarefree, char 0) vanishes iff the
weight function is a sum of prime-fiber components
`A p (e % (n/p))` over the prime divisors of `n`. -/
theorem rat_squarefree_classification :
    ∀ n : ℕ, Squarefree n → 0 < n → ∀ ζ : L, IsPrimitiveRoot ζ n →
      ∀ w : ℕ → ℚ,
      ((∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) ↔
        ∃ A : ℕ → ℕ → ℚ, ∀ e < n,
          w e = ∑ p ∈ n.primeFactors, A p (e % (n / p))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hsq hn0 ζ hζ w
    constructor
    case mpr =>
      rintro ⟨A, hA⟩
      exact GeneralPacketCombination.rat_packet_combination_vanishes hn0 hζ A w hA
    case mp =>
      intro hsum
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0.ne') with hn1 | hn1
      · -- BASE: `n = 1`
        subst hn1
        refine ⟨fun _ _ => 0, fun e he => ?_⟩
        interval_cases e
        have h1 : ∑ e ∈ Finset.range 1, (w e : L) * ζ ^ e = (w 0 : L) := by
          rw [Finset.sum_range_one, pow_zero, mul_one]
        rw [h1] at hsum
        have hw0 : w 0 = 0 := by exact_mod_cast hsum
        simp [hw0]
      · -- STEP: peel `p = minFac n`
        set p := n.minFac with hpdef
        have hp : p.Prime := Nat.minFac_prime (by omega)
        have hpdvd : p ∣ n := Nat.minFac_dvd n
        set m := n / p with hmdef
        have hpm : p * m = n := Nat.mul_div_cancel' hpdvd
        have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd hn0 hpdvd) hp.pos
        have hpnm : ¬ p ∣ m := by
          intro hdvd
          have hsq2 : p * p ∣ n := by
            rw [← hpm]
            exact mul_dvd_mul_left p hdvd
          exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hsq2))
        have hco : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpnm
        have hmdvdn : m ∣ n := ⟨p, by rw [← hpm]; ring⟩
        have hsqm : Squarefree m := hsq.squarefree_of_dvd hmdvdn
        have hmn : m < n := Nat.div_lt_self hn0 hp.one_lt
        -- CRT section
        obtain ⟨e₁, he₁p, he₁m⟩ := Nat.chineseRemainder hco 1 0
        obtain ⟨e₂, he₂p, he₂m⟩ := Nat.chineseRemainder hco 0 1
        have hmodp : ∀ i f : ℕ, (e₁ * i + e₂ * f) % p = i % p := by
          intro i f
          have h : e₁ * i + e₂ * f ≡ 1 * i + 0 * f [MOD p] :=
            Nat.ModEq.add (he₁p.mul_right i) (he₂p.mul_right f)
          simpa only [one_mul, zero_mul, add_zero] using h
        have hmodm : ∀ i f : ℕ, (e₁ * i + e₂ * f) % m = f % m := by
          intro i f
          have h : e₁ * i + e₂ * f ≡ 0 * i + 1 * f [MOD m] :=
            Nat.ModEq.add (he₁m.mul_right i) (he₂m.mul_right f)
          simpa only [one_mul, zero_mul, zero_add] using h
        have hpdn : p ∣ p * m := ⟨m, rfl⟩
        have hmdn : m ∣ p * m := ⟨p, Nat.mul_comm p m⟩
        have hsection : ∀ e < n, (e₁ * (e % p) + e₂ * (e % m)) % n = e := by
          intro e he
          have h1 : (e₁ * (e % p) + e₂ * (e % m)) % n % p = e % p := by
            rw [← hpm, Nat.mod_mod_of_dvd _ hpdn, hmodp,
              Nat.mod_mod_of_dvd _ (dvd_refl p)]
          have h2 : (e₁ * (e % p) + e₂ * (e % m)) % n % m = e % m := by
            rw [← hpm, Nat.mod_mod_of_dvd _ hmdn, hmodm,
              Nat.mod_mod_of_dvd _ (dvd_refl m)]
          have h3 : (e₁ * (e % p) + e₂ * (e % m)) % n ≡ e [MOD p * m] :=
            (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h1, h2⟩
          rw [hpm] at h3
          have h4 : (e₁ * (e % p) + e₂ * (e % m)) % n % n = e % n := h3
          rwa [Nat.mod_mod_of_dvd _ (dvd_refl n), Nat.mod_eq_of_lt he] at h4
        -- the coordinate roots
        have hmdvd₁ : m ∣ e₁ := (Nat.modEq_zero_iff_dvd).mp he₁m
        have hpdvd₂ : p ∣ e₂ := (Nat.modEq_zero_iff_dvd).mp he₂p
        have hpnd₁ : ¬ p ∣ e₁ := by
          intro hdvd
          obtain ⟨k, hk⟩ := hdvd
          have h0 : e₁ % p = 0 := by rw [hk]; exact Nat.mul_mod_right p k
          have h1 : e₁ % p = 1 % p := he₁p
          have h2 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
          omega
        obtain ⟨c₁, hc₁⟩ := hmdvd₁
        obtain ⟨c₂, hc₂⟩ := hpdvd₂
        have hpc₁ : ¬ p ∣ c₁ := fun hd => hpnd₁ (hc₁ ▸ hd.mul_left m)
        have hξ' : IsPrimitiveRoot (ζ ^ e₁) p := by
          have hbase : IsPrimitiveRoot (ζ ^ m) p :=
            hζ.pow hn0 (by rw [← hpm]; ring)
          have h := hbase.pow_of_coprime c₁
            (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpc₁))
          rwa [← pow_mul, ← hc₁] at h
        have hcop_e₂m : Nat.Coprime e₂ m := by
          rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm0.ne') with hm1 | hm1
          · rw [← hm1]
            exact Nat.coprime_one_right e₂
          · have h1 : e₂ % m = 1 := by
              have h' : e₂ % m = 1 % m := he₂m
              rwa [Nat.mod_eq_of_lt hm1] at h'
            have h2 : Nat.gcd m e₂ = 1 := by
              rw [Nat.gcd_rec, h1, Nat.gcd_one_left]
            exact Nat.coprime_comm.mp h2
        have hcop_c₂m : Nat.Coprime c₂ m :=
          Nat.Coprime.coprime_dvd_left ⟨p, by rw [hc₂]; ring⟩ hcop_e₂m
        have hη' : IsPrimitiveRoot (ζ ^ e₂) m := by
          have hbase : IsPrimitiveRoot (ζ ^ p) m := hζ.pow hn0 hpm.symm
          have h := hbase.pow_of_coprime c₂ hcop_c₂m
          rwa [← pow_mul, ← hc₂] at h
        -- the grid transport
        have hexp : ∀ i f : ℕ,
            (ζ ^ e₁) ^ i * (ζ ^ e₂) ^ f = ζ ^ ((e₁ * i + e₂ * f) % n) := by
          intro i f
          rw [← pow_mul, ← pow_mul, ← pow_add,
            DeBruijnWeightedSquarefreeExp.pow_mod_eq hζ]
        have htrans : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e
            = ∑ x ∈ Finset.range p ×ˢ Finset.range m,
                (w ((e₁ * x.1 + e₂ * x.2) % n) : L)
                  * ((ζ ^ e₁) ^ x.1 * (ζ ^ e₂) ^ x.2) := by
          refine Finset.sum_nbij' (fun e => (e % p, e % m))
            (fun x => (e₁ * x.1 + e₂ * x.2) % n) ?_ ?_ ?_ ?_ ?_
          · intro e _
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
            exact ⟨Nat.mod_lt _ hp.pos, Nat.mod_lt _ hm0⟩
          · intro x _
            rw [Finset.mem_range]
            exact Nat.mod_lt _ hn0
          · intro e he
            exact hsection e (Finset.mem_range.mp he)
          · rintro ⟨i, f⟩ hx
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
            have h1 : (e₁ * i + e₂ * f) % n % p = i := by
              rw [← hpm, Nat.mod_mod_of_dvd _ hpdn, hmodp,
                Nat.mod_eq_of_lt hx.1]
            have h2 : (e₁ * i + e₂ * f) % n % m = f := by
              rw [← hpm, Nat.mod_mod_of_dvd _ hmdn, hmodm,
                Nat.mod_eq_of_lt hx.2]
            exact Prod.ext h1 h2
          · intro e he
            rw [hsection e (Finset.mem_range.mp he)]
            congr 1
            rw [hexp (e % p) (e % m), hsection e (Finset.mem_range.mp he)]
        -- the K-side fiber coefficients and the slice
        set η' : L := ζ ^ e₂ with hη'def
        set g : ℚ⟮η'⟯ := IntermediateField.AdjoinSimple.gen ℚ η' with hg
        have hgen : algebraMap ℚ⟮η'⟯ L g = η' :=
          IntermediateField.AdjoinSimple.algebraMap_gen ℚ η'
        have hmapA : ∀ i : ℕ,
            algebraMap ℚ⟮η'⟯ L (∑ f ∈ Finset.range m,
                (w ((e₁ * i + e₂ * f) % n) : ℚ⟮η'⟯) * g ^ f)
              = ∑ f ∈ Finset.range m,
                  (w ((e₁ * i + e₂ * f) % n) : L) * η' ^ f := by
          intro i
          rw [map_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [map_mul, map_pow, hgen, map_ratCast]
        have hmin := CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom
          hm0 hp (Nat.coprime_comm.mp hco) hη' hξ'
        have hsumA : ∑ i ∈ Finset.range (p * 1),
            (∑ f ∈ Finset.range m,
              (w ((e₁ * i + e₂ * f) % n) : ℚ⟮η'⟯) * g ^ f) • (ζ ^ e₁) ^ i
              = 0 := by
          rw [mul_one]
          have hswap : ∑ i ∈ Finset.range p,
              (∑ f ∈ Finset.range m,
                (w ((e₁ * i + e₂ * f) % n) : ℚ⟮η'⟯) * g ^ f) • (ζ ^ e₁) ^ i
              = ∑ x ∈ Finset.range p ×ˢ Finset.range m,
                  (w ((e₁ * x.1 + e₂ * x.2) % n) : L)
                    * ((ζ ^ e₁) ^ x.1 * (ζ ^ e₂) ^ x.2) := by
            rw [Finset.sum_product]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Algebra.smul_def, hmapA, Finset.sum_mul]
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [hη'def]
            ring
          rw [hswap, ← htrans]
          exact hsum
        -- all p-fibers equal ⟹ fiber differences vanish at level m
        have hfiber : ∀ i < p,
            ∑ f ∈ Finset.range m,
              ((w ((e₁ * i + e₂ * f) % n) - w ((e₁ * 0 + e₂ * f) % n) : ℚ) : L)
                * η' ^ f = 0 := by
          intro i hi
          have hAeq := CRTDoubleSlice.slice_of_packet_minpoly hmin hsumA hi
            hp.pos Nat.zero_lt_one
          simp only [mul_one, add_zero] at hAeq
          have hmapped := congrArg (algebraMap ℚ⟮η'⟯ L) hAeq
          rw [hmapA, hmapA] at hmapped
          have hterm : ∀ f ∈ Finset.range m,
              ((w ((e₁ * i + e₂ * f) % n) - w ((e₁ * 0 + e₂ * f) % n) : ℚ) : L)
                  * η' ^ f
                = (w ((e₁ * i + e₂ * f) % n) : L) * η' ^ f
                  - (w ((e₁ * 0 + e₂ * f) % n) : L) * η' ^ f := by
            intro f _
            push_cast
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hmapped,
            sub_self]
        -- inductive components per fiber
        have hIH : ∀ i : ℕ, ∃ B : ℕ → ℕ → ℚ, i < p →
            ∀ f < m, w ((e₁ * i + e₂ * f) % n) - w ((e₁ * 0 + e₂ * f) % n)
              = ∑ q ∈ m.primeFactors, B q (f % (m / q)) := by
          intro i
          by_cases hi : i < p
          · obtain ⟨B, hB⟩ := (ih m hmn hsqm hm0 η' hη'
              (fun f => w ((e₁ * i + e₂ * f) % n)
                - w ((e₁ * 0 + e₂ * f) % n))).mp (hfiber i hi)
            exact ⟨B, fun _ => hB⟩
          · exact ⟨fun _ _ => 0, fun h => absurd h hi⟩
        choose B hB using hIH
        -- the prime factor split of n
        have hfactors : n.primeFactors = insert p m.primeFactors := by
          rw [← hpm, Nat.primeFactors_mul hp.pos.ne' hm0.ne',
            hp.primeFactors, Finset.singleton_union]
        have hpnotin : p ∉ m.primeFactors := fun hmem =>
          hpnm (Nat.dvd_of_mem_primeFactors hmem)
        have hdivp : n / p = m := hmdef.symm
        -- the assembled components
        refine ⟨fun q' y => if q' = p then w ((e₁ * 0 + e₂ * y) % n)
          else B (y % p) q' (y % (m / q')), fun e he => ?_⟩
        rw [hfactors, Finset.sum_insert hpnotin]
        show w e = (if p = p then w ((e₁ * 0 + e₂ * (e % (n / p))) % n)
            else B ((e % (n / p)) % p) p ((e % (n / p)) % (m / p)))
          + ∑ x ∈ m.primeFactors,
              (if x = p then w ((e₁ * 0 + e₂ * (e % (n / x))) % n)
                else B ((e % (n / x)) % p) x ((e % (n / x)) % (m / x)))
        -- the master identity at (e%p, e%m)
        have hkey := hB (e % p) (Nat.mod_lt _ hp.pos) (e % m) (Nat.mod_lt _ hm0)
        have hwe : w ((e₁ * (e % p) + e₂ * (e % m)) % n) = w e := by
          rw [hsection e he]
        rw [hwe] at hkey
        -- the `p`-component
        have hpcomp : (if p = p then w ((e₁ * 0 + e₂ * (e % (n / p))) % n)
            else B ((e % (n / p)) % p) p ((e % (n / p)) % (m / p)))
            = w ((e₁ * 0 + e₂ * (e % m)) % n) := by
          rw [if_pos rfl, hdivp]
        -- the `q`-components decode
        have hqcomp : ∀ q ∈ m.primeFactors,
            (if q = p then w ((e₁ * 0 + e₂ * (e % (n / q))) % n)
              else B ((e % (n / q)) % p) q ((e % (n / q)) % (m / q)))
            = B (e % p) q ((e % m) % (m / q)) := by
          intro q hq
          have hqp : q ≠ p := fun h => hpnotin (h ▸ hq)
          have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
          have hnq : n / q = p * (m / q) := by
            rw [← hpm, Nat.mul_div_assoc p hqm]
          have h1 : (e % (n / q)) % p = e % p := by
            rw [hnq, Nat.mod_mod_of_dvd _ ⟨m / q, rfl⟩]
          have h2 : (e % (n / q)) % (m / q) = (e % m) % (m / q) := by
            have hd1 : (m / q) ∣ (n / q) := hnq ▸ ⟨p, Nat.mul_comm p (m / q)⟩
            have hd2 : (m / q) ∣ m := ⟨q, (Nat.div_mul_cancel hqm).symm⟩
            rw [Nat.mod_mod_of_dvd _ hd1, Nat.mod_mod_of_dvd _ hd2]
          rw [if_neg hqp, h1, h2]
        rw [hpcomp, Finset.sum_congr rfl hqcomp]
        linarith [hkey]

end RatSquarefreeClassification

#print axioms RatSquarefreeClassification.rat_squarefree_classification
