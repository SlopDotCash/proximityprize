/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RatSquarefreeClassification

/-!
# Issue #232 — RÉDEI–DE BRUIJN–SCHOENBERG AT EVERY SQUAREFREE MODULUS: the
ℤ-classification (O115)

The coefficient trilogy completed at full squarefree generality: O109 gave the
ℚ-classification at every squarefree `n`; O108 gave ℤ at `pqr`; this file gives
ℤ everywhere —

    `∑_{e<n} w_e·ζ^e = 0   ⟺   ∃ A : ℕ → ℕ → ℤ, ∀ e < n,
        w e = ∑_{p ∈ primeFactors n} A p (e % (n/p))`

for INTEGER weights `w : ℕ → ℤ` — Schoenberg's theorem (the lattice of vanishing
sums is packet-spanned over ℤ) at every squarefree modulus, arbitrary arity.

Proof: the O109 strong induction reruns verbatim with ℤ-weights — and is in fact
SIMPLER: the fiber differences are ℤ-valued, so the inductive hypothesis applies
directly with no rational detour; the analytic steps (the CRT transport, the
O106 gate, the slice engine) consume only the `L`-casts.  The construction is
manifestly integral (`A p y := w(section(0,y))`, decode through the IH), which is
exactly why the theorem holds.  Converse: each packet part dies against its full
geometric sum (`Int`-cast mirror of O109a).

Combined with O105 (ℕ-components impossible at three primes), the
positivity boundary of the general squarefree theory is now sharp at every
arity: ℤ always, ℕ exactly up to two primes (O103).  The surviving ℕ-content is
Lam–Leung's positivity induction for the TOTAL weight — the linear and integral
structure on which it must run is now complete.
-/

namespace IntSquarefreeClassification

open Polynomial Finset IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- **RÉDEI–DE BRUIJN–SCHOENBERG, SQUAREFREE CASE** (arbitrary arity): an
INTEGER-weighted power sum at a primitive `n`-th root (`n` squarefree, char 0)
vanishes iff the weight function is a ℤ-combination of prime-fiber components —
the vanishing lattice is packet-spanned over ℤ. -/
theorem int_squarefree_classification :
    ∀ n : ℕ, Squarefree n → 0 < n → ∀ ζ : L, IsPrimitiveRoot ζ n →
      ∀ w : ℕ → ℤ,
      ((∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) ↔
        ∃ A : ℕ → ℕ → ℤ, ∀ e < n,
          w e = ∑ p ∈ n.primeFactors, A p (e % (n / p))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hsq hn0 ζ hζ w
    constructor
    case mpr =>
      rintro ⟨A, hA⟩
      have hstep : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e
          = ∑ p ∈ n.primeFactors, ∑ e ∈ Finset.range n,
              (A p (e % (n / p)) : L) * ζ ^ e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [hA e (Finset.mem_range.mp he), Int.cast_sum, Finset.sum_mul]
      rw [hstep]
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hk : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hpp.pos
      have hsplit : (n / p) * p = n := Nat.div_mul_cancel hpn
      rw [show Finset.range n = Finset.range ((n / p) * p) from by rw [hsplit]]
      have hregroup : ∑ e ∈ Finset.range ((n / p) * p),
          (A p (e % (n / p)) : L) * ζ ^ e
          = ∑ r ∈ Finset.range (n / p), ζ ^ r *
              ∑ e' ∈ Finset.range p, (A p ((r + (n / p) * e') % (n / p)) : L)
                * (ζ ^ (n / p)) ^ e' := by
        calc ∑ e ∈ Finset.range ((n / p) * p), (A p (e % (n / p)) : L) * ζ ^ e
            = ∑ x ∈ Finset.range (n / p) ×ˢ Finset.range p,
                (A p ((x.1 + (n / p) * x.2) % (n / p)) : L)
                  * ζ ^ (x.1 + (n / p) * x.2) := by
              refine (Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 + (n / p) * x.2)
                (fun e => (e % (n / p), e / (n / p))) ?_ ?_ ?_ ?_ ?_).symm
              · rintro ⟨r, c⟩ hx
                rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
                rw [Finset.mem_range]
                calc r + (n / p) * c < (n / p) + (n / p) * c := by omega
                  _ = (n / p) * (c + 1) := by ring
                  _ ≤ (n / p) * p := Nat.mul_le_mul_left _ (by omega)
              · intro e he
                rw [Finset.mem_range] at he
                rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
                refine ⟨Nat.mod_lt _ hk, ?_⟩
                rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm p (n / p)]
                exact he
              · rintro ⟨r, c⟩ hx
                rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
                have h1 : (r + (n / p) * c) % (n / p) = r := by
                  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1]
                have h2 : (r + (n / p) * c) / (n / p) = c := by
                  rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hx.1,
                    Nat.zero_add]
                exact Prod.ext h1 h2
              · intro e _
                exact Nat.mod_add_div e (n / p)
              · rintro ⟨r, c⟩ _
                rfl
          _ = ∑ r ∈ Finset.range (n / p), ∑ e' ∈ Finset.range p,
                (A p ((r + (n / p) * e') % (n / p)) : L)
                  * ζ ^ (r + (n / p) * e') := Finset.sum_product _ _ _
          _ = ∑ r ∈ Finset.range (n / p), ζ ^ r *
                ∑ e' ∈ Finset.range p, (A p ((r + (n / p) * e') % (n / p)) : L)
                  * (ζ ^ (n / p)) ^ e' := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun e' _ => ?_
              rw [pow_add, pow_mul]
              ring
      rw [hregroup]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hconst : ∀ e' ∈ Finset.range p,
          (A p ((r + (n / p) * e') % (n / p)) : L) * (ζ ^ (n / p)) ^ e'
            = (A p r : L) * (ζ ^ (n / p)) ^ e' := by
        intro e' _
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum,
        (hζ.pow hn0 hsplit.symm).geom_sum_eq_zero hpp.one_lt, mul_zero, mul_zero]
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
          rw [map_mul, map_pow, hgen, map_intCast]
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
              ((w ((e₁ * i + e₂ * f) % n) - w ((e₁ * 0 + e₂ * f) % n) : ℤ) : L)
                * η' ^ f = 0 := by
          intro i hi
          have hAeq := CRTDoubleSlice.slice_of_packet_minpoly hmin hsumA hi
            hp.pos Nat.zero_lt_one
          simp only [mul_one, add_zero] at hAeq
          have hmapped := congrArg (algebraMap ℚ⟮η'⟯ L) hAeq
          rw [hmapA, hmapA] at hmapped
          have hterm : ∀ f ∈ Finset.range m,
              ((w ((e₁ * i + e₂ * f) % n) - w ((e₁ * 0 + e₂ * f) % n) : ℤ) : L)
                  * η' ^ f
                = (w ((e₁ * i + e₂ * f) % n) : L) * η' ^ f
                  - (w ((e₁ * 0 + e₂ * f) % n) : L) * η' ^ f := by
            intro f _
            push_cast
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hmapped,
            sub_self]
        -- inductive components per fiber
        have hIH : ∀ i : ℕ, ∃ B : ℕ → ℕ → ℤ, i < p →
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

end IntSquarefreeClassification

#print axioms IntSquarefreeClassification.int_squarefree_classification
