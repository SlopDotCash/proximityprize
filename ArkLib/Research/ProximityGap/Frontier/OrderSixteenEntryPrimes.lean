import Mathlib

/-!
# The single-moment norm certificate at order sixteen

A signed choice from the eight antipodal pairs is a degree-seven polynomial.
Successively multiplying by the conjugate under X ↦ -X reduces its vanishing
at an eighth root of -1 to the vanishing of an explicit integer.
-/

namespace ProximityGap.Frontier.OrderSixteenEntryPrimes

structure Four (R : Type*) where
  a : R
  b : R
  c : R
  d : R

namespace Four

variable {R : Type*} [CommRing R]

def eval (q : Four R) (x : R) : R := q.a + q.b*x + q.c*x^2 + q.d*x^3

/-- Squaring modulo X^4+1. -/
def square (q : Four R) : Four R :=
  ⟨q.a^2-2*q.b*q.d-q.c^2, 2*q.a*q.b-2*q.c*q.d,
   2*q.a*q.c+q.b^2-q.d^2, 2*q.a*q.d+2*q.b*q.c⟩

def norm (q : Four R) : R :=
  (q.a^2-q.c^2+2*q.b*q.d)^2 + (2*q.a*q.c-q.b^2+q.d^2)^2

theorem eval_square (q : Four R) {x : R} (hx : x^4 = -1) :
    (q.eval x)^2 = q.square.eval x := by
  unfold eval square
  linear_combination (2*q.b*q.d+q.c^2+2*q.c*q.d*x+q.d^2*x^2)*hx

theorem norm_zero_of_eval (q : Four R) {x : R} (hx : x^4 = -1) (h : q.eval x = 0) :
    q.norm = 0 := by
  unfold eval at h
  let u := q.a^2-q.c^2+2*q.b*q.d
  let v := 2*q.a*q.c-q.b^2+q.d^2
  have huv : u + x^2*v = 0 := by
    dsimp [u,v]
    linear_combination (q.a-q.b*x+q.c*x^2-q.d*x^3)*h -
      (q.c^2-2*q.b*q.d-q.d^2*x^2)*hx
  change u^2+v^2 = 0
  linear_combination (u-x^2*v)*huv + v^2*hx

/-- The coefficient vector of E(X)^2-X O(X)^2 modulo X^4+1. -/
def descend (E O : Four R) : Four R :=
  ⟨E.square.a+O.square.d, E.square.b-O.square.a,
   E.square.c-O.square.b, E.square.d-O.square.c⟩

theorem eval_descend (E O : Four R) {x : R} (hx : x^4 = -1) :
    E.eval x ^ 2 - x * O.eval x ^ 2 = (descend E O).eval x := by
  rw [E.eval_square hx, O.eval_square hx]
  unfold eval descend
  linear_combination -O.square.d * hx

theorem norm_zero_at_order_sixteen (E O : Four R) {x : R} (hx : x^8 = -1)
    (h : E.eval (x^2) + x * O.eval (x^2) = 0) : (descend E O).norm = 0 := by
  have hx4 : (x^2)^4 = -1 := by simpa only [← pow_mul] using hx
  apply norm_zero_of_eval _ hx4
  rw [← eval_descend E O hx4]
  linear_combination (E.eval (x^2) - x * O.eval (x^2))*h

end Four

def digits (a b c d : Fin 3) : Four ℤ :=
  ⟨(a.val : ℤ)-1, (b.val : ℤ)-1, (c.val : ℤ)-1, (d.val : ℤ)-1⟩

def Four.castZMod (p : ℕ) (q : Four ℤ) : Four (ZMod p) := ⟨q.a,q.b,q.c,q.d⟩

/-- Least common multiple of the nonzero signed norms in this model. -/
def normMultiple : ℕ := 19578399097634641832363784947218309144704

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem signed_norms_divide :
    ∀ a b c d e f g h : Fin 3,
      (a,b,c,d,e,f,g,h) ≠ (1,1,1,1,1,1,1,1) →
      ((Four.descend (digits a c e g) (digits b d f h)).norm).natAbs ∣ normMultiple := by
  decide +kernel

theorem normMultiple_factorization : normMultiple =
    2^7 * 3^4 * 7^4 * 17^2 * 23^2 * 31^2 *
      97 * 113 * 193 * 241 * 337 * 353 * 401 * 433 * 577 * 881 := by decide +kernel

theorem modulus_dvd_of_signed_zero (p : ℕ) (x : ZMod p) (hx : x^8 = -1)
    (a b c d e f g h : Fin 3) (hv : (a,b,c,d,e,f,g,h) ≠ (1,1,1,1,1,1,1,1))
    (hz : ((digits a c e g).castZMod p).eval (x^2) +
      x * ((digits b d f h).castZMod p).eval (x^2) = 0) : p ∣ normMultiple := by
  let N := (Four.descend (digits a c e g) (digits b d f h)).norm
  have hzero : (N : ZMod p) = 0 := by
    have hh := Four.norm_zero_at_order_sixteen _ _ hx hz
    simpa [N, Four.norm, Four.descend, Four.square, Four.castZMod] using hh
  have hd : (p : ℤ) ∣ N := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  apply Nat.dvd_trans _ (signed_norms_divide a b c d e f g h hv)
  exact_mod_cast (Int.dvd_natAbs.mpr hd)

private def primeSupport : List ℕ :=
  [2,3,7,17,23,31,97,113,193,241,337,353,401,433,577,881]

private theorem mem_support_of_prime_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ normMultiple) :
    p ∈ primeSupport := by
  have hm : normMultiple ∣ primeSupport.prod ^ 7 := by decide +kernel
  have hprod := hp.dvd_of_dvd_pow (h.trans hm)
  obtain ⟨q,hq,hd⟩ := hp.prime.dvd_prod_iff.mp hprod
  have hall : primeSupport.all (fun t => decide (Nat.Prime t)) = true := by decide +kernel
  have hprime : q.Prime := of_decide_eq_true (List.all_eq_true.mp hall q hq)
  rwa [(Nat.prime_dvd_prime_iff_eq hp hprime).mp hd]

/-- Every prime divisor of the common multiple is at most 881. -/
theorem prime_le_of_dvd_normMultiple {p : ℕ} (hp : p.Prime) (h : p ∣ normMultiple) :
    p ≤ 881 := by
  have hall : primeSupport.all (fun t => decide (0<t ∧ t≤881)) = true := by decide +kernel
  have hbounds : 0<p ∧ p≤881 :=
    of_decide_eq_true (List.all_eq_true.mp hall p (mem_support_of_prime_dvd hp h))
  exact hbounds.2

theorem split_prime_mem_of_dvd_normMultiple {p : ℕ} (hp : p.Prime) (hres : p % 16 = 1)
    (h : p ∣ normMultiple) : p ∈ [17,97,113,193,241,337,353,401,433,577,881] := by
  have heq : primeSupport.filter (fun t => t % 16 == 1) =
      [17,97,113,193,241,337,353,401,433,577,881] := by decide +kernel
  rw [← heq]
  exact List.mem_filter.mpr ⟨mem_support_of_prime_dvd hp h, by simp [hres]⟩

/-- A nonempty signed choice from the eight antipodal pairs cannot have a
vanishing first moment beyond the last exceptional prime. -/
theorem signed_entry_ne_zero {p : ℕ} (hp : p.Prime) (hlarge : 881 < p)
    (x : ZMod p) (hx : x^8 = -1)
    (a b c d e f g h : Fin 3) (hv : (a,b,c,d,e,f,g,h) ≠ (1,1,1,1,1,1,1,1)) :
    ((digits a c e g).castZMod p).eval (x^2) +
      x * ((digits b d f h).castZMod p).eval (x^2) ≠ 0 := by
  intro hz
  exact hlarge.not_ge (prime_le_of_dvd_normMultiple hp
    (modulus_dvd_of_signed_zero p x hx a b c d e f g h hv hz))

/-- Existence of an order-sixteen signed antipodal-pair entry with zero first moment.
The Fin 3 codes 0, 1 and 2 denote coefficients -1, 0 and 1. -/
def HasSignedEntry (p : ℕ) : Prop :=
  ∃ x : ZMod p, x^8 = -1 ∧ ∃ a b c d e f g h : Fin 3,
    (a,b,c,d,e,f,g,h) ≠ (1,1,1,1,1,1,1,1) ∧
    ((digits a c e g).castZMod p).eval (x^2) +
      x * ((digits b d f h).castZMod p).eval (x^2) = 0

/-- Exact exceptional split primes; the reverse implication gives eleven concrete witnesses. -/
theorem hasSignedEntry_iff {p : ℕ} (hp : p.Prime) (hres : p % 16 = 1) :
    HasSignedEntry p ↔ p ∈ [17,97,113,193,241,337,353,401,433,577,881] := by
  constructor
  · rintro ⟨x, hx, a,b,c,d,e,f,g,h,hv,hz⟩
    exact split_prime_mem_of_dvd_normMultiple hp hres
      (modulus_dvd_of_signed_zero p x hx a b c d e f g h hv hz)
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨3, by decide +kernel, 1, 1, 1, 1, 2, 1, 2, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨8, by decide +kernel, 1, 1, 2, 2, 1, 0, 1, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨35, by decide +kernel, 1, 2, 1, 0, 1, 2, 2, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨3, by decide +kernel, 1, 1, 2, 2, 1, 2, 0, 2, by decide +kernel, by decide +kernel⟩
    · exact ⟨44, by decide +kernel, 1, 1, 2, 0, 2, 2, 1, 2, by decide +kernel, by decide +kernel⟩
    · exact ⟨30, by decide +kernel, 1, 2, 0, 0, 2, 2, 2, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨36, by decide +kernel, 1, 1, 2, 0, 2, 0, 0, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨30, by decide +kernel, 1, 1, 2, 0, 2, 2, 1, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨151, by decide +kernel, 1, 1, 2, 2, 2, 1, 0, 2, by decide +kernel, by decide +kernel⟩
    · exact ⟨27, by decide +kernel, 1, 2, 2, 2, 0, 1, 2, 0, by decide +kernel, by decide +kernel⟩
    · exact ⟨68, by decide +kernel, 1, 2, 2, 2, 2, 2, 0, 2, by decide +kernel, by decide +kernel⟩

/-- Witness at the claimed last prime, in the generating element 68. -/
theorem attains_last_prime :
    (68 : ZMod 881)^8 = -1 ∧
      (68 : ZMod 881) + 68^2 + 68^3 + 68^4 + 68^5 - 68^6 + 68^7 = 0 := by
  decide +kernel

#print axioms Four.norm_zero_at_order_sixteen
#print axioms signed_norms_divide
#print axioms normMultiple_factorization
#print axioms modulus_dvd_of_signed_zero
#print axioms prime_le_of_dvd_normMultiple
#print axioms split_prime_mem_of_dvd_normMultiple
#print axioms signed_entry_ne_zero
#print axioms hasSignedEntry_iff
#print axioms attains_last_prime

end ProximityGap.Frontier.OrderSixteenEntryPrimes
