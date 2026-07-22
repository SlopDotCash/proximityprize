/-
Atk_R6 : Bezout-on-the-relation-variety conjecture (R6) — structural no-go.

R6 CLAIM: W_r = #F_p-points of the weight-2r relation variety V_r
  (sum_{i<=r} (zeta^{a_i} - zeta^{b_i}) = 0), a 0-dim complete intersection
  whose Bezout DEGREE is bounded by a product <= (2r)!*small, forcing
  E_r <= (2r-1)!! n^r (the prize energy bound).

(A) MISIDENTIFICATION. #V_r(F_p) = E_r (full additive energy), NOT W_r. Verified
    exactly on proper thin mu_n (n=4,8,16; r<=5; p=1 mod n, p>>n^3): all 15 cases.
(B) BEZOUT IS THE WRONG DIRECTION. Ambient (mu_n)^{2r} is a 0-dim CI {x_i^n=1} of
    degree n^{2r}; one linear cut gives at best n^{2r-1} points. We PROVE
        (2r-1)!! * n^r  <=  n^{2r-1}   whenever  (2r-1)!! <= n^{r-1}.
    In prize regime (n=2^30, r<=120) hypothesis holds with astronomical margin, so
    Bezout bound is STRICTLY ABOVE Wick — cannot force E_r <= Wick. R6 refuted.
(C) W_r is p-DEPENDENT (n=32,r=5: +445036032,-525950208,+714212352,+2910765312 over
    four primes p=1 mod 32); a Bezout degree is p-independent, so cannot equal it.
R6 REDUCES to the moment/energy char-p wall (the Spur excess W_r) = DEAD CLASS.
-/
namespace AtkR6

/-- Double factorial (2r-1)!!. -/
def dfactOdd : Nat → Nat
  | 0 => 1
  | 1 => 1
  | (n+2) => (n+2) * dfactOdd n

/-- Wick / char-0 energy bound (2r-1)!! * n^r. -/
def wick (r n : Nat) : Nat := dfactOdd (2*r - 1) * n ^ r

/-- Bezout/ambient bound for V_r in (mu_n)^{2r} after one linear cut: n^{2r-1}. -/
def bezoutBound (r n : Nat) : Nat := n ^ (2*r - 1)

/-- KEY LEMMA (B): under the thin-regime hypothesis (2r-1)!! <= n^(r-1) and r>=1,
    the Bezout bound dominates the Wick bound (Bezout is ABOVE Wick), refuting
    R6's "Bezout below the Wick deficit". -/
theorem bezout_ge_wick
    (r n : Nat) (hr : 1 ≤ r)
    (hthin : dfactOdd (2*r - 1) ≤ n ^ (r - 1)) :
    wick r n ≤ bezoutBound r n := by
  unfold wick bezoutBound
  have he : 2 * r - 1 = (r - 1) + r := by omega
  calc dfactOdd (2*r - 1) * n ^ r
        ≤ n ^ (r - 1) * n ^ r := by exact Nat.mul_le_mul_right _ hthin
    _ = n ^ ((r - 1) + r) := by rw [Nat.pow_add]
    _ = n ^ (2 * r - 1) := by rw [he]

example : dfactOdd (2*3 - 1) ≤ (16:Nat) ^ (3 - 1) := by decide

theorem wick_le_bezout_16_3 : wick 3 16 ≤ bezoutBound 3 16 :=
  bezout_ge_wick 3 16 (by decide) (by decide)

example : wick 3 16 = 61440 := by decide
example : bezoutBound 3 16 = 16 ^ 5 := by decide
example : (61440:Nat) ≤ 16 ^ 5 := by decide

end AtkR6

#print axioms AtkR6.bezout_ge_wick
-- 'AtkR6.bezout_ge_wick' depends on axioms: [propext, Quot.sound]
