module

public import Veir.Data.ModArith.Basic

namespace Veir.Data.ModArith

public section

/-! # Barrett reduction

Barrett reduction computes `x mod q` without a division by `q` at runtime: with the
precomputed *ratio* `r = ⌊2^k / q⌋`, the estimate `s = ⌊x·r / 2^k⌋` of the quotient
`⌊x / q⌋` is off by at most one, so `t = x - s·q` lands in `[x mod q, x mod q + q)` —
that is, `t` is either `x mod q` or `x mod q + q`. A single conditional subtraction
(`mod_arith.subifge`) then produces the canonical representative.

This file proves the integer-level correctness of this scheme. It corresponds to HEIR's
`mod_arith.barrett_reduce` operation, whose documented semantics is exactly
`x - ⌊x·⌊2^k/q⌋/2^k⌋·q`.
-/

/--
The quotient estimate of Barrett reduction underestimates the true quotient by at most
one: `x/q - 1 ≤ ⌊x·r/2^k⌋ ≤ x/q` for `0 ≤ x ≤ 2^k` and `r = ⌊2^k/q⌋`.

Consequently `barrett q k x = x - ⌊x·r/2^k⌋·q` is congruent to `x` modulo `q` and lies
in `[0, 2q)`.
-/
theorem barrett_core {q x r s : Int} (hq : 0 < q) {k : Nat} (hx0 : 0 ≤ x) (hxk : x ≤ 2 ^ k)
    (hr : r = 2 ^ k / q) (hs : s = x * r / 2 ^ k) :
    0 ≤ x - s * q ∧ x - s * q < 2 * q ∧ (x - s * q) % q = x % q := by
  have hK : (0 : Int) < 2 ^ k := Int.pow_pos (by omega)
  -- `q * r` is `2^k` minus the remainder, which is in `[0, q)`.
  have hqr : q * r + 2 ^ k % q = 2 ^ k := by
    rw [hr]; exact Int.ediv_add_emod (2 ^ k) q
  have hrem0 : 0 ≤ 2 ^ k % q := Int.emod_nonneg _ (by omega)
  have hremq : 2 ^ k % q < q := Int.emod_lt_of_pos _ hq
  have hr0 : 0 ≤ r := by
    rw [hr]; exact Int.ediv_nonneg (by omega) (by omega)
  -- The fundamental division facts for `s`.
  have hsle : s ≤ x * r / 2 ^ k := by simp [hs]
  have hsK : s * 2 ^ k ≤ x * r := (Int.le_ediv_iff_mul_le hK).mp hsle
  have hs0 : 0 ≤ s := by
    rw [hs]; exact Int.ediv_nonneg (Int.mul_nonneg hx0 hr0) (by omega)
  have hrq : r * q ≤ 2 ^ k := by
    have := Int.mul_comm q r
    omega
  -- Upper bound: `s * q ≤ x`, so the result is nonnegative.
  have hsq : s * q ≤ x := by
    have h1 : s * 2 ^ k * q ≤ x * r * q := Int.mul_le_mul_of_nonneg_right hsK (by omega)
    have e1 : s * 2 ^ k * q = s * q * 2 ^ k := by ac_rfl
    have e2 : x * r * q = x * (r * q) := by ac_rfl
    have h2 : x * (r * q) ≤ x * 2 ^ k := Int.mul_le_mul_of_nonneg_left hrq hx0
    have h3 : s * q * 2 ^ k ≤ x * 2 ^ k := by omega
    exact Int.le_of_mul_le_mul_right h3 hK
  -- Division facts for `x / q`.
  have hdivq : q * (x / q) + x % q = x := Int.ediv_add_emod x q
  have hxmod0 : 0 ≤ x % q := Int.emod_nonneg _ (by omega)
  have hxmodq : x % q < q := Int.emod_lt_of_pos _ hq
  -- Lower bound: `x/q - 1 ≤ s`, so the result is `< 2q`.
  have hsLow : x / q - 1 ≤ s := by
    rw [hs, Int.le_ediv_iff_mul_le hK]
    -- key estimate, multiplied by `q`: `(x/q)·2^k·q ≤ x·r·q + 2^k·q`
    have hA : x / q * 2 ^ k * q ≤ x * 2 ^ k := by
      have ha1 : q * (x / q) ≤ x := by omega
      have ha2 : q * (x / q) * 2 ^ k ≤ x * 2 ^ k :=
        Int.mul_le_mul_of_nonneg_right ha1 (by omega)
      have ea : q * (x / q) * 2 ^ k = x / q * 2 ^ k * q := by ac_rfl
      omega
    have hB : x * 2 ^ k ≤ x * r * q + x * q := by
      have hb1 : x * (2 ^ k % q) ≤ x * q :=
        Int.mul_le_mul_of_nonneg_left (by omega) hx0
      have eb1 : x * (r * q + 2 ^ k % q) = x * (r * q) + x * (2 ^ k % q) :=
        Int.mul_add x (r * q) (2 ^ k % q)
      have eb2 : r * q + 2 ^ k % q = 2 ^ k := by
        have := Int.mul_comm q r
        omega
      have eb3 : x * (r * q) = x * r * q := by ac_rfl
      rw [eb2] at eb1
      omega
    have hC : x * q ≤ 2 ^ k * q := Int.mul_le_mul_of_nonneg_right hxk (by omega)
    have h1 : x / q * 2 ^ k * q ≤ x * r * q + 2 ^ k * q := by omega
    have e1 : (x / q - 1) * 2 ^ k = x / q * 2 ^ k - 1 * 2 ^ k :=
      Int.sub_mul (x / q) 1 (2 ^ k)
    have e2 : (x / q * 2 ^ k - 1 * 2 ^ k) * q = x / q * 2 ^ k * q - 1 * 2 ^ k * q :=
      Int.sub_mul (x / q * 2 ^ k) (1 * 2 ^ k) q
    have e3 : (1 : Int) * 2 ^ k * q = 2 ^ k * q := by
      rw [Int.one_mul]
    have h2 : (x / q - 1) * 2 ^ k * q ≤ x * r * q := by
      rw [e1, e2, e3]
      omega
    exact Int.le_of_mul_le_mul_right h2 hq
  refine ⟨by omega, ?_, by simp⟩
  -- `t = x - s*q ≤ x%q + q < 2q` using `s ≥ x/q - 1`.
  have h9 : (x / q - 1) * q ≤ s * q := Int.mul_le_mul_of_nonneg_right hsLow (by omega)
  have h10 : (x / q - 1) * q = x / q * q - 1 * q := Int.sub_mul (x / q) 1 q
  have h11 : x / q * q = q * (x / q) := by ac_rfl
  have h12 : (1 : Int) * q = q := Int.one_mul q
  omega

/--
The conditional subtraction (`mod_arith.subifge`) canonicalizes the Barrett result:
any `t ∈ [0, 2q)` congruent to `x` modulo `q` reduces to `x mod q`.
-/
theorem subifge_eq_mod {q t x : Int} (hq : 0 < q) (h0 : 0 ≤ t) (h2 : t < 2 * q)
    (hmod : t % q = x % q) :
    (if q ≤ t then t - q else t) = x % q := by
  split
  case isTrue h =>
    have h3 : (t - q) % q = t % q := Int.sub_emod_right t q
    have h4 : (t - q) % q = t - q := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  case isFalse h =>
    have h4 : t % q = t := Int.emod_eq_of_lt h0 (by omega)
    omega

end

end Veir.Data.ModArith
