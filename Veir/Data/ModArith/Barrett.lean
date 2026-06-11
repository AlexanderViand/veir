module

public import Veir.Data.ModArith.Basic
public import Veir.Data.ModArith.Lemmas

import all Veir.Data.ModArith.Basic

namespace Veir.Data.ModArith

public section

open Veir.Data.LLVM

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

/-! ## The Barrett multiplication pipeline at the bitvector level

The planned Barrett-based lowering of `mod_arith.mul` for `!mod_arith.int<q : iN>`
computes, at a uniform intermediate width `W = 4N` with `k = 2N`:

  p  = zext(x) * zext(y)               -- exact: p < q² < 2^(2N-2)
  pr = p * r                           -- r = ⌊2^(2N)/q⌋ ≤ 2^(2N), so pr < 2^(4N-2)
  s  = pr >>> 2N                       -- the Barrett quotient estimate
  t  = p - s * q                       -- ∈ [0, 2q) by `barrett_core`
  u  = if q ≤ t then t - q else t      -- subifge: cmpi uge + subi + select
  result = truncate N u                -- canonical product

The lemmas below bridge `barrett_core`
to this bitvector pipeline, in the same style as `Veir.Data.ModArith.Lemmas`.
-/

/-- The condition `arith.select` tests, `BitVec.ofBool b == 1#1`, is just `b`. -/
@[simp]
theorem ofBool_beq_one (b : Bool) : (BitVec.ofBool b == 1#1) = b := by
  cases b <;> rfl

variable {n : Nat} {q : Int}

/-! ## The add / sub conditional-subtraction pipelines (no widening) -/

/--
The `add`-conditional-subtraction pipeline (Barrett `add` lowering, computed at the
storage width `n` with no widening) computes the reference semantics of `mod_arith.add`.
The sum `x + y` of canonical operands lies in `[0, 2q) ⊆ [0, 2^n)`, so it does not wrap,
and one conditional subtraction canonicalizes it.
-/
theorem addSubifge_eq_add (hq : 0 < q) (hqn : 2 * q ≤ 2 ^ n)
    {x y : BitVec n} (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (if (BitVec.ofBool ((BitVec.ofInt n q).ule (x + y)) == 1#1)
      then (x + y - BitVec.ofInt n q) else (x + y)) = add q x y := by
  have hcastn : (2:Int)^n = ((2^n : Nat) : Int) := by push_cast; rfl
  have hxq : x.toNat < q.toNat := by omega
  have hyq : y.toNat < q.toNat := by omega
  have hqtoNat : (BitVec.ofInt n q).toNat = q.toNat :=
    toNat_ofInt_modulus (by omega) (by omega)
  have hqInt : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
  have hsumlt : x.toNat + y.toNat < 2 ^ n := by omega
  have hsum : (x + y).toNat = x.toNat + y.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsumlt]
  rw [show (BitVec.ofBool ((BitVec.ofInt n q).ule (x + y)) == 1#1)
    = ((BitVec.ofInt n q).ule (x + y)) from by cases ((BitVec.ofInt n q).ule (x + y)) <;> rfl]
  apply BitVec.eq_of_toNat_eq
  rw [Data.ModArith.add, BitVec.toNat_ofNat]
  have hmodnn : (0:Int) ≤ ((x.toNat : Int) + y.toNat) % q := Int.emod_nonneg _ (by omega)
  have hmodlt : ((x.toNat : Int) + y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hrhsLt : (((x.toNat : Int) + y.toNat) % q).toNat < 2 ^ n := by omega
  rw [Nat.mod_eq_of_lt hrhsLt]
  by_cases hcond : (BitVec.ofInt n q).ule (x + y) = true
  · rw [if_pos hcond]
    rw [BitVec.ule] at hcond
    simp only [decide_eq_true_eq] at hcond
    rw [hqtoNat, hsum] at hcond
    have hsub : (x + y - BitVec.ofInt n q).toNat = (x.toNat + y.toNat) - q.toNat := by
      rw [BitVec.toNat_sub, hqtoNat, hsum]
      have h2 : 2^n - q.toNat + (x.toNat + y.toNat) = 2^n + ((x.toNat + y.toNat) - q.toNat) := by
        omega
      rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    have key : ((x.toNat : Int) + y.toNat - q) % q = (x.toNat : Int) + y.toNat - q :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have shift : ((x.toNat : Int) + y.toNat) % q = ((x.toNat : Int) + y.toNat - q) % q := by
      rw [← Int.add_emod_right ((x.toNat:Int)+y.toNat-q) q]; congr 1; omega
    rw [shift, key]
    omega
  · rw [if_neg hcond]
    simp only [Bool.not_eq_true] at hcond
    rw [BitVec.ule] at hcond
    simp only [decide_eq_false_iff_not, Nat.not_le] at hcond
    rw [hqtoNat, hsum] at hcond
    rw [hsum]
    have hmod : ((x.toNat : Int) + y.toNat) % q = (x.toNat : Int) + y.toNat :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]
    omega

/--
The `sub`-conditional-subtraction pipeline (Barrett `sub` lowering, computed at the
storage width `n`) computes the reference semantics of `mod_arith.sub`. Adding `q`
before subtracting avoids unsigned underflow; `x + q - y` lies in `(0, 2q) ⊆ [0, 2^n)`.
-/
theorem subSubifge_eq_sub (hq : 0 < q) (hqn : 2 * q ≤ 2 ^ n)
    {x y : BitVec n} (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (if (BitVec.ofBool ((BitVec.ofInt n q).ule (x + BitVec.ofInt n q - y)) == 1#1)
      then (x + BitVec.ofInt n q - y - BitVec.ofInt n q)
      else (x + BitVec.ofInt n q - y)) = sub q x y := by
  have hcastn : (2:Int)^n = ((2^n : Nat) : Int) := by push_cast; rfl
  have hxq : x.toNat < q.toNat := by omega
  have hyq : y.toNat < q.toNat := by omega
  have hqtoNat : (BitVec.ofInt n q).toNat = q.toNat :=
    toNat_ofInt_modulus (by omega) (by omega)
  have hqInt : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
  have htlt : x.toNat + q.toNat - y.toNat < 2 ^ n := by omega
  have ht : (x + BitVec.ofInt n q - y).toNat = x.toNat + q.toNat - y.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, hqtoNat]
    rw [Nat.mod_eq_of_lt (show x.toNat + q.toNat < 2^n from by omega)]
    have h2 : 2^n - y.toNat + (x.toNat + q.toNat) = 2^n + (x.toNat + q.toNat - y.toNat) := by omega
    rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [show (BitVec.ofBool ((BitVec.ofInt n q).ule (x + BitVec.ofInt n q - y)) == 1#1)
    = ((BitVec.ofInt n q).ule (x + BitVec.ofInt n q - y)) from by
      cases ((BitVec.ofInt n q).ule (x + BitVec.ofInt n q - y)) <;> rfl]
  apply BitVec.eq_of_toNat_eq
  rw [Data.ModArith.sub, BitVec.toNat_ofNat]
  have hmodnn : (0:Int) ≤ ((x.toNat : Int) - y.toNat) % q := Int.emod_nonneg _ (by omega)
  have hmodlt : ((x.toNat : Int) - y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hrhsLt : (((x.toNat : Int) - y.toNat) % q).toNat < 2 ^ n := by omega
  rw [Nat.mod_eq_of_lt hrhsLt]
  have hspec : ((x.toNat : Int) - y.toNat) % q = ((x.toNat : Int) + q - y.toNat) % q := by
    rw [← Int.add_emod_right ((x.toNat:Int) - y.toNat) q]; congr 1; omega
  by_cases hcond : (BitVec.ofInt n q).ule (x + BitVec.ofInt n q - y) = true
  · rw [if_pos hcond]
    rw [BitVec.ule] at hcond
    simp only [decide_eq_true_eq] at hcond
    rw [hqtoNat, ht] at hcond
    have hsub : (x + BitVec.ofInt n q - y - BitVec.ofInt n q).toNat
        = (x.toNat + q.toNat - y.toNat) - q.toNat := by
      rw [BitVec.toNat_sub, hqtoNat, ht]
      have h2 : 2^n - q.toNat + (x.toNat + q.toNat - y.toNat)
          = 2^n + ((x.toNat + q.toNat - y.toNat) - q.toNat) := by omega
      rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hspec]
    have key : ((x.toNat : Int) + q - y.toNat - q) % q = (x.toNat:Int) + q - y.toNat - q :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have shift : ((x.toNat : Int) + q - y.toNat) % q = ((x.toNat : Int) + q - y.toNat - q) % q := by
      rw [← Int.add_emod_right ((x.toNat:Int)+q-y.toNat-q) q]; congr 1; omega
    rw [shift, key]
    omega
  · rw [if_neg hcond]
    simp only [Bool.not_eq_true] at hcond
    rw [BitVec.ule] at hcond
    simp only [decide_eq_false_iff_not, Nat.not_le] at hcond
    rw [hqtoNat, ht] at hcond
    rw [ht, hspec]
    have hmod2 : ((x.toNat : Int) + q - y.toNat) % q = (x.toNat : Int) + q - y.toNat :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod2]
    omega

/-! ## The Barrett multiplication pipeline (width `W = 4N`)

The Barrett `mul` lowering, computed at width `W = 4n` with shift `k = 2n` and ratio
`r = ⌊2^(2n)/q⌋`, computes the reference semantics of `mod_arith.mul`. The estimate
`s = ⌊p·r / 2^(2n)⌋` underestimates the true quotient `⌊p/q⌋` by at most one
(`barrett_core`), so `t = p - s·q ∈ [0, 2q)` and a single conditional subtraction
canonicalizes the product; truncating to `n` bits is then exact.
-/

set_option maxHeartbeats 4000000 in
/-- The Barrett `mul` lowering pipeline computes the reference semantics of `mod_arith.mul`. -/
theorem mulBarrettPipeline_eq_mul (hq : 0 < q) (hqw : q < 2 ^ (n - 1)) (hn : 1 ≤ n)
    {x y : BitVec n} (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (if (BitVec.ofInt (4*n) q).ule
          (x.zeroExtend (4*n) * y.zeroExtend (4*n)
            - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
                >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q)
      then (x.zeroExtend (4*n) * y.zeroExtend (4*n)
            - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
                >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q
            - BitVec.ofInt (4*n) q)
      else (x.zeroExtend (4*n) * y.zeroExtend (4*n)
            - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
                >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q)).truncate n
      = mul q x y := by
  have hP : ∀ m : Nat, (2:Int)^m = ((2^m:Nat):Int) := fun m => by push_cast; rfl
  -- An Int in `[0, 2^(4n))` has its `toNat` below `2^(4n)` (as a `Nat`).
  have hcvt : ∀ z : Int, 0 ≤ z → z < 2^(4*n) → z.toNat < 2^(4*n) := by
    intro z hz0 hzlt
    rw [Int.toNat_lt hz0]
    rw [hP (4*n)] at hzlt
    exact_mod_cast hzlt
  have hxn : x.toNat < 2^n := x.isLt
  have hyn : y.toNat < 2^n := y.isLt
  have hn4 : (2:Nat)^n ≤ 2^(4*n) := Nat.pow_le_pow_right (by omega) (by omega)
  -- power inequalities at the Int level.
  have hpow_2n_4n : (2:Int)^(2*n) ≤ 2^(4*n) := by
    rw [hP (2*n), hP (4*n)]; exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_2nm2_2n : (2:Int)^(2*n-2) ≤ 2^(2*n) := by
    rw [hP (2*n-2), hP (2*n)]; exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  have h2nm2_4 : (2:Int)^(2*n-2) * 4 = 2^(2*n) := by
    have hnat : (2:Nat)^(2*n-2) * 4 = 2^(2*n) := by
      rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_add]; congr 1; omega
    rw [hP (2*n-2), hP (2*n)]; exact_mod_cast hnat
  -- `q * q ≤ 2^(2n-2)`.
  have hqq : q * q ≤ 2^(2*n-2) := by
    have hpp : (0:Int) < 2^(n-1) := Int.pow_pos (by omega)
    have hqle : q ≤ 2 ^ (n-1) := by omega
    have hpow : (2:Int)^(n-1) * 2^(n-1) = 2^(2*n-2) := by
      have hnat : (2:Nat)^(n-1)*2^(n-1) = 2^(2*n-2) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hP (n-1), hP (2*n-2)]; exact_mod_cast hnat
    have ha : q * q ≤ 2^(n-1) * q := Int.mul_le_mul_of_nonneg_right hqle (by omega)
    have hb : 2^(n-1) * q ≤ 2^(n-1) * 2^(n-1) := Int.mul_le_mul_of_nonneg_left hqle (by omega)
    calc q*q ≤ 2^(n-1)*q := ha
      _ ≤ 2^(n-1)*2^(n-1) := hb
      _ = 2^(2*n-2) := hpow
  -- `p = zext x * zext y`, exact at width `4n`.
  have hpnat : x.toNat * y.toNat < 2^(4*n) := by
    have h1 : x.toNat * y.toNat < 2^n * 2^n := Nat.mul_lt_mul'' hxn hyn
    have h2 : (2:Nat)^n * 2^n = 2^(2*n) := by rw [← Nat.pow_add]; congr 1; omega
    have h3 : (2:Nat)^(2*n) ≤ 2^(4*n) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hp : (x.zeroExtend (4*n) * y.zeroExtend (4*n)).toNat = x.toNat * y.toNat := by
    rw [BitVec.toNat_mul]
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
      Nat.mod_eq_of_lt hpnat]
  -- `p_int := (x.toNat * y.toNat : Int)` satisfies `0 ≤ p_int < q² ≤ 2^(2n-2) ≤ 2^(2n)`.
  have hpInt0 : (0:Int) ≤ (x.toNat : Int) * y.toNat := Int.mul_nonneg (by omega) (by omega)
  have hpInt_lt_qq : (x.toNat : Int) * y.toNat < q * q := by
    have hqI : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
    have hprodN : x.toNat * y.toNat < q.toNat * q.toNat := Nat.mul_lt_mul'' (by omega) (by omega)
    have hc : ((x.toNat * y.toNat : Nat) : Int) < ((q.toNat * q.toNat : Nat) : Int) := by
      exact_mod_cast hprodN
    push_cast [hqI] at hc; omega
  have hpInt_le2 : (x.toNat : Int) * y.toNat ≤ 2^(2*n-2) := by omega
  have hpInt_le : (x.toNat : Int) * y.toNat ≤ 2^(2*n) := by omega
  -- ratio facts.
  have hratio0 : (0:Int) ≤ 2^(2*n)/q := Int.ediv_nonneg (by omega) (by omega)
  have hratio_le : (2:Int)^(2*n)/q ≤ 2^(2*n) := by
    have hpos : (0:Int) ≤ 2^(2*n) := by have h : (0:Int) < 2^(2*n) := Int.pow_pos (by omega); omega
    exact Int.ediv_le_self _ hpos
  -- `2^(2n) < 2^(4n)` (strict), used for several `ofInt` exactness bounds.
  have hpow_2n_4n_lt : (2:Int)^(2*n) < 2^(4*n) := by
    rw [hP (2*n), hP (4*n)]
    exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
  -- `rBV = ofInt (4n) ratio`, exact.
  have hrtoNat : (BitVec.ofInt (4*n) (2^(2*n)/q)).toNat = (2^(2*n)/q).toNat :=
    toNat_ofInt_modulus hratio0 (by omega)
  -- The barrett quotient estimate `s_int`.
  -- bring barrett_core into scope with `k = 2n`, `x := x.toNat*y.toNat`.
  obtain ⟨hbc0, hbc1, hbc2⟩ := barrett_core (q := q) (x := (x.toNat : Int) * y.toNat)
    (r := 2^(2*n)/q) (s := (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)) hq (k := 2*n)
    hpInt0 hpInt_le rfl rfl
  -- `s_int := x_int * ratio / 2^(2n)`; nonneg.
  have hs0 : (0:Int) ≤ (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) :=
    Int.ediv_nonneg (Int.mul_nonneg hpInt0 hratio0) (by have h : (0:Int) < 2^(2*n) := Int.pow_pos (by omega); omega)
  -- `s_int * q ≤ p_int` from `0 ≤ p_int - s_int * q`.
  have hsq_le_p : (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q ≤ (x.toNat : Int) * y.toNat := by
    omega
  -- `pr = p * rBV`, exact at width `4n`:  `p_int * ratio ≤ 2^(2n-2) * 2^(2n) = 2^(4n-2) < 2^(4n)`.
  have hprInt_lt : x.toNat * (2^(2*n)/q).toNat * y.toNat < 2^(4*n) := by
    -- bound `p.toNat * ratio.toNat` in Nat via the Int bound.
    have hpr_le : (x.toNat : Int) * y.toNat * (2^(2*n)/q) ≤ 2^(2*n-2) * 2^(2*n) := by
      have ha : (x.toNat : Int) * y.toNat * (2^(2*n)/q) ≤ 2^(2*n-2) * (2^(2*n)/q) :=
        Int.mul_le_mul_of_nonneg_right (by omega) hratio0
      have hb : (2:Int)^(2*n-2) * (2^(2*n)/q) ≤ 2^(2*n-2) * 2^(2*n) :=
        Int.mul_le_mul_of_nonneg_left hratio_le (by have h : (0:Int) < 2^(2*n-2) := Int.pow_pos (by omega); omega)
      omega
    have hpow42 : (2:Int)^(2*n-2) * 2^(2*n) < 2^(4*n) := by
      have hnat : (2:Nat)^(2*n-2) * 2^(2*n) = 2^(4*n-2) := by rw [← Nat.pow_add]; congr 1; omega
      have hlt : (2:Nat)^(4*n-2) < 2^(4*n) := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [hP (2*n-2), hP (2*n), hP (4*n)]
      have : ((2^(2*n-2):Nat):Int) * ((2^(2*n):Nat):Int) = ((2^(4*n-2):Nat):Int) := by
        exact_mod_cast hnat
      rw [this]; exact_mod_cast hlt
    -- transfer to Nat: x.toNat * ratio.toNat * y.toNat = (p_int * ratio).toNat
    have hkey : ((x.toNat : Int) * y.toNat * (2^(2*n)/q)) < 2^(4*n) := by omega
    have hcast : ((x.toNat * (2^(2*n)/q).toNat * y.toNat : Nat) : Int)
        = (x.toNat : Int) * y.toNat * (2^(2*n)/q) := by
      have hrr : ((2^(2*n)/q).toNat : Int) = 2^(2*n)/q := Int.toNat_of_nonneg hratio0
      push_cast [hrr]; ac_rfl
    have hfin : ((x.toNat * (2^(2*n)/q).toNat * y.toNat : Nat) : Int) < ((2^(4*n) : Nat) : Int) := by
      rw [hcast, ← hP (4*n)]; omega
    exact_mod_cast hfin
  have hpr : ((x.zeroExtend (4*n) * y.zeroExtend (4*n)) * BitVec.ofInt (4*n) (2^(2*n)/q)).toNat
      = x.toNat * y.toNat * (2^(2*n)/q).toNat := by
    rw [BitVec.toNat_mul, hp, hrtoNat, Nat.mod_eq_of_lt (by
      have hreorder : x.toNat * y.toNat * (2^(2*n)/q).toNat = x.toNat * (2^(2*n)/q).toNat * y.toNat := by
        ac_rfl
      omega)]
  -- `s = pr >>> ofInt (2n)`. shift amount exact = `2n`.
  have hshtoNat : (BitVec.ofInt (4*n) (2*n : Int)).toNat = 2*n := by
    have h1 : (2:Nat) * n < 2 ^ (2 * n) := Nat.lt_two_pow_self
    have hlt2n4n : (2:Nat)^(2*n) ≤ 2^(4*n) := Nat.pow_le_pow_right (by omega) (by omega)
    have hlt : (2*(n:Int)) < 2 ^ (4*n) := by
      have hh : ((2*n:Nat):Int) < ((2^(4*n):Nat):Int) := by exact_mod_cast (by omega : 2*n < 2^(4*n))
      push_cast at hh; exact_mod_cast hh
    have hkey := toNat_ofInt_modulus (m := 4*n) (q := (2*(n:Int))) (by omega) hlt
    rw [hkey]; omega
  have hs : (((x.zeroExtend (4*n) * y.zeroExtend (4*n)) * BitVec.ofInt (4*n) (2^(2*n)/q))
        >>> BitVec.ofInt (4*n) (2*n : Int)).toNat
      = (x.toNat * y.toNat * (2^(2*n)/q).toNat) / 2^(2*n) := by
    rw [show (x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
            >>> BitVec.ofInt (4*n) (2*n : Int)
          = (x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
            >>> (BitVec.ofInt (4*n) (2*n : Int)).toNat from BitVec.ushiftRight_eq _ _,
      BitVec.toNat_ushiftRight, hpr, hshtoNat, Nat.shiftRight_eq_div_pow]
  -- `s.toNat = s_int.toNat` (the Int barrett estimate).
  have hsInt : ((x.toNat * y.toNat * (2^(2*n)/q).toNat) / 2^(2*n) : Nat)
      = ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat := by
    have hrr : ((2^(2*n)/q).toNat : Int) = 2^(2*n)/q := Int.toNat_of_nonneg hratio0
    have hnum : ((x.toNat * y.toNat * (2^(2*n)/q).toNat : Nat) : Int)
        = (x.toNat : Int) * y.toNat * (2^(2*n)/q) := by push_cast [hrr]; ac_rfl
    have hstep : (((x.toNat * y.toNat * (2^(2*n)/q).toNat) / 2^(2*n) : Nat) : Int)
        = (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) := by
      rw [show (((x.toNat * y.toNat * (2^(2*n)/q).toNat) / 2^(2*n) : Nat) : Int)
          = ((x.toNat * y.toNat * (2^(2*n)/q).toNat : Nat) : Int) / ((2^(2*n) : Nat) : Int) from by
        push_cast; rfl, hnum, hP (2*n)]
    rw [← hstep]; exact (Int.toNat_natCast _).symm
  -- `s.toNat` as a Nat, named for brevity.
  have hsN_eq : (((x.zeroExtend (4*n) * y.zeroExtend (4*n)) * BitVec.ofInt (4*n) (2^(2*n)/q))
        >>> BitVec.ofInt (4*n) (2*n : Int)).toNat
      = ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat := by
    rw [hs, hsInt]
  -- `qBV` exact.
  have hq_lt_4n : q < 2^(4*n) := by
    have hle : (2:Nat)^(n-1) ≤ 2^(4*n) := Nat.pow_le_pow_right (by omega) (by omega)
    have hc1 : (2:Int)^(n-1) = ((2^(n-1):Nat):Int) := hP (n-1)
    have hc2 : (2:Int)^(4*n) = ((2^(4*n):Nat):Int) := hP (4*n)
    rw [hc1] at hqw
    have : ((2^(n-1):Nat):Int) ≤ ((2^(4*n):Nat):Int) := by exact_mod_cast hle
    rw [hc2]; omega
  have hqtoNat : (BitVec.ofInt (4*n) q).toNat = q.toNat :=
    toNat_ofInt_modulus (by omega) hq_lt_4n
  -- `sq = s * qBV`, exact (since `s_int * q ≤ p_int ≤ 2^(2n) < 2^(4n)`).
  have hsqlt : (((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat) * q.toNat < 2^(4*n) := by
    have hsqI : ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat
        = (((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)) * q).toNat := by
      rw [← Int.toNat_mul hs0 (by omega)]
    have hbnd : (((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)) * q) < 2^(4*n) := by
      have hpos : (0:Int) < 2^(2*n) := Int.pow_pos (by omega)
      omega
    rw [hsqI]
    exact hcvt _ (Int.mul_nonneg hs0 (by omega)) hbnd
  have hsq : (((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
        >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q).toNat
      = ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat := by
    rw [BitVec.toNat_mul, hsN_eq, hqtoNat, Nat.mod_eq_of_lt hsqlt]
  -- `t = p - sq`, exact since `s_int * q ≤ p_int`.
  have hsq_le_pN : ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat
      ≤ x.toNat * y.toNat := by
    have hsqI : ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat
        = (((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)) * q).toNat := by
      rw [← Int.toNat_mul hs0 (by omega)]
    have hpI : (x.toNat * y.toNat : Nat) = ((x.toNat : Int) * y.toNat).toNat := by
      rw [Int.toNat_mul (by omega) (by omega)]; simp
    rw [hsqI, hpI]
    apply Int.toNat_le_toNat hsq_le_p
  have ht : (x.zeroExtend (4*n) * y.zeroExtend (4*n)
        - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
            >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q).toNat
      = x.toNat * y.toNat - ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat := by
    rw [BitVec.toNat_sub, hsq, hp]
    have hpltW : x.toNat * y.toNat < 2^(4*n) := hpnat
    have e : 2^(4*n) - ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat
          + x.toNat * y.toNat
        = 2^(4*n) + (x.toNat * y.toNat
          - ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat) := by omega
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- The Int barrett value `tInt = p_int - s_int * q`, with `t.toNat = tInt.toNat`.
  have htN : (x.zeroExtend (4*n) * y.zeroExtend (4*n)
        - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
            >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q).toNat
      = ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat := by
    rw [ht]
    have hsqI : (((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)) * q).toNat
        = ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat := by
      rw [Int.toNat_mul hs0 (by omega)]
    have hpI : ((x.toNat : Int) * y.toNat).toNat = x.toNat * y.toNat := by
      rw [Int.toNat_mul (by omega) (by omega)]; simp
    have hdiff : ((x.toNat : Int) * y.toNat
          - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
        = (x.toNat * y.toNat) - ((x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n)).toNat * q.toNat := by
      have hsqnn : (0:Int) ≤ (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q :=
        Int.mul_nonneg hs0 (by omega)
      omega
    rw [hdiff]
  -- ## The final conditional subtraction and truncation.
  have hQle : q ≤ 2^n := by
    have hle : (2:Nat)^(n-1) ≤ 2^n := Nat.pow_le_pow_right (by omega) (by omega)
    have hc : (2:Int)^(n-1) = ((2^(n-1):Nat):Int) := hP (n-1)
    have hc2 : (2:Int)^n = ((2^n:Nat):Int) := hP n
    rw [hc] at hqw; rw [hc2]
    have : ((2^(n-1):Nat):Int) ≤ ((2^n:Nat):Int) := by exact_mod_cast hle
    omega
  -- bound `tInt < 2q ≤ 2^(2n) ≤ 2^(4n)` so `tInt.toNat < 2^(4n)`.
  have h2qle : 2 * q ≤ 2^(2*n) := by
    have hle : (2:Nat)^(n-1) ≤ 2^(2*n-1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hsplit : (2:Nat)^(2*n-1) * 2 = 2^(2*n) := by rw [← Nat.pow_succ]; congr 1; omega
    have hc1 : (2:Int)^(n-1) = ((2^(n-1):Nat):Int) := hP (n-1)
    have hc3 : (2:Int)^(2*n) = ((2^(2*n):Nat):Int) := hP (2*n)
    rw [hc1] at hqw; rw [hc3]
    have hcast1 : ((2^(n-1):Nat):Int) ≤ ((2^(2*n-1):Nat):Int) := by exact_mod_cast hle
    have hcast2 : ((2^(2*n-1):Nat):Int) * 2 = ((2^(2*n):Nat):Int) := by exact_mod_cast hsplit
    omega
  have htW : ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q)
      < 2^(4*n) := by omega
  apply BitVec.eq_of_toNat_eq
  rw [mul, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hmodnn : (0:Int) ≤ ((x.toNat : Int) * y.toNat) % q := Int.emod_nonneg _ (by omega)
  have hmodlt : ((x.toNat : Int) * y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hQleN : (2:Int)^n = ((2^n:Nat):Int) := hP n
  have hrhsLt : (((x.toNat : Int) * y.toNat) % q).toNat < 2 ^ n := by
    rw [hQleN] at hQle; omega
  rw [Nat.mod_eq_of_lt hrhsLt]
  -- `subifge_eq_mod` gives `(if q ≤ tInt then tInt - q else tInt) = (x*y) % q`.
  have hsubeq : (if q ≤ (x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q
      then ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q) - q
      else ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q))
      = (x.toNat : Int) * y.toNat % q :=
    subifge_eq_mod hq hbc0 hbc1 hbc2
  have hqInt : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
  by_cases hcond : (BitVec.ofInt (4*n) q).ule
      (x.zeroExtend (4*n) * y.zeroExtend (4*n)
        - ((x.zeroExtend (4*n) * y.zeroExtend (4*n) * BitVec.ofInt (4*n) (2^(2*n)/q))
            >>> BitVec.ofInt (4*n) (2*n : Int)) * BitVec.ofInt (4*n) q) = true
  · rw [if_pos hcond, BitVec.toNat_sub, htN, hqtoNat]
    rw [BitVec.ule] at hcond
    simp only [decide_eq_true_eq, htN, hqtoNat] at hcond
    -- `hcond : q.toNat ≤ tInt.toNat`, so `q ≤ tInt`.
    have e1 : (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat : Int)
        = (x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q :=
      Int.toNat_of_nonneg hbc0
    have e2 : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
    have hqle_t : q ≤ (x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q := by
      omega
    rw [if_pos hqle_t] at hsubeq
    have htWlt : ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
        < 2^(4*n) := hcvt _ hbc0 htW
    -- `tInt.toNat - q.toNat = ((x*y) % q).toNat`, the canonical value.
    have hval : ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
          - q.toNat = ((x.toNat : Int) * y.toNat % q).toNat := by
      have hcastInt : (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
            - q.toNat : Nat)
          = (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q) - q).toNat := by
        omega
      rw [hcastInt, hsubeq]
    -- the outer `% 2^(4n)` then `% 2^n` both vanish.
    have hmod4n : (2^(4*n) - q.toNat
          + ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat) % 2^(4*n)
        = ((x.toNat : Int) * y.toNat % q).toNat := by
      have e : 2^(4*n) - q.toNat
            + ((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
          = 2^(4*n)
            + (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat
                - q.toNat) := by omega
      have hrhs4n : ((x.toNat : Int) * y.toNat % q).toNat < 2^(4*n) := by
        have hle : (2:Nat)^n ≤ 2^(4*n) := hn4
        omega
      rw [e, Nat.add_mod_left, hval, Nat.mod_eq_of_lt hrhs4n]
    rw [hmod4n, Nat.mod_eq_of_lt hrhsLt]
  · rw [if_neg hcond, htN]
    rw [BitVec.ule, htN, hqtoNat] at hcond
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le, Bool.not_eq_true] at hcond
    -- `hcond : tInt.toNat < q.toNat`, so `tInt < q`.
    have e1 : (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat : Int)
        = (x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q :=
      Int.toNat_of_nonneg hbc0
    have e2 : (q.toNat : Int) = q := Int.toNat_of_nonneg (by omega)
    have hlt_q : (x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q < q := by
      omega
    rw [if_neg (by omega)] at hsubeq
    have hcast : (((x.toNat : Int) * y.toNat - (x.toNat : Int) * y.toNat * (2^(2*n)/q) / 2^(2*n) * q).toNat)
        = (((x.toNat : Int) * y.toNat % q).toNat) := by rw [hsubeq]
    rw [hcast, Nat.mod_eq_of_lt hrhsLt]

end

end Veir.Data.ModArith
