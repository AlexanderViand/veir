module

public import Veir.Data.ModArith.Basic

import all Veir.Data.ModArith.Basic

namespace Veir.Data.ModArith

public section

/-! # Correctness of the trivial mod_arith lowering pipeline

The trivial mod-arith-to-arith lowering computes `x ⊙ y (mod q)` for canonical
representatives `x, y : BitVec n` by zero-extending to a wider width `m` (so that the
intermediate result cannot wrap), computing `⊙` followed by an unsigned remainder there,
and truncating the (canonical, hence in-range) result back to `n` bits.

This file proves that pipeline equal to the reference semantics `Veir.Data.ModArith.add`
/ `sub` / `mul`, along with the side conditions needed to interpret the lowered program:
the materialized modulus is nonzero (so `arith.remui` is defined) and the final
`arith.trunci` with `nuw` does not produce poison.

The hypotheses mirror the `mod_arith` invariants: `0 < q` and `q < 2^(n-1)` come from
the type verifier (`TypeAttr.verifyModArithType`), canonicity of the operands comes from
the runtime value invariant (`RuntimeValue.Conforms`).
-/

variable {n m : Nat} {q : Int}

/-- The modulus constant materialized at width `m` is exact. -/
theorem toNat_ofInt_modulus (hq : 0 ≤ q) (hqm : q < 2 ^ m) :
    (BitVec.ofInt m q).toNat = q.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hq (by exact_mod_cast hqm)]

/-- The modulus constant materialized at width `m` is nonzero, so `remui` is defined. -/
theorem ofInt_modulus_ne_zero (hq : 0 < q) (hqm : q < 2 ^ m) :
    BitVec.ofInt m q ≠ 0#m := by
  intro h
  have htoNat := congrArg BitVec.toNat h
  rw [toNat_ofInt_modulus (by omega) hqm] at htoNat
  simp at htoNat
  omega

/--
Truncating a value that fits in `n` bits and zero-extending it back is the identity;
this is the no-poison condition of the final `arith.trunci` with `nuw`.
-/
theorem zeroExtend_truncate_eq_self {v : BitVec m} (hv : v.toNat < 2 ^ n) :
    (v.truncate n).zeroExtend m = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt v.isLt]

/-! ## `mod_arith.add` -/

/--
The unsigned remainder computed by the `add` lowering pipeline at width `m` is exactly
`(x + y) % q`, provided the sum cannot wrap at width `m`.
-/
theorem toNat_addPipeline (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m + y.zeroExtend m) % BitVec.ofInt m q).toNat
      = (x.toNat + y.toNat) % q.toNat := by
  have hqm' : (2 ^ m : Int) = ((2 ^ m : Nat) : Int) := by push_cast; rfl
  have hxq : x.toNat < q.toNat := by omega
  have hyq : y.toNat < q.toNat := by omega
  have hsum : x.toNat + y.toNat < 2 ^ m := by omega
  rw [BitVec.toNat_umod, BitVec.toNat_add,
    toNat_ofInt_modulus (by omega) (by omega)]
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt hsum]

/-- The `add` pipeline produces a canonical value: its result is `< q`. -/
theorem toNat_addPipeline_lt (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (((x.zeroExtend m + y.zeroExtend m) % BitVec.ofInt m q).toNat : Int) < q := by
  rw [toNat_addPipeline hq hqm hnm hx hy]
  have := Nat.mod_lt (x.toNat + y.toNat) (y := q.toNat) (by omega)
  omega

/-- The `add` lowering pipeline computes the reference semantics of `mod_arith.add`. -/
theorem addPipeline_eq_add (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m + y.zeroExtend m) % BitVec.ofInt m q).truncate n = add q x y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, add, BitVec.toNat_ofNat]
  rw [toNat_addPipeline hq hqm hnm hx hy]
  rw [Int.toNat_emod (by omega) (by omega)]
  norm_cast

/-! ## `mod_arith.sub` -/

/--
The unsigned remainder computed by the `sub` lowering pipeline at width `m` is exactly
`(x + q - y) % q`: adding `q` before subtracting avoids unsigned underflow.
-/
theorem toNat_subPipeline (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m + BitVec.ofInt m q - y.zeroExtend m) % BitVec.ofInt m q).toNat
      = (x.toNat + q.toNat - y.toNat) % q.toNat := by
  have hqm' : (2 ^ m : Int) = ((2 ^ m : Nat) : Int) := by push_cast; rfl
  have hxq : x.toNat < q.toNat := by omega
  have hyq : y.toNat < q.toNat := by omega
  have hs : x.toNat + q.toNat < 2 ^ m := by omega
  rw [BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_add,
    toNat_ofInt_modulus (by omega) (by omega)]
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt hs]
  have heq : 2 ^ m - y.toNat + (x.toNat + q.toNat)
      = 2 ^ m + (x.toNat + q.toNat - y.toNat) := by omega
  rw [heq, Nat.add_mod_left,
    Nat.mod_eq_of_lt (a := x.toNat + q.toNat - y.toNat) (b := 2 ^ m) (by omega)]

/-- The `sub` pipeline produces a canonical value: its result is `< q`. -/
theorem toNat_subPipeline_lt (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (((x.zeroExtend m + BitVec.ofInt m q - y.zeroExtend m) % BitVec.ofInt m q).toNat : Int)
      < q := by
  rw [toNat_subPipeline hq hqm hnm hx hy]
  have := Nat.mod_lt (x.toNat + q.toNat - y.toNat) (y := q.toNat) (by omega)
  omega

/-- The `sub` lowering pipeline computes the reference semantics of `mod_arith.sub`. -/
theorem subPipeline_eq_sub (hq : 0 < q) (hqm : 2 * q ≤ 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m + BitVec.ofInt m q - y.zeroExtend m) % BitVec.ofInt m q).truncate n
      = sub q x y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, sub, BitVec.toNat_ofNat]
  rw [toNat_subPipeline hq hqm hnm hx hy]
  -- align the Int-level specification with the Nat-level pipeline result:
  -- `(x - y) % q = (x + q - y) % q` and the latter is nonnegative.
  have hyq : y.toNat ≤ x.toNat + q.toNat := by omega
  have hspec : ((x.toNat : Int) - y.toNat) % q
      = (((x.toNat + q.toNat - y.toNat : Nat) : Int)) % q := by
    have : ((x.toNat + q.toNat - y.toNat : Nat) : Int)
        = (x.toNat : Int) - y.toNat + q := by
      push_cast [hyq]
      have : ((q.toNat : Int)) = q := Int.toNat_of_nonneg (by omega)
      omega
    rw [this, Int.add_emod_right]
  rw [hspec, Int.toNat_emod (by omega) (by omega)]
  norm_cast

/-! ## `mod_arith.mul` -/

/--
The unsigned remainder computed by the `mul` lowering pipeline at width `m` is exactly
`(x * y) % q`, provided the product cannot wrap at width `m`.
-/
theorem toNat_mulPipeline (hq : 0 < q) (hqm : q * q ≤ 2 ^ m) (hqm2 : q < 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m * y.zeroExtend m) % BitVec.ofInt m q).toNat
      = (x.toNat * y.toNat) % q.toNat := by
  have hqm' : (2 ^ m : Int) = ((2 ^ m : Nat) : Int) := by push_cast; rfl
  have hqqpos : (0 : Int) ≤ q * q := Int.mul_nonneg (by omega) (by omega)
  have hqq : (q * q).toNat = q.toNat * q.toNat := Int.toNat_mul (by omega) (by omega)
  have hprod : x.toNat * y.toNat < q.toNat * q.toNat := Nat.mul_lt_mul'' (by omega) (by omega)
  rw [BitVec.toNat_umod, BitVec.toNat_mul,
    toNat_ofInt_modulus (by omega) (by omega)]
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat * y.toNat) (b := 2 ^ m) (by omega)]

/-- The `mul` pipeline produces a canonical value: its result is `< q`. -/
theorem toNat_mulPipeline_lt (hq : 0 < q) (hqm : q * q ≤ 2 ^ m) (hqm2 : q < 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    (((x.zeroExtend m * y.zeroExtend m) % BitVec.ofInt m q).toNat : Int) < q := by
  rw [toNat_mulPipeline hq hqm hqm2 hnm hx hy]
  have := Nat.mod_lt (x.toNat * y.toNat) (y := q.toNat) (by omega)
  omega

/-- The `mul` lowering pipeline computes the reference semantics of `mod_arith.mul`. -/
theorem mulPipeline_eq_mul (hq : 0 < q) (hqm : q * q ≤ 2 ^ m) (hqm2 : q < 2 ^ m)
    {x y : BitVec n} (hnm : n ≤ m)
    (hx : (x.toNat : Int) < q) (hy : (y.toNat : Int) < q) :
    ((x.zeroExtend m * y.zeroExtend m) % BitVec.ofInt m q).truncate n = mul q x y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, mul, BitVec.toNat_ofNat]
  rw [toNat_mulPipeline hq hqm hqm2 hnm hx hy]
  rw [Int.toNat_emod (Int.mul_nonneg (by omega) (by omega)) (by omega)]
  norm_cast

/-! ## Canonicity of the reference semantics -/

/-- `mod_arith.add` maps canonical representatives to canonical representatives. -/
theorem isCanonical_add (hq : 0 < q) (hqn : q ≤ 2 ^ n) {x y : BitVec n} :
    ((add q x y).toNat : Int) < q := by
  have hqn' : (2 ^ n : Int) = ((2 ^ n : Nat) : Int) := by push_cast; rfl
  have h1 : 0 ≤ ((x.toNat : Int) + y.toNat) % q := Int.emod_nonneg _ (by omega)
  have h2 : ((x.toNat : Int) + y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hlt : (((x.toNat : Int) + y.toNat) % q).toNat < 2 ^ n := by omega
  simp only [add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- `mod_arith.sub` maps canonical representatives to canonical representatives. -/
theorem isCanonical_sub (hq : 0 < q) (hqn : q ≤ 2 ^ n) {x y : BitVec n} :
    ((sub q x y).toNat : Int) < q := by
  have hqn' : (2 ^ n : Int) = ((2 ^ n : Nat) : Int) := by push_cast; rfl
  have h1 : 0 ≤ ((x.toNat : Int) - y.toNat) % q := Int.emod_nonneg _ (by omega)
  have h2 : ((x.toNat : Int) - y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hlt : (((x.toNat : Int) - y.toNat) % q).toNat < 2 ^ n := by omega
  simp only [sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- `mod_arith.mul` maps canonical representatives to canonical representatives. -/
theorem isCanonical_mul (hq : 0 < q) (hqn : q ≤ 2 ^ n) {x y : BitVec n} :
    ((mul q x y).toNat : Int) < q := by
  have hqn' : (2 ^ n : Int) = ((2 ^ n : Nat) : Int) := by push_cast; rfl
  have h1 : 0 ≤ ((x.toNat : Int) * y.toNat) % q := Int.emod_nonneg _ (by omega)
  have h2 : ((x.toNat : Int) * y.toNat) % q < q := Int.emod_lt_of_pos _ hq
  have hlt : (((x.toNat : Int) * y.toNat) % q).toNat < 2 ^ n := by omega
  simp only [mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]
  omega

end

end Veir.Data.ModArith
