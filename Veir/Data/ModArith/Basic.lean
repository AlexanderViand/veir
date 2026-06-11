module

public import Veir.Data.LLVM.Int.Basic

namespace Veir.Data.ModArith

public section

/-! # HEIR ModArith Dialect Semantics

A value of type `!mod_arith.int<q : iN>` is represented at runtime by the canonical
representative of its residue class: a concrete `N`-bit integer in `[0, q)`. The
`mod_arith` operations may assume their operands are canonical, and must produce
canonical results.
-/

/--
`v` is the canonical representative of a residue class modulo `q`: a concrete
(non-poison) value in `[0, q)`.
-/
def IsCanonical (q : Int) {w : Nat} : LLVM.Int w → Prop
  | .val x => (x.toNat : Int) < q
  | .poison => False

instance {q : Int} {w : Nat} {v : LLVM.Int w} : Decidable (IsCanonical q v) :=
  match v with
  | .val x => inferInstanceAs (Decidable ((x.toNat : Int) < q))
  | .poison => inferInstanceAs (Decidable False)

@[simp, grind =]
theorem isCanonical_val {q : Int} {w : Nat} {x : BitVec w} :
    IsCanonical q (.val x) ↔ (x.toNat : Int) < q := Iff.rfl

@[simp, grind .]
theorem not_isCanonical_poison {q : Int} {w : Nat} :
    ¬ IsCanonical q (.poison : LLVM.Int w) := fun h => h

/-! ## Reference semantics

The reference semantics of the `mod_arith` operations on canonical representatives:
compute the exact integer result and reduce it modulo `q`.

For a positive modulus `q`, `Int.emod` always returns a value in `[0, q)`, so these
operations map canonical representatives to canonical representatives. The bitvector
faithfully represents the result whenever `q ≤ 2^w`, which is guaranteed by the
verifier invariant `q < 2^(w-1)` (see `TypeAttr.verifyModArithType`).
-/

/--
`add q x y` is the canonical representative of `x + y` modulo `q`, where `x` and `y`
are themselves canonical representatives in `[0, q)`.
-/
def add {w : Nat} (q : Int) (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w ((((x.toNat : Int) + (y.toNat : Int)) % q).toNat)

/--
`sub q x y` is the canonical representative of `x - y` modulo `q`, where `x` and `y`
are themselves canonical representatives in `[0, q)`.
-/
def sub {w : Nat} (q : Int) (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w ((((x.toNat : Int) - (y.toNat : Int)) % q).toNat)

/--
`mul q x y` is the canonical representative of `x * y` modulo `q`, where `x` and `y`
are themselves canonical representatives in `[0, q)`.
-/
def mul {w : Nat} (q : Int) (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w ((((x.toNat : Int) * (y.toNat : Int)) % q).toNat)

end

end Veir.Data.ModArith
