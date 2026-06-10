import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.ModArithToArith

namespace Veir

/-!
  # ModArithToArithBarrett pass

  An efficient variant of the mod-arith-to-arith lowering that avoids the per-operation
  `arith.remui` (an integer division) of the trivial lowering:

  * `mod_arith.add` / `mod_arith.sub` exploit the type invariant `q < 2^(N-1)`: the exact
    sum `x + y` (resp. the shifted difference `x + q - y`) of canonical operands lies in
    `[0, 2q) ⊆ [0, 2^N)`, so it fits in the storage type **without widening** and a single
    conditional subtraction (`cmpi uge` + `subi` + `select`, HEIR's `mod_arith.subifge`
    idiom) produces the canonical representative.

  * `mod_arith.mul` uses Barrett reduction: with the compile-time ratio `r = ⌊2^(2N)/q⌋`,
    the quotient `⌊p/q⌋` of the exact product `p = x·y` is estimated by `s = p·r >> 2N`,
    which is off by at most one (see `Veir.Data.ModArith.Barrett.barrett_core`); thus
    `p - s·q ∈ [0, 2q)` and one conditional subtraction canonicalizes. All arithmetic is
    performed at width `4N`, replacing the division of the trivial lowering with two
    multiplications and a shift.

  The patterns reuse the recipe infrastructure of `ModArithToArith`.
-/

namespace ModArithToArith

/-- Describe `arith.cmpi uge %lhs, %rhs : i1`. -/
def cmpiUgeDescr (lhs rhs : OperandRef) : OpDescr :=
  { opType := .arith .cmpi
    resultTypes := #[(IntegerType.mk 1 : TypeAttr)]
    operands := #[lhs, rhs]
    properties := { predicate := .uge } }

/-- Describe `arith.select %cond, %ifTrue, %ifFalse : i<width>`. -/
def selectDescr (cond ifTrue ifFalse : OperandRef) (width : Nat) : OpDescr :=
  { opType := .arith .select
    resultTypes := #[(IntegerType.mk width : TypeAttr)]
    operands := #[cond, ifTrue, ifFalse]
    properties := () }

/--
  Lower `mod_arith.add` without widening or division: the exact sum of canonical
  operands fits in `iN` (since `2q < 2^N`), and a conditional subtraction
  canonicalizes it.
-/
def addBarrettRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,            -- 0: lhs as iN
    castDescr (.outer rhs) storageTy,            -- 1: rhs as iN
    binopDescr .addi { nsw := false, nuw := false } (.created 0 0) (.created 1 0) n,
                                                 -- 2: t = x + y < 2q
    constantDescr mt.modulus.value n,            -- 3: q
    cmpiUgeDescr (.created 2 0) (.created 3 0),  -- 4: t ≥ q
    binopDescr .subi { nsw := false, nuw := false } (.created 2 0) (.created 3 0) n,
                                                 -- 5: t - q
    selectDescr (.created 4 0) (.created 5 0) (.created 2 0) n,
                                                 -- 6: canonical result
    castDescr (.created 6 0) (mt : TypeAttr) ]   -- 7: result as !mod_arith.int

/--
  Lower `mod_arith.sub` without widening or division: `x + q - y` of canonical
  operands lies in `(0, 2q) ⊆ [0, 2^N)`, and a conditional subtraction
  canonicalizes it.
-/
def subBarrettRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,            -- 0: lhs as iN
    castDescr (.outer rhs) storageTy,            -- 1: rhs as iN
    constantDescr mt.modulus.value n,            -- 2: q
    binopDescr .addi { nsw := false, nuw := false } (.created 0 0) (.created 2 0) n,
                                                 -- 3: x + q < 2q
    binopDescr .subi { nsw := false, nuw := false } (.created 3 0) (.created 1 0) n,
                                                 -- 4: t = x + q - y ∈ (0, 2q)
    cmpiUgeDescr (.created 4 0) (.created 2 0),  -- 5: t ≥ q
    binopDescr .subi { nsw := false, nuw := false } (.created 4 0) (.created 2 0) n,
                                                 -- 6: t - q
    selectDescr (.created 5 0) (.created 6 0) (.created 4 0) n,
                                                 -- 7: canonical result
    castDescr (.created 7 0) (mt : TypeAttr) ]   -- 8: result as !mod_arith.int

/--
  Lower `mod_arith.mul` via Barrett reduction at width `4N`: estimate the quotient of
  the exact product by `p·r >> 2N` with the precomputed ratio `r = ⌊2^(2N)/q⌋`, subtract
  the estimated multiple of `q`, and canonicalize with one conditional subtraction.
-/
def mulBarrettRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let w := 4 * n
  let ratio := (2 : Int) ^ (2 * n) / mt.modulus.value
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,            -- 0: lhs as iN
    extuiDescr (.created 0 0) w,                 -- 1: lhs as iW
    castDescr (.outer rhs) storageTy,            -- 2: rhs as iN
    extuiDescr (.created 2 0) w,                 -- 3: rhs as iW
    binopDescr .muli { nsw := false, nuw := false } (.created 1 0) (.created 3 0) w,
                                                 -- 4: p = x·y < q²
    constantDescr ratio w,                       -- 5: r = ⌊2^(2N)/q⌋
    binopDescr .muli { nsw := false, nuw := false } (.created 4 0) (.created 5 0) w,
                                                 -- 6: p·r < 2^(4N-2)
    constantDescr (2 * n) w,                     -- 7: the shift amount 2N
    binopDescr .shrui { exact := false } (.created 6 0) (.created 7 0) w,
                                                 -- 8: s = ⌊p·r / 2^(2N)⌋
    constantDescr mt.modulus.value w,            -- 9: q
    binopDescr .muli { nsw := false, nuw := false } (.created 8 0) (.created 9 0) w,
                                                 -- 10: s·q ≤ p
    binopDescr .subi { nsw := false, nuw := false } (.created 4 0) (.created 10 0) w,
                                                 -- 11: t = p - s·q ∈ [0, 2q)
    cmpiUgeDescr (.created 11 0) (.created 9 0), -- 12: t ≥ q
    binopDescr .subi { nsw := false, nuw := false } (.created 11 0) (.created 9 0) w,
                                                 -- 13: t - q
    selectDescr (.created 12 0) (.created 13 0) (.created 11 0) w,
                                                 -- 14: canonical result as iW
    trunciNuwDescr (.created 14 0) n,            -- 15: result as iN
    castDescr (.created 15 0) (mt : TypeAttr) ]  -- 16: result as !mod_arith.int

end ModArithToArith

/-! ## Pass implementation -/

def lowerModArithAddBarrett : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .add ModArithToArith.addBarrettRecipe)

def lowerModArithSubBarrett : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .sub ModArithToArith.subBarrettRecipe)

def lowerModArithMulBarrett : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .mul ModArithToArith.mulBarrettRecipe)

def ModArithToArithBarrettPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerModArithConstant,
    lowerModArithAddBarrett,
    lowerModArithSubBarrett,
    lowerModArithMulBarrett
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying mod-arith-to-arith-barrett lowering"
  | some ctx => pure ctx

public def ModArithToArithBarrettPass : Pass OpCode :=
  { name := "mod-arith-to-arith-barrett"
    description := "Lower mod_arith operations to the arith dialect using Barrett reduction and conditional subtraction instead of remui."
    run := ModArithToArithBarrettPass.impl }

end Veir
