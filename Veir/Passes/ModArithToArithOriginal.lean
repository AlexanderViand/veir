import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  # ModArithToArithOriginal pass

  The trivial mod-arith-to-arith lowering, written in the "natural" imperative
  `PatternRewriter` style: helpers emit operations one by one at an insertion point,
  exactly like the first version of this pass (and like a conversion pattern in MLIR).

  Where the first version discharged the rewriter's well-formedness side conditions with
  `sorry`, this version is sorry-free: every proof obligation of `createOp`,
  `replaceValue`, and `eraseOp` is decidable (in-bounds checks, use counts, region
  counts), so each former `sorry` is replaced by a *dynamic check* (`if h : ¬ ... then
  none else ...`) whose hypothesis discharges the obligation via `grind`. On well-formed
  input the checks always pass, and the pass emits exactly the same IR as
  `--mod-arith-to-arith` (the FileCheck expectations of the two passes are identical).

  Note on verification status: this pass is structurally verified — it cannot violate
  the IR well-formedness invariants, since `WfIRContext` is maintained by construction —
  and it is validated against the interpreter by differential tests. The full semantic
  proof (`LocalRewritePattern.PreservesSemantics`) lives with the recipe-based
  `--mod-arith-to-arith` pass, since the proof framework operates on
  `LocalRewritePattern`s rather than imperative rewrites.
-/

namespace ModArithToArithOriginal

/-! ## Unrealized Conversion Casts -/

/-- Emit `unrealized_conversion_cast v : !mod_arith.int<q:iN> → iN`. -/
def castToStorage (rewriter : PatternRewriter OpCode) (v : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let .modArithType mt := (v.getType! rewriter.ctx.raw).val
    | none
  if hv : ¬ v.InBounds rewriter.ctx.raw then none else
  if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
  let storageType : TypeAttr := mt.modulus.type
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
    #[storageType] #[v] #[] #[] () (some ip) (by grind) (by simp) (by simp)
    (by grind [Option.maybe])
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-- Emit `unrealized_conversion_cast x : iN → ty`, where `ty` is a `mod_arith` type. -/
def castToModArith (rewriter : PatternRewriter OpCode) (x : ValuePtr) (ty : ModArithType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  if hx : ¬ x.InBounds rewriter.ctx.raw then none else
  if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
    #[ty] #[x] #[] #[] () (some ip) (by grind) (by simp) (by simp)
    (by grind [Option.maybe])
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-! ## Unpack / Pack ModArithType -/

/--
  Unpack a `!mod_arith.int<q:iN>` value `v` into the IntegerType `intermediateType`
-/
def unpackValue (rewriter : PatternRewriter OpCode) (v : ValuePtr) (intermediateType : IntegerType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, stored) ← castToStorage rewriter v ip
  let .integerType storageType := (stored.getType! rewriter.ctx.raw).val
    | none
  if intermediateType.bitwidth > storageType.bitwidth then
    if hs : ¬ stored.InBounds rewriter.ctx.raw then none else
    if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
    let (rewriter, ext) ← rewriter.createOp (.arith .extui)
      #[intermediateType] #[stored] #[] #[] { nneg := false } (some ip) (by grind) (by simp)
      (by simp) (by grind [Option.maybe])
    return (rewriter, (ext.getResult 0 : ValuePtr))
  else
    return (rewriter, stored)

/--
  Pack an IntegerType value `v` of IntegerType `intermediateType` into a value of `!mod_arith.int<q:iN>` type `ty`.
-/
def packValue (rewriter : PatternRewriter OpCode) (v : ValuePtr) (ty : ModArithType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let .integerType intermediateType := (v.getType! rewriter.ctx.raw).val
    | none
  let storageType := ty.modulus.type
  if intermediateType.bitwidth > storageType.bitwidth then
    if hv : ¬ v.InBounds rewriter.ctx.raw then none else
    if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
    let (rewriter, narrowed) ← rewriter.createOp (.arith .trunci)
      #[storageType] #[v] #[] #[] { nsw := false, nuw := true }
      (some ip) (by grind) (by simp) (by simp) (by grind [Option.maybe])
    castToModArith rewriter (narrowed.getResult 0 : ValuePtr) ty ip
  else
    castToModArith rewriter (v : ValuePtr) ty ip


/-! ## Arith Helpers -/

/-- Emit `arith.constant c : i<width>`. Requires c to fit into width (unsigned) -/
def emitArithConstant (rewriter : PatternRewriter OpCode) (c : Int) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
  let ty : TypeAttr := IntegerType.mk width
  let props : ArithConstantProperties := { value := IntegerAttr.mk c (IntegerType.mk width) }
  let (rewriter, c) ← rewriter.createOp (.arith .constant)
    #[ty] #[] #[] #[] props (some ip) (by simp) (by simp) (by simp)
    (by grind [Option.maybe])
  return (rewriter, (c.getResult 0 : ValuePtr))

/-- Emit a binary Arith op `arithOp` on `a` and `b` -/
def emitArithBinOp (rewriter : PatternRewriter OpCode) (arithOp : Arith)
    (props : propertiesOf (.arith arithOp)) (a b : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  if ha : ¬ a.InBounds rewriter.ctx.raw then none else
  if hb : ¬ b.InBounds rewriter.ctx.raw then none else
  if hip : ¬ ip.InBounds rewriter.ctx.raw then none else
  let ty := a.getType! rewriter.ctx.raw
  let (rewriter, r) ← rewriter.createOp (.arith arithOp)
    #[ty] #[a, b] #[] #[] props (some ip) (by grind) (by simp) (by simp)
    (by grind [Option.maybe])
  return (rewriter, (r.getResult 0 : ValuePtr))


/-! ## Binary op lowering Template -/

abbrev Builder :=
  (rewriter : PatternRewriter OpCode) →
  (lhs rhs modulus : ValuePtr) →
  (ip : InsertPoint) →
  Option (PatternRewriter OpCode × ValuePtr)

/-- Replace the (single) result of `op` with `r` and erase `op`, dynamically checking
    the side conditions of `replaceValue` and `eraseOp`. -/
def replaceAndErase (rewriter : PatternRewriter OpCode) (op : OperationPtr) (r : ValuePtr) :
    Option (PatternRewriter OpCode) := do
  if hne : (op.getResult 0 : ValuePtr) = r then none else
  if hold : ¬ (op.getResult 0 : ValuePtr).InBounds rewriter.ctx.raw then none else
  if hnew : ¬ r.InBounds rewriter.ctx.raw then none else
  let rewriter := rewriter.replaceValue (op.getResult 0) r (by grind) (by grind) (by grind)
  if hregions : op.getNumRegions! rewriter.ctx.raw ≠ 0 then none else
  if huses : op.hasUses! rewriter.ctx.raw then none else
  if hop : ¬ op.InBounds rewriter.ctx.raw then none else
  rewriter.eraseOp op (by grind) (by grind) (by grind)

/-- Lower a binary `mod_arith` op `modOp`,
    using intermediate Type iM given storage type iN, with M = `widen` N,
    and using Builder `build` to determine the exact `arith` operations to emit -/
def lowerModArithBinOp (modOp : Mod_Arith) (widen : Nat → Nat) (build : Builder)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr) : Option (PatternRewriter OpCode) := do
  -- match op and extract operands:
  let some (operands, _) := matchOp op rewriter.ctx (.mod_arith modOp) 2
    | return rewriter
  let lhs := operands[0]!
  let rhs := operands[1]!
  -- type setup
  let .modArithType modArithType := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  let intermediateWidth := widen modArithType.modulus.type.bitwidth
  let intermediateType  := IntegerType.mk intermediateWidth
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, a) ← unpackValue rewriter lhs intermediateType ip
  let (rewriter, b) ← unpackValue rewriter rhs intermediateType ip
  let (rewriter, q) ← emitArithConstant rewriter modArithType.modulus.value intermediateWidth ip
  let (rewriter, r) ← build rewriter a b q ip
  let (rewriter, r) ← emitArithBinOp rewriter .remui () r q ip
  let (rewriter, r) ← packValue rewriter r modArithType ip
  replaceAndErase rewriter op r

/-! ## Binary op lowering Patterns -/

def buildAdd : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .addi { nsw := false, nuw := false } a b ip

def lowerModArithAddOp := lowerModArithBinOp .add (· + 1) buildAdd

def buildMul : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .muli { nsw := false, nuw := false } a b ip

def lowerModArithMulOp := lowerModArithBinOp .mul (2 * ·) buildMul

def buildSub : Builder :=
  fun (rewriter : PatternRewriter OpCode) (a b q : ValuePtr) (ip : InsertPoint) => do
    -- we compute a - b (mod q) as ((a+q) - b) % q to avoid unsigned underflow when a < b.
    let (rewriter, aq) ← emitArithBinOp rewriter .addi { nsw := false, nuw := false } a q ip
    emitArithBinOp rewriter .subi { nsw := false, nuw := false } aq b ip

def lowerModArithSubOp := lowerModArithBinOp .sub (· + 1) buildSub

/-! ## Constant lowering Pattern -/

/-- Lower `mod_arith.constant` to an `arith.constant` (the verifier guarantees the value
    is in `[0, q)` already). -/
def lowerModArithConstant (rewriter : PatternRewriter OpCode) (op : OperationPtr) : Option (PatternRewriter OpCode) := do
  -- match op and extract attribute:
  let some (_, props) := matchOp op rewriter.ctx (.mod_arith .constant) 0
    | return rewriter
  let c := props.value.value
  -- type setup
  let .modArithType modArithType := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  let storageType := modArithType.modulus.type
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, r) ← emitArithConstant rewriter c storageType.bitwidth ip
  let (rewriter, out) ← castToModArith rewriter (r : ValuePtr) modArithType ip
  replaceAndErase rewriter op out

end ModArithToArithOriginal

/-! ## Pass implementation -/

def ModArithToArithOriginalPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    ModArithToArithOriginal.lowerModArithConstant,
    ModArithToArithOriginal.lowerModArithAddOp,
    ModArithToArithOriginal.lowerModArithSubOp,
    ModArithToArithOriginal.lowerModArithMulOp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying mod-arith-to-arith-original lowering"
  | some ctx => pure ctx

public def ModArithToArithOriginalPass : Pass OpCode :=
  { name := "mod-arith-to-arith-original"
    description := "Lower mod_arith operations to the arith dialect (imperative-style implementation of --mod-arith-to-arith)."
    run := ModArithToArithOriginalPass.impl }

end Veir
