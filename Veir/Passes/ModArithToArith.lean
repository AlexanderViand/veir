import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  # ModArithToArith pass

  Lowers operations from the `mod_arith` dialect into operations in the `arith` dialect,
  translating `!mod_arith.int<q : iN>` values to their canonical representation in `[0, q)`.
  The current lowering is trivial, eagerly reducing at all times.

  Since Veir has no Dialect Conversion framework, this pass eagerly inserts
  `unrealized_conversion_casts` to handle the type conversions between `!mod_arith.int<q:iN>`
  and `iN` that are needed.

  Each lowering is written as a `LocalRewritePattern`: it describes the operations to create
  as a pure *recipe* (`List OpDescr`), which a generic driver (`buildOps`) materializes as
  detached operations. The `RewritePattern.fromLocalRewrite` adapter then inserts them before
  the matched operation, replaces its results, and erases it. This shape lets us prove the
  patterns correct against the interpreter semantics of `mod_arith`.
-/

namespace ModArithToArith

/-!
  ## Op recipes

  A lowering pattern is described by a list of `OpDescr`s, each of which describes one
  operation to create. Operands refer either to values that already exist in the context
  (`OperandRef.outer`) or to results of operations created earlier in the same recipe
  (`OperandRef.created`).
-/

/--
  A reference to an operand of an operation that is about to be created: either a value
  that already exists in the context, or the `result`-th result of the `op`-th operation
  created earlier in the same recipe.
-/
inductive OperandRef where
  | outer (v : ValuePtr)
  | created (op : Nat) (result : Nat)

/-- A description of a single operation to create. -/
structure OpDescr where
  opType : OpCode
  resultTypes : Array TypeAttr
  operands : Array OperandRef
  properties : propertiesOf opType

/--
  Resolve an operand reference to a value that is in bounds of the given context.
  Returns `none` if the reference is dangling.
-/
def OperandRef.resolve (ctx : WfIRContext OpCode) (ops : Array OperationPtr) :
    OperandRef → Option {v : ValuePtr // v.InBounds ctx.raw}
  | .outer v =>
    if h : v.InBounds ctx.raw then some ⟨v, h⟩ else none
  | .created idx res => do
    let some op := ops[idx]? | none
    if h : (op.getResult res : ValuePtr).InBounds ctx.raw then
      some ⟨(op.getResult res : ValuePtr), h⟩
    else
      none

/--
  Create the operations described by `descrs`, without inserting them into a block.
  Return the new context and the created operations (appended to `ops`), or `none` if
  an operand reference cannot be resolved or an operation cannot be created.
-/
def buildOps (ctx : WfIRContext OpCode) (descrs : List OpDescr)
    (ops : Array OperationPtr := #[]) :
    Option (WfIRContext OpCode × Array OperationPtr) :=
  match descrs with
  | [] => some (ctx, ops)
  | descr :: rest => do
    let some resolved := descr.operands.mapM (OperandRef.resolve ctx ops) | none
    match WfRewriter.createOp ctx descr.opType descr.resultTypes (resolved.map (·.val))
        #[] #[] descr.properties none
        (by intro oper hmem
            obtain ⟨s, _, rfl⟩ := Array.exists_of_mem_map hmem
            exact s.2)
        (by simp) (by simp) (by simp [Option.maybe]) with
    | none => none
    | some (ctx, newOp) => buildOps ctx rest (ops.push newOp)

/-- Describe `builtin.unrealized_conversion_cast %input : ... -> resultType`. -/
def castDescr (input : OperandRef) (resultType : TypeAttr) : OpDescr :=
  { opType := .builtin .unrealized_conversion_cast
    resultTypes := #[resultType]
    operands := #[input]
    properties := () }

/-- Describe `arith.constant c : i<width>`. Requires `c` to fit into `width` (unsigned). -/
def constantDescr (c : Int) (width : Nat) : OpDescr :=
  { opType := .arith .constant
    resultTypes := #[(IntegerType.mk width : TypeAttr)]
    operands := #[]
    properties := { value := IntegerAttr.mk c (IntegerType.mk width) } }

/-- Describe `arith.extui %input : i<N> -> i<width>`. -/
def extuiDescr (input : OperandRef) (width : Nat) : OpDescr :=
  { opType := .arith .extui
    resultTypes := #[(IntegerType.mk width : TypeAttr)]
    operands := #[input]
    properties := { nneg := false } }

/-- Describe `arith.trunci %input : ... -> i<width>` with `nuw` set. -/
def trunciNuwDescr (input : OperandRef) (width : Nat) : OpDescr :=
  { opType := .arith .trunci
    resultTypes := #[(IntegerType.mk width : TypeAttr)]
    operands := #[input]
    properties := { attr := { nsw := false, nuw := true } } }

/-- Describe a binary `arith` operation with both operands and result of type `i<width>`. -/
def binopDescr (arithOp : Arith) (props : propertiesOf (.arith arithOp))
    (lhs rhs : OperandRef) (width : Nat) : OpDescr :=
  { opType := .arith arithOp
    resultTypes := #[(IntegerType.mk width : TypeAttr)]
    operands := #[lhs, rhs]
    properties := props }

/-!
  ## Lowering recipes

  All binary lowerings share a common shape: unpack both operands from `!mod_arith.int<q:iN>`
  into a wider intermediate type `iM` (so that the intermediate result cannot overflow),
  compute the operation followed by a final `arith.remui` reduction there, and pack the result
  back down to `iN` / `!mod_arith.int`.

  The recipes assume canonical operands in `[0, q)` and produce canonical results.
-/

/--
  Lower `mod_arith.add` with intermediate width `N+1`:
  `(x + y) % q` cannot overflow `i(N+1)` since `x, y < q < 2^N`.
-/
def addRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let m := n + 1
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,           -- 0: lhs as iN
    extuiDescr (.created 0 0) m,                -- 1: lhs as iM
    castDescr (.outer rhs) storageTy,           -- 2: rhs as iN
    extuiDescr (.created 2 0) m,                -- 3: rhs as iM
    constantDescr mt.modulus.value m,           -- 4: q as iM
    binopDescr .addi { attr := { nsw := false, nuw := false } } (.created 1 0) (.created 3 0) m, -- 5: x + y
    binopDescr .remui () (.created 5 0) (.created 4 0) m, -- 6: (x + y) % q
    trunciNuwDescr (.created 6 0) n,            -- 7: result as iN
    castDescr (.created 7 0) (mt : TypeAttr) ]  -- 8: result as !mod_arith.int

/--
  Lower `mod_arith.sub` with intermediate width `N+1`: we compute `x - y (mod q)` as
  `((x + q) - y) % q` to avoid unsigned underflow when `x < y`.
-/
def subRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let m := n + 1
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,           -- 0: lhs as iN
    extuiDescr (.created 0 0) m,                -- 1: lhs as iM
    castDescr (.outer rhs) storageTy,           -- 2: rhs as iN
    extuiDescr (.created 2 0) m,                -- 3: rhs as iM
    constantDescr mt.modulus.value m,           -- 4: q as iM
    binopDescr .addi { attr := { nsw := false, nuw := false } } (.created 1 0) (.created 4 0) m, -- 5: x + q
    binopDescr .subi { attr := { nsw := false, nuw := false } } (.created 5 0) (.created 3 0) m, -- 6: (x+q) - y
    binopDescr .remui () (.created 6 0) (.created 4 0) m, -- 7: ((x+q) - y) % q
    trunciNuwDescr (.created 7 0) n,            -- 8: result as iN
    castDescr (.created 8 0) (mt : TypeAttr) ]  -- 9: result as !mod_arith.int

/--
  Lower `mod_arith.mul` with intermediate width `2*N`:
  `x * y` cannot overflow `i(2N)` since `x, y < q < 2^N`.
-/
def mulRecipe (lhs rhs : ValuePtr) (mt : ModArithType) : List OpDescr :=
  let n := mt.modulus.type.bitwidth
  let m := 2 * n
  let storageTy : TypeAttr := (mt.modulus.type : TypeAttr)
  [ castDescr (.outer lhs) storageTy,           -- 0: lhs as iN
    extuiDescr (.created 0 0) m,                -- 1: lhs as iM
    castDescr (.outer rhs) storageTy,           -- 2: rhs as iN
    extuiDescr (.created 2 0) m,                -- 3: rhs as iM
    constantDescr mt.modulus.value m,           -- 4: q as iM
    binopDescr .muli { attr := { nsw := false, nuw := false } } (.created 1 0) (.created 3 0) m, -- 5: x * y
    binopDescr .remui () (.created 5 0) (.created 4 0) m, -- 6: (x * y) % q
    trunciNuwDescr (.created 6 0) n,            -- 7: result as iN
    castDescr (.created 7 0) (mt : TypeAttr) ]  -- 8: result as !mod_arith.int

/--
  Lower `mod_arith.constant` to an `arith.constant` (the verifier ensures the value is
  already in `[0, q)`).
-/
def constantRecipe (value : Int) (mt : ModArithType) : List OpDescr :=
  [ constantDescr value mt.modulus.type.bitwidth, -- 0: the value as iN
    castDescr (.created 0 0) (mt : TypeAttr) ]    -- 1: the value as !mod_arith.int

/-!
  ## Lowering patterns
-/

/--
  Lower a binary `mod_arith` operation `modOp` by materializing the operations
  described by `recipe` and replacing the matched operation's result with the
  last created operation's result.
-/
def lowerBinop (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    LocalRewritePattern OpCode :=
  fun ctx op => do
    -- match op and extract operands:
    let some (operands, _) := matchOp op ctx.raw (.mod_arith modOp) 2
      | return (ctx, none)
    let .modArithType mt := ((op.getResult 0 : ValuePtr).getType! ctx.raw).val
      | return (ctx, none)
    -- the lowering is only defined for non-trivial storage types:
    if mt.modulus.type.bitwidth = 0 then
      return (ctx, none)
    -- materialize the recipe:
    let some (newCtx, newOps) := buildOps ctx (recipe operands[0]! operands[1]! mt)
      | none
    let some result := newOps.back? | none
    if _hres : ¬ (result.getResult 0 : ValuePtr).InBounds newCtx.raw then none else
    return (newCtx, some (newOps, #[(result.getResult 0 : ValuePtr)]))

/-- Lower `mod_arith.constant` (see `constantRecipe`). -/
def lowerConstant : LocalRewritePattern OpCode :=
  fun ctx op => do
    -- match op and extract the value attribute:
    let some (_, props) := matchOp op ctx.raw (.mod_arith .constant) 0
      | return (ctx, none)
    let .modArithType mt := ((op.getResult 0 : ValuePtr).getType! ctx.raw).val
      | return (ctx, none)
    -- materialize the recipe:
    let some (newCtx, newOps) := buildOps ctx (constantRecipe props.value.value mt)
      | none
    let some result := newOps.back? | none
    if _hres : ¬ (result.getResult 0 : ValuePtr).InBounds newCtx.raw then none else
    return (newCtx, some (newOps, #[(result.getResult 0 : ValuePtr)]))

end ModArithToArith

/-! ## Pass implementation -/

def lowerModArithConstant : RewritePattern OpCode :=
  .fromLocalRewrite ModArithToArith.lowerConstant

def lowerModArithAddOp : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .add ModArithToArith.addRecipe)

def lowerModArithSubOp : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .sub ModArithToArith.subRecipe)

def lowerModArithMulOp : RewritePattern OpCode :=
  .fromLocalRewrite (ModArithToArith.lowerBinop .mul ModArithToArith.mulRecipe)

def ModArithToArithPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerModArithConstant,
    lowerModArithAddOp,
    lowerModArithSubOp,
    lowerModArithMulOp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying mod-arith-to-arith lowering"
  | some ctx => pure ctx

public def ModArithToArithPass : Pass OpCode :=
  { name := "mod-arith-to-arith"
    description := "Lower mod_arith operations to the arith dialect."
    run := ModArithToArithPass.impl }

end Veir
