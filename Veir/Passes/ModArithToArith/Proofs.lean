import Veir.Passes.ModArithToArith
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.ModArith.Lemmas

/-!
# Correctness of the ModArithToArith lowering patterns

This file proves the structural properties (`ReturnOps`, `ReturnCtxChanges`, ...) of the
mod-arith-to-arith lowering patterns, building on generic lemmas about the `buildOps`
recipe driver.
-/

namespace Veir

/--
A `WithCreatedOps` chain can be extended at the front by a detached `createOp`.
-/
theorem WfIRContext.WithCreatedOps.prepend {ctx ctx₁ ctx₂ : WfIRContext OpCode}
    {opType resultTypes operands successors regions properties h₁ h₂ h₃ h₄} {newOp}
    (hCreate : WfRewriter.createOp ctx opType resultTypes operands successors regions
      properties none h₁ h₂ h₃ h₄ = some (ctx₁, newOp))
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) :
    WfIRContext.WithCreatedOps ctx ctx₂ := by
  induction h with
  | Nil => exact .CreatedOp _ _ _ (.Nil _) ⟨_, _, _, _, _, _, _, _, _, _, hCreate⟩
  | CreatedOp _ _ _ _ hstep ih => exact .CreatedOp _ _ _ (ih hCreate) hstep

/--
After a `WfRewriter.createOp`, an operation is in bounds iff it was in bounds before or
it is the newly created operation.
-/
theorem WfRewriter.createOp_operation_inBounds_iff {ctx ctx' : WfIRContext OpCode}
    {opType resultTypes operands blockOperands regions properties ip h₁ h₂ h₃ h₄} {newOp}
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions
      properties ip h₁ h₂ h₃ h₄ = some (ctx', newOp))
    (p : OperationPtr) :
    p.InBounds ctx'.raw ↔ (p.InBounds ctx.raw ∨ p = newOp) := by
  grind [WfRewriter.createOp]

section getPropertiesOther

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
`createEmptyOp` does not change the properties of other operations, at any opcode.
(The existing `getProperties!_createEmptyOp` lemma is restricted to the created opcode.)
-/
theorem OperationPtr.getProperties!_createEmptyOp_other {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {properties : HasOpInfo.propertiesOf opType}
    {newOp operation : OperationPtr} {T : OpInfo}
    (h : Rewriter.createEmptyOp ctx opType properties = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx' T = operation.getProperties! ctx T := by
  grind [Rewriter.createEmptyOp, OperationPtr.getProperties!, OperationPtr.get!]

grind_pattern OperationPtr.getProperties!_createEmptyOp_other =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', newOp),
  operation.getProperties! ctx' T

/--
`createOp` does not change the properties of other operations, at any opcode. (The
existing `getProperties!_createOp` lemma is restricted to the created opcode.)
-/
theorem OperationPtr.getProperties!_createOp_other {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {resultTypes operands blockOperands regions}
    {properties : HasOpInfo.propertiesOf opType} {ip h₁ h₂ h₃ h₄ h₅}
    {newOp operation : OperationPtr} {T : OpInfo}
    (h : Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx' T = operation.getProperties! ctx T := by
  simp only [Rewriter.createOp] at h
  grind (gen := 20)

grind_pattern OperationPtr.getProperties!_createOp_other =>
  Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
    ip h₁ h₂ h₃ h₄ h₅, some (ctx', newOp), operation.getProperties! ctx' T

/--
`WfRewriter.createOp` does not change the properties of other operations, at any opcode.
-/
theorem OperationPtr.getProperties!_WfRewriter_createOp_other
    {ctx ctx' : WfIRContext OpInfo}
    {opType : OpInfo} {resultTypes operands blockOperands regions}
    {properties : HasOpInfo.propertiesOf opType} {ip h₁ h₂ h₃ h₄}
    {newOp operation : OperationPtr} {T : OpInfo}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip h₁ h₂ h₃ h₄ = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx'.raw T = operation.getProperties! ctx.raw T := by
  grind [WfRewriter.createOp]

end getPropertiesOther

namespace ModArithToArith

/-! ## Generic properties of `buildOps` -/

variable {ctx ctx' : WfIRContext OpCode} {descrs : List OpDescr}
  {ops ops' : Array OperationPtr}

/-- `buildOps` only creates detached operations. -/
theorem buildOps_withCreatedOps (h : buildOps ctx descrs ops = some (ctx', ops')) :
    WfIRContext.WithCreatedOps ctx ctx' := by
  induction descrs generalizing ctx ops with
  | nil =>
    simp only [buildOps] at h
    cases h
    exact .Nil _
  | cons d rest ih =>
    simp only [buildOps, bind, Option.bind] at h
    split at h
    case h_2 => contradiction
    split at h
    case h_1 => contradiction
    case h_2 ctx₁ newOp hCreate =>
    exact (ih h).prepend hCreate

/-- `buildOps` only adds to the context: in-bounds pointers stay in bounds. -/
theorem buildOps_inBounds_mono (h : buildOps ctx descrs ops = some (ctx', ops'))
    (ptr : GenericPtr) (hptr : ptr.InBounds ctx.raw) : ptr.InBounds ctx'.raw :=
  (buildOps_withCreatedOps h).inBounds_mono ptr hptr

/--
The operations returned by `buildOps` are the input accumulator plus exactly the
operations that are in bounds of the output context but not the input context.
-/
theorem buildOps_mem_iff (h : buildOps ctx descrs ops = some (ctx', ops'))
    (hops : ∀ o ∈ ops, o.InBounds ctx.raw) :
    ∀ o, o ∈ ops' ↔ (o ∈ ops ∨ (o.InBounds ctx'.raw ∧ ¬ o.InBounds ctx.raw)) := by
  induction descrs generalizing ctx ops with
  | nil =>
    simp only [buildOps] at h
    cases h
    grind
  | cons d rest ih =>
    simp only [buildOps, bind, Option.bind] at h
    split at h
    case h_2 => contradiction
    split at h
    case h_1 => contradiction
    case h_2 ctx₁ newOp hCreate =>
    have hOpIff := WfRewriter.createOp_operation_inBounds_iff hCreate
    have hNew : newOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hCreate
    have hNewNot : ¬ newOp.InBounds ctx.raw := WfRewriter.createOp_new_not_inBounds _ hCreate
    have hops₁ : ∀ o ∈ ops.push newOp, o.InBounds ctx₁.raw := by grind
    have hiff := ih h hops₁
    have hCtxMono := buildOps_inBounds_mono h
    grind

/-! ## Inversion lemmas for the lowering patterns -/

/-- Successful `matchOp` constrains the operation's shape. -/
theorem _root_.Veir.matchOp_some_inv {op : OperationPtr} {rawCtx : IRContext OpCode}
    {opType : OpCode} {k : Nat} {operands props}
    (h : matchOp op rawCtx opType k = some (operands, props)) :
    op.getOpType! rawCtx = opType ∧ op.getNumOperands! rawCtx = k ∧
    op.getNumResults! rawCtx = 1 ∧ operands = op.getOperands! rawCtx ∧
    props = op.getProperties! rawCtx opType := by
  unfold matchOp at h
  simp only [guard, bind, Option.bind, pure, failure] at h
  repeat' split at h
  all_goals grind

/-- Inversion of a successful application of `lowerBinop`. -/
theorem lowerBinop_some_inv {modOp : Mod_Arith}
    {recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr}
    {op : OperationPtr} {newCtx : WfIRContext OpCode}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : lowerBinop modOp recipe ctx op = some (newCtx, some (newOps, newValues))) :
    ∃ operands props mt result,
      matchOp op ctx.raw (.mod_arith modOp) 2 = some (operands, props) ∧
      ((op.getResult 0 : ValuePtr).getType! ctx.raw).val = .modArithType mt ∧
      mt.modulus.type.bitwidth ≠ 0 ∧
      buildOps ctx (recipe operands[0]! operands[1]! mt) = some (newCtx, newOps) ∧
      newOps.back? = some result ∧
      (result.getResult 0 : ValuePtr).InBounds newCtx.raw ∧
      newValues = #[(result.getResult 0 : ValuePtr)] := by
  unfold lowerBinop at h
  simp only [bind, Option.bind, pure] at h
  split at h
  case h_2 => simp at h
  next operands props hmatch =>
  split at h
  case h_2 => simp at h
  next mt hmt =>
  split at h
  case isTrue => simp at h
  next hbw =>
  split at h
  case h_2 => simp at h
  next newCtx' newOps' hbuild =>
  split at h
  case h_2 => simp at h
  next result hback =>
  split at h
  case isTrue => simp at h
  next hres =>
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨operands, props, mt, result, hmatch, hmt, hbw, by grind, by grind, by grind, by grind⟩

/-- A `lowerBinop` "no-match" application does not change the context. -/
theorem lowerBinop_none_inv {modOp : Mod_Arith}
    {recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr}
    {op : OperationPtr} {newCtx : WfIRContext OpCode}
    (h : lowerBinop modOp recipe ctx op = some (newCtx, none)) :
    ctx = newCtx := by
  unfold lowerBinop at h
  simp only [bind, Option.bind, pure] at h
  split at h
  case h_2 => grind
  split at h
  case h_2 => grind
  split at h
  case isTrue => grind
  split at h
  case h_2 => grind
  split at h
  case h_2 => grind
  split at h
  case isTrue => grind
  grind

/-- Inversion of a successful application of `lowerConstant`. -/
theorem lowerConstant_some_inv
    {op : OperationPtr} {newCtx : WfIRContext OpCode}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : lowerConstant ctx op = some (newCtx, some (newOps, newValues))) :
    ∃ operands props mt result,
      matchOp op ctx.raw (.mod_arith .constant) 0 = some (operands, props) ∧
      ((op.getResult 0 : ValuePtr).getType! ctx.raw).val = .modArithType mt ∧
      buildOps ctx (constantRecipe props.value.value mt) = some (newCtx, newOps) ∧
      newOps.back? = some result ∧
      (result.getResult 0 : ValuePtr).InBounds newCtx.raw ∧
      newValues = #[(result.getResult 0 : ValuePtr)] := by
  unfold lowerConstant at h
  simp only [bind, Option.bind, pure] at h
  split at h
  case h_2 => simp at h
  next operands props hmatch =>
  split at h
  case h_2 => simp at h
  next mt hmt =>
  split at h
  case h_2 => simp at h
  next newCtx' newOps' hbuild =>
  split at h
  case h_2 => simp at h
  next result hback =>
  split at h
  case isTrue => simp at h
  next hres =>
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨operands, props, mt, result, hmatch, hmt, by grind, by grind, by grind, by grind⟩

/-- A `lowerConstant` "no-match" application does not change the context. -/
theorem lowerConstant_none_inv
    {op : OperationPtr} {newCtx : WfIRContext OpCode}
    (h : lowerConstant ctx op = some (newCtx, none)) :
    ctx = newCtx := by
  unfold lowerConstant at h
  simp only [bind, Option.bind, pure] at h
  split at h
  case h_2 => grind
  split at h
  case h_2 => grind
  split at h
  case h_2 => grind
  split at h
  case h_2 => grind
  split at h
  case isTrue => grind
  grind

/-! ## Structural properties of the lowering patterns -/

theorem lowerBinop_returnsCtxNoChanges (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    (lowerBinop modOp recipe).ReturnsCtxNoChanges :=
  fun _ _ _ h => lowerBinop_none_inv h

theorem lowerBinop_returnCtxChanges (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    (lowerBinop modOp recipe).ReturnCtxChanges := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, _, hbuild, _⟩ := lowerBinop_some_inv h
  exact buildOps_withCreatedOps hbuild

theorem lowerBinop_returnOps (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    (lowerBinop modOp recipe).ReturnOps := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, _, hbuild, _⟩ := lowerBinop_some_inv h
  have := buildOps_mem_iff hbuild (by simp)
  grind

theorem lowerBinop_returnValues (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    (lowerBinop modOp recipe).ReturnValues := by
  intro ctx op _ newCtx newOps newValues h
  obtain ⟨_, _, _, _, hmatch, _, _, _, _, _, hvals⟩ := lowerBinop_some_inv h
  obtain ⟨_, _, hres, _⟩ := matchOp_some_inv hmatch
  grind

theorem lowerBinop_returnValuesInBounds (modOp : Mod_Arith)
    (recipe : ValuePtr → ValuePtr → ModArithType → List OpDescr) :
    (lowerBinop modOp recipe).ReturnValuesInBounds := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, _, _, _, hin, hvals⟩ := lowerBinop_some_inv h
  grind

theorem lowerConstant_returnsCtxNoChanges : lowerConstant.ReturnsCtxNoChanges :=
  fun _ _ _ h => lowerConstant_none_inv h

theorem lowerConstant_returnCtxChanges : lowerConstant.ReturnCtxChanges := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, hbuild, _⟩ := lowerConstant_some_inv h
  exact buildOps_withCreatedOps hbuild

theorem lowerConstant_returnOps : lowerConstant.ReturnOps := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, hbuild, _⟩ := lowerConstant_some_inv h
  have := buildOps_mem_iff hbuild (by simp)
  grind

theorem lowerConstant_returnValues : lowerConstant.ReturnValues := by
  intro ctx op _ newCtx newOps newValues h
  obtain ⟨_, _, _, _, hmatch, _, _, _, _, hvals⟩ := lowerConstant_some_inv h
  obtain ⟨_, _, hres, _⟩ := matchOp_some_inv hmatch
  grind

theorem lowerConstant_returnValuesInBounds : lowerConstant.ReturnValuesInBounds := by
  intro ctx op newCtx newOps newValues h
  obtain ⟨_, _, _, _, _, _, _, _, hin, hvals⟩ := lowerConstant_some_inv h
  grind

/-! ## Inversion of `buildOps` steps -/

/-- `buildOps` with an empty recipe returns its inputs. -/
theorem buildOps_nil_inv (h : buildOps ctx [] ops = some (ctx', ops')) :
    ctx' = ctx ∧ ops' = ops := by
  simp only [buildOps] at h
  grind

/-- Inversion of one step of `buildOps`. -/
theorem buildOps_cons_inv {d : OpDescr} {rest : List OpDescr}
    (h : buildOps ctx (d :: rest) ops = some (ctx', ops')) :
    ∃ resolved ctx₁ newOp h₁ h₂ h₃ h₄,
      d.operands.mapM (OperandRef.resolve ctx ops) = some resolved ∧
      WfRewriter.createOp ctx d.opType d.resultTypes (resolved.map (·.val)) #[] #[]
        d.properties none h₁ h₂ h₃ h₄ = some (ctx₁, newOp) ∧
      buildOps ctx₁ rest (ops.push newOp) = some (ctx', ops') := by
  simp only [buildOps, bind, Option.bind] at h
  split at h
  case h_2 => contradiction
  case h_1 resolved hres =>
  split at h
  case h_1 => contradiction
  case h_2 ctx₁ newOp hCreate =>
  exact ⟨resolved, ctx₁, newOp, _, _, _, _, hres, hCreate, h⟩

/-- Inversion of resolving a reference to an earlier created operation's result. -/
theorem resolve_created_inv {ops : Array OperationPtr} {i j : Nat}
    {v : {v : ValuePtr // v.InBounds ctx.raw}}
    (h : OperandRef.resolve ctx ops (.created i j) = some v) :
    ∃ o, ops[i]? = some o ∧ v.val = (o.getResult j : ValuePtr) := by
  unfold OperandRef.resolve at h
  simp only [bind, Option.bind] at h
  split at h
  case h_2 => contradiction
  case h_1 o ho =>
  split at h
  · grind
  · contradiction

/-! ## Interpretation helpers -/

/--
Interpreting an operation whose opcode is known: this restates `interpretOp` with the
known opcode substituted, sidestepping the dependent typing of the properties.
-/
theorem _root_.Veir.interpretOp_congr {ctx : WfIRContext OpCode} {op : OperationPtr}
    {T : OpCode} (hty : op.getOpType! ctx = T) {state : InterpreterState ctx}
    {inB : op.InBounds ctx.raw} :
    interpretOp op state inB = (do
      let some operands := state.variables.getOperandValues op | none
      let (resultValues, mem, action) ← interpretOp' T (op.getProperties! ctx T)
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) state.memory
      let newVars ← state.variables.setResultValues? op resultValues (by grind)
      let newState : InterpreterState ctx := ⟨newVars, mem⟩
      return (newState, action)) := by
  subst hty
  rfl

/--
Interpreting a single memory-preserving operation, given its opcode, operand values,
the evaluation of its semantics function, and conformance of its results.
-/
theorem _root_.Veir.interpretOp_step {ctx : WfIRContext OpCode} {op : OperationPtr}
    {T : OpCode} {state : InterpreterState ctx} {inB : op.InBounds ctx.raw}
    {operandVals resVals : Array RuntimeValue} {act : Option ControlFlowAction}
    (hty : op.getOpType! ctx = T)
    (hopvals : state.variables.getOperandValues op = some operandVals)
    (heval : interpretOp' T (op.getProperties! ctx T) (op.getResultTypes! ctx.raw)
      operandVals (op.getSuccessors! ctx.raw) state.memory
      = some (.ok (resVals, state.memory, act)))
    (hconf : RuntimeValue.ArrayConforms resVals (op.getResultTypes! ctx.raw)) :
    ∃ varState', state.variables.setResultValues? op resVals = some varState' ∧
      interpretOp op state inB = some (.ok (⟨varState', state.memory⟩, act)) := by
  obtain ⟨varState', hset⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms
      (varState := state.variables) (inBounds := inB)).mp hconf
  refine ⟨varState', hset, ?_⟩
  rw [interpretOp_congr hty]
  simp only [hopvals, heval, hset, bind, Option.bind, pure, liftM, monadLift,
    MonadLift.monadLift]

/--
Inversion of a successful `interpretOp` with a known opcode: restates
`interpretOp_some_iff` with the opcode substituted.
-/
theorem _root_.Veir.interpretOp_some_inv {ctx : WfIRContext OpCode} {op : OperationPtr}
    {T : OpCode} {state state' : InterpreterState ctx} {cf} {inB : op.InBounds ctx.raw}
    (hty : op.getOpType! ctx.raw = T)
    (h : interpretOp op state inB = some (.ok (state', cf))) :
    ∃ operandVals resVals mem' varState',
      state.variables.getOperandValues op = some operandVals ∧
      interpretOp' T (op.getProperties! ctx.raw T) (op.getResultTypes! ctx.raw) operandVals
        (op.getSuccessors! ctx.raw) state.memory = some (.ok (resVals, mem', cf)) ∧
      state.variables.setResultValues? op resVals = some varState' ∧
      state' = ⟨varState', mem'⟩ := by
  subst hty
  exact interpretOp_some_iff.mp h

/-! ## Semantics preservation -/

theorem lowerConstant_preservesSemantics :
    lowerConstant.PreservesSemantics lowerConstant_returnOps lowerConstant_returnCtxChanges
      lowerConstant_returnValuesInBounds lowerConstant_returnValues := by
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern
  intro state hstateEq newState cf hinterp sourceValues hsource state' hstateEq' hrefines
  obtain ⟨operands, props, mt, result, hmatch, hmt, hbuild, hback, hresIn, rfl⟩ :=
    lowerConstant_some_inv hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Facts from the verifier: the constant is canonical and the modulus is valid.
  have hVerified : op.Verified ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hValTy, hValNonneg, hValLt, hQpos, hQwidth⟩ :=
    hVerified.mod_arith_constant hOpType
  -- The verifier and the pattern see the same `!mod_arith.int` type.
  have hmtv : mtv = mt := by
    have := hResTy
    grind [ValuePtr.getType!]
  subst hmtv
  rw [← hProps] at hValTy hValNonneg hValLt
  -- Unpack the two operations created by the recipe.
  rw [constantRecipe] at hbuild
  obtain ⟨res₀, ctx₁, op₀, _, _, _, _, hres₀, hC₀, hbuild₁⟩ := buildOps_cons_inv hbuild
  obtain ⟨res₁, ctx₂, op₁, _, _, _, _, hres₁, hC₁, hbuild₂⟩ := buildOps_cons_inv hbuild₁
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₂
  -- Resolve the operand arrays of the two created operations.
  have hres₀' : res₀.map (·.val) = #[] := by
    simp only [constantDescr] at hres₀
    grind
  have hres₁' : res₁.map (·.val) = #[(op₀.getResult 0 : ValuePtr)] := by
    have hsize : res₁.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₁
      simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₁ 0 (by omega)
    obtain ⟨o, ho, hval⟩ := resolve_created_inv hidx
    have ho' : op₀ = o := by simpa using ho
    subst ho'
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by
        simp only [Array.size_map, hsize] at h1
        omega
      subst hi
      simpa using hval
  -- Shape of the created operations in the final context.
  have hOp01 : op₀ ≠ op₁ := by
    have h₁ : op₀.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hC₀
    have h₂ : ¬ op₁.InBounds ctx₁.raw := WfRewriter.createOp_new_not_inBounds _ hC₁
    grind
  have hTy₀ : op₀.getOpType! newCtx.raw = .arith .constant := by grind [constantDescr]
  have hTy₁ : op₁.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    grind [castDescr]
  -- The recipe result is the final cast operation.
  have hresult : op₁ = result := by simpa using hback
  subst hresult
  -- Shape of the created operations in the final context.
  have hProps₀ : op₀.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk props.value.value (IntegerType.mk mtv.modulus.type.bitwidth) } := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_other hC₁ hOp01]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₀ (operation := op₀)
    rw [if_pos rfl] at h2
    exact h2
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[] := by
    grind [constantDescr]
  have hResultTypes₀ : op₀.getResultTypes! newCtx.raw
      = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    have h1 := OperationPtr.getResultTypes!_WfRewriter_createOp hC₁ (operation := op₀)
    have h2 := OperationPtr.getResultTypes!_WfRewriter_createOp hC₀ (operation := op₀)
    rw [h1, if_neg hOp01, h2, if_pos rfl]
    rfl
  have hSucc₀ : op₀.getSuccessors! newCtx.raw = #[] := by grind [constantDescr]
  have hNumRes₀ : op₀.getNumResults! newCtx.raw = 1 := by grind [constantDescr]
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[(op₀.getResult 0 : ValuePtr)] := by
    grind [castDescr]
  have hResultTypes₁ : op₁.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    grind [castDescr]
  have hSucc₁ : op₁.getSuccessors! newCtx.raw = #[] := by grind [castDescr]
  have hNumRes₁ : op₁.getNumResults! newCtx.raw = 1 := by grind [castDescr]
  have hInB₀ : op₀.InBounds newCtx.raw := by grind
  have hInB₁ : op₁.InBounds newCtx.raw := by grind
  -- ## Source interpretation
  have hOperandsNil : op.getOperands! ctx.raw = #[] := by
    have : (op.getOperands! ctx.raw).size = 0 := by grind
    grind
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp
  have hSrcOpValsNil : srcOperandVals = #[] := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOperandsNil] at hSrcOpVals
    simpa using hSrcOpVals.symm
  subst hSrcOpValsNil
  have hResTy0 : (op.getResultTypes! ctx.raw)[0]? = some ⟨.modArithType mtv, by rfl⟩ := by
    have hsz : (op.getResultTypes! ctx.raw).size = 1 := by grind
    have h0 : (op.getResultTypes! ctx.raw)[0]?
        = some ((op.getResultTypes! ctx.raw)[0]'(by omega)) := by
      simp [hsz]
    rw [h0]
    congr 1
    apply Subtype.ext
    have hElem : (op.getResultTypes! ctx.raw)[0]'(by omega)
        = (op.getResult 0 : ValuePtr).getType! ctx.raw := by
      grind [OperationPtr.getResultTypes!, ValuePtr.getType!, OpResultPtr.get!]
    rw [hElem]
    exact hmt
  have hSrcEval' : interpretOp' (.mod_arith .constant)
      (op.getProperties! ctx.raw (.mod_arith .constant)) (op.getResultTypes! ctx.raw) #[]
      (op.getSuccessors! ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))],
          state.memory, none)) := by
    simp only [interpretOp', ModArith.interpretOp', hResTy0, ← hProps]
    rfl
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mtv.modulus.type.bitwidth
      (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf
  subst hSrcMemEq
  subst hSrcState
  -- The single source value.
  have hNumResultsNB : op.getNumResults ctx.raw opInBounds = 1 := by grind
  have hGetResults : op.getResults ctx.raw opInBounds = #[(op.getResult 0 : ValuePtr)] := by
    unfold OperationPtr.getResults
    rw [hNumResultsNB]
    simp [Array.range_succ, show Array.range 0 = #[] from by simp [Array.range]]
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hSourceVals : sourceValues
      = #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))] := by
    rw [hGetResults, Array.mapM_eq_mapM_toList] at hsource
    simp [hvSrc] at hsource
    exact hsource.symm
  -- ## Target interpretation
  -- Step 1: the `arith.constant`.
  have hOpVals₀ : state'.variables.getOperandValues op₀ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₀, Array.mapM_eq_mapM_toList]
    simp
  have hResTy₀ : (op₀.getResultTypes! newCtx.raw)[0]?
      = some (IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr) := by
    rw [hResultTypes₀]
    rfl
  have hEval₀ : interpretOp' (.arith .constant) (op₀.getProperties! newCtx.raw (.arith .constant))
      (op₀.getResultTypes! newCtx.raw) #[] (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))],
          state'.memory, none)) := by
    rw [hResultTypes₀, hProps₀]
    rfl
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))]
      (op₀.getResultTypes! newCtx.raw) := by
    rw [hResultTypes₀]
    refine ⟨by rfl, ?_⟩
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp [RuntimeValue.Conforms]
  obtain ⟨varState₁, hSet₀, hStep₀⟩ :=
    interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  -- Step 2: the cast back to `!mod_arith.int`.
  have hv₁ : varState₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]
    simp [hNumRes₀]
  have hOpVals₁ : (InterpreterState.mk varState₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁, Array.mapM_eq_mapM_toList]
    simp [hv₁]
  have hEval₁ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₁.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))],
          state'.memory, none)) := by
    rw [hResultTypes₁]
    simp [interpretOp', pure]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))]
      (op₁.getResultTypes! newCtx.raw) := by
    rw [hResultTypes₁]
    refine ⟨by rfl, ?_⟩
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    refine ⟨rfl, ?_⟩
    -- canonicity of the constant value
    simp only [Data.ModArith.isCanonical_val]
    have hPowLe : ((2 : Int) ^ (mtv.modulus.type.bitwidth - 1))
        ≤ 2 ^ mtv.modulus.type.bitwidth := by
      have := Nat.pow_le_pow_right (n := 2) (by omega)
        (Nat.sub_le mtv.modulus.type.bitwidth 1)
      exact_mod_cast this
    have hofInt := Data.ModArith.toNat_ofInt_modulus
      (m := mtv.modulus.type.bitwidth) hValNonneg (by omega)
    omega
  obtain ⟨varState₂, hSet₁, hStep₁⟩ :=
    interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  -- ## Assemble
  refine ⟨⟨varState₂, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁] state' _ = liftM (some (⟨varState₂, state'.memory⟩, none))
    rw [interpretOpList_cons]
    simp only [hStep₀]
    rw [interpretOpList_cons]
    simp only [hStep₁]
    simp [liftM, monadLift, MonadLift.monadLift]
  · obtain ⟨hmem, _⟩ := hrefines
    simpa using hmem
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))], ?_, ?_⟩
    · have hv₂ : varState₂.getVar? (op₁.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (BitVec.ofInt mtv.modulus.type.bitwidth props.value.value))) := by
        rw [VariableState.getVar?_setResultValues? hSet₁]
        simp [hNumRes₁]
      rw [Array.mapM_eq_mapM_toList]
      simp [hv₂]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp [RuntimeValue.isRefinedBy]

end ModArithToArith

end Veir
