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

/-- Inversion of resolving a reference to an outer value. -/
theorem resolve_outer_inv {ops : Array OperationPtr} {v : ValuePtr}
    {w : {v : ValuePtr // v.InBounds ctx.raw}}
    (h : OperandRef.resolve ctx ops (.outer v) = some w) :
    v.InBounds ctx.raw ∧ w.val = v := by
  unfold OperandRef.resolve at h
  split at h
  · grind
  · contradiction

/-- A variable that conforms in a variable state has a runtime value matching its type. -/
theorem getVar?_conforms {ctx : WfIRContext OpCode} {vs : VariableState ctx} {val : ValuePtr}
    {v : RuntimeValue} (h : vs.getVar? val = some v) :
    v.Conforms (val.getType! ctx.raw) := by
  unfold VariableState.getVar? at h
  have hmem : val ∈ vs.variables := by
    rw [Std.ExtHashMap.mem_iff_isSome_getElem?, h]; rfl
  have hget : vs.variables[val] = v := by
    rw [Std.ExtHashMap.getElem?_eq_some_getElem hmem] at h
    exact (Option.some.injEq _ _).mp h
  exact vs.conforms val v hmem hget

/-- `getOpType!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getOpType!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getOpType! c'.raw = o.getOpType! c.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC, if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/-- `getOperands!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getOperands!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getOperands! c'.raw = o.getOperands! c.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC, if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/-- `getSuccessors!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getSuccessors!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getSuccessors! c'.raw = o.getSuccessors! c.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hC, if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/-- `getNumResults!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getNumResults!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getNumResults! c'.raw = o.getNumResults! c.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC, if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/-- `getResultTypes!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getResultTypes!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getResultTypes! c'.raw = o.getResultTypes! c.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC, if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/-- `getProperties!` is unchanged for an op that is already in bounds before a `WithCreatedOps`. -/
theorem WithCreatedOps.getProperties!_eq {c c' : WfIRContext OpCode} {o : OperationPtr} {T : OpCode}
    (h : WfIRContext.WithCreatedOps c c') (hin : o.InBounds c.raw) :
    o.getProperties! c'.raw T = o.getProperties! c.raw T := by
  induction h with
  | Nil => rfl
  | CreatedOp c₁ c₂ c₃ hstep hcreate ih =>
    obtain ⟨oT, rT, ops, bo, rg, pr, h₁, h₂, h₃, h₄, hC⟩ := hcreate
    have hinc₂ : o.InBounds c₂.raw := hstep.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getProperties!_WfRewriter_createOp_other hC
      (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinc₂), ih hin]

/--
Looking up a value `v` that is in bounds of `ctx` through a `setResultValues?` of a freshly
created operation `o` (not in bounds of `ctx`) is unaffected: such a `v` cannot be a result of `o`.
-/
theorem getVar?_setResultValues?_outer {ctx ctxOuter : WfIRContext OpCode}
    {vs : VariableState ctx} {o : OperationPtr} {resVals : Array RuntimeValue} {inBounds}
    {vs' : VariableState ctx} {v : ValuePtr}
    (hvIn : v.InBounds ctxOuter.raw) (hoNot : ¬ o.InBounds ctxOuter.raw)
    (hset : vs.setResultValues? o resVals inBounds = some vs') :
    vs'.getVar? v = vs.getVar? v := by
  rw [VariableState.getVar?_setResultValues? hset]
  cases v with
  | blockArgument _ => rfl
  | opResult opr =>
    cases opr with
    | mk op' index =>
      simp only
      by_cases hcond : op' = o ∧ index < o.getNumResults! ctx.raw
      · exfalso
        obtain ⟨hopeq, hidx⟩ := hcond
        subst hopeq
        apply hoNot
        grind [OpResultPtr.InBounds, OperationPtr.InBounds, ValuePtr.InBounds]
      · rw [if_neg hcond]

/--
Looking up a result of operation `o₁` through a `setResultValues?` of a different operation `o₂`
is unaffected.
-/
theorem getVar?_setResultValues?_ne {ctx : WfIRContext OpCode} {vs : VariableState ctx}
    {o₁ o₂ : OperationPtr} {k : Nat} {resVals : Array RuntimeValue} {inBounds}
    {vs' : VariableState ctx} (hne : o₁ ≠ o₂)
    (hset : vs.setResultValues? o₂ resVals inBounds = some vs') :
    vs'.getVar? (o₁.getResult k : ValuePtr) = vs.getVar? (o₁.getResult k : ValuePtr) := by
  rw [VariableState.getVar?_setResultValues? hset]
  simp only [OperationPtr.getResult]
  rw [if_neg (by rintro ⟨h, _⟩; exact hne h)]

/-- Resolution of a recipe step whose operands are a single `.created` reference. -/
theorem resolve_one_created {c : WfIRContext OpCode} {acc : Array OperationPtr} {o : OperationPtr}
    {i : Nat} {res : Array {v : ValuePtr // v.InBounds c.raw}} {d : OpDescr}
    (hd : d.operands = #[.created i 0]) (hgeti : acc[i]? = some o)
    (hres : Array.mapM (OperandRef.resolve c acc) d.operands = some res) :
    res.map (·.val) = #[(o.getResult 0 : ValuePtr)] := by
  rw [hd] at hres
  have hsize : res.size = 1 := by
    have := Array.size_eq_of_mapM_eq_some hres; simpa using this.symm
  have hidx := Array.mapM_option_eq_some_implies hres 0 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero] at hidx
  obtain ⟨o', ho', hval⟩ := resolve_created_inv (by simpa using hidx)
  have : o = o' := by rw [hgeti] at ho'; simpa using ho'
  subst this
  apply Array.ext
  · simpa using hsize
  · intro k h1 h2
    have hk : k = 0 := by simp only [Array.size_map, hsize] at h1; omega
    subst hk; simpa using hval

/-- Resolution of a recipe step whose operands are two `.created` references. -/
theorem resolve_two_created {c : WfIRContext OpCode} {acc : Array OperationPtr}
    {o0 o1 : OperationPtr} {i j : Nat} {res : Array {v : ValuePtr // v.InBounds c.raw}} {d : OpDescr}
    (hd : d.operands = #[.created i 0, .created j 0]) (hgeti : acc[i]? = some o0)
    (hgetj : acc[j]? = some o1)
    (hres : Array.mapM (OperandRef.resolve c acc) d.operands = some res) :
    res.map (·.val) = #[(o0.getResult 0 : ValuePtr), (o1.getResult 0 : ValuePtr)] := by
  rw [hd] at hres
  have hsize : res.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hres; simpa using this.symm
  have hidx0 := Array.mapM_option_eq_some_implies hres 0 (by omega)
  have hidx1 := Array.mapM_option_eq_some_implies hres 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hidx0 hidx1
  obtain ⟨a0, ha0, hval0⟩ := resolve_created_inv (by simpa using hidx0)
  obtain ⟨a1, ha1, hval1⟩ := resolve_created_inv (by simpa using hidx1)
  have e0 : o0 = a0 := by rw [hgeti] at ha0; simpa using ha0
  have e1 : o1 = a1 := by rw [hgetj] at ha1; simpa using ha1
  subst e0; subst e1
  apply Array.ext
  · simpa using hsize
  · intro k h1 h2
    simp only [Array.size_map, hsize] at h1
    match k, h1 with
    | 0, _ => simpa using hval0
    | 1, _ => simpa using hval1

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

/--
Conformance of a single-result operation's output: the produced value array `#[v]` conforms to
the result-type array as soon as the result types are `#[ty]` and `v` conforms to `ty`.  This is
the shape of every per-step `RuntimeValue.ArrayConforms` obligation in the lowering proofs below.
-/
theorem _root_.Veir.arrayConforms_singleton {v : RuntimeValue} {ty : TypeAttr}
    {tys : Array TypeAttr} (htys : tys = #[ty]) (hv : v.Conforms ty) :
    RuntimeValue.ArrayConforms #[v] tys := by
  subst htys
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 := by simpa using hi
  subst this; simpa using hv

/--
Operand values of a unary operation: if `op` has the single operand `a` bound to `va` in `vs`,
then `getOperandValues` returns `#[va]`.  Used to thread per-step operand lookups through the
sequential interpretation of the lowering recipes.
-/
theorem getOperandValues_one {ctx : WfIRContext OpCode} {vs : VariableState ctx}
    {op : OperationPtr} {a : ValuePtr} {va : RuntimeValue}
    (ha : op.getOperands! ctx.raw = #[a]) (hva : vs.getVar? a = some va) :
    vs.getOperandValues op = some #[va] := by
  unfold VariableState.getOperandValues
  rw [ha, Array.mapM_eq_mapM_toList]; simp [hva]

/--
Operand values of a binary operation: if `op` has operands `a, b` bound to `va, vb` in `vs`,
then `getOperandValues` returns `#[va, vb]`.
-/
theorem getOperandValues_two {ctx : WfIRContext OpCode} {vs : VariableState ctx}
    {op : OperationPtr} {a b : ValuePtr} {va vb : RuntimeValue}
    (hab : op.getOperands! ctx.raw = #[a, b])
    (hva : vs.getVar? a = some va) (hvb : vs.getVar? b = some vb) :
    vs.getOperandValues op = some #[va, vb] := by
  unfold VariableState.getOperandValues
  rw [hab, Array.mapM_eq_mapM_toList]; simp [hva, hvb]

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
      (op₀.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hResultTypes₀ (by simp [RuntimeValue.Conforms])
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
    refine arrayConforms_singleton hResultTypes₁ ⟨rfl, ?_⟩
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

set_option maxHeartbeats 2000000 in
theorem lowerAdd_preservesSemantics :
    (lowerBinop .add addRecipe).PreservesSemantics
      (lowerBinop_returnOps _ _) (lowerBinop_returnCtxChanges _ _)
      (lowerBinop_returnValuesInBounds _ _) (lowerBinop_returnValues _ _) := by
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern
  intro state hstateEq newState cf hinterp sourceValues hsource state' hstateEq' hrefines
  obtain ⟨operands, props, mt, result, hmatch, hmt, hbw, hbuild, hback, hresIn, rfl⟩ :=
    lowerBinop_some_inv hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Facts from the verifier: operand and result types are the modulus type; modulus is valid.
  have hVerified : op.Verified ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inl rfl)
  obtain ⟨hQpos, hQwidth⟩ := hValid
  -- The verifier and the pattern see the same `!mod_arith.int` type.
  have hmtv : mtv = mt := by
    have := hResTy
    grind [ValuePtr.getType!]
  subst hmtv
  -- Unpack the nine operations created by the recipe.
  rw [addRecipe] at hbuild
  obtain ⟨res₀, ctx₁, op₀, _, _, _, _, hres₀, hC₀, hbuild₁⟩ := buildOps_cons_inv hbuild
  obtain ⟨res₁, ctx₂, op₁, _, _, _, _, hres₁, hC₁, hbuild₂⟩ := buildOps_cons_inv hbuild₁
  obtain ⟨res₂, ctx₃, op₂, _, _, _, _, hres₂, hC₂, hbuild₃⟩ := buildOps_cons_inv hbuild₂
  obtain ⟨res₃, ctx₄, op₃, _, _, _, _, hres₃, hC₃, hbuild₄⟩ := buildOps_cons_inv hbuild₃
  obtain ⟨res₄, ctx₅, op₄, _, _, _, _, hres₄, hC₄, hbuild₅⟩ := buildOps_cons_inv hbuild₄
  obtain ⟨res₅, ctx₆, op₅, _, _, _, _, hres₅, hC₅, hbuild₆⟩ := buildOps_cons_inv hbuild₅
  obtain ⟨res₆, ctx₇, op₆, _, _, _, _, hres₆, hC₆, hbuild₇⟩ := buildOps_cons_inv hbuild₆
  obtain ⟨res₇, ctx₈, op₇, _, _, _, _, hres₇, hC₇, hbuild₈⟩ := buildOps_cons_inv hbuild₇
  obtain ⟨res₈, ctx₉, op₈, _, _, _, _, hres₈, hC₈, hbuild₉⟩ := buildOps_cons_inv hbuild₈
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₉
  -- The recipe result is the final cast operation `op₈`.
  have hresult : op₈ = result := by simpa using hback
  subst hresult
  -- The operand array of `op` has two entries, both in bounds.
  have hOpSize : (op.getOperands! ctx.raw).size = 2 := by grind
  have hFields : ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed ctx).inBounds
  have hlhsIn : operands[0]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]
    exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]
    exact Array.getElem_mem _
  -- Resolve the `.outer` operand arrays of ops 0 and 2 (the casts of `lhs` and `rhs`).
  have hres₀' : res₀.map (·.val) = #[operands[0]!] := by
    have hsize : res₀.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₀; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₀ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  have hres₂' : res₂.map (·.val) = #[operands[1]!] := by
    have hsize : res₂.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₂; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₂ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  -- Resolve the `.created` operand arrays of ops 1, 3, 5, 6, 7, 8.
  have hres₁' : res₁.map (·.val) = #[(op₀.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 0) (by simp [extuiDescr]) (by simp) hres₁
  have hres₃' : res₃.map (·.val) = #[(op₂.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 2) (by simp [extuiDescr]) (by simp) hres₃
  have hres₅' : res₅.map (·.val) = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 1) (j := 3) (by simp [binopDescr]) (by simp) (by simp) hres₅
  have hres₆' : res₆.map (·.val) = #[(op₅.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 5) (j := 4) (by simp [binopDescr]) (by simp) (by simp) hres₆
  have hres₇' : res₇.map (·.val) = #[(op₆.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 6) (by simp [trunciNuwDescr]) (by simp) hres₇
  have hres₈' : res₈.map (·.val) = #[(op₇.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 7) (by simp [castDescr]) (by simp) hres₈
  -- Each created op is fresh in its creation context and in bounds afterwards.
  have hfresh₀ := WfRewriter.createOp_new_inBounds _ hC₀
  have hnf₀ := WfRewriter.createOp_new_not_inBounds _ hC₀
  have hfresh₁ := WfRewriter.createOp_new_inBounds _ hC₁
  have hnf₁ := WfRewriter.createOp_new_not_inBounds _ hC₁
  have hfresh₂ := WfRewriter.createOp_new_inBounds _ hC₂
  have hnf₂ := WfRewriter.createOp_new_not_inBounds _ hC₂
  have hfresh₃ := WfRewriter.createOp_new_inBounds _ hC₃
  have hnf₃ := WfRewriter.createOp_new_not_inBounds _ hC₃
  have hfresh₄ := WfRewriter.createOp_new_inBounds _ hC₄
  have hnf₄ := WfRewriter.createOp_new_not_inBounds _ hC₄
  have hfresh₅ := WfRewriter.createOp_new_inBounds _ hC₅
  have hnf₅ := WfRewriter.createOp_new_not_inBounds _ hC₅
  have hfresh₆ := WfRewriter.createOp_new_inBounds _ hC₆
  have hnf₆ := WfRewriter.createOp_new_not_inBounds _ hC₆
  have hfresh₇ := WfRewriter.createOp_new_inBounds _ hC₇
  have hnf₇ := WfRewriter.createOp_new_not_inBounds _ hC₇
  have hfresh₈ := WfRewriter.createOp_new_inBounds _ hC₈
  have hnf₈ := WfRewriter.createOp_new_not_inBounds _ hC₈
  -- All created ops are in bounds of the final context, by pushing each fresh op forward.
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  -- `op₁` is not in bounds of the original context (needed to thread the `rhs` operand past it).
  have hnfc₁ : ¬ op₁.InBounds ctx.raw := fun h => hnf₁ (mono hC₀ h)
  have hInB₀ : op₀.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀)))))))
  have hInB₁ : op₁.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁))))))
  have hInB₂ : op₂.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂)))))
  have hInB₃ : op₃.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃))))
  have hInB₄ : op₄.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ hfresh₄)))
  have hInB₅ : op₅.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ hfresh₅))
  have hInB₆ : op₆.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ hfresh₆)
  have hInB₇ : op₇.InBounds newCtx.raw :=
    mono hC₈ hfresh₇
  have hInB₈ : op₈.InBounds newCtx.raw := hfresh₈
  -- Pairwise distinctness of the created ops.  `ne` says: if `a` is in bounds of a context where
  -- `b` is freshly created (hence not yet in bounds), then `a ≠ b`.  We only need the distinctness
  -- facts consumed when threading operand values through `setResultValues?` below; each is built
  -- by pushing the earlier op's freshness forward (`mono`) to the context where the later op is new.
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  have d12 : op₁ ≠ op₂ := ne hfresh₁ hnf₂
  have d13 : op₁ ≠ op₃ := ne (mono hC₂ hfresh₁) hnf₃
  have d14 : op₁ ≠ op₄ := ne (mono hC₃ (mono hC₂ hfresh₁)) hnf₄
  have d34 : op₃ ≠ op₄ := ne hfresh₃ hnf₄
  have d45 : op₄ ≠ op₅ := ne hfresh₄ hnf₅
  -- `WithCreatedOps` chains from each creation context to the final one.
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  have w8 : WfIRContext.WithCreatedOps ctx₈ newCtx := buildOps_withCreatedOps hbuild₈
  -- Operation shapes in the final context: reduce to the creating `createOp` step.
  -- Op types.
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .addi := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .remui := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .arith .trunci := by
    rw [WithCreatedOps.getOpType!_eq w8 hfresh₇, OperationPtr.getOpType!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hTy₈ : op₈.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Operands.
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀,
      if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[(op₀.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁,
      if_pos rfl, hres₁']
  have hOperands₂ : op₂.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂,
      if_pos rfl, hres₂']
  have hOperands₃ : op₃.getOperands! newCtx.raw = #[(op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃,
      if_pos rfl, hres₃']
  have hres₄' : res₄.map (·.val) = #[] := by
    have hsz : res₄.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₄; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₄ : op₄.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄,
      if_pos rfl, hres₄']
  have hOperands₅ : op₅.getOperands! newCtx.raw
      = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅,
      if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₅.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆,
      if_pos rfl, hres₆']
  have hOperands₇ : op₇.getOperands! newCtx.raw = #[(op₆.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w8 hfresh₇, OperationPtr.getOperands!_WfRewriter_createOp hC₇,
      if_pos rfl, hres₇']
  have hOperands₈ : op₈.getOperands! newCtx.raw = #[(op₇.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₈, if_pos rfl, hres₈']
  -- Successors (all empty).
  have hSucc₀ : op₀.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w1 hfresh₀, OperationPtr.getSuccessors!_WfRewriter_createOp hC₀,
      if_pos rfl]
  have hSucc₁ : op₁.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w2 hfresh₁, OperationPtr.getSuccessors!_WfRewriter_createOp hC₁,
      if_pos rfl]
  have hSucc₂ : op₂.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w3 hfresh₂, OperationPtr.getSuccessors!_WfRewriter_createOp hC₂,
      if_pos rfl]
  have hSucc₃ : op₃.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w4 hfresh₃, OperationPtr.getSuccessors!_WfRewriter_createOp hC₃,
      if_pos rfl]
  have hSucc₄ : op₄.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w5 hfresh₄, OperationPtr.getSuccessors!_WfRewriter_createOp hC₄,
      if_pos rfl]
  have hSucc₅ : op₅.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w6 hfresh₅, OperationPtr.getSuccessors!_WfRewriter_createOp hC₅,
      if_pos rfl]
  have hSucc₆ : op₆.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w7 hfresh₆, OperationPtr.getSuccessors!_WfRewriter_createOp hC₆,
      if_pos rfl]
  have hSucc₇ : op₇.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w8 hfresh₇, OperationPtr.getSuccessors!_WfRewriter_createOp hC₇,
      if_pos rfl]
  have hSucc₈ : op₈.getSuccessors! newCtx.raw = #[] := by
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hC₈, if_pos rfl]
  -- Number of results (all one).
  have hNumRes₀ : op₀.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w1 hfresh₀, OperationPtr.getNumResults!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hNumRes₁ : op₁.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w2 hfresh₁, OperationPtr.getNumResults!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hNumRes₂ : op₂.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w3 hfresh₂, OperationPtr.getNumResults!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hNumRes₃ : op₃.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w4 hfresh₃, OperationPtr.getNumResults!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hNumRes₄ : op₄.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w5 hfresh₄, OperationPtr.getNumResults!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hNumRes₅ : op₅.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w6 hfresh₅, OperationPtr.getNumResults!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hNumRes₆ : op₆.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w7 hfresh₆, OperationPtr.getNumResults!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hNumRes₇ : op₇.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w8 hfresh₇, OperationPtr.getNumResults!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hNumRes₈ : op₈.getNumResults! newCtx.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Result types.
  have hRT₀ : op₀.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w1 hfresh₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w8 hfresh₇, OperationPtr.getResultTypes!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hRT₈ : op₈.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Properties (only the ones we need to evaluate the interpreter).
  have hP₁ : op₁.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w2 hfresh₁]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁ (operation := op₁)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk (mtv.modulus.type.bitwidth + 1)) } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .addi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  have hP₇ : op₇.getProperties! newCtx.raw (.arith .trunci) = { nsw := false, nuw := true } := by
    rw [WithCreatedOps.getProperties!_eq w8 hfresh₇]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₇ (operation := op₇)
    rw [if_pos rfl] at h2; exact h2
  -- ## Source interpretation
  -- Each operand of `op` has the modulus type.
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  -- Normalise the source-interpretation hypothesis.
  have hinterp' : interpretOp op state opInBounds = some (.ok (newState, cf)) := by
    simpa [liftM, monadLift, MonadLift.monadLift] using hinterp
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp'
  have hOpArr : op.getOperands! ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  -- The two source operand values are concrete canonical integers.
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  -- Concrete value and canonicity of the first operand.
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) ∧
      (x.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) ∧
      (y.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  -- Hence `srcOperandVals = #[.int N (.val x), .int N (.val y)]`.
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
      RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  -- The (single) result type of `op` is the modulus type.
  have hSrcNumRes : (op.getResultTypes! ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! ctx.raw)[0]? = some ⟨.modArithType mtv, by rfl⟩ := by
    have h0 : (op.getResultTypes! ctx.raw)[0]?
        = some ((op.getResultTypes! ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  -- Evaluate the source `mod_arith.add`.
  have hSrcEval' : interpretOp' (.mod_arith .add)
      (op.getProperties! ctx.raw (.mod_arith .add)) (op.getResultTypes! ctx.raw) srcOperandVals
      (op.getSuccessors! ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.add mtv.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mtv.modulus.type.bitwidth
      (.val (Data.ModArith.add mtv.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  -- The single source result value.
  have hNumResultsNB : op.getNumResults ctx.raw opInBounds = 1 := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opInBounds]; exact hNumResults
  have hGetResults : op.getResults ctx.raw = #[(op.getResult 0 : ValuePtr)] := by
    unfold OperationPtr.getResults
    rw [hNumResultsNB]
    simp [Array.range_succ, show Array.range 0 = #[] from by simp [Array.range]]
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.add mtv.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hSourceVals : sourceValues
      = #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.add mtv.modulus.value x y))] := by
    rw [hGetResults, Array.mapM_eq_mapM_toList] at hsource
    simp [hvSrc] at hsource
    exact hsource.symm
  -- ## Refinement transfer: the operands have the same concrete value in the target state.
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  -- The mapping is the identity on `lhs`/`rhs` because they are operands (not results) of `op`.
  have hLhsMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hLhsNotRes : operands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes : operands[1]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hMapLhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[0]!, hlhsIn⟩ : ValuePtr) = operands[0]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hLhsNotRes]
  have hMapRhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[1]!, hrhsIn⟩ : ValuePtr) = operands[1]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hRhsNotRes]
  -- Hence the target state binds the operands to the same concrete values.
  have hTLhs : state'.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    rw [hMapLhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  -- ## Width side conditions and the pipeline arithmetic core.
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  have hqm : 2 * mtv.modulus.value ≤ 2 ^ (mtv.modulus.type.bitwidth + 1) :=
    Data.ModArith.two_mul_modulus_le_two_pow_succ hN1 hQwidth
  have hnm : mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth + 1 := by omega
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  -- The pipeline result and its canonicity.
  have hPipeEq : ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth = Data.ModArith.add mtv.modulus.value x y :=
    Data.ModArith.addPipeline_eq_add hQpos hqm hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).toNat : Int)
        < mtv.modulus.value :=
    Data.ModArith.toNat_addPipeline_lt hQpos hqm hnm hxlt hylt
  -- ## Target interpretation: step through the nine created operations.
  -- Notation for the intermediate `BitVec`s flowing through the pipeline.
  -- Step op₀: cast `lhs : iN`.  Value: `.int N (.val x)`.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₀ hTLhs
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₀ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  -- Lookups in `vs₁`.
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnf₀ hSet₀]; exact hTRhs
  -- Step op₁: `extui` of `x` to width `M = N + 1`.  Value: `.int M (.val (x.zeroExtend M))`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₁ hv₁_0
  have hEval₁ : interpretOp' (.arith .extui) (op₁.getProperties! newCtx.raw (.arith .extui))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT₁, hP₁]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth + 1 ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₁.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₁ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  -- Step op₂: cast `rhs : iN`.  Value: `.int N (.val y)`.
  have hv₂_rhs : vs₂.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnfc₁ hSet₁]; exact hv₁_rhs
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₂ hv₂_rhs
  have hEval₂ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₂.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₂.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₂]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₂.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₂ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  -- Step op₃: `extui` of `y` to width `M`.
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₃ hv₃_2
  have hEval₃ : interpretOp' (.arith .extui) (op₃.getProperties! newCtx.raw (.arith .extui))
      (op₃.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT₃, hP₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth + 1 ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₃.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₃ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  -- Step op₄: the modulus constant `q : iM`.
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp
  have hEval₄ : interpretOp' (.arith .constant) (op₄.getProperties! newCtx.raw (.arith .constant))
      (op₄.getResultTypes! newCtx.raw) #[] (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))],
          state'.memory, none)) := by
    rw [hRT₄, hP₄]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₄.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₄ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  -- Step op₅: `addi` of the two extended operands.
  have hv₂_1 : vs₂.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  have hv₅_1 : vs₅.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [getVar?_setResultValues?_ne d14 hSet₄, getVar?_setResultValues?_ne d13 hSet₃,
      getVar?_setResultValues?_ne d12 hSet₂]; exact hv₂_1
  have hv₅_3 : vs₅.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [getVar?_setResultValues?_ne d34 hSet₄]; exact hv₄_3
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))] :=
      getOperandValues_two hOperands₅ hv₅_1 hv₅_3
  have hEval₅ : interpretOp' (.arith .addi) (op₅.getProperties! newCtx.raw (.arith .addi))
      (op₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hP₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₅.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₅ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  -- Step op₆: `remui` reducing modulo `q`.
  have hv₅_4 : vs₅.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]; exact hv₅_4
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + y.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))] :=
      getOperandValues_two hOperands₆ hv₆_5 hv₆_4
  have hEval₆ : interpretOp' (.arith .remui) (op₆.getProperties! newCtx.raw (.arith .remui))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + y.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))],
          state'.memory, none)) := by
    have hqne : BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        ≠ 0#(mtv.modulus.type.bitwidth + 1) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := mtv.modulus.type.bitwidth + 1) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₆.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₆ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  -- Step op₇: `trunci` (nuw) back to width `N`.
  have hv₇_6 : vs₇.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))] :=
      getOperandValues_one hOperands₇ hv₇_6
  -- No-poison side condition for the `nuw` truncation, from canonicity.
  have hNoPoison : (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth).zeroExtend (mtv.modulus.type.bitwidth + 1)
        = (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    -- canonicity: `remM.toNat < q ≤ 2^N`.
    have hcast : (2:Int)^mtv.modulus.type.bitwidth = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval₇ : interpretOp' (.arith .trunci) (op₇.getProperties! newCtx.raw (.arith .trunci))
      (op₇.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT₇, hP₇]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth ≥ mtv.modulus.type.bitwidth + 1) from by omega)]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₇.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₇ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  -- Step op₈: cast the result back to `!mod_arith.int`.
  have hv₈_7 : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
  have hOpVals₈ : (InterpreterState.mk vs₈ state'.memory).variables.getOperandValues op₈
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))] :=
      getOperandValues_one hOperands₈ hv₈_7
  have hEval₈ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₈.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₈.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₈.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.add mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₈, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₈ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.add mtv.modulus.value x y))]
      (op₈.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₈ ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_add hQpos hQle⟩
  obtain ⟨vs₉, hSet₈, hStep₈⟩ := interpretOp_step (inB := hInB₈) hTy₈ hOpVals₈ hEval₈ hConf₈
  -- ## Assemble the nine steps into the full target interpretation.
  refine ⟨⟨vs₉, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁, op₂, op₃, op₄, op₅, op₆, op₇, op₈] state' _
      = liftM (some (⟨vs₉, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep₀]
    rw [interpretOpList_cons]; simp only [hStep₁]
    rw [interpretOpList_cons]; simp only [hStep₂]
    rw [interpretOpList_cons]; simp only [hStep₃]
    rw [interpretOpList_cons]; simp only [hStep₄]
    rw [interpretOpList_cons]; simp only [hStep₅]
    rw [interpretOpList_cons]; simp only [hStep₆]
    rw [interpretOpList_cons]; simp only [hStep₇]
    rw [interpretOpList_cons]; simp only [hStep₈]
    simp [liftM, monadLift, MonadLift.monadLift]
  · simpa using hMemEq
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (Data.ModArith.add mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₉ : vs₉.getVar? (op₈.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.add mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₈]; simp [hNumRes₈]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₉]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]

set_option maxHeartbeats 2000000 in
theorem lowerSub_preservesSemantics :
    (lowerBinop .sub subRecipe).PreservesSemantics
      (lowerBinop_returnOps _ _) (lowerBinop_returnCtxChanges _ _)
      (lowerBinop_returnValuesInBounds _ _) (lowerBinop_returnValues _ _) := by
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern
  intro state hstateEq newState cf hinterp sourceValues hsource state' hstateEq' hrefines
  obtain ⟨operands, props, mt, result, hmatch, hmt, hbw, hbuild, hback, hresIn, rfl⟩ :=
    lowerBinop_some_inv hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  have hVerified : op.Verified ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inr (Or.inl rfl))
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by have := hResTy; grind [ValuePtr.getType!]
  subst hmtv
  rw [subRecipe] at hbuild
  obtain ⟨res₀, ctx₁, op₀, _, _, _, _, hres₀, hC₀, hbuild₁⟩ := buildOps_cons_inv hbuild
  obtain ⟨res₁, ctx₂, op₁, _, _, _, _, hres₁, hC₁, hbuild₂⟩ := buildOps_cons_inv hbuild₁
  obtain ⟨res₂, ctx₃, op₂, _, _, _, _, hres₂, hC₂, hbuild₃⟩ := buildOps_cons_inv hbuild₂
  obtain ⟨res₃, ctx₄, op₃, _, _, _, _, hres₃, hC₃, hbuild₄⟩ := buildOps_cons_inv hbuild₃
  obtain ⟨res₄, ctx₅, op₄, _, _, _, _, hres₄, hC₄, hbuild₅⟩ := buildOps_cons_inv hbuild₄
  obtain ⟨res₅, ctx₆, op₅, _, _, _, _, hres₅, hC₅, hbuild₆⟩ := buildOps_cons_inv hbuild₅
  obtain ⟨res₆, ctx₇, op₆, _, _, _, _, hres₆, hC₆, hbuild₇⟩ := buildOps_cons_inv hbuild₆
  obtain ⟨res₇, ctx₈, op₇, _, _, _, _, hres₇, hC₇, hbuild₈⟩ := buildOps_cons_inv hbuild₇
  obtain ⟨res₈, ctx₉, op₈, _, _, _, _, hres₈, hC₈, hbuild₉⟩ := buildOps_cons_inv hbuild₈
  obtain ⟨res₉, ctx₁₀, op₉, _, _, _, _, hres₉, hC₉, hbuild₁₀⟩ := buildOps_cons_inv hbuild₉
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₁₀
  have hresult : op₉ = result := by simpa using hback
  subst hresult
  have hOpSize : (op.getOperands! ctx.raw).size = 2 := by grind
  have hFields : ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed ctx).inBounds
  have hlhsIn : operands[0]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]; exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]; exact Array.getElem_mem _
  have hres₀' : res₀.map (·.val) = #[operands[0]!] := by
    have hsize : res₀.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₀; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₀ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  have hres₂' : res₂.map (·.val) = #[operands[1]!] := by
    have hsize : res₂.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₂; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₂ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  have hres₁' : res₁.map (·.val) = #[(op₀.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 0) (by simp [extuiDescr]) (by simp) hres₁
  have hres₃' : res₃.map (·.val) = #[(op₂.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 2) (by simp [extuiDescr]) (by simp) hres₃
  have hres₅' : res₅.map (·.val) = #[(op₁.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 1) (j := 4) (by simp [binopDescr]) (by simp) (by simp) hres₅
  have hres₆' : res₆.map (·.val) = #[(op₅.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 5) (j := 3) (by simp [binopDescr]) (by simp) (by simp) hres₆
  have hres₇' : res₇.map (·.val) = #[(op₆.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 6) (j := 4) (by simp [binopDescr]) (by simp) (by simp) hres₇
  have hres₈' : res₈.map (·.val) = #[(op₇.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 7) (by simp [trunciNuwDescr]) (by simp) hres₈
  have hres₉' : res₉.map (·.val) = #[(op₈.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 8) (by simp [castDescr]) (by simp) hres₉
  have hfresh₀ := WfRewriter.createOp_new_inBounds _ hC₀
  have hnf₀ := WfRewriter.createOp_new_not_inBounds _ hC₀
  have hfresh₁ := WfRewriter.createOp_new_inBounds _ hC₁
  have hnf₁ := WfRewriter.createOp_new_not_inBounds _ hC₁
  have hfresh₂ := WfRewriter.createOp_new_inBounds _ hC₂
  have hnf₂ := WfRewriter.createOp_new_not_inBounds _ hC₂
  have hfresh₃ := WfRewriter.createOp_new_inBounds _ hC₃
  have hnf₃ := WfRewriter.createOp_new_not_inBounds _ hC₃
  have hfresh₄ := WfRewriter.createOp_new_inBounds _ hC₄
  have hnf₄ := WfRewriter.createOp_new_not_inBounds _ hC₄
  have hfresh₅ := WfRewriter.createOp_new_inBounds _ hC₅
  have hnf₅ := WfRewriter.createOp_new_not_inBounds _ hC₅
  have hfresh₆ := WfRewriter.createOp_new_inBounds _ hC₆
  have hnf₆ := WfRewriter.createOp_new_not_inBounds _ hC₆
  have hfresh₇ := WfRewriter.createOp_new_inBounds _ hC₇
  have hnf₇ := WfRewriter.createOp_new_not_inBounds _ hC₇
  have hfresh₈ := WfRewriter.createOp_new_inBounds _ hC₈
  have hnf₈ := WfRewriter.createOp_new_not_inBounds _ hC₈
  have hfresh₉ := WfRewriter.createOp_new_inBounds _ hC₉
  have hnf₉ := WfRewriter.createOp_new_not_inBounds _ hC₉
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  -- `op₀`/`op₁` are not in bounds of the original context (needed to thread `rhs` past them).
  have hnfc₀ : ¬ op₀.InBounds ctx.raw := hnf₀
  have hnfc₁ : ¬ op₁.InBounds ctx.raw := fun h => hnf₁ (mono hC₀ h)
  have hInB₀ : op₀.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀))))))))
  have hInB₁ : op₁.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁)))))))
  have hInB₂ : op₂.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂))))))
  have hInB₃ : op₃.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃)))))
  have hInB₄ : op₄.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ hfresh₄))))
  have hInB₅ : op₅.InBounds newCtx.raw :=
    mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ hfresh₅)))
  have hInB₆ : op₆.InBounds newCtx.raw := mono hC₉ (mono hC₈ (mono hC₇ hfresh₆))
  have hInB₇ : op₇.InBounds newCtx.raw := mono hC₉ (mono hC₈ hfresh₇)
  have hInB₈ : op₈.InBounds newCtx.raw := mono hC₉ hfresh₈
  have hInB₉ : op₉.InBounds newCtx.raw := hfresh₉
  -- Pairwise distinctness of the created ops.  `ne` says: if `a` is in bounds of a context where
  -- `b` is freshly created (hence not yet in bounds), then `a ≠ b`.  We only need the distinctness
  -- facts consumed when threading operand values through `setResultValues?` below; each is built
  -- by pushing the earlier op's freshness forward (`mono`) to the context where the later op is new.
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  have d12 : op₁ ≠ op₂ := ne hfresh₁ hnf₂
  have d13 : op₁ ≠ op₃ := ne (mono hC₂ hfresh₁) hnf₃
  have d14 : op₁ ≠ op₄ := ne (mono hC₃ (mono hC₂ hfresh₁)) hnf₄
  have d34 : op₃ ≠ op₄ := ne hfresh₃ hnf₄
  have d35 : op₃ ≠ op₅ := ne (mono hC₄ hfresh₃) hnf₅
  have d45 : op₄ ≠ op₅ := ne hfresh₄ hnf₅
  have d46 : op₄ ≠ op₆ := ne (mono hC₅ hfresh₄) hnf₆
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  have w8 : WfIRContext.WithCreatedOps ctx₈ newCtx := buildOps_withCreatedOps hbuild₈
  have w9 : WfIRContext.WithCreatedOps ctx₉ newCtx := buildOps_withCreatedOps hbuild₉
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀, if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁, if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂, if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃, if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄, if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .addi := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅, if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆, if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .arith .remui := by
    rw [WithCreatedOps.getOpType!_eq w8 hfresh₇, OperationPtr.getOpType!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  have hTy₈ : op₈.getOpType! newCtx.raw = .arith .trunci := by
    rw [WithCreatedOps.getOpType!_eq w9 hfresh₈, OperationPtr.getOpType!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  have hTy₉ : op₉.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀, if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[(op₀.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁, if_pos rfl, hres₁']
  have hOperands₂ : op₂.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂, if_pos rfl, hres₂']
  have hOperands₃ : op₃.getOperands! newCtx.raw = #[(op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃, if_pos rfl, hres₃']
  have hres₄' : res₄.map (·.val) = #[] := by
    have hsz : res₄.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₄; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₄ : op₄.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄, if_pos rfl, hres₄']
  have hOperands₅ : op₅.getOperands! newCtx.raw
      = #[(op₁.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅, if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₅.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆, if_pos rfl, hres₆']
  have hOperands₇ : op₇.getOperands! newCtx.raw
      = #[(op₆.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w8 hfresh₇, OperationPtr.getOperands!_WfRewriter_createOp hC₇, if_pos rfl, hres₇']
  have hOperands₈ : op₈.getOperands! newCtx.raw = #[(op₇.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w9 hfresh₈, OperationPtr.getOperands!_WfRewriter_createOp hC₈, if_pos rfl, hres₈']
  have hOperands₉ : op₉.getOperands! newCtx.raw = #[(op₈.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₉, if_pos rfl, hres₉']
  have hNumRes₀ : op₀.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w1 hfresh₀, OperationPtr.getNumResults!_WfRewriter_createOp hC₀, if_pos rfl]; rfl
  have hNumRes₁ : op₁.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w2 hfresh₁, OperationPtr.getNumResults!_WfRewriter_createOp hC₁, if_pos rfl]; rfl
  have hNumRes₂ : op₂.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w3 hfresh₂, OperationPtr.getNumResults!_WfRewriter_createOp hC₂, if_pos rfl]; rfl
  have hNumRes₃ : op₃.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w4 hfresh₃, OperationPtr.getNumResults!_WfRewriter_createOp hC₃, if_pos rfl]; rfl
  have hNumRes₄ : op₄.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w5 hfresh₄, OperationPtr.getNumResults!_WfRewriter_createOp hC₄, if_pos rfl]; rfl
  have hNumRes₅ : op₅.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w6 hfresh₅, OperationPtr.getNumResults!_WfRewriter_createOp hC₅, if_pos rfl]; rfl
  have hNumRes₆ : op₆.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w7 hfresh₆, OperationPtr.getNumResults!_WfRewriter_createOp hC₆, if_pos rfl]; rfl
  have hNumRes₇ : op₇.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w8 hfresh₇, OperationPtr.getNumResults!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  have hNumRes₈ : op₈.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w9 hfresh₈, OperationPtr.getNumResults!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  have hNumRes₉ : op₉.getNumResults! newCtx.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hRT₀ : op₀.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w1 hfresh₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₀, if_pos rfl]; rfl
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁, if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂, if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃, if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄, if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅, if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆, if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[(IntegerType.mk (mtv.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w8 hfresh₇, OperationPtr.getResultTypes!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  have hRT₈ : op₈.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w9 hfresh₈, OperationPtr.getResultTypes!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  have hRT₉ : op₉.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hP₁ : op₁.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w2 hfresh₁]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁ (operation := op₁)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk (mtv.modulus.type.bitwidth + 1)) } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .addi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  have hP₆ : op₆.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w7 hfresh₆]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₆ (operation := op₆)
    rw [if_pos rfl] at h2; exact h2
  have hP₈ : op₈.getProperties! newCtx.raw (.arith .trunci) = { nsw := false, nuw := true } := by
    rw [WithCreatedOps.getProperties!_eq w9 hfresh₈]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₈ (operation := op₈)
    rw [if_pos rfl] at h2; exact h2
  have hinterp' : interpretOp op state opInBounds = some (.ok (newState, cf)) := by
    simpa [liftM, monadLift, MonadLift.monadLift] using hinterp
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp'
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  have hOpArr : op.getOperands! ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) ∧
      (x.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) ∧
      (y.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
      RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  have hSrcNumRes : (op.getResultTypes! ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! ctx.raw)[0]? = some ⟨.modArithType mtv, by rfl⟩ := by
    have h0 : (op.getResultTypes! ctx.raw)[0]?
        = some ((op.getResultTypes! ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  have hSrcEval' : interpretOp' (.mod_arith .sub)
      (op.getProperties! ctx.raw (.mod_arith .sub)) (op.getResultTypes! ctx.raw) srcOperandVals
      (op.getSuccessors! ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.sub mtv.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mtv.modulus.type.bitwidth
      (.val (Data.ModArith.sub mtv.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  have hNumResultsNB : op.getNumResults ctx.raw opInBounds = 1 := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opInBounds]; exact hNumResults
  have hGetResults : op.getResults ctx.raw = #[(op.getResult 0 : ValuePtr)] := by
    unfold OperationPtr.getResults
    rw [hNumResultsNB]
    simp [Array.range_succ, show Array.range 0 = #[] from by simp [Array.range]]
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.sub mtv.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hSourceVals : sourceValues
      = #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.sub mtv.modulus.value x y))] := by
    rw [hGetResults, Array.mapM_eq_mapM_toList] at hsource
    simp [hvSrc] at hsource
    exact hsource.symm
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  have hLhsMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hLhsNotRes : operands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes : operands[1]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hMapLhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[0]!, hlhsIn⟩ : ValuePtr) = operands[0]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hLhsNotRes]
  have hMapRhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[1]!, hrhsIn⟩ : ValuePtr) = operands[1]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hRhsNotRes]
  have hTLhs : state'.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    rw [hMapLhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  have hqm : 2 * mtv.modulus.value ≤ 2 ^ (mtv.modulus.type.bitwidth + 1) :=
    Data.ModArith.two_mul_modulus_le_two_pow_succ hN1 hQwidth
  have hnm : mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth + 1 := by omega
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  have hPipeEq : ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth = Data.ModArith.sub mtv.modulus.value x y :=
    Data.ModArith.subPipeline_eq_sub hQpos hqm hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).toNat : Int)
        < mtv.modulus.value :=
    Data.ModArith.toNat_subPipeline_lt hQpos hqm hnm hxlt hylt
  -- Step op₀: cast `lhs : iN`.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₀ hTLhs
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw) #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₀ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnfc₀ hSet₀]; exact hTRhs
  -- Step op₁: `extui` of `x` to width `M`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₁ hv₁_0
  have hEval₁ : interpretOp' (.arith .extui) (op₁.getProperties! newCtx.raw (.arith .extui))
      (op₁.getResultTypes! newCtx.raw) #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT₁, hP₁]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth + 1 ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))] (op₁.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₁ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  -- Step op₂: cast `rhs : iN`.
  have hv₂_rhs : vs₂.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnfc₁ hSet₁]; exact hv₁_rhs
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₂ hv₂_rhs
  have hEval₂ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₂.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₂.getResultTypes! newCtx.raw) #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₂]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₂.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₂ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  -- Step op₃: `extui` of `y` to width `M`.
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₃ hv₃_2
  have hEval₃ : interpretOp' (.arith .extui) (op₃.getProperties! newCtx.raw (.arith .extui))
      (op₃.getResultTypes! newCtx.raw) #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT₃, hP₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth + 1 ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))] (op₃.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₃ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  -- Step op₄: the modulus constant.
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp
  have hEval₄ : interpretOp' (.arith .constant) (op₄.getProperties! newCtx.raw (.arith .constant))
      (op₄.getResultTypes! newCtx.raw) #[] (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))],
          state'.memory, none)) := by
    rw [hRT₄, hP₄]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₄.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₄ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  -- Step op₅: `addi` computing `x_ext + q`.
  have hv₂_1 : vs₂.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  have hv₅_1 : vs₅.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [getVar?_setResultValues?_ne d14 hSet₄, getVar?_setResultValues?_ne d13 hSet₃,
      getVar?_setResultValues?_ne d12 hSet₂]; exact hv₂_1
  have hv₅_4 : vs₅.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))] :=
      getOperandValues_two hOperands₅ hv₅_1 hv₅_4
  have hEval₅ : interpretOp' (.arith .addi) (op₅.getProperties! newCtx.raw (.arith .addi))
      (op₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))],
          state'.memory, none)) := by
    rw [hP₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₅.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₅ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  -- Step op₆: `subi` computing `(x_ext + q) - y_ext`.
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  have hv₆_3 : vs₆.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [getVar?_setResultValues?_ne d35 hSet₅, getVar?_setResultValues?_ne d34 hSet₄]; exact hv₄_3
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value)),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))] :=
      getOperandValues_two hOperands₆ hv₆_5 hv₆_3
  have hEval₆ : interpretOp' (.arith .subi) (op₆.getProperties! newCtx.raw (.arith .subi))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value)),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hP₆]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1)))]
      (op₆.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₆ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  -- Step op₇: `remui` reducing modulo `q`.
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]; exact hv₅_4
  have hv₇_6 : vs₇.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  have hv₇_4 : vs₇.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d46 hSet₆]; exact hv₆_4
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
              - y.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))] :=
      getOperandValues_two hOperands₇ hv₇_6 hv₇_4
  have hEval₇ : interpretOp' (.arith .remui) (op₇.getProperties! newCtx.raw (.arith .remui))
      (op₇.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
              + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
              - y.zeroExtend (mtv.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))],
          state'.memory, none)) := by
    have hqne : BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        ≠ 0#(mtv.modulus.type.bitwidth + 1) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := mtv.modulus.type.bitwidth + 1) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₇.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₇ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  -- Step op₈: `trunci` (nuw) back to width `N`.
  have hv₈_7 : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
  have hOpVals₈ : (InterpreterState.mk vs₈ state'.memory).variables.getOperandValues op₈
      = some #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))] :=
      getOperandValues_one hOperands₈ hv₈_7
  have hNoPoison : (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth).zeroExtend (mtv.modulus.type.bitwidth + 1)
        = (x.zeroExtend (mtv.modulus.type.bitwidth + 1)
        + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
        - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    have hcast : (2:Int)^mtv.modulus.type.bitwidth = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval₈ : interpretOp' (.arith .trunci) (op₈.getProperties! newCtx.raw (.arith .trunci))
      (op₈.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (mtv.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value))]
      (op₈.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT₈, hP₈]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth ≥ mtv.modulus.type.bitwidth + 1) from by omega)]
  have hConf₈ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₈.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₈ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₉, hSet₈, hStep₈⟩ := interpretOp_step (inB := hInB₈) hTy₈ hOpVals₈ hEval₈ hConf₈
  -- Step op₉: cast the result back to `!mod_arith.int`.
  have hv₉_8 : vs₉.getVar? (op₈.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet₈]; simp [hNumRes₈]
  have hOpVals₉ : (InterpreterState.mk vs₉ state'.memory).variables.getOperandValues op₉
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))] :=
      getOperandValues_one hOperands₉ hv₉_8
  have hEval₉ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₉.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₉.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (mtv.modulus.type.bitwidth + 1)
            + BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value
            - y.zeroExtend (mtv.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mtv.modulus.type.bitwidth + 1) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₉.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.sub mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₉, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₉ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.sub mtv.modulus.value x y))]
      (op₉.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₉ ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_sub hQpos hQle⟩
  obtain ⟨vs₁₀, hSet₉, hStep₉⟩ := interpretOp_step (inB := hInB₉) hTy₉ hOpVals₉ hEval₉ hConf₉
  -- ## Assemble.
  refine ⟨⟨vs₁₀, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁, op₂, op₃, op₄, op₅, op₆, op₇, op₈, op₉] state' _
      = liftM (some (⟨vs₁₀, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep₀]
    rw [interpretOpList_cons]; simp only [hStep₁]
    rw [interpretOpList_cons]; simp only [hStep₂]
    rw [interpretOpList_cons]; simp only [hStep₃]
    rw [interpretOpList_cons]; simp only [hStep₄]
    rw [interpretOpList_cons]; simp only [hStep₅]
    rw [interpretOpList_cons]; simp only [hStep₆]
    rw [interpretOpList_cons]; simp only [hStep₇]
    rw [interpretOpList_cons]; simp only [hStep₈]
    rw [interpretOpList_cons]; simp only [hStep₉]
    simp [liftM, monadLift, MonadLift.monadLift]
  · simpa using hMemEq
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (Data.ModArith.sub mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₁₀ : vs₁₀.getVar? (op₉.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.sub mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₉]; simp [hNumRes₉]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₁₀]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]


set_option maxHeartbeats 2000000 in
theorem lowerMul_preservesSemantics :
    (lowerBinop .mul mulRecipe).PreservesSemantics
      (lowerBinop_returnOps _ _) (lowerBinop_returnCtxChanges _ _)
      (lowerBinop_returnValuesInBounds _ _) (lowerBinop_returnValues _ _) := by
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern
  intro state hstateEq newState cf hinterp sourceValues hsource state' hstateEq' hrefines
  obtain ⟨operands, props, mt, result, hmatch, hmt, hbw, hbuild, hback, hresIn, rfl⟩ :=
    lowerBinop_some_inv hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Facts from the verifier: operand and result types are the modulus type; modulus is valid.
  have hVerified : op.Verified ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inr (Or.inr rfl))
  obtain ⟨hQpos, hQwidth⟩ := hValid
  -- The verifier and the pattern see the same `!mod_arith.int` type.
  have hmtv : mtv = mt := by
    have := hResTy
    grind [ValuePtr.getType!]
  subst hmtv
  -- Unpack the nine operations created by the recipe.
  rw [mulRecipe] at hbuild
  obtain ⟨res₀, ctx₁, op₀, _, _, _, _, hres₀, hC₀, hbuild₁⟩ := buildOps_cons_inv hbuild
  obtain ⟨res₁, ctx₂, op₁, _, _, _, _, hres₁, hC₁, hbuild₂⟩ := buildOps_cons_inv hbuild₁
  obtain ⟨res₂, ctx₃, op₂, _, _, _, _, hres₂, hC₂, hbuild₃⟩ := buildOps_cons_inv hbuild₂
  obtain ⟨res₃, ctx₄, op₃, _, _, _, _, hres₃, hC₃, hbuild₄⟩ := buildOps_cons_inv hbuild₃
  obtain ⟨res₄, ctx₅, op₄, _, _, _, _, hres₄, hC₄, hbuild₅⟩ := buildOps_cons_inv hbuild₄
  obtain ⟨res₅, ctx₆, op₅, _, _, _, _, hres₅, hC₅, hbuild₆⟩ := buildOps_cons_inv hbuild₅
  obtain ⟨res₆, ctx₇, op₆, _, _, _, _, hres₆, hC₆, hbuild₇⟩ := buildOps_cons_inv hbuild₆
  obtain ⟨res₇, ctx₈, op₇, _, _, _, _, hres₇, hC₇, hbuild₈⟩ := buildOps_cons_inv hbuild₇
  obtain ⟨res₈, ctx₉, op₈, _, _, _, _, hres₈, hC₈, hbuild₉⟩ := buildOps_cons_inv hbuild₈
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₉
  -- The recipe result is the final cast operation `op₈`.
  have hresult : op₈ = result := by simpa using hback
  subst hresult
  -- The operand array of `op` has two entries, both in bounds.
  have hOpSize : (op.getOperands! ctx.raw).size = 2 := by grind
  have hFields : ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed ctx).inBounds
  have hlhsIn : operands[0]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]
    exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]
    exact Array.getElem_mem _
  -- Resolve the `.outer` operand arrays of ops 0 and 2 (the casts of `lhs` and `rhs`).
  have hres₀' : res₀.map (·.val) = #[operands[0]!] := by
    have hsize : res₀.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₀; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₀ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  have hres₂' : res₂.map (·.val) = #[operands[1]!] := by
    have hsize : res₂.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₂; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₂ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  -- Resolve the `.created` operand arrays of ops 1, 3, 5, 6, 7, 8.
  have hres₁' : res₁.map (·.val) = #[(op₀.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 0) (by simp [extuiDescr]) (by simp) hres₁
  have hres₃' : res₃.map (·.val) = #[(op₂.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 2) (by simp [extuiDescr]) (by simp) hres₃
  have hres₅' : res₅.map (·.val) = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 1) (j := 3) (by simp [binopDescr]) (by simp) (by simp) hres₅
  have hres₆' : res₆.map (·.val) = #[(op₅.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 5) (j := 4) (by simp [binopDescr]) (by simp) (by simp) hres₆
  have hres₇' : res₇.map (·.val) = #[(op₆.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 6) (by simp [trunciNuwDescr]) (by simp) hres₇
  have hres₈' : res₈.map (·.val) = #[(op₇.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 7) (by simp [castDescr]) (by simp) hres₈
  -- Each created op is fresh in its creation context and in bounds afterwards.
  have hfresh₀ := WfRewriter.createOp_new_inBounds _ hC₀
  have hnf₀ := WfRewriter.createOp_new_not_inBounds _ hC₀
  have hfresh₁ := WfRewriter.createOp_new_inBounds _ hC₁
  have hnf₁ := WfRewriter.createOp_new_not_inBounds _ hC₁
  have hfresh₂ := WfRewriter.createOp_new_inBounds _ hC₂
  have hnf₂ := WfRewriter.createOp_new_not_inBounds _ hC₂
  have hfresh₃ := WfRewriter.createOp_new_inBounds _ hC₃
  have hnf₃ := WfRewriter.createOp_new_not_inBounds _ hC₃
  have hfresh₄ := WfRewriter.createOp_new_inBounds _ hC₄
  have hnf₄ := WfRewriter.createOp_new_not_inBounds _ hC₄
  have hfresh₅ := WfRewriter.createOp_new_inBounds _ hC₅
  have hnf₅ := WfRewriter.createOp_new_not_inBounds _ hC₅
  have hfresh₆ := WfRewriter.createOp_new_inBounds _ hC₆
  have hnf₆ := WfRewriter.createOp_new_not_inBounds _ hC₆
  have hfresh₇ := WfRewriter.createOp_new_inBounds _ hC₇
  have hnf₇ := WfRewriter.createOp_new_not_inBounds _ hC₇
  have hfresh₈ := WfRewriter.createOp_new_inBounds _ hC₈
  have hnf₈ := WfRewriter.createOp_new_not_inBounds _ hC₈
  -- All created ops are in bounds of the final context, by pushing each fresh op forward.
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  -- `op₁` is not in bounds of the original context (needed to thread the `rhs` operand past it).
  have hnfc₁ : ¬ op₁.InBounds ctx.raw := fun h => hnf₁ (mono hC₀ h)
  have hInB₀ : op₀.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀)))))))
  have hInB₁ : op₁.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁))))))
  have hInB₂ : op₂.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂)))))
  have hInB₃ : op₃.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃))))
  have hInB₄ : op₄.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ hfresh₄)))
  have hInB₅ : op₅.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ hfresh₅))
  have hInB₆ : op₆.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ hfresh₆)
  have hInB₇ : op₇.InBounds newCtx.raw :=
    mono hC₈ hfresh₇
  have hInB₈ : op₈.InBounds newCtx.raw := hfresh₈
  -- Pairwise distinctness of the created ops.  `ne` says: if `a` is in bounds of a context where
  -- `b` is freshly created (hence not yet in bounds), then `a ≠ b`.  We only need the distinctness
  -- facts consumed when threading operand values through `setResultValues?` below; each is built
  -- by pushing the earlier op's freshness forward (`mono`) to the context where the later op is new.
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  have d12 : op₁ ≠ op₂ := ne hfresh₁ hnf₂
  have d13 : op₁ ≠ op₃ := ne (mono hC₂ hfresh₁) hnf₃
  have d14 : op₁ ≠ op₄ := ne (mono hC₃ (mono hC₂ hfresh₁)) hnf₄
  have d34 : op₃ ≠ op₄ := ne hfresh₃ hnf₄
  have d45 : op₄ ≠ op₅ := ne hfresh₄ hnf₅
  -- `WithCreatedOps` chains from each creation context to the final one.
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  have w8 : WfIRContext.WithCreatedOps ctx₈ newCtx := buildOps_withCreatedOps hbuild₈
  -- Operation shapes in the final context: reduce to the creating `createOp` step.
  -- Op types.
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .muli := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .remui := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .arith .trunci := by
    rw [WithCreatedOps.getOpType!_eq w8 hfresh₇, OperationPtr.getOpType!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hTy₈ : op₈.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Operands.
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀,
      if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[(op₀.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁,
      if_pos rfl, hres₁']
  have hOperands₂ : op₂.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂,
      if_pos rfl, hres₂']
  have hOperands₃ : op₃.getOperands! newCtx.raw = #[(op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃,
      if_pos rfl, hres₃']
  have hres₄' : res₄.map (·.val) = #[] := by
    have hsz : res₄.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₄; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₄ : op₄.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄,
      if_pos rfl, hres₄']
  have hOperands₅ : op₅.getOperands! newCtx.raw
      = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅,
      if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₅.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆,
      if_pos rfl, hres₆']
  have hOperands₇ : op₇.getOperands! newCtx.raw = #[(op₆.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w8 hfresh₇, OperationPtr.getOperands!_WfRewriter_createOp hC₇,
      if_pos rfl, hres₇']
  have hOperands₈ : op₈.getOperands! newCtx.raw = #[(op₇.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₈, if_pos rfl, hres₈']
  -- Successors (all empty).
  have hSucc₀ : op₀.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w1 hfresh₀, OperationPtr.getSuccessors!_WfRewriter_createOp hC₀,
      if_pos rfl]
  have hSucc₁ : op₁.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w2 hfresh₁, OperationPtr.getSuccessors!_WfRewriter_createOp hC₁,
      if_pos rfl]
  have hSucc₂ : op₂.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w3 hfresh₂, OperationPtr.getSuccessors!_WfRewriter_createOp hC₂,
      if_pos rfl]
  have hSucc₃ : op₃.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w4 hfresh₃, OperationPtr.getSuccessors!_WfRewriter_createOp hC₃,
      if_pos rfl]
  have hSucc₄ : op₄.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w5 hfresh₄, OperationPtr.getSuccessors!_WfRewriter_createOp hC₄,
      if_pos rfl]
  have hSucc₅ : op₅.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w6 hfresh₅, OperationPtr.getSuccessors!_WfRewriter_createOp hC₅,
      if_pos rfl]
  have hSucc₆ : op₆.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w7 hfresh₆, OperationPtr.getSuccessors!_WfRewriter_createOp hC₆,
      if_pos rfl]
  have hSucc₇ : op₇.getSuccessors! newCtx.raw = #[] := by
    rw [WithCreatedOps.getSuccessors!_eq w8 hfresh₇, OperationPtr.getSuccessors!_WfRewriter_createOp hC₇,
      if_pos rfl]
  have hSucc₈ : op₈.getSuccessors! newCtx.raw = #[] := by
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hC₈, if_pos rfl]
  -- Number of results (all one).
  have hNumRes₀ : op₀.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w1 hfresh₀, OperationPtr.getNumResults!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hNumRes₁ : op₁.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w2 hfresh₁, OperationPtr.getNumResults!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hNumRes₂ : op₂.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w3 hfresh₂, OperationPtr.getNumResults!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hNumRes₃ : op₃.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w4 hfresh₃, OperationPtr.getNumResults!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hNumRes₄ : op₄.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w5 hfresh₄, OperationPtr.getNumResults!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hNumRes₅ : op₅.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w6 hfresh₅, OperationPtr.getNumResults!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hNumRes₆ : op₆.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w7 hfresh₆, OperationPtr.getNumResults!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hNumRes₇ : op₇.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w8 hfresh₇, OperationPtr.getNumResults!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hNumRes₈ : op₈.getNumResults! newCtx.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Result types.
  have hRT₀ : op₀.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w1 hfresh₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(IntegerType.mk (2 * mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk (2 * mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk (2 * mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk (2 * mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk (2 * mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w8 hfresh₇, OperationPtr.getResultTypes!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hRT₈ : op₈.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Properties (only the ones we need to evaluate the interpreter).
  have hP₁ : op₁.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w2 hfresh₁]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁ (operation := op₁)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk (2 * mtv.modulus.type.bitwidth)) } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .muli) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  have hP₇ : op₇.getProperties! newCtx.raw (.arith .trunci) = { nsw := false, nuw := true } := by
    rw [WithCreatedOps.getProperties!_eq w8 hfresh₇]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₇ (operation := op₇)
    rw [if_pos rfl] at h2; exact h2
  -- ## Source interpretation
  -- Each operand of `op` has the modulus type.
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  -- Normalise the source-interpretation hypothesis.
  have hinterp' : interpretOp op state opInBounds = some (.ok (newState, cf)) := by
    simpa [liftM, monadLift, MonadLift.monadLift] using hinterp
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp'
  have hOpArr : op.getOperands! ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  -- The two source operand values are concrete canonical integers.
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  -- Concrete value and canonicity of the first operand.
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) ∧
      (x.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) ∧
      (y.toNat : Int) < mtv.modulus.value := by
    have hconf := getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  -- Hence `srcOperandVals = #[.int N (.val x), .int N (.val y)]`.
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
      RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  -- The (single) result type of `op` is the modulus type.
  have hSrcNumRes : (op.getResultTypes! ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! ctx.raw)[0]? = some ⟨.modArithType mtv, by rfl⟩ := by
    have h0 : (op.getResultTypes! ctx.raw)[0]?
        = some ((op.getResultTypes! ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  -- Evaluate the source `mod_arith.mul`.
  have hSrcEval' : interpretOp' (.mod_arith .mul)
      (op.getProperties! ctx.raw (.mod_arith .mul)) (op.getResultTypes! ctx.raw) srcOperandVals
      (op.getSuccessors! ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.mul mtv.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mtv.modulus.type.bitwidth
      (.val (Data.ModArith.mul mtv.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  -- The single source result value.
  have hNumResultsNB : op.getNumResults ctx.raw opInBounds = 1 := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opInBounds]; exact hNumResults
  have hGetResults : op.getResults ctx.raw = #[(op.getResult 0 : ValuePtr)] := by
    unfold OperationPtr.getResults
    rw [hNumResultsNB]
    simp [Array.range_succ, show Array.range 0 = #[] from by simp [Array.range]]
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.mul mtv.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hSourceVals : sourceValues
      = #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.mul mtv.modulus.value x y))] := by
    rw [hGetResults, Array.mapM_eq_mapM_toList] at hsource
    simp [hvSrc] at hsource
    exact hsource.symm
  -- ## Refinement transfer: the operands have the same concrete value in the target state.
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  -- The mapping is the identity on `lhs`/`rhs` because they are operands (not results) of `op`.
  have hLhsMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! ctx.raw := by rw [hOpArr]; simp
  have hLhsNotRes : operands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes : operands[1]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hMapLhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[0]!, hlhsIn⟩ : ValuePtr) = operands[0]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hLhsNotRes]
  have hMapRhs : (LocalRewritePattern.mapping hpattern (by grind) (by grind) (by grind)
      ⟨operands[1]!, hrhsIn⟩ : ValuePtr) = operands[1]! := by
    simp only [LocalRewritePattern.mapping, dif_neg hRhsNotRes]
  -- Hence the target state binds the operands to the same concrete values.
  have hTLhs : state'.variables.getVar? operands[0]! = some (.int mtv.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    rw [hMapLhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    rw [htv]; congr 1
    cases tv with
    | int bw t =>
      simp only [RuntimeValue.isRefinedBy] at href
      obtain ⟨hbweq, href⟩ := href
      subst hbweq
      cases t with
      | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
      | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
    | _ => simp [RuntimeValue.isRefinedBy] at href
  -- ## Width side conditions and the pipeline arithmetic core.
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  have hnm : mtv.modulus.type.bitwidth ≤ 2 * mtv.modulus.type.bitwidth := by omega
  obtain ⟨hqm, hqm2⟩ :=
    Data.ModArith.modulus_sq_lt_two_pow_two_mul hN1 (by omega) hQwidth
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  -- The pipeline result and its canonicity.
  have hPipeEq : ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
        * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth = Data.ModArith.mul mtv.modulus.value x y :=
    Data.ModArith.mulPipeline_eq_mul hQpos hqm hqm2 hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
        * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).toNat : Int)
        < mtv.modulus.value :=
    Data.ModArith.toNat_mulPipeline_lt hQpos hqm hqm2 hnm hxlt hylt
  -- ## Target interpretation: step through the nine created operations.
  -- Notation for the intermediate `BitVec`s flowing through the pipeline.
  -- Step op₀: cast `lhs : iN`.  Value: `.int N (.val x)`.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₀ hTLhs
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₀ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  -- Lookups in `vs₁`.
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnf₀ hSet₀]; exact hTRhs
  -- Step op₁: `extui` of `x` to width `M = N + 1`.  Value: `.int M (.val (x.zeroExtend M))`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] :=
      getOperandValues_one hOperands₁ hv₁_0
  have hEval₁ : interpretOp' (.arith .extui) (op₁.getProperties! newCtx.raw (.arith .extui))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT₁, hP₁]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (2 * mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)))]
      (op₁.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₁ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  -- Step op₂: cast `rhs : iN`.  Value: `.int N (.val y)`.
  have hv₂_rhs : vs₂.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnfc₁ hSet₁]; exact hv₁_rhs
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₂ hv₂_rhs
  have hEval₂ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₂.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₂.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₂]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₂.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₂ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  -- Step op₃: `extui` of `y` to width `M`.
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] :=
      getOperandValues_one hOperands₃ hv₃_2
  have hEval₃ : interpretOp' (.arith .extui) (op₃.getProperties! newCtx.raw (.arith .extui))
      (op₃.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT₃, hP₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (2 * mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))]
      (op₃.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₃ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  -- Step op₄: the modulus constant `q : iM`.
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp
  have hEval₄ : interpretOp' (.arith .constant) (op₄.getProperties! newCtx.raw (.arith .constant))
      (op₄.getResultTypes! newCtx.raw) #[] (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))],
          state'.memory, none)) := by
    rw [hRT₄, hP₄]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))]
      (op₄.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₄ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  -- Step op₅: `muli` of the two extended operands.
  have hv₂_1 : vs₂.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  have hv₅_1 : vs₅.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)))) := by
    rw [getVar?_setResultValues?_ne d14 hSet₄, getVar?_setResultValues?_ne d13 hSet₃,
      getVar?_setResultValues?_ne d12 hSet₂]; exact hv₂_1
  have hv₅_3 : vs₅.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))) := by
    rw [getVar?_setResultValues?_ne d34 hSet₄]; exact hv₄_3
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅
      = some #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))] :=
      getOperandValues_two hOperands₅ hv₅_1 hv₅_3
  have hEval₅ : interpretOp' (.arith .muli) (op₅.getProperties! newCtx.raw (.arith .muli))
      (op₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (y.zeroExtend (2 * mtv.modulus.type.bitwidth)))]
      (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hP₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.mul, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth)))]
      (op₅.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₅ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  -- Step op₆: `remui` reducing modulo `q`.
  have hv₅_4 : vs₅.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]; exact hv₅_4
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
              * y.zeroExtend (2 * mtv.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))] :=
      getOperandValues_two hOperands₆ hv₆_5 hv₆_4
  have hEval₆ : interpretOp' (.arith .remui) (op₆.getProperties! newCtx.raw (.arith .remui))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
              * y.zeroExtend (2 * mtv.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
            (.val (BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))],
          state'.memory, none)) := by
    have hqne : BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value
        ≠ 0#(2 * mtv.modulus.type.bitwidth) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := 2 * mtv.modulus.type.bitwidth) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))]
      (op₆.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₆ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  -- Step op₇: `trunci` (nuw) back to width `N`.
  have hv₇_6 : vs₇.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇
      = some #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))] :=
      getOperandValues_one hOperands₇ hv₇_6
  -- No-poison side condition for the `nuw` truncation, from canonicity.
  have hNoPoison : (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
        * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
        mtv.modulus.type.bitwidth).zeroExtend (2 * mtv.modulus.type.bitwidth)
        = (x.zeroExtend (2 * mtv.modulus.type.bitwidth)
        * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    -- canonicity: `remM.toNat < q ≤ 2^N`.
    have hcast : (2:Int)^mtv.modulus.type.bitwidth = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval₇ : interpretOp' (.arith .trunci) (op₇.getProperties! newCtx.raw (.arith .trunci))
      (op₇.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (2 * mtv.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value))]
      (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT₇, hP₇]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth ≥ 2 * mtv.modulus.type.bitwidth) from by omega)]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₇.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₇ (by simp [RuntimeValue.Conforms])
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  -- Step op₈: cast the result back to `!mod_arith.int`.
  have hv₈_7 : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
  have hOpVals₈ : (InterpreterState.mk vs₈ state'.memory).variables.getOperandValues op₈
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))] :=
      getOperandValues_one hOperands₈ hv₈_7
  have hEval₈ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₈.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₈.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mtv.modulus.type.bitwidth)
            * y.zeroExtend (2 * mtv.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mtv.modulus.type.bitwidth) mtv.modulus.value).truncate
            mtv.modulus.type.bitwidth))]
      (op₈.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.mul mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₈, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₈ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.mul mtv.modulus.value x y))]
      (op₈.getResultTypes! newCtx.raw) :=
    arrayConforms_singleton hRT₈ ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_mul hQpos hQle⟩
  obtain ⟨vs₉, hSet₈, hStep₈⟩ := interpretOp_step (inB := hInB₈) hTy₈ hOpVals₈ hEval₈ hConf₈
  -- ## Assemble the nine steps into the full target interpretation.
  refine ⟨⟨vs₉, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁, op₂, op₃, op₄, op₅, op₆, op₇, op₈] state' _
      = liftM (some (⟨vs₉, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep₀]
    rw [interpretOpList_cons]; simp only [hStep₁]
    rw [interpretOpList_cons]; simp only [hStep₂]
    rw [interpretOpList_cons]; simp only [hStep₃]
    rw [interpretOpList_cons]; simp only [hStep₄]
    rw [interpretOpList_cons]; simp only [hStep₅]
    rw [interpretOpList_cons]; simp only [hStep₆]
    rw [interpretOpList_cons]; simp only [hStep₇]
    rw [interpretOpList_cons]; simp only [hStep₈]
    simp [liftM, monadLift, MonadLift.monadLift]
  · simpa using hMemEq
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (Data.ModArith.mul mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₉ : vs₉.getVar? (op₈.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.mul mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₈]; simp [hNumRes₈]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₉]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]


end ModArithToArith

end Veir
