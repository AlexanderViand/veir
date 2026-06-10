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
    op.getNumResults! rawCtx = 1 ∧ operands = op.getOperands! rawCtx := by
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

end ModArithToArith

end Veir
