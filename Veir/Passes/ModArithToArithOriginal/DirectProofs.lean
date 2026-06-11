import Veir.Passes.ModArithToArithOriginal
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.ModArith.Lemmas
import Veir.Passes.ModArithToArith.Proofs

/-!
# Direct correctness of the imperative `--mod-arith-to-arith-original` lowering

This file proves a semantics-preservation theorem for the imperative-style lowering pass
(`Veir/Passes/ModArithToArithOriginal.lean`) *directly*, driven off the imperative code itself
rather than through the recipe-based `--mod-arith-to-arith` pass.

The pass helpers (`castToStorage`, `unpackValue`, `emitArithBinOp`, …) each run
`PatternRewriter.createOp ... (some (InsertPoint.before op))` guarded by decidable `dite` checks;
`replaceAndErase` performs a checked `WfRewriter.replaceValue` followed by `WfRewriter.eraseOp`.
Since an imperative pattern returns only the resulting rewriter, the correctness statement
`ImperativePatternCorrect` *exhibits* what the pattern did: the freshly created ops `newOps`, the
replacement value `newValue`, and the guarantee that interpreting `newOps` in any refining state
mirrors interpreting `op`.

The pure-arithmetic core, the interpreter step machinery, and the get-set lemmas are all shared
infrastructure; only the inversion of the imperative helper chain and the bookkeeping that the new
ops survive `replaceValue` + `eraseOp` is specific to this pass.
-/

namespace Veir

open ModArithToArithOriginal

/-! ## Bridging `PatternRewriter` operations to the underlying `WfRewriter` -/

namespace ModArithToArithOriginal

/-- `PatternRewriter.createOp` modifies the context exactly as `WfRewriter.createOp`. -/
theorem patternCreateOp_ctx {rw : PatternRewriter OpCode} {opType : OpCode}
    {rt : Array TypeAttr} {operands : Array ValuePtr} {bo : Array BlockPtr} {rg : Array RegionPtr}
    {props : propertiesOf opType} {ip : Option InsertPoint} {h1 h2 h3 h4}
    {rw' : PatternRewriter OpCode} {newOp : OperationPtr}
    (h : rw.createOp opType rt operands bo rg props ip h1 h2 h3 h4 = some (rw', newOp)) :
    WfRewriter.createOp rw.ctx opType rt operands bo rg props ip h1 h2 h3 h4
      = some (rw'.ctx, newOp) := by
  simp only [PatternRewriter.createOp] at h
  split at h
  · simp at h
  · rename_i wfctx newOp' heq
    split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simpa using heq)

/-- `PatternRewriter.replaceValue` modifies the context exactly as `WfRewriter.replaceValue`. -/
theorem patternReplaceValue_ctx {rw : PatternRewriter OpCode} {oldVal newVal : ValuePtr} {h1 h2 h3} :
    (rw.replaceValue oldVal newVal h1 h2 h3).ctx
      = WfRewriter.replaceValue rw.ctx oldVal newVal h1 h2 h3 := by
  simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]

/-- `PatternRewriter.eraseOp` modifies the context exactly as `WfRewriter.eraseOp`. -/
theorem patternEraseOp_ctx {rw : PatternRewriter OpCode} {op : OperationPtr} {h1 h2 h3}
    {rw' : PatternRewriter OpCode} (h : rw.eraseOp op h1 h2 h3 = some rw') :
    WfRewriter.eraseOp rw.ctx op h1 h2 h3 = rw'.ctx := by
  simp only [PatternRewriter.eraseOp, bind, Option.bind, Option.some.injEq] at h
  subst h
  rfl

/-! ## Inversion of the imperative helpers

Each helper runs decidable `dite`-guards around a `PatternRewriter.createOp` (or a `WfRewriter`
replace/erase pair).  These lemmas peel the guards off and expose the underlying
`WfRewriter.createOp` equations (related to `rw'.ctx` via `patternCreateOp_ctx`), so the rest of
the proof can reason purely about the well-formed rewriter primitives. -/

/-- Inversion of `castToStorage`: it emits a single `unrealized_conversion_cast`. -/
theorem castToStorage_inv {rw : PatternRewriter OpCode} {v : ValuePtr} {ip : InsertPoint}
    {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : castToStorage rw v ip = some (rw', cv)) :
    ∃ (mt : ModArithType) (castOp : OperationPtr),
      (v.getType! rw.ctx.raw).val = .modArithType mt ∧ cv = (castOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.builtin .unrealized_conversion_cast) #[mt.modulus.type] #[v]
          #[] #[] () (some ip) h1 h2 h3 h4 = some (rw'.ctx, castOp) := by
  unfold castToStorage at h
  split at h
  · rename_i mt hmt
    split at h
    · simp at h
    split at h
    · simp at h
    simp only [bind, Option.bind] at h
    split at h
    · simp at h
    rename_i res hcreate
    obtain ⟨rwNew, castOp⟩ := res
    simp only at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨mt, castOp, hmt, rfl, _, _, _, _, patternCreateOp_ctx hcreate⟩
  · nomatch h

/-- Inversion of `castToModArith`: it emits a single `unrealized_conversion_cast`. -/
theorem castToModArith_inv {rw : PatternRewriter OpCode} {x : ValuePtr} {ty : ModArithType}
    {ip : InsertPoint} {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : castToModArith rw x ty ip = some (rw', cv)) :
    ∃ (castOp : OperationPtr), cv = (castOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.builtin .unrealized_conversion_cast) #[ty] #[x]
          #[] #[] () (some ip) h1 h2 h3 h4 = some (rw'.ctx, castOp) := by
  unfold castToModArith at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i res hcreate
  obtain ⟨rwNew, castOp⟩ := res
  simp only at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨castOp, rfl, _, _, _, _, patternCreateOp_ctx hcreate⟩

/-- Inversion of `emitArithConstant`: it emits a single `arith.constant`. -/
theorem emitArithConstant_inv {rw : PatternRewriter OpCode} {c : Int} {width : Nat}
    {ip : InsertPoint} {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : emitArithConstant rw c width ip = some (rw', cv)) :
    ∃ (cOp : OperationPtr), cv = (cOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.arith .constant) #[(IntegerType.mk width : TypeAttr)] #[]
          #[] #[] ({ value := IntegerAttr.mk c (IntegerType.mk width) } : ArithConstantProperties)
          (some ip) h1 h2 h3 h4 = some (rw'.ctx, cOp) := by
  unfold emitArithConstant at h
  split at h
  · simp at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i res hcreate
  obtain ⟨rwNew, cOp⟩ := res
  simp only at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨cOp, rfl, _, _, _, _, patternCreateOp_ctx hcreate⟩

/-- Inversion of `emitArithBinOp`: it emits a single binary `arith` op. -/
theorem emitArithBinOp_inv {rw : PatternRewriter OpCode} {arithOp : Arith}
    {props : propertiesOf (.arith arithOp)} {a b : ValuePtr} {ip : InsertPoint}
    {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : emitArithBinOp rw arithOp props a b ip = some (rw', cv)) :
    ∃ (binOp : OperationPtr), cv = (binOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.arith arithOp) #[a.getType! rw.ctx.raw] #[a, b]
          #[] #[] props (some ip) h1 h2 h3 h4 = some (rw'.ctx, binOp) := by
  unfold emitArithBinOp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i res hcreate
  obtain ⟨rwNew, binOp⟩ := res
  simp only at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨binOp, rfl, _, _, _, _, patternCreateOp_ctx hcreate⟩

/-- Inversion of `unpackValue`: a `castToStorage` followed (under width widening) by an `extui`. -/
theorem unpackValue_inv {rw : PatternRewriter OpCode} {v : ValuePtr} {it : IntegerType}
    {ip : InsertPoint} {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : unpackValue rw v it ip = some (rw', cv)) :
    ∃ (mt : ModArithType) (rw1 : PatternRewriter OpCode) (castOp : OperationPtr)
        (storageType : IntegerType),
      (v.getType! rw.ctx.raw).val = .modArithType mt ∧
      ((castOp.getResult 0 : ValuePtr).getType! rw1.ctx.raw).val = .integerType storageType ∧
      (∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.builtin .unrealized_conversion_cast) #[mt.modulus.type] #[v]
          #[] #[] () (some ip) h1 h2 h3 h4 = some (rw1.ctx, castOp)) ∧
      ((it.bitwidth > storageType.bitwidth ∧
        ∃ (extOp : OperationPtr), cv = (extOp.getResult 0 : ValuePtr) ∧
          ∃ h1 h2 h3 h4,
            WfRewriter.createOp rw1.ctx (.arith .extui) #[(it : TypeAttr)]
              #[(castOp.getResult 0 : ValuePtr)] #[] #[]
              ({ nneg := false } : propertiesOf (.arith .extui))
              (some ip) h1 h2 h3 h4 = some (rw'.ctx, extOp)) ∨
       (¬ it.bitwidth > storageType.bitwidth ∧ rw' = rw1 ∧ cv = (castOp.getResult 0 : ValuePtr))) := by
  unfold unpackValue at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i res hcast
  obtain ⟨rw1, stored⟩ := res
  simp only at h
  obtain ⟨mt, castOp, hvty, rfl, hc⟩ := castToStorage_inv hcast
  split at h
  · rename_i storageType hst
    split at h
    · rename_i hgt
      split at h
      · simp at h
      split at h
      · simp at h
      split at h
      · simp at h
      rename_i res2 hext
      obtain ⟨rw2, ext⟩ := res2
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨mt, rw1, castOp, storageType, hvty, hst, hc,
        Or.inl ⟨by omega, ext, rfl, _, _, _, _, patternCreateOp_ctx hext⟩⟩
    · rename_i hngt
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨mt, rw1, castOp, storageType, hvty, hst, hc, Or.inr ⟨by omega, rfl, rfl⟩⟩
  · nomatch h

/-- Inversion of `packValue`: (under width widening) a `trunci` followed by a
`castToModArith`. -/
theorem packValue_inv {rw : PatternRewriter OpCode} {v : ValuePtr} {ty : ModArithType}
    {ip : InsertPoint} {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : packValue rw v ty ip = some (rw', cv)) :
    ∃ (it : IntegerType),
      (v.getType! rw.ctx.raw).val = .integerType it ∧
      ((it.bitwidth > ty.modulus.type.bitwidth ∧
        ∃ (rw1 : PatternRewriter OpCode) (truncOp castOp : OperationPtr),
          cv = (castOp.getResult 0 : ValuePtr) ∧
          (∃ h1 h2 h3 h4,
            WfRewriter.createOp rw.ctx (.arith .trunci) #[ty.modulus.type] #[v]
              #[] #[] ({ attr := { nsw := false, nuw := true } } : propertiesOf (.arith .trunci))
              (some ip) h1 h2 h3 h4 = some (rw1.ctx, truncOp)) ∧
          (∃ h1 h2 h3 h4,
            WfRewriter.createOp rw1.ctx (.builtin .unrealized_conversion_cast) #[ty]
              #[(truncOp.getResult 0 : ValuePtr)] #[] #[] () (some ip) h1 h2 h3 h4
                = some (rw'.ctx, castOp))) ∨
       (¬ it.bitwidth > ty.modulus.type.bitwidth ∧
        ∃ (castOp : OperationPtr), cv = (castOp.getResult 0 : ValuePtr) ∧
          ∃ h1 h2 h3 h4,
            WfRewriter.createOp rw.ctx (.builtin .unrealized_conversion_cast) #[ty] #[v]
              #[] #[] () (some ip) h1 h2 h3 h4 = some (rw'.ctx, castOp))) := by
  unfold packValue at h
  split at h
  · rename_i it hit
    simp only at h
    split at h
    · rename_i hgt
      split at h
      · simp at h
      split at h
      · simp at h
      rename_i hv hip
      simp only [bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rw1, narrowed⟩, htrunc, h⟩ := h
      obtain ⟨castOp, hcv, hcast⟩ := castToModArith_inv h
      exact ⟨it, hit, Or.inl ⟨hgt, rw1, narrowed, castOp, hcv,
        ⟨_, _, _, _, patternCreateOp_ctx htrunc⟩, hcast⟩⟩
    · rename_i hngt
      obtain ⟨castOp, hcv, hcast⟩ := castToModArith_inv h
      exact ⟨it, hit, Or.inr ⟨hngt, castOp, hcv, hcast⟩⟩
  · nomatch h

/-- Inversion of `replaceAndErase`: it `replaceValue`s `op`'s result by `r` and then `eraseOp`s
`op`, exposing the final context as the erase of the replace. -/
theorem replaceAndErase_inv {rw : PatternRewriter OpCode} {op : OperationPtr} {r : ValuePtr}
    {rw' : PatternRewriter OpCode} (h : replaceAndErase rw op r = some rw') :
    ∃ (ctxR : WfIRContext OpCode) (hne : (op.getResult 0 : ValuePtr) ≠ r)
      (hold : (op.getResult 0 : ValuePtr).InBounds rw.ctx.raw)
      (hnew : r.InBounds rw.ctx.raw),
      ctxR = WfRewriter.replaceValue rw.ctx (op.getResult 0) r hne hold hnew ∧
      ∃ (hregions : op.getNumRegions! ctxR.raw = 0)
        (huses : ¬ op.hasUses! ctxR.raw)
        (hop : op.InBounds ctxR.raw),
        rw'.ctx = WfRewriter.eraseOp ctxR op hregions (by grind) hop := by
  unfold replaceAndErase at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i hne
  split at h
  · simp at h
  rename_i hold
  split at h
  · simp at h
  rename_i hnew
  split at h
  · simp at h
  rename_i hregions
  split at h
  · simp at h
  rename_i huses
  split at h
  · simp at h
  rename_i hop
  have hbridge : (rw.replaceValue (op.getResult 0) r hne (by grind) (by grind)).ctx
      = WfRewriter.replaceValue rw.ctx (op.getResult 0) r hne (by grind) (by grind) :=
    patternReplaceValue_ctx
  refine ⟨(rw.replaceValue (op.getResult 0) r hne (by grind) (by grind)).ctx,
    hne, by grind, by grind, hbridge, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind
  · simp only [PatternRewriter.eraseOp, bind, Option.bind, Option.some.injEq] at h
    rw [← h]

end ModArithToArithOriginal

/-! ## A sequence of `createOp`s (with insertion points)

The lowering builds its new ops with `PatternRewriter.createOp ... (some (InsertPoint.before op))`.
`WfIRContext.WithCreatedOps` (used by the recipe-pass proofs) only covers detached creation
(`none` insertion point), so we mirror it here for *inserted* creation.  Each getter of an op that
predates the sequence is unaffected, exactly as for `WithCreatedOps`. -/

/-- `ctx'` is obtained from `ctx` by a sequence of `WfRewriter.createOp`s. -/
inductive WfCreatedSeq (start : WfIRContext OpCode) : WfIRContext OpCode → Prop
  | nil : WfCreatedSeq start start
  | step (mid fin : WfIRContext OpCode) (h : WfCreatedSeq start mid)
      (h₂ : ∃ opType rt operands bo rg props ip h₁ h₂ h₃ h₄ newOp,
        WfRewriter.createOp mid opType rt operands bo rg props ip h₁ h₂ h₃ h₄ = some (fin, newOp)) :
      WfCreatedSeq start fin

theorem WfCreatedSeq.inBounds_mono {c c' : WfIRContext OpCode} (h : WfCreatedSeq c c')
    (ptr : GenericPtr) (hin : ptr.InBounds c.raw) : ptr.InBounds c'.raw := by
  induction h with
  | nil => exact hin
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    exact WfRewriter.createOp_inBounds_mono hC ih

/-- Extend a sequence by one more `createOp` at the end. -/
theorem WfCreatedSeq.snoc {c c' c'' : WfIRContext OpCode}
    {opType rt operands bo rg props ip h₁ h₂ h₃ h₄ newOp}
    (h : WfCreatedSeq c c')
    (hCreate : WfRewriter.createOp c' opType rt operands bo rg props ip h₁ h₂ h₃ h₄
      = some (c'', newOp)) :
    WfCreatedSeq c c'' :=
  .step c' c'' h ⟨_, _, _, _, _, _, _, _, _, _, _, _, hCreate⟩

/-- A single `createOp` step. -/
theorem WfCreatedSeq.single {c c' : WfIRContext OpCode}
    {opType rt operands bo rg props ip h₁ h₂ h₃ h₄ newOp}
    (hCreate : WfRewriter.createOp c opType rt operands bo rg props ip h₁ h₂ h₃ h₄
      = some (c', newOp)) :
    WfCreatedSeq c c' :=
  WfCreatedSeq.nil.snoc hCreate

theorem WfCreatedSeq.getOpType!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getOpType! c'.raw = o.getOpType! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC,
      if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

theorem WfCreatedSeq.getOperands!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getOperands! c'.raw = o.getOperands! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC,
      if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

theorem WfCreatedSeq.getResultTypes!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getResultTypes! c'.raw = o.getResultTypes! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC,
      if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

theorem WfCreatedSeq.getNumResults!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getNumResults! c'.raw = o.getNumResults! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC,
      if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

theorem WfCreatedSeq.getSuccessors!_eq {c c' : WfIRContext OpCode} {o : OperationPtr}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getSuccessors! c'.raw = o.getSuccessors! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hC,
      if_neg (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

theorem WfCreatedSeq.getProperties!_eq {c c' : WfIRContext OpCode} {o : OperationPtr} {T : OpCode}
    (h : WfCreatedSeq c c') (hin : o.InBounds c.raw) :
    o.getProperties! c'.raw T = o.getProperties! c.raw T := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩ := hcreate
    have hinMid : o.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.operation o) hin
    rw [OperationPtr.getProperties!_WfRewriter_createOp_other hC
      (by intro heq; subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hinMid), ih]

/-- The type of result 0 of a single-result op freshly created with result types `#[ty]`. -/
theorem createOp_result0_type {c c' : WfIRContext OpCode} {T : OpCode} {ty : TypeAttr}
    {operands bo rg} {props : propertiesOf T} {ip h₁ h₂ h₃ h₄} {newOp}
    (hC : WfRewriter.createOp c T #[ty] operands bo rg props ip h₁ h₂ h₃ h₄ = some (c', newOp)) :
    (newOp.getResult 0 : ValuePtr).getType! c'.raw = ty := by
  have := ValuePtr.getType!_WfRewriter_createOp hC (value := (newOp.getResult 0 : ValuePtr))
  simp only [OperationPtr.getResult] at this ⊢
  rw [this]; simp

theorem WfCreatedSeq.getType!_eq {c c' : WfIRContext OpCode} {v : ValuePtr}
    (h : WfCreatedSeq c c') (hin : v.InBounds c.raw) :
    v.getType! c'.raw = v.getType! c.raw := by
  induction h with
  | nil => rfl
  | step mid fin hsub hcreate ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, newOp, hC⟩ := hcreate
    have hinMid : v.InBounds mid.raw := hsub.inBounds_mono (GenericPtr.value v) hin
    have hnf : ¬ newOp.InBounds mid.raw := WfRewriter.createOp_new_not_inBounds _ hC
    rw [ValuePtr.getType!_WfRewriter_createOp hC]
    cases v with
    | blockArgument _ => exact ih
    | opResult opr =>
      simp only
      rw [dif_neg (by
        rintro ⟨heq, _⟩
        apply hnf
        have : opr.op.InBounds mid.raw := by
          grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.InBounds]
        grind)]
      exact ih

/-! ## Get-set survival through `replaceValue` and `eraseOp`

After the pass has built its new ops it rewires the uses of `op`'s old result to the new value
(`replaceValue`) and removes `op` (`eraseOp`).  Neither touches the *shape* of the new ops, as long
as we know the new op is not `op` and does not use `op`'s old result as an operand.  The following
lemmas isolate the survival facts we need to interpret the new ops in the final context. -/

namespace ModArithToArithOriginal

variable {ctx : WfIRContext OpCode}

/-- The operands of an op survive `replaceValue` when the replaced value is not among them. -/
theorem getOperands!_replaceValue_of_notMem {o : OperationPtr} {oldVal newVal : ValuePtr}
    {ne : oldVal ≠ newVal} {oldIn : oldVal.InBounds ctx.raw} {newIn : newVal.InBounds ctx.raw}
    (hin : o.InBounds ctx.raw) (hnotmem : oldVal ∉ o.getOperands! ctx.raw) :
    o.getOperands! (WfRewriter.replaceValue ctx oldVal newVal ne oldIn newIn).raw
      = o.getOperands! ctx.raw := by
  rw [OperationPtr.getOperands!_WfRewriter_replaceValue hin]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map]
    rw [if_neg]
    intro heq
    exact hnotmem (heq ▸ Array.getElem_mem _)

/--
A new op `o` (distinct from the erased `op`, in bounds before the final rewiring, and not using the
replaced value `oldVal` among its operands) keeps all of its shape data — in bounds, opcode,
operands, result types, result count, successors, and properties — after `replaceValue oldVal newVal`
followed by `eraseOp op`.  This is the bookkeeping that lets the new ops be interpreted in the final
context exactly as they were created.
-/
theorem opSurvives {ctxP : WfIRContext OpCode} {op o : OperationPtr} {oldVal newVal : ValuePtr}
    (ne : oldVal ≠ newVal) (oldIn : oldVal.InBounds ctxP.raw) (newIn : newVal.InBounds ctxP.raw)
    (hregions : op.getNumRegions! (WfRewriter.replaceValue ctxP oldVal newVal ne oldIn newIn).raw = 0)
    (hUses : (!op.hasUses! (WfRewriter.replaceValue ctxP oldVal newVal ne oldIn newIn).raw) = true)
    (hOp : op.InBounds (WfRewriter.replaceValue ctxP oldVal newVal ne oldIn newIn).raw)
    (hne : o ≠ op) (hin : o.InBounds ctxP.raw)
    (hnotmem : oldVal ∉ o.getOperands! ctxP.raw) :
    let final := WfRewriter.eraseOp (WfRewriter.replaceValue ctxP oldVal newVal ne oldIn newIn)
      op hregions hUses hOp
    o.InBounds final.raw ∧
    o.getOpType! final.raw = o.getOpType! ctxP.raw ∧
    o.getOperands! final.raw = o.getOperands! ctxP.raw ∧
    o.getResultTypes! final.raw = o.getResultTypes! ctxP.raw ∧
    o.getNumResults! final.raw = o.getNumResults! ctxP.raw ∧
    o.getSuccessors! final.raw = o.getSuccessors! ctxP.raw ∧
    (∀ T, o.getProperties! final.raw T = o.getProperties! ctxP.raw T) := by
  intro final
  have hinR : o.InBounds (WfRewriter.replaceValue ctxP oldVal newVal ne oldIn newIn).raw := by grind
  have hinE : o.InBounds final.raw := by simp only [final]; grind [WfRewriter.eraseOp]
  refine ⟨hinE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [final, OperationPtr.getOpType!_wfRewriter_eraseOp hinE,
      OperationPtr.getOpType!_WfRewriter_replaceValue]
  · simp only [final]
    rw [OperationPtr.getOperands!_wfRewriter_eraseOp hinE]
    exact getOperands!_replaceValue_of_notMem hin hnotmem
  · simp only [final, OperationPtr.getResultTypes!_wfRewriter_eraseOp hinE,
      OperationPtr.getResultTypes!_WfRewriter_replaceValue]
  · simp only [final, OperationPtr.getNumResults!_wfRewriter_eraseOp hinE,
      OperationPtr.getNumResults!_WfRewriter_replaceValue]
  · simp only [final, OperationPtr.getSuccessors!_wfRewriter_eraseOp hinE,
      OperationPtr.getSuccessors!_WfRewriter_replaceValue]
  · intro T
    simp only [final, OperationPtr.getProperties!_wfRewriter_eraseOp hinE,
      OperationPtr.getProperties!_WfRewriter_replaceValue]

/-- A variable bound in a conforming variable state matches its declared type. -/
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

/-- A value `v` that is in bounds and is not a result of `op` survives `eraseOp op`. -/
theorem valueSurvivesErase {ctxP : WfIRContext OpCode} {op : OperationPtr} {v : ValuePtr}
    {hregions hUses hOp} (hin : v.InBounds ctxP.raw) (hnotRes : v ∉ op.getResults! ctxP.raw) :
    v.InBounds (WfRewriter.eraseOp ctxP op hregions hUses hOp).raw := by
  have hcond : (match GenericPtr.value v with
      | .operation op' => op' ≠ op
      | .opResult or => or.op ≠ op
      | .opOperand oo => oo.op ≠ op
      | .blockOperand bo => bo.op ≠ op
      | .value (.opResult or) => or.op ≠ op
      | .opOperandPtr (.operandNextUse oo) => oo.op ≠ op
      | .opOperandPtr (.valueFirstUse (.opResult or)) => or.op ≠ op
      | .blockOperandPtr (.blockOperandNextUse oo) => oo.op ≠ op
      | _ => True) := by
    cases v with
    | blockArgument _ => trivial
    | opResult or =>
      simp only
      intro heq
      apply hnotRes
      have hin' : or.InBounds ctxP.raw := by simpa [ValuePtr.InBounds] using hin
      have hidx0 := OpResultPtr.inBounds_OperationPtr_getNumResults! or ctxP.raw hin'
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      refine ⟨or.index, heq ▸ hidx0, ?_⟩
      rw [OperationPtr.getResult]
      grind [cases OpResultPtr]
  have hiff := Rewriter.eraseOp_inBounds (ctx := ctxP.raw) (op := op) (hCtx := by grind)
    (hOp := hOp) (GenericPtr.value v) hcond
  show (GenericPtr.value v).InBounds (WfRewriter.eraseOp ctxP op hregions hUses hOp).raw
  simp only [WfRewriter.eraseOp]
  exact hiff.mpr (by simpa [GenericPtr.InBounds, ValuePtr.InBounds] using hin)

/--
The shape data of a freshly created op `o`, read off in the "all ops created" context `ctxP`:
combine the `createOp` getter equations with the `WfCreatedSeq` transfer over the remaining
creations.
-/
theorem newOpFactsAtPack {ctxMid ctxNext ctxP : WfIRContext OpCode} {o : OperationPtr}
    {T : OpCode} {rt : Array TypeAttr} {ops : Array ValuePtr} {bo rg} {props : propertiesOf T}
    {ip h₁ h₂ h₃ h₄}
    (hCo : WfRewriter.createOp ctxMid T rt ops bo rg props ip h₁ h₂ h₃ h₄ = some (ctxNext, o))
    (seq : WfCreatedSeq ctxNext ctxP) :
    o.InBounds ctxP.raw ∧
    o.getOpType! ctxP.raw = T ∧
    o.getOperands! ctxP.raw = ops ∧
    o.getResultTypes! ctxP.raw = rt ∧
    o.getNumResults! ctxP.raw = rt.size ∧
    o.getSuccessors! ctxP.raw = bo ∧
    o.getProperties! ctxP.raw T = props := by
  have hfresh : o.InBounds ctxNext.raw := WfRewriter.createOp_new_inBounds _ hCo
  refine ⟨seq.inBounds_mono (GenericPtr.operation o) hfresh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [seq.getOpType!_eq hfresh, OperationPtr.getOpType!_WfRewriter_createOp hCo, if_pos rfl]
  · rw [seq.getOperands!_eq hfresh, OperationPtr.getOperands!_WfRewriter_createOp hCo, if_pos rfl]
  · rw [seq.getResultTypes!_eq hfresh, OperationPtr.getResultTypes!_WfRewriter_createOp hCo,
      if_pos rfl]
  · rw [seq.getNumResults!_eq hfresh, OperationPtr.getNumResults!_WfRewriter_createOp hCo,
      if_pos rfl]
  · rw [seq.getSuccessors!_eq hfresh, OperationPtr.getSuccessors!_WfRewriter_createOp hCo,
      if_pos rfl]
  · rw [seq.getProperties!_eq hfresh]
    have := OperationPtr.getProperties!_WfRewriter_createOp hCo (operation := o)
    rw [if_pos rfl] at this; exact this

end ModArithToArithOriginal

/-! ## The imperative correctness statement -/

/--
The value mapping exhibited by a fired imperative pattern: it renames `op`'s single result to the
new value `newValue`, and is the identity on every other value.  This mirrors
`LocalRewritePattern.mapping`, specialised to the single-result, single-replacement-value shape of
the lowering patterns.  `mapInBounds` packages the in-bounds facts the mapping needs.
-/
def ImperativeMapping {ctx ctx' : WfIRContext OpCode} (op : OperationPtr) (newValue : ValuePtr)
    (mapInBounds : (∀ v : ValuePtr, v.InBounds ctx.raw → v ∉ op.getResults! ctx.raw →
        v.InBounds ctx'.raw) ∧ newValue.InBounds ctx'.raw) :
    ValueMapping ctx ctx' :=
  fun ⟨v, vInBounds⟩ =>
    if h : v ∈ op.getResults! ctx.raw then
      ⟨newValue, mapInBounds.2⟩
    else
      ⟨v, mapInBounds.1 v vInBounds h⟩

/--
Correctness of an imperative `RewritePattern`.  Whenever the pattern *fires* on a verified,
dominating operation `op` (whose single result is `op.getResult 0`), it exhibits a list of fresh
operations `newOps` and a replacement value `newValue` such that:

* every op in `newOps` is fresh (in bounds afterwards, not before);
* `newValue` is in bounds afterwards;
* for every source interpretation of `op` and every target state refining the source state through
  the exhibited `ImperativeMapping`, interpreting `newOps` reaches a state with the *same memory*
  whose binding for `newValue` refines `op`'s result.

This is the imperative analogue of `LocalRewritePattern.PreservesSemantics`.
-/
def ImperativePatternCorrect (pattern : RewritePattern OpCode) : Prop :=
  ∀ (rw : PatternRewriter OpCode) (op : OperationPtr) (rw' : PatternRewriter OpCode),
    rw.ctx.Dom → rw.ctx.Verified → (opInBounds : op.InBounds rw.ctx.raw) →
    pattern rw op = some rw' → rw'.ctx ≠ rw.ctx →
    ∃ (newOps : List OperationPtr) (newValue : ValuePtr)
      (hfresh : ∀ o ∈ newOps, o.InBounds rw'.ctx.raw ∧ ¬ o.InBounds rw.ctx.raw)
      (hnewIn : newValue.InBounds rw'.ctx.raw)
      (mapInBounds : (∀ v : ValuePtr, v.InBounds rw.ctx.raw → v ∉ op.getResults! rw.ctx.raw →
          v.InBounds rw'.ctx.raw) ∧ newValue.InBounds rw'.ctx.raw),
      ∀ (state : InterpreterState rw.ctx) (newState : InterpreterState rw.ctx) cf,
        interpretOp op state opInBounds = some (.ok (newState, cf)) →
        ∀ srcVal, newState.variables.getVar? (op.getResult 0) = some srcVal →
        ∀ (state' : InterpreterState rw'.ctx),
          state.isRefinedBy state' (ImperativeMapping op newValue mapInBounds) →
          ∃ newState',
            interpretOpList newOps state'
                (by exact fun o ho => (hfresh o ho).1) = some (.ok (newState', cf)) ∧
              newState.memory = newState'.memory ∧
              ∃ tgtVal, newState'.variables.getVar? newValue = some tgtVal ∧ srcVal ⊒ tgtVal

/-! ## Inversion of `lowerModArithBinOp`

When the pattern fired (`rw'.ctx ≠ rw.ctx`), it matched a `.mod_arith modOp` op of `!mod_arith.int`
type, ran the unpack/const/build/remui/pack helper chain, and finished with `replaceAndErase`.  This
exposes the six helper-level step equations, leaving the pattern-specific `build` step abstract. -/

namespace ModArithToArithOriginal

theorem lowerModArithBinOp_fired_inv {modOp : Mod_Arith} {widen : Nat → Nat} {build : Builder}
    {rw : PatternRewriter OpCode} {op : OperationPtr} {rw' : PatternRewriter OpCode}
    (h : lowerModArithBinOp modOp widen build rw op = some rw') (hne : rw'.ctx ≠ rw.ctx) :
    ∃ (operands : Array ValuePtr) (mt : ModArithType)
      (rwA : PatternRewriter OpCode) (a : ValuePtr)
      (rwB : PatternRewriter OpCode) (b : ValuePtr)
      (rwQ : PatternRewriter OpCode) (q : ValuePtr)
      (rwBuild : PatternRewriter OpCode) (rBuild : ValuePtr)
      (rwRem : PatternRewriter OpCode) (rRem : ValuePtr)
      (rwPack : PatternRewriter OpCode) (rPack : ValuePtr),
      matchOp op rw.ctx.raw (.mod_arith modOp) 2 = some (operands,
        op.getProperties! rw.ctx.raw (.mod_arith modOp)) ∧
      ((op.getResult 0 : ValuePtr).getType! rw.ctx.raw).val = .modArithType mt ∧
      unpackValue rw operands[0]! (IntegerType.mk (widen mt.modulus.type.bitwidth))
        (InsertPoint.before op) = some (rwA, a) ∧
      unpackValue rwA operands[1]! (IntegerType.mk (widen mt.modulus.type.bitwidth))
        (InsertPoint.before op) = some (rwB, b) ∧
      emitArithConstant rwB mt.modulus.value (widen mt.modulus.type.bitwidth)
        (InsertPoint.before op) = some (rwQ, q) ∧
      build rwQ a b q (InsertPoint.before op) = some (rwBuild, rBuild) ∧
      emitArithBinOp rwBuild .remui () rBuild q (InsertPoint.before op) = some (rwRem, rRem) ∧
      packValue rwRem rRem mt (InsertPoint.before op) = some (rwPack, rPack) ∧
      replaceAndErase rwPack op rPack = some rw' := by
  unfold lowerModArithBinOp at h
  split at h
  · rename_i operands props hmatch
    simp only at h
    split at h
    · rename_i mt hmt
      simp only [bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwA, a⟩, hunpackA, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwB, b⟩, hunpackB, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwQ, q⟩, hconst, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwBuild, rBuild⟩, hbuild, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwRem, rRem⟩, hrem, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwPack, rPack⟩, hpack, h⟩ := h
      -- recover the matched properties from `matchOp`
      obtain ⟨_, _, _, hopr, hprops⟩ := matchOp_some_inv hmatch
      refine ⟨operands, mt, rwA, a, rwB, b, rwQ, q, rwBuild, rBuild, rwRem, rRem, rwPack, rPack,
        ?_, hmt, hunpackA, hunpackB, hconst, hbuild, hrem, hpack, h⟩
      rw [← hprops]; exact hmatch
    · rename_i hnotmod
      simp only [pure, Option.some.injEq] at h
      exact absurd (by rw [← h]) hne
  · rename_i hnomatch
    simp only [pure, Option.some.injEq] at h
    exact absurd (by rw [← h]) hne

/-- `buildAdd` emits a single `addi`. -/
theorem buildAdd_inv {rw : PatternRewriter OpCode} {a b q : ValuePtr} {ip : InsertPoint}
    {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : buildAdd rw a b q ip = some (rw', cv)) :
    ∃ (addOp : OperationPtr), cv = (addOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.arith .addi) #[a.getType! rw.ctx.raw] #[a, b]
          #[] #[] ({ attr := { nsw := false, nuw := false } } : propertiesOf (.arith .addi))
          (some ip) h1 h2 h3 h4 = some (rw'.ctx, addOp) :=
  emitArithBinOp_inv h

/-- `buildMul` emits a single `muli`. -/
theorem buildMul_inv {rw : PatternRewriter OpCode} {a b q : ValuePtr} {ip : InsertPoint}
    {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : buildMul rw a b q ip = some (rw', cv)) :
    ∃ (mulOp : OperationPtr), cv = (mulOp.getResult 0 : ValuePtr) ∧
      ∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.arith .muli) #[a.getType! rw.ctx.raw] #[a, b]
          #[] #[] ({ attr := { nsw := false, nuw := false } } : propertiesOf (.arith .muli))
          (some ip) h1 h2 h3 h4 = some (rw'.ctx, mulOp) :=
  emitArithBinOp_inv h

/-- `buildSub` emits `addi a q` (producing `aq`) then `subi aq b`. -/
theorem buildSub_inv {rw : PatternRewriter OpCode} {a b q : ValuePtr} {ip : InsertPoint}
    {rw' : PatternRewriter OpCode} {cv : ValuePtr}
    (h : buildSub rw a b q ip = some (rw', cv)) :
    ∃ (rwAdd : PatternRewriter OpCode) (addOp subOp : OperationPtr),
      cv = (subOp.getResult 0 : ValuePtr) ∧
      (∃ h1 h2 h3 h4,
        WfRewriter.createOp rw.ctx (.arith .addi) #[a.getType! rw.ctx.raw] #[a, q]
          #[] #[] ({ attr := { nsw := false, nuw := false } } : propertiesOf (.arith .addi))
          (some ip) h1 h2 h3 h4 = some (rwAdd.ctx, addOp)) ∧
      (∃ h1 h2 h3 h4,
        WfRewriter.createOp rwAdd.ctx (.arith .subi)
          #[(addOp.getResult 0 : ValuePtr).getType! rwAdd.ctx.raw]
          #[(addOp.getResult 0 : ValuePtr), b] #[] #[]
          ({ attr := { nsw := false, nuw := false } } : propertiesOf (.arith .subi))
          (some ip) h1 h2 h3 h4 = some (rw'.ctx, subOp)) := by
  unfold buildSub at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨⟨rwAdd, aq⟩, hadd, h⟩ := h
  obtain ⟨addOp, haq_eq, _, _, _, _, hCadd⟩ := emitArithBinOp_inv hadd
  obtain ⟨subOp, hsub_eq, _, _, _, _, hCsub⟩ := emitArithBinOp_inv h
  subst haq_eq
  exact ⟨rwAdd, addOp, subOp, hsub_eq, ⟨_, _, _, _, hCadd⟩, ⟨_, _, _, _, hCsub⟩⟩

end ModArithToArithOriginal

set_option maxHeartbeats 2000000 in
/-- Direct semantics correctness of the imperative `mod_arith.add` lowering. -/
theorem lowerModArithAddOp_correct :
    ImperativePatternCorrect ModArithToArithOriginal.lowerModArithAddOp := by
  intro rw op rw' ctxDom ctxVerif opInBounds hpat hctxne
  -- Inversion of the imperative pattern into its nine helper-emitted ops.
  obtain ⟨operands, mt, rwA, a, rwB, b, rwQ, q, rwBuild, rBuild, rwRem, rRem, rwPack, rPack,
      hmatch, hmt, hunpA, hunpB, hconst, hbuild, hrem, hpack, herase⟩ :=
    ModArithToArithOriginal.lowerModArithBinOp_fired_inv hpat hctxne
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Verifier facts: operand/result types are the modulus type, modulus is valid.
  have hVerified : op.Verified rw.ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inl rfl)
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by
    rw [ValuePtr.getType!_opResult, hResTy] at hmt
    simp only [Attribute.modArithType.injEq] at hmt
    exact hmt
  subst mtv
  -- N ≥ 1 from a valid modulus, so the widen width N+1 > N: the ext/trunc branches fire.
  have hN1 : 1 ≤ mt.modulus.type.bitwidth := by
    rcases Nat.eq_zero_or_pos mt.modulus.type.bitwidth with h0 | h0
    · rw [h0] at hQwidth
      simp only [Nat.zero_sub, Int.pow_zero] at hQwidth
      omega
    · omega
  -- Operands of `op` are in bounds.
  have hFields : rw.ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed rw.ctx).inBounds
  have hOpSize : (op.getOperands! rw.ctx.raw).size = 2 := by grind
  have hlhsIn : operands[0]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]; exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]; exact Array.getElem_mem _
  -- The two operands carry the modulus type.
  have hLhsTy : operands[0]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  -- The result of a freshly created cast-to-storage op has the storage integer type `iN`.
  have castResTy : ∀ (c c' : PatternRewriter OpCode) (v : ValuePtr) (castOp : OperationPtr) h1 h2 h3 h4,
      WfRewriter.createOp c.ctx (.builtin .unrealized_conversion_cast) #[mt.modulus.type] #[v]
        #[] #[] () (some (InsertPoint.before op)) h1 h2 h3 h4 = some (c'.ctx, castOp) →
      ((castOp.getResult 0 : ValuePtr).getType! c'.ctx.raw).val = .integerType mt.modulus.type := by
    intro c c' v castOp h1 h2 h3 h4 hC
    have := ValuePtr.getType!_WfRewriter_createOp hC (value := (castOp.getResult 0 : ValuePtr))
    simp only [OperationPtr.getResult] at this ⊢
    rw [this]
    simp
  -- # Extract the nine created operations.
  -- unpack lhs: cast₀ (iN), then ext₁ (iN → iN+1).
  obtain ⟨mt0, rwCastA, cast0, st0, hlhsTy0, hcast0Ty, ⟨_, _, _, _, hC0⟩, hbranchA⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpA
  have hmt0 : mt0 = mt := by
    have := hlhsTy0; rw [hLhsTy] at this; simpa using this.symm
  subst mt0
  -- The stored type is iN, so width N+1 > N: the ext branch must have fired.
  have hst0 : st0 = mt.modulus.type := by
    have h := castResTy rw rwCastA operands[0]! cast0 _ _ _ _ hC0
    rw [hcast0Ty] at h
    simp only [Attribute.integerType.injEq] at h
    exact h
  subst hst0
  obtain ⟨_, ext1, ha_eq, _, _, _, _, hC1⟩ | ⟨hbad, _, _⟩ := hbranchA
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- unpack rhs: cast₂ (iN), then ext₃.
  -- `WfCreatedSeq` from `rw.ctx` up to `rwA.ctx` (cast₀ then ext₁), to transfer the rhs type.
  have seq_rwA : WfCreatedSeq rw.ctx rwA.ctx := (WfCreatedSeq.single hC0).snoc hC1
  have hRhsTyA : operands[1]!.getType! rwA.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [seq_rwA.getType!_eq hrhsIn]; exact hRhsTy
  obtain ⟨mt2, rwCastB, cast2, st2, hrhsTy2, hcast2Ty, ⟨_, _, _, _, hC2⟩, hbranchB⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpB
  have hmt2 : mt2 = mt := by
    have := hrhsTy2; rw [hRhsTyA] at this; simpa using this.symm
  subst mt2
  have hst2 : st2 = mt.modulus.type := by
    have h := castResTy rwA rwCastB operands[1]! cast2 _ _ _ _ hC2
    rw [hcast2Ty] at h; simp only [Attribute.integerType.injEq] at h; exact h
  subst hst2
  obtain ⟨_, ext3, hb_eq, _, _, _, _, hC3⟩ | ⟨hbad, _, _⟩ := hbranchB
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- constant q : i(N+1).
  obtain ⟨const4, hq_eq, _, _, _, _, hC4⟩ := ModArithToArithOriginal.emitArithConstant_inv hconst
  -- add₅ : i(N+1).
  obtain ⟨add5, hrBuild_eq, _, _, _, _, hC5⟩ := ModArithToArithOriginal.buildAdd_inv hbuild
  -- rem₆ : i(N+1).
  obtain ⟨rem6, hrRem_eq, _, _, _, _, hC6⟩ := ModArithToArithOriginal.emitArithBinOp_inv hrem
  -- ## The intermediate-value width is N+1 along the add → remui chain.
  -- `a` (ext₁'s result) has type i(N+1).
  have haTyA : (ext1.getResult 0 : ValuePtr).getType! rwA.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := createOp_result0_type hC1
  -- Transfer `a`'s type along cast₂, ext₃, const₄ to `rwQ.ctx`.
  have seq_AtoQ : WfCreatedSeq rwA.ctx rwQ.ctx :=
    (((WfCreatedSeq.single hC2).snoc hC3).snoc hC4)
  have hExt1InA : (ext1.getResult 0 : ValuePtr).InBounds rwA.ctx.raw := by
    have hfr := WfRewriter.createOp_new_inBounds _ hC1
    have hnr : ext1.getNumResults! rwA.ctx.raw = 1 := by
      rw [OperationPtr.getNumResults!_WfRewriter_createOp hC1, if_pos rfl]; rfl
    have : (OpResultPtr.mk ext1 0).InBounds rwA.ctx.raw :=
      OpResultPtr.inBounds_of hfr (by simp only [hnr]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have haTyQ : (ext1.getResult 0 : ValuePtr).getType! rwQ.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    rw [seq_AtoQ.getType!_eq hExt1InA]; exact haTyA
  -- add₅'s result (`rBuild`) has type i(N+1): its result type is `a`'s type in `rwQ.ctx`.
  have hrBuildTy : (add5.getResult 0 : ValuePtr).getType! rwBuild.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    have h := createOp_result0_type hC5
    rw [ha_eq, haTyQ] at h; exact h
  -- rem₆'s result (`rRem`) has type i(N+1): its result type is `rBuild`'s type in `rwBuild.ctx`.
  have hrRemTy : (rem6.getResult 0 : ValuePtr).getType! rwRem.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    have h := createOp_result0_type hC6
    rw [hrBuild_eq, hrBuildTy] at h; exact h
  -- pack: trunc₇ (i(N+1) → iN), cast₈ (iN → modArith).
  obtain ⟨it7, hrRemTy7, hbranchP⟩ := ModArithToArithOriginal.packValue_inv hpack
  -- `it7 = i(N+1)`, so the trunc branch fired.
  have hit7 : it7 = IntegerType.mk (mt.modulus.type.bitwidth + 1) := by
    have := hrRemTy7
    rw [hrRem_eq, hrRemTy] at this
    simp only [Attribute.integerType.injEq] at this
    exact this.symm
  subst hit7
  obtain ⟨hgt7, rwTrunc, trunc7, cast8, hrPack_eq, ⟨_, _, _, _, hC7⟩, ⟨_, _, _, _, hC8⟩⟩
    | ⟨hbad7, _⟩ := hbranchP
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad7; omega
  -- Result-value abbreviations.
  subst ha_eq hb_eq hq_eq hrBuild_eq hrRem_eq hrPack_eq
  -- # `WfCreatedSeq` suffix chains from each creation context up to `rwPack.ctx`.
  have s8 : WfCreatedSeq rwPack.ctx rwPack.ctx := .nil
  have s7 : WfCreatedSeq rwTrunc.ctx rwPack.ctx := .single hC8
  have s6 : WfCreatedSeq rwRem.ctx rwPack.ctx := (WfCreatedSeq.single hC7).snoc hC8
  have s5 : WfCreatedSeq rwBuild.ctx rwPack.ctx := ((WfCreatedSeq.single hC6).snoc hC7).snoc hC8
  have s4 : WfCreatedSeq rwQ.ctx rwPack.ctx :=
    (((WfCreatedSeq.single hC5).snoc hC6).snoc hC7).snoc hC8
  have s3 : WfCreatedSeq rwB.ctx rwPack.ctx :=
    ((((WfCreatedSeq.single hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s2 : WfCreatedSeq rwCastB.ctx rwPack.ctx :=
    (((((WfCreatedSeq.single hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s1 : WfCreatedSeq rwA.ctx rwPack.ctx :=
    ((((((WfCreatedSeq.single hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s0 : WfCreatedSeq rwCastA.ctx rwPack.ctx :=
    (((((((WfCreatedSeq.single hC1).snoc hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc
      hC8
  -- # Per-op shape facts in `rwPack.ctx` (where all nine ops exist).
  obtain ⟨f0In, f0Ty, f0Ops, f0RT, f0NR, f0Succ, f0P⟩ := newOpFactsAtPack hC0 s0
  obtain ⟨f1In, f1Ty, f1Ops, f1RT, f1NR, f1Succ, f1P⟩ := newOpFactsAtPack hC1 s1
  obtain ⟨f2In, f2Ty, f2Ops, f2RT, f2NR, f2Succ, f2P⟩ := newOpFactsAtPack hC2 s2
  obtain ⟨f3In, f3Ty, f3Ops, f3RT, f3NR, f3Succ, f3P⟩ := newOpFactsAtPack hC3 s3
  obtain ⟨f4In, f4Ty, f4Ops, f4RT, f4NR, f4Succ, f4P⟩ := newOpFactsAtPack hC4 s4
  obtain ⟨f5In, f5Ty, f5Ops, f5RT, f5NR, f5Succ, f5P⟩ := newOpFactsAtPack hC5 s5
  obtain ⟨f6In, f6Ty, f6Ops, f6RT, f6NR, f6Succ, f6P⟩ := newOpFactsAtPack hC6 s6
  obtain ⟨f7In, f7Ty, f7Ops, f7RT, f7NR, f7Succ, f7P⟩ := newOpFactsAtPack hC7 s7
  obtain ⟨f8In, f8Ty, f8Ops, f8RT, f8NR, f8Succ, f8P⟩ := newOpFactsAtPack hC8 s8
  -- # The final rewiring: replaceValue (op's result → rPack) then eraseOp op.
  obtain ⟨ctxR, hRne, hRold, hRnew, hctxR, hRregions, hRuses, hRop, hfinal⟩ :=
    ModArithToArithOriginal.replaceAndErase_inv herase
  -- Each new op is distinct from `op` (it is fresh, `op` is not).
  have freshNe : ∀ {o : OperationPtr}, o.InBounds rwPack.ctx.raw →
      ¬ o.InBounds rw.ctx.raw → o ≠ op := by
    intro o hPack hNotRw heq; subst heq; exact hNotRw opInBounds
  -- All nine ops are fresh w.r.t. `rw.ctx`.
  have notRw : ∀ {cM cN : WfIRContext OpCode} {T rt ops bo rg} {p : propertiesOf T} {ipx ha hb hc hd}
      {o : OperationPtr},
      WfRewriter.createOp cM T rt ops bo rg p ipx ha hb hc hd = some (cN, o) →
      WfCreatedSeq rw.ctx cM → ¬ o.InBounds rw.ctx.raw := by
    intro cM cN T rt ops bo rg p ipx ha hb hc hd o hCo seqPre hin
    exact (WfRewriter.createOp_new_not_inBounds _ hCo) (seqPre.inBounds_mono (.operation o) hin)
  -- Prefix chains `rw.ctx → <creation ctx>` for each op, giving freshness.
  have p1 : WfCreatedSeq rw.ctx rwCastA.ctx := .single hC0
  have p2 : WfCreatedSeq rw.ctx rwA.ctx := p1.snoc hC1
  have p3 : WfCreatedSeq rw.ctx rwCastB.ctx := p2.snoc hC2
  have p4 : WfCreatedSeq rw.ctx rwB.ctx := p3.snoc hC3
  have p5 : WfCreatedSeq rw.ctx rwQ.ctx := p4.snoc hC4
  have p6 : WfCreatedSeq rw.ctx rwBuild.ctx := p5.snoc hC5
  have p7 : WfCreatedSeq rw.ctx rwRem.ctx := p6.snoc hC6
  have p8 : WfCreatedSeq rw.ctx rwTrunc.ctx := p7.snoc hC7
  have n0 : ¬ cast0.InBounds rw.ctx.raw := notRw hC0 .nil
  have n1 : ¬ ext1.InBounds rw.ctx.raw := notRw hC1 p1
  have n2 : ¬ cast2.InBounds rw.ctx.raw := notRw hC2 p2
  have n3 : ¬ ext3.InBounds rw.ctx.raw := notRw hC3 p3
  have n4 : ¬ const4.InBounds rw.ctx.raw := notRw hC4 p4
  have n5 : ¬ add5.InBounds rw.ctx.raw := notRw hC5 p5
  have n6 : ¬ rem6.InBounds rw.ctx.raw := notRw hC6 p6
  have n7 : ¬ trunc7.InBounds rw.ctx.raw := notRw hC7 p7
  have n8 : ¬ cast8.InBounds rw.ctx.raw := notRw hC8 p8
  -- `op`'s result differs from any other op's result, and from `lhs`/`rhs` (dominance).
  have resNe : ∀ {o' : OperationPtr}, o' ≠ op →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hne heq
    apply hne
    simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at heq
    exact heq.1.symm
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  have hLhsMem : operands[0]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hLhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[0]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  have hRhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[1]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  subst hctxR
  have hRuses' : (!op.hasUses! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
      (cast8.getResult 0) hRne hRold hRnew).raw) = true := by simpa using hRuses
  -- `opSurvives` packaged for our fixed replace/erase, transferring `rwPack.ctx` facts to `rw'.ctx`.
  have surv : ∀ (o : OperationPtr), o ≠ op → o.InBounds rwPack.ctx.raw →
      (op.getResult 0 : ValuePtr) ∉ o.getOperands! rwPack.ctx.raw →
      o.InBounds rw'.ctx.raw ∧
      o.getOpType! rw'.ctx.raw = o.getOpType! rwPack.ctx.raw ∧
      o.getOperands! rw'.ctx.raw = o.getOperands! rwPack.ctx.raw ∧
      o.getResultTypes! rw'.ctx.raw = o.getResultTypes! rwPack.ctx.raw ∧
      o.getNumResults! rw'.ctx.raw = o.getNumResults! rwPack.ctx.raw ∧
      o.getSuccessors! rw'.ctx.raw = o.getSuccessors! rwPack.ctx.raw ∧
      (∀ T, o.getProperties! rw'.ctx.raw T = o.getProperties! rwPack.ctx.raw T) := by
    intro o hne hin hnm
    have := ModArithToArithOriginal.opSurvives (op := op) (o := o) hRne hRold hRnew hRregions
      hRuses' hRop hne hin hnm
    rw [hfinal]; exact this
  -- `op`'s result differs from each fresh op's result.
  have neNew : ∀ {o' : OperationPtr}, ¬ o'.InBounds rw.ctx.raw →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hfr
    exact resNe (fun heq => hfr (heq ▸ opInBounds))
  -- The replaced value is not among any new op's operands (in `rwPack.ctx`).
  have nm0 : (op.getResult 0 : ValuePtr) ∉ cast0.getOperands! rwPack.ctx.raw := by
    rw [f0Ops]; simp only [Array.mem_singleton]; exact hLhsNeRes
  have nm1 : (op.getResult 0 : ValuePtr) ∉ ext1.getOperands! rwPack.ctx.raw := by
    rw [f1Ops]; simp only [Array.mem_singleton]; exact neNew n0
  have nm2 : (op.getResult 0 : ValuePtr) ∉ cast2.getOperands! rwPack.ctx.raw := by
    rw [f2Ops]; simp only [Array.mem_singleton]; exact hRhsNeRes
  have nm3 : (op.getResult 0 : ValuePtr) ∉ ext3.getOperands! rwPack.ctx.raw := by
    rw [f3Ops]; simp only [Array.mem_singleton]; exact neNew n2
  have nm4 : (op.getResult 0 : ValuePtr) ∉ const4.getOperands! rwPack.ctx.raw := by
    rw [f4Ops]; simp
  have nm5 : (op.getResult 0 : ValuePtr) ∉ add5.getOperands! rwPack.ctx.raw := by
    rw [f5Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n1 h
    · exact neNew n3 h
  have nm6 : (op.getResult 0 : ValuePtr) ∉ rem6.getOperands! rwPack.ctx.raw := by
    rw [f6Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n5 h
    · exact neNew n4 h
  have nm7 : (op.getResult 0 : ValuePtr) ∉ trunc7.getOperands! rwPack.ctx.raw := by
    rw [f7Ops]; simp only [Array.mem_singleton]; exact neNew n6
  have nm8 : (op.getResult 0 : ValuePtr) ∉ cast8.getOperands! rwPack.ctx.raw := by
    rw [f8Ops]; simp only [Array.mem_singleton]; exact neNew n7
  -- # Survive to `rw'.ctx`.
  obtain ⟨g0In, g0Ty, g0Ops, g0RT, g0NR, g0Succ, g0P⟩ := surv cast0 (freshNe f0In n0) f0In nm0
  obtain ⟨g1In, g1Ty, g1Ops, g1RT, g1NR, g1Succ, g1P⟩ := surv ext1 (freshNe f1In n1) f1In nm1
  obtain ⟨g2In, g2Ty, g2Ops, g2RT, g2NR, g2Succ, g2P⟩ := surv cast2 (freshNe f2In n2) f2In nm2
  obtain ⟨g3In, g3Ty, g3Ops, g3RT, g3NR, g3Succ, g3P⟩ := surv ext3 (freshNe f3In n3) f3In nm3
  obtain ⟨g4In, g4Ty, g4Ops, g4RT, g4NR, g4Succ, g4P⟩ := surv const4 (freshNe f4In n4) f4In nm4
  obtain ⟨g5In, g5Ty, g5Ops, g5RT, g5NR, g5Succ, g5P⟩ := surv add5 (freshNe f5In n5) f5In nm5
  obtain ⟨g6In, g6Ty, g6Ops, g6RT, g6NR, g6Succ, g6P⟩ := surv rem6 (freshNe f6In n6) f6In nm6
  obtain ⟨g7In, g7Ty, g7Ops, g7RT, g7NR, g7Succ, g7P⟩ := surv trunc7 (freshNe f7In n7) f7In nm7
  obtain ⟨g8In, g8Ty, g8Ops, g8RT, g8NR, g8Succ, g8P⟩ := surv cast8 (freshNe f8In n8) f8In nm8
  -- # Combined op facts in `rw'.ctx`.
  -- Opcodes.
  have hTy0 : cast0.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g0Ty.trans f0Ty
  have hTy1 : ext1.getOpType! rw'.ctx.raw = .arith .extui := g1Ty.trans f1Ty
  have hTy2 : cast2.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g2Ty.trans f2Ty
  have hTy3 : ext3.getOpType! rw'.ctx.raw = .arith .extui := g3Ty.trans f3Ty
  have hTy4 : const4.getOpType! rw'.ctx.raw = .arith .constant := g4Ty.trans f4Ty
  have hTy5 : add5.getOpType! rw'.ctx.raw = .arith .addi := g5Ty.trans f5Ty
  have hTy6 : rem6.getOpType! rw'.ctx.raw = .arith .remui := g6Ty.trans f6Ty
  have hTy7 : trunc7.getOpType! rw'.ctx.raw = .arith .trunci := g7Ty.trans f7Ty
  have hTy8 : cast8.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g8Ty.trans f8Ty
  -- Operands.
  have hOperands0 : cast0.getOperands! rw'.ctx.raw = #[operands[0]!] := g0Ops.trans f0Ops
  have hOperands1 : ext1.getOperands! rw'.ctx.raw = #[(cast0.getResult 0 : ValuePtr)] :=
    g1Ops.trans f1Ops
  have hOperands2 : cast2.getOperands! rw'.ctx.raw = #[operands[1]!] := g2Ops.trans f2Ops
  have hOperands3 : ext3.getOperands! rw'.ctx.raw = #[(cast2.getResult 0 : ValuePtr)] :=
    g3Ops.trans f3Ops
  have hOperands4 : const4.getOperands! rw'.ctx.raw = #[] := g4Ops.trans f4Ops
  have hOperands5 : add5.getOperands! rw'.ctx.raw
      = #[(ext1.getResult 0 : ValuePtr), (ext3.getResult 0 : ValuePtr)] := g5Ops.trans f5Ops
  have hOperands6 : rem6.getOperands! rw'.ctx.raw
      = #[(add5.getResult 0 : ValuePtr), (const4.getResult 0 : ValuePtr)] := g6Ops.trans f6Ops
  have hOperands7 : trunc7.getOperands! rw'.ctx.raw = #[(rem6.getResult 0 : ValuePtr)] :=
    g7Ops.trans f7Ops
  have hOperands8 : cast8.getOperands! rw'.ctx.raw = #[(trunc7.getResult 0 : ValuePtr)] :=
    g8Ops.trans f8Ops
  -- Successors (all empty).
  have hSucc0 : cast0.getSuccessors! rw'.ctx.raw = #[] := g0Succ.trans f0Succ
  have hSucc1 : ext1.getSuccessors! rw'.ctx.raw = #[] := g1Succ.trans f1Succ
  have hSucc2 : cast2.getSuccessors! rw'.ctx.raw = #[] := g2Succ.trans f2Succ
  have hSucc3 : ext3.getSuccessors! rw'.ctx.raw = #[] := g3Succ.trans f3Succ
  have hSucc4 : const4.getSuccessors! rw'.ctx.raw = #[] := g4Succ.trans f4Succ
  have hSucc5 : add5.getSuccessors! rw'.ctx.raw = #[] := g5Succ.trans f5Succ
  have hSucc6 : rem6.getSuccessors! rw'.ctx.raw = #[] := g6Succ.trans f6Succ
  have hSucc7 : trunc7.getSuccessors! rw'.ctx.raw = #[] := g7Succ.trans f7Succ
  have hSucc8 : cast8.getSuccessors! rw'.ctx.raw = #[] := g8Succ.trans f8Succ
  -- Number of results (all one).
  have hNR0 : cast0.getNumResults! rw'.ctx.raw = 1 := g0NR.trans f0NR
  have hNR1 : ext1.getNumResults! rw'.ctx.raw = 1 := g1NR.trans f1NR
  have hNR2 : cast2.getNumResults! rw'.ctx.raw = 1 := g2NR.trans f2NR
  have hNR3 : ext3.getNumResults! rw'.ctx.raw = 1 := g3NR.trans f3NR
  have hNR4 : const4.getNumResults! rw'.ctx.raw = 1 := g4NR.trans f4NR
  have hNR5 : add5.getNumResults! rw'.ctx.raw = 1 := g5NR.trans f5NR
  have hNR6 : rem6.getNumResults! rw'.ctx.raw = 1 := g6NR.trans f6NR
  have hNR7 : trunc7.getNumResults! rw'.ctx.raw = 1 := g7NR.trans f7NR
  have hNR8 : cast8.getNumResults! rw'.ctx.raw = 1 := g8NR.trans f8NR
  -- Result types.
  have hRT0 : cast0.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g0RT.trans f0RT
  have hRT1 : ext1.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g1RT, f1RT]; rfl
  have hRT2 : cast2.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g2RT.trans f2RT
  have hRT3 : ext3.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g3RT, f3RT]; rfl
  have hRT4 : const4.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g4RT, f4RT]; rfl
  have hRT5 : add5.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [g5RT, f5RT, haTyQ]; rfl
  have hRT6 : rem6.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [g6RT, f6RT, hrBuildTy]; rfl
  have hRT7 : trunc7.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g7RT.trans f7RT
  have hRT8 : cast8.getResultTypes! rw'.ctx.raw = #[⟨.modArithType mt, by rfl⟩] := g8RT.trans f8RT
  -- Properties (only the ones the interpreter reads).
  have hP1 : ext1.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g1P _).trans f1P
  have hP3 : ext3.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g3P _).trans f3P
  have hP4 : const4.getProperties! rw'.ctx.raw (.arith .constant)
      = { value := IntegerAttr.mk mt.modulus.value (IntegerType.mk (mt.modulus.type.bitwidth + 1)) } :=
    (g4P _).trans f4P
  have hP5 : add5.getProperties! rw'.ctx.raw (.arith .addi) = { attr := { nsw := false, nuw := false } } :=
    (g5P _).trans f5P
  have hP7 : trunc7.getProperties! rw'.ctx.raw (.arith .trunci) = { attr := { nsw := false, nuw := true } } :=
    (g7P _).trans f7P
  -- The new value `cast8.getResult 0` is in bounds of `rw'.ctx`.
  have hNewValIn : (cast8.getResult 0 : ValuePtr).InBounds rw'.ctx.raw := by
    have : (OpResultPtr.mk cast8 0).InBounds rw'.ctx.raw :=
      OpResultPtr.inBounds_of g8In (by simp only [hNR8]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have seqFull : WfCreatedSeq rw.ctx rwPack.ctx := p8.snoc hC8
  -- `op`'s number of results is preserved into `rwPack.ctx`.
  have hOpNRPack : op.getNumResults! rwPack.ctx.raw = 1 := by
    rw [seqFull.getNumResults!_eq opInBounds]; exact hNumResults
  -- # Provide `newOps`, `newValue`, freshness, mapping in-bounds.
  refine ⟨[cast0, ext1, cast2, ext3, const4, add5, rem6, trunc7, cast8],
    (cast8.getResult 0 : ValuePtr), ?_, hNewValIn, ⟨?_, hNewValIn⟩, ?_⟩
  · -- freshness of every new op
    intro o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨g0In, n0⟩ | exact ⟨g1In, n1⟩ | exact ⟨g2In, n2⟩ | exact ⟨g3In, n3⟩
        | exact ⟨g4In, n4⟩ | exact ⟨g5In, n5⟩ | exact ⟨g6In, n6⟩ | exact ⟨g7In, n7⟩
        | exact ⟨g8In, n8⟩
  · -- in-bounds-preservation of the identity-on-non-results part of the mapping
    intro v hvIn hvNotRes
    have hvPack : v.InBounds rwPack.ctx.raw := seqFull.inBounds_mono (GenericPtr.value v) hvIn
    -- `v` is not a result of `op` in `rwPack.ctx` either (results depend only on numResults).
    have hvNotResPack : v ∉ op.getResults! rwPack.ctx.raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      rintro ⟨i, hi, heqv⟩
      apply hvNotRes
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      exact ⟨i, by rw [hNumResults]; rw [hOpNRPack] at hi; exact hi, heqv⟩
    have hvR : v.InBounds (WfRewriter.replaceValue rwPack.ctx (op.getResult 0) (cast8.getResult 0)
        hRne hRold hRnew).raw := by
      have := (WfRewriter.replaceValue_inBounds (ptr := GenericPtr.value v)
        (ne := hRne) (oldIn := hRold) (newIn := hRnew)).mpr
        (by simpa [GenericPtr.InBounds] using hvPack)
      simpa [GenericPtr.InBounds] using this
    have hvNotResR : v ∉ op.getResults! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
        (cast8.getResult 0) hRne hRold hRnew).raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index] at hvNotResPack ⊢
      simp only [OperationPtr.getNumResults!_WfRewriter_replaceValue] at *
      exact hvNotResPack
    rw [hfinal]
    exact ModArithToArithOriginal.valueSurvivesErase hvR hvNotResR
  -- # The semantics replay.
  intro state newState cf hinterp srcVal hsrcVal state' hrefines
  -- ## Source interpretation of `mod_arith.add`.
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := hOpArr
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) ∧ (x.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) ∧ (y.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mt.modulus.type.bitwidth (.val x),
      RuntimeValue.int mt.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  have hSrcNumRes : (op.getResultTypes! rw.ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! rw.ctx.raw)[0]? = some ⟨.modArithType mt, by rfl⟩ := by
    have h0 : (op.getResultTypes! rw.ctx.raw)[0]?
        = some ((op.getResultTypes! rw.ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  have hSrcEval' : interpretOp' (.mod_arith .add)
      (op.getProperties! rw.ctx.raw (.mod_arith .add)) (op.getResultTypes! rw.ctx.raw) srcOperandVals
      (op.getSuccessors! rw.ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.add mt.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.add mt.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  -- The single source result value.
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.add mt.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hsrcVal' : srcVal = RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.add mt.modulus.value x y)) := by
    rw [hvSrc] at hsrcVal; exact (Option.some.injEq _ _).mp hsrcVal.symm
  subst hsrcVal'
  -- ## Refinement transfer: operands take the same concrete value in `state'`.
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  have hLhsNotRes' : operands[0]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes' : operands[1]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hTLhs : state'.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    simp only [ImperativeMapping, dif_neg hLhsNotRes'] at htv
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
  have hTRhs : state'.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    simp only [ImperativeMapping, dif_neg hRhsNotRes'] at htv
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
  have hqm : 2 * mt.modulus.value ≤ 2 ^ (mt.modulus.type.bitwidth + 1) :=
    Data.ModArith.two_mul_modulus_le_two_pow_succ hN1 hQwidth
  have hnm : mt.modulus.type.bitwidth ≤ mt.modulus.type.bitwidth + 1 := by omega
  have hQle : mt.modulus.value ≤ 2 ^ mt.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  have hPipeEq : ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
        + y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
        mt.modulus.type.bitwidth = Data.ModArith.add mt.modulus.value x y :=
    Data.ModArith.addPipeline_eq_add hQpos hqm hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
        + y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).toNat : Int)
        < mt.modulus.value :=
    Data.ModArith.toNat_addPipeline_lt hQpos hqm hnm hxlt hylt
  -- ## Target interpretation: step through the nine created operations.
  -- Step cast₀: cast `lhs : iN`.
  have hOpVals0 : state'.variables.getOperandValues cast0
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands0 hTLhs
  have hEval0 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast0.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast0.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (cast0.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT0]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf0 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] (cast0.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT0 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs1, hSet0, hStep0⟩ := interpretOp_step (inB := g0In) hTy0 hOpVals0 hEval0 hConf0
  have hv1_0 : vs1.getVar? (cast0.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet0]; simp [hNR0]
  have hv1_rhs : vs1.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n0 hSet0]; exact hTRhs
  -- Step ext₁: `extui` of `x` to width `N+1`.
  have hOpVals1 : (InterpreterState.mk vs1 state'.memory).variables.getOperandValues ext1
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands1 hv1_0
  have hEval1 : interpretOp' (.arith .extui) (ext1.getProperties! rw'.ctx.raw (.arith .extui))
      (ext1.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (ext1.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT1, hP1]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mt.modulus.type.bitwidth + 1 ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf1 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (ext1.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT1 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs2, hSet1, hStep1⟩ := interpretOp_step (inB := g1In) hTy1 hOpVals1 hEval1 hConf1
  -- Step cast₂: cast `rhs : iN`.
  have hv2_rhs : vs2.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n1 hSet1]; exact hv1_rhs
  have hOpVals2 : (InterpreterState.mk vs2 state'.memory).variables.getOperandValues cast2
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands2 hv2_rhs
  have hEval2 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast2.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast2.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (cast2.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT2]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf2 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] (cast2.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT2 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs3, hSet2, hStep2⟩ := interpretOp_step (inB := g2In) hTy2 hOpVals2 hEval2 hConf2
  -- Step ext₃: `extui` of `y` to width `N+1`.
  have hv3_2 : vs3.getVar? (cast2.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet2]; simp [hNR2]
  have hOpVals3 : (InterpreterState.mk vs3 state'.memory).variables.getOperandValues ext3
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands3 hv3_2
  have hEval3 : interpretOp' (.arith .extui) (ext3.getProperties! rw'.ctx.raw (.arith .extui))
      (ext3.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (ext3.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT3, hP3]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mt.modulus.type.bitwidth + 1 ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf3 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (ext3.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT3 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs4, hSet3, hStep3⟩ := interpretOp_step (inB := g3In) hTy3 hOpVals3 hEval3 hConf3
  -- Step const₄: the modulus constant `q : i(N+1)`.
  have hOpVals4 : (InterpreterState.mk vs4 state'.memory).variables.getOperandValues const4
      = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands4, Array.mapM_eq_mapM_toList]; simp
  have hEval4 : interpretOp' (.arith .constant) (const4.getProperties! rw'.ctx.raw (.arith .constant))
      (const4.getResultTypes! rw'.ctx.raw) #[] (const4.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))],
          state'.memory, none)) := by
    rw [hRT4, hP4]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf4 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (const4.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT4 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs5, hSet4, hStep4⟩ := interpretOp_step (inB := g4In) hTy4 hOpVals4 hEval4 hConf4
  -- Step add₅.
  have hv2_1 : vs2.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet1]; simp [hNR1]
  have hv4_3 : vs4.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet3]; simp [hNR3]
  -- Distinctness of the created ops we thread operands through.
  -- `o₁` is in bounds at `o₂`'s creation context (a fresh `o₂` is not), so `o₁ ≠ o₂`.
  have d12 : ext1 ≠ cast2 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC2) (h ▸ WfRewriter.createOp_new_inBounds _ hC1)
  have d13 : ext1 ≠ ext3 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC3)
      (h ▸ ((WfCreatedSeq.single hC2).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d14 : ext1 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4)
      (h ▸ (((WfCreatedSeq.single hC2).snoc hC3).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d34 : ext3 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4) (h ▸ WfRewriter.createOp_new_inBounds _ hC3)
  have d45 : const4 ≠ add5 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC5) (h ▸ WfRewriter.createOp_new_inBounds _ hC4)
  have hv5_1 : vs5.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d14 hSet4, ModArithToArith.getVar?_setResultValues?_ne d13 hSet3,
      ModArithToArith.getVar?_setResultValues?_ne d12 hSet2]; exact hv2_1
  have hv5_3 : vs5.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d34 hSet4]; exact hv4_3
  have hOpVals5 : (InterpreterState.mk vs5 state'.memory).variables.getOperandValues add5
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))] :=
    ModArithToArith.getOperandValues_two hOperands5 hv5_1 hv5_3
  have hEval5 : interpretOp' (.arith .addi) (add5.getProperties! rw'.ctx.raw (.arith .addi))
      (add5.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (add5.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hP5]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf5 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (add5.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT5 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs6, hSet5, hStep5⟩ := interpretOp_step (inB := g5In) hTy5 hOpVals5 hEval5 hConf5
  -- Step rem₆: `remui` modulo `q`.
  have hv5_4 : vs5.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet4]; simp [hNR4]
  have hv6_5 : vs6.getVar? (add5.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet5]; simp [hNR5]
  have hv6_4 : vs6.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d45 hSet5]; exact hv5_4
  have hOpVals6 : (InterpreterState.mk vs6 state'.memory).variables.getOperandValues rem6
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)
              + y.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_two hOperands6 hv6_5 hv6_4
  have hEval6 : interpretOp' (.arith .remui) (rem6.getProperties! rw'.ctx.raw (.arith .remui))
      (rem6.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)
              + y.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (rem6.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))],
          state'.memory, none)) := by
    have hqne : BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value
        ≠ 0#(mt.modulus.type.bitwidth + 1) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := mt.modulus.type.bitwidth + 1) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf6 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (rem6.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT6 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs7, hSet6, hStep6⟩ := interpretOp_step (inB := g6In) hTy6 hOpVals6 hEval6 hConf6
  -- Step trunc₇: `trunci` (nuw) back to width `N`.
  have hv7_6 : vs7.getVar? (rem6.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet6]; simp [hNR6]
  have hOpVals7 : (InterpreterState.mk vs7 state'.memory).variables.getOperandValues trunc7
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_one hOperands7 hv7_6
  have hNoPoison : (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
        + y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
        mt.modulus.type.bitwidth).zeroExtend (mt.modulus.type.bitwidth + 1)
        = (x.zeroExtend (mt.modulus.type.bitwidth + 1)
        + y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    have hcast : (2:Int)^mt.modulus.type.bitwidth = ((2^mt.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval7 : interpretOp' (.arith .trunci) (trunc7.getProperties! rw'.ctx.raw (.arith .trunci))
      (trunc7.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (trunc7.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT7, hP7]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mt.modulus.type.bitwidth ≥ mt.modulus.type.bitwidth + 1) from by omega)]
  have hConf7 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (trunc7.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT7 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs8, hSet7, hStep7⟩ := interpretOp_step (inB := g7In) hTy7 hOpVals7 hEval7 hConf7
  -- Step cast₈: cast back to `!mod_arith.int`.
  have hv8_7 : vs8.getVar? (trunc7.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet7]; simp [hNR7]
  have hOpVals8 : (InterpreterState.mk vs8 state'.memory).variables.getOperandValues cast8
      = some #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))] :=
    ModArithToArith.getOperandValues_one hOperands8 hv8_7
  have hEval8 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast8.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast8.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1)
            + y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (cast8.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.add mt.modulus.value x y))], state'.memory, none)) := by
    rw [hRT8, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf8 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val (Data.ModArith.add mt.modulus.value x y))]
      (cast8.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT8 ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_add hQpos hQle⟩
  obtain ⟨vs9, hSet8, hStep8⟩ := interpretOp_step (inB := g8In) hTy8 hOpVals8 hEval8 hConf8
  -- ## Assemble the nine steps.
  refine ⟨⟨vs9, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [cast0, ext1, cast2, ext3, const4, add5, rem6, trunc7, cast8] state' _
      = some (.ok (⟨vs9, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep0]
    rw [interpretOpList_cons]; simp only [hStep1]
    rw [interpretOpList_cons]; simp only [hStep2]
    rw [interpretOpList_cons]; simp only [hStep3]
    rw [interpretOpList_cons]; simp only [hStep4]
    rw [interpretOpList_cons]; simp only [hStep5]
    rw [interpretOpList_cons]; simp only [hStep6]
    rw [interpretOpList_cons]; simp only [hStep7]
    rw [interpretOpList_cons]; simp only [hStep8]
    rfl
  · -- memory unchanged
    simpa using hMemEq
  · -- target value refines the source result
    refine ⟨RuntimeValue.int mt.modulus.type.bitwidth
        (.val (Data.ModArith.add mt.modulus.value x y)), ?_, ?_⟩
    · rw [VariableState.getVar?_setResultValues? hSet8]; simp [hNR8]
    · simp [RuntimeValue.isRefinedBy]


set_option maxHeartbeats 2000000 in
/-- Direct semantics correctness of the imperative `mod_arith.mul` lowering. -/
theorem lowerModArithMulOp_correct :
    ImperativePatternCorrect ModArithToArithOriginal.lowerModArithMulOp := by
  intro rw op rw' ctxDom ctxVerif opInBounds hpat hctxne
  -- Inversion of the imperative pattern into its nine helper-emitted ops.
  obtain ⟨operands, mt, rwA, a, rwB, b, rwQ, q, rwBuild, rBuild, rwRem, rRem, rwPack, rPack,
      hmatch, hmt, hunpA, hunpB, hconst, hbuild, hrem, hpack, herase⟩ :=
    ModArithToArithOriginal.lowerModArithBinOp_fired_inv hpat hctxne
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Verifier facts: operand/result types are the modulus type, modulus is valid.
  have hVerified : op.Verified rw.ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inr (Or.inr rfl))
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by
    rw [ValuePtr.getType!_opResult, hResTy] at hmt
    simp only [Attribute.modArithType.injEq] at hmt
    exact hmt
  subst mtv
  -- N ≥ 1 from a valid modulus, so the widen width N+1 > N: the ext/trunc branches fire.
  have hN1 : 1 ≤ mt.modulus.type.bitwidth := by
    rcases Nat.eq_zero_or_pos mt.modulus.type.bitwidth with h0 | h0
    · rw [h0] at hQwidth
      simp only [Nat.zero_sub, Int.pow_zero] at hQwidth
      omega
    · omega
  -- Operands of `op` are in bounds.
  have hFields : rw.ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed rw.ctx).inBounds
  have hOpSize : (op.getOperands! rw.ctx.raw).size = 2 := by grind
  have hlhsIn : operands[0]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]; exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]; exact Array.getElem_mem _
  -- The two operands carry the modulus type.
  have hLhsTy : operands[0]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  -- The result of a freshly created cast-to-storage op has the storage integer type `iN`.
  have castResTy : ∀ (c c' : PatternRewriter OpCode) (v : ValuePtr) (castOp : OperationPtr) h1 h2 h3 h4,
      WfRewriter.createOp c.ctx (.builtin .unrealized_conversion_cast) #[mt.modulus.type] #[v]
        #[] #[] () (some (InsertPoint.before op)) h1 h2 h3 h4 = some (c'.ctx, castOp) →
      ((castOp.getResult 0 : ValuePtr).getType! c'.ctx.raw).val = .integerType mt.modulus.type := by
    intro c c' v castOp h1 h2 h3 h4 hC
    have := ValuePtr.getType!_WfRewriter_createOp hC (value := (castOp.getResult 0 : ValuePtr))
    simp only [OperationPtr.getResult] at this ⊢
    rw [this]
    simp
  -- # Extract the nine created operations.
  -- unpack lhs: cast₀ (iN), then ext₁ (iN → iN+1).
  obtain ⟨mt0, rwCastA, cast0, st0, hlhsTy0, hcast0Ty, ⟨_, _, _, _, hC0⟩, hbranchA⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpA
  have hmt0 : mt0 = mt := by
    have := hlhsTy0; rw [hLhsTy] at this; simpa using this.symm
  subst mt0
  -- The stored type is iN, so width N+1 > N: the ext branch must have fired.
  have hst0 : st0 = mt.modulus.type := by
    have h := castResTy rw rwCastA operands[0]! cast0 _ _ _ _ hC0
    rw [hcast0Ty] at h
    simp only [Attribute.integerType.injEq] at h
    exact h
  subst hst0
  obtain ⟨_, ext1, ha_eq, _, _, _, _, hC1⟩ | ⟨hbad, _, _⟩ := hbranchA
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- unpack rhs: cast₂ (iN), then ext₃.
  -- `WfCreatedSeq` from `rw.ctx` up to `rwA.ctx` (cast₀ then ext₁), to transfer the rhs type.
  have seq_rwA : WfCreatedSeq rw.ctx rwA.ctx := (WfCreatedSeq.single hC0).snoc hC1
  have hRhsTyA : operands[1]!.getType! rwA.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [seq_rwA.getType!_eq hrhsIn]; exact hRhsTy
  obtain ⟨mt2, rwCastB, cast2, st2, hrhsTy2, hcast2Ty, ⟨_, _, _, _, hC2⟩, hbranchB⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpB
  have hmt2 : mt2 = mt := by
    have := hrhsTy2; rw [hRhsTyA] at this; simpa using this.symm
  subst mt2
  have hst2 : st2 = mt.modulus.type := by
    have h := castResTy rwA rwCastB operands[1]! cast2 _ _ _ _ hC2
    rw [hcast2Ty] at h; simp only [Attribute.integerType.injEq] at h; exact h
  subst hst2
  obtain ⟨_, ext3, hb_eq, _, _, _, _, hC3⟩ | ⟨hbad, _, _⟩ := hbranchB
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- constant q : i(N+1).
  obtain ⟨const4, hq_eq, _, _, _, _, hC4⟩ := ModArithToArithOriginal.emitArithConstant_inv hconst
  -- add₅ : i(N+1).
  obtain ⟨mul5, hrBuild_eq, _, _, _, _, hC5⟩ := ModArithToArithOriginal.buildMul_inv hbuild
  -- rem₆ : i(N+1).
  obtain ⟨rem6, hrRem_eq, _, _, _, _, hC6⟩ := ModArithToArithOriginal.emitArithBinOp_inv hrem
  -- ## The intermediate-value width is N+1 along the add → remui chain.
  -- `a` (ext₁'s result) has type i(N+1).
  have haTyA : (ext1.getResult 0 : ValuePtr).getType! rwA.ctx.raw
      = (IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr) := createOp_result0_type hC1
  -- Transfer `a`'s type along cast₂, ext₃, const₄ to `rwQ.ctx`.
  have seq_AtoQ : WfCreatedSeq rwA.ctx rwQ.ctx :=
    (((WfCreatedSeq.single hC2).snoc hC3).snoc hC4)
  have hExt1InA : (ext1.getResult 0 : ValuePtr).InBounds rwA.ctx.raw := by
    have hfr := WfRewriter.createOp_new_inBounds _ hC1
    have hnr : ext1.getNumResults! rwA.ctx.raw = 1 := by
      rw [OperationPtr.getNumResults!_WfRewriter_createOp hC1, if_pos rfl]; rfl
    have : (OpResultPtr.mk ext1 0).InBounds rwA.ctx.raw :=
      OpResultPtr.inBounds_of hfr (by simp only [hnr]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have haTyQ : (ext1.getResult 0 : ValuePtr).getType! rwQ.ctx.raw
      = (IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr) := by
    rw [seq_AtoQ.getType!_eq hExt1InA]; exact haTyA
  -- add₅'s result (`rBuild`) has type i(N+1): its result type is `a`'s type in `rwQ.ctx`.
  have hrBuildTy : (mul5.getResult 0 : ValuePtr).getType! rwBuild.ctx.raw
      = (IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr) := by
    have h := createOp_result0_type hC5
    rw [ha_eq, haTyQ] at h; exact h
  -- rem₆'s result (`rRem`) has type i(N+1): its result type is `rBuild`'s type in `rwBuild.ctx`.
  have hrRemTy : (rem6.getResult 0 : ValuePtr).getType! rwRem.ctx.raw
      = (IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr) := by
    have h := createOp_result0_type hC6
    rw [hrBuild_eq, hrBuildTy] at h; exact h
  -- pack: trunc₇ (i(N+1) → iN), cast₈ (iN → modArith).
  obtain ⟨it7, hrRemTy7, hbranchP⟩ := ModArithToArithOriginal.packValue_inv hpack
  -- `it7 = i(N+1)`, so the trunc branch fired.
  have hit7 : it7 = IntegerType.mk (2 * mt.modulus.type.bitwidth) := by
    have := hrRemTy7
    rw [hrRem_eq, hrRemTy] at this
    simp only [Attribute.integerType.injEq] at this
    exact this.symm
  subst hit7
  obtain ⟨hgt7, rwTrunc, trunc7, cast8, hrPack_eq, ⟨_, _, _, _, hC7⟩, ⟨_, _, _, _, hC8⟩⟩
    | ⟨hbad7, _⟩ := hbranchP
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad7; omega
  -- Result-value abbreviations.
  subst ha_eq hb_eq hq_eq hrBuild_eq hrRem_eq hrPack_eq
  -- # `WfCreatedSeq` suffix chains from each creation context up to `rwPack.ctx`.
  have s8 : WfCreatedSeq rwPack.ctx rwPack.ctx := .nil
  have s7 : WfCreatedSeq rwTrunc.ctx rwPack.ctx := .single hC8
  have s6 : WfCreatedSeq rwRem.ctx rwPack.ctx := (WfCreatedSeq.single hC7).snoc hC8
  have s5 : WfCreatedSeq rwBuild.ctx rwPack.ctx := ((WfCreatedSeq.single hC6).snoc hC7).snoc hC8
  have s4 : WfCreatedSeq rwQ.ctx rwPack.ctx :=
    (((WfCreatedSeq.single hC5).snoc hC6).snoc hC7).snoc hC8
  have s3 : WfCreatedSeq rwB.ctx rwPack.ctx :=
    ((((WfCreatedSeq.single hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s2 : WfCreatedSeq rwCastB.ctx rwPack.ctx :=
    (((((WfCreatedSeq.single hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s1 : WfCreatedSeq rwA.ctx rwPack.ctx :=
    ((((((WfCreatedSeq.single hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8
  have s0 : WfCreatedSeq rwCastA.ctx rwPack.ctx :=
    (((((((WfCreatedSeq.single hC1).snoc hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc
      hC8
  -- # Per-op shape facts in `rwPack.ctx` (where all nine ops exist).
  obtain ⟨f0In, f0Ty, f0Ops, f0RT, f0NR, f0Succ, f0P⟩ := newOpFactsAtPack hC0 s0
  obtain ⟨f1In, f1Ty, f1Ops, f1RT, f1NR, f1Succ, f1P⟩ := newOpFactsAtPack hC1 s1
  obtain ⟨f2In, f2Ty, f2Ops, f2RT, f2NR, f2Succ, f2P⟩ := newOpFactsAtPack hC2 s2
  obtain ⟨f3In, f3Ty, f3Ops, f3RT, f3NR, f3Succ, f3P⟩ := newOpFactsAtPack hC3 s3
  obtain ⟨f4In, f4Ty, f4Ops, f4RT, f4NR, f4Succ, f4P⟩ := newOpFactsAtPack hC4 s4
  obtain ⟨f5In, f5Ty, f5Ops, f5RT, f5NR, f5Succ, f5P⟩ := newOpFactsAtPack hC5 s5
  obtain ⟨f6In, f6Ty, f6Ops, f6RT, f6NR, f6Succ, f6P⟩ := newOpFactsAtPack hC6 s6
  obtain ⟨f7In, f7Ty, f7Ops, f7RT, f7NR, f7Succ, f7P⟩ := newOpFactsAtPack hC7 s7
  obtain ⟨f8In, f8Ty, f8Ops, f8RT, f8NR, f8Succ, f8P⟩ := newOpFactsAtPack hC8 s8
  -- # The final rewiring: replaceValue (op's result → rPack) then eraseOp op.
  obtain ⟨ctxR, hRne, hRold, hRnew, hctxR, hRregions, hRuses, hRop, hfinal⟩ :=
    ModArithToArithOriginal.replaceAndErase_inv herase
  -- Each new op is distinct from `op` (it is fresh, `op` is not).
  have freshNe : ∀ {o : OperationPtr}, o.InBounds rwPack.ctx.raw →
      ¬ o.InBounds rw.ctx.raw → o ≠ op := by
    intro o hPack hNotRw heq; subst heq; exact hNotRw opInBounds
  -- All nine ops are fresh w.r.t. `rw.ctx`.
  have notRw : ∀ {cM cN : WfIRContext OpCode} {T rt ops bo rg} {p : propertiesOf T} {ipx ha hb hc hd}
      {o : OperationPtr},
      WfRewriter.createOp cM T rt ops bo rg p ipx ha hb hc hd = some (cN, o) →
      WfCreatedSeq rw.ctx cM → ¬ o.InBounds rw.ctx.raw := by
    intro cM cN T rt ops bo rg p ipx ha hb hc hd o hCo seqPre hin
    exact (WfRewriter.createOp_new_not_inBounds _ hCo) (seqPre.inBounds_mono (.operation o) hin)
  -- Prefix chains `rw.ctx → <creation ctx>` for each op, giving freshness.
  have p1 : WfCreatedSeq rw.ctx rwCastA.ctx := .single hC0
  have p2 : WfCreatedSeq rw.ctx rwA.ctx := p1.snoc hC1
  have p3 : WfCreatedSeq rw.ctx rwCastB.ctx := p2.snoc hC2
  have p4 : WfCreatedSeq rw.ctx rwB.ctx := p3.snoc hC3
  have p5 : WfCreatedSeq rw.ctx rwQ.ctx := p4.snoc hC4
  have p6 : WfCreatedSeq rw.ctx rwBuild.ctx := p5.snoc hC5
  have p7 : WfCreatedSeq rw.ctx rwRem.ctx := p6.snoc hC6
  have p8 : WfCreatedSeq rw.ctx rwTrunc.ctx := p7.snoc hC7
  have n0 : ¬ cast0.InBounds rw.ctx.raw := notRw hC0 .nil
  have n1 : ¬ ext1.InBounds rw.ctx.raw := notRw hC1 p1
  have n2 : ¬ cast2.InBounds rw.ctx.raw := notRw hC2 p2
  have n3 : ¬ ext3.InBounds rw.ctx.raw := notRw hC3 p3
  have n4 : ¬ const4.InBounds rw.ctx.raw := notRw hC4 p4
  have n5 : ¬ mul5.InBounds rw.ctx.raw := notRw hC5 p5
  have n6 : ¬ rem6.InBounds rw.ctx.raw := notRw hC6 p6
  have n7 : ¬ trunc7.InBounds rw.ctx.raw := notRw hC7 p7
  have n8 : ¬ cast8.InBounds rw.ctx.raw := notRw hC8 p8
  -- `op`'s result differs from any other op's result, and from `lhs`/`rhs` (dominance).
  have resNe : ∀ {o' : OperationPtr}, o' ≠ op →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hne heq
    apply hne
    simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at heq
    exact heq.1.symm
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  have hLhsMem : operands[0]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hLhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[0]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  have hRhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[1]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  subst hctxR
  have hRuses' : (!op.hasUses! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
      (cast8.getResult 0) hRne hRold hRnew).raw) = true := by simpa using hRuses
  -- `opSurvives` packaged for our fixed replace/erase, transferring `rwPack.ctx` facts to `rw'.ctx`.
  have surv : ∀ (o : OperationPtr), o ≠ op → o.InBounds rwPack.ctx.raw →
      (op.getResult 0 : ValuePtr) ∉ o.getOperands! rwPack.ctx.raw →
      o.InBounds rw'.ctx.raw ∧
      o.getOpType! rw'.ctx.raw = o.getOpType! rwPack.ctx.raw ∧
      o.getOperands! rw'.ctx.raw = o.getOperands! rwPack.ctx.raw ∧
      o.getResultTypes! rw'.ctx.raw = o.getResultTypes! rwPack.ctx.raw ∧
      o.getNumResults! rw'.ctx.raw = o.getNumResults! rwPack.ctx.raw ∧
      o.getSuccessors! rw'.ctx.raw = o.getSuccessors! rwPack.ctx.raw ∧
      (∀ T, o.getProperties! rw'.ctx.raw T = o.getProperties! rwPack.ctx.raw T) := by
    intro o hne hin hnm
    have := ModArithToArithOriginal.opSurvives (op := op) (o := o) hRne hRold hRnew hRregions
      hRuses' hRop hne hin hnm
    rw [hfinal]; exact this
  -- `op`'s result differs from each fresh op's result.
  have neNew : ∀ {o' : OperationPtr}, ¬ o'.InBounds rw.ctx.raw →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hfr
    exact resNe (fun heq => hfr (heq ▸ opInBounds))
  -- The replaced value is not among any new op's operands (in `rwPack.ctx`).
  have nm0 : (op.getResult 0 : ValuePtr) ∉ cast0.getOperands! rwPack.ctx.raw := by
    rw [f0Ops]; simp only [Array.mem_singleton]; exact hLhsNeRes
  have nm1 : (op.getResult 0 : ValuePtr) ∉ ext1.getOperands! rwPack.ctx.raw := by
    rw [f1Ops]; simp only [Array.mem_singleton]; exact neNew n0
  have nm2 : (op.getResult 0 : ValuePtr) ∉ cast2.getOperands! rwPack.ctx.raw := by
    rw [f2Ops]; simp only [Array.mem_singleton]; exact hRhsNeRes
  have nm3 : (op.getResult 0 : ValuePtr) ∉ ext3.getOperands! rwPack.ctx.raw := by
    rw [f3Ops]; simp only [Array.mem_singleton]; exact neNew n2
  have nm4 : (op.getResult 0 : ValuePtr) ∉ const4.getOperands! rwPack.ctx.raw := by
    rw [f4Ops]; simp
  have nm5 : (op.getResult 0 : ValuePtr) ∉ mul5.getOperands! rwPack.ctx.raw := by
    rw [f5Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n1 h
    · exact neNew n3 h
  have nm6 : (op.getResult 0 : ValuePtr) ∉ rem6.getOperands! rwPack.ctx.raw := by
    rw [f6Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n5 h
    · exact neNew n4 h
  have nm7 : (op.getResult 0 : ValuePtr) ∉ trunc7.getOperands! rwPack.ctx.raw := by
    rw [f7Ops]; simp only [Array.mem_singleton]; exact neNew n6
  have nm8 : (op.getResult 0 : ValuePtr) ∉ cast8.getOperands! rwPack.ctx.raw := by
    rw [f8Ops]; simp only [Array.mem_singleton]; exact neNew n7
  -- # Survive to `rw'.ctx`.
  obtain ⟨g0In, g0Ty, g0Ops, g0RT, g0NR, g0Succ, g0P⟩ := surv cast0 (freshNe f0In n0) f0In nm0
  obtain ⟨g1In, g1Ty, g1Ops, g1RT, g1NR, g1Succ, g1P⟩ := surv ext1 (freshNe f1In n1) f1In nm1
  obtain ⟨g2In, g2Ty, g2Ops, g2RT, g2NR, g2Succ, g2P⟩ := surv cast2 (freshNe f2In n2) f2In nm2
  obtain ⟨g3In, g3Ty, g3Ops, g3RT, g3NR, g3Succ, g3P⟩ := surv ext3 (freshNe f3In n3) f3In nm3
  obtain ⟨g4In, g4Ty, g4Ops, g4RT, g4NR, g4Succ, g4P⟩ := surv const4 (freshNe f4In n4) f4In nm4
  obtain ⟨g5In, g5Ty, g5Ops, g5RT, g5NR, g5Succ, g5P⟩ := surv mul5 (freshNe f5In n5) f5In nm5
  obtain ⟨g6In, g6Ty, g6Ops, g6RT, g6NR, g6Succ, g6P⟩ := surv rem6 (freshNe f6In n6) f6In nm6
  obtain ⟨g7In, g7Ty, g7Ops, g7RT, g7NR, g7Succ, g7P⟩ := surv trunc7 (freshNe f7In n7) f7In nm7
  obtain ⟨g8In, g8Ty, g8Ops, g8RT, g8NR, g8Succ, g8P⟩ := surv cast8 (freshNe f8In n8) f8In nm8
  -- # Combined op facts in `rw'.ctx`.
  -- Opcodes.
  have hTy0 : cast0.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g0Ty.trans f0Ty
  have hTy1 : ext1.getOpType! rw'.ctx.raw = .arith .extui := g1Ty.trans f1Ty
  have hTy2 : cast2.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g2Ty.trans f2Ty
  have hTy3 : ext3.getOpType! rw'.ctx.raw = .arith .extui := g3Ty.trans f3Ty
  have hTy4 : const4.getOpType! rw'.ctx.raw = .arith .constant := g4Ty.trans f4Ty
  have hTy5 : mul5.getOpType! rw'.ctx.raw = .arith .muli := g5Ty.trans f5Ty
  have hTy6 : rem6.getOpType! rw'.ctx.raw = .arith .remui := g6Ty.trans f6Ty
  have hTy7 : trunc7.getOpType! rw'.ctx.raw = .arith .trunci := g7Ty.trans f7Ty
  have hTy8 : cast8.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g8Ty.trans f8Ty
  -- Operands.
  have hOperands0 : cast0.getOperands! rw'.ctx.raw = #[operands[0]!] := g0Ops.trans f0Ops
  have hOperands1 : ext1.getOperands! rw'.ctx.raw = #[(cast0.getResult 0 : ValuePtr)] :=
    g1Ops.trans f1Ops
  have hOperands2 : cast2.getOperands! rw'.ctx.raw = #[operands[1]!] := g2Ops.trans f2Ops
  have hOperands3 : ext3.getOperands! rw'.ctx.raw = #[(cast2.getResult 0 : ValuePtr)] :=
    g3Ops.trans f3Ops
  have hOperands4 : const4.getOperands! rw'.ctx.raw = #[] := g4Ops.trans f4Ops
  have hOperands5 : mul5.getOperands! rw'.ctx.raw
      = #[(ext1.getResult 0 : ValuePtr), (ext3.getResult 0 : ValuePtr)] := g5Ops.trans f5Ops
  have hOperands6 : rem6.getOperands! rw'.ctx.raw
      = #[(mul5.getResult 0 : ValuePtr), (const4.getResult 0 : ValuePtr)] := g6Ops.trans f6Ops
  have hOperands7 : trunc7.getOperands! rw'.ctx.raw = #[(rem6.getResult 0 : ValuePtr)] :=
    g7Ops.trans f7Ops
  have hOperands8 : cast8.getOperands! rw'.ctx.raw = #[(trunc7.getResult 0 : ValuePtr)] :=
    g8Ops.trans f8Ops
  -- Successors (all empty).
  have hSucc0 : cast0.getSuccessors! rw'.ctx.raw = #[] := g0Succ.trans f0Succ
  have hSucc1 : ext1.getSuccessors! rw'.ctx.raw = #[] := g1Succ.trans f1Succ
  have hSucc2 : cast2.getSuccessors! rw'.ctx.raw = #[] := g2Succ.trans f2Succ
  have hSucc3 : ext3.getSuccessors! rw'.ctx.raw = #[] := g3Succ.trans f3Succ
  have hSucc4 : const4.getSuccessors! rw'.ctx.raw = #[] := g4Succ.trans f4Succ
  have hSucc5 : mul5.getSuccessors! rw'.ctx.raw = #[] := g5Succ.trans f5Succ
  have hSucc6 : rem6.getSuccessors! rw'.ctx.raw = #[] := g6Succ.trans f6Succ
  have hSucc7 : trunc7.getSuccessors! rw'.ctx.raw = #[] := g7Succ.trans f7Succ
  have hSucc8 : cast8.getSuccessors! rw'.ctx.raw = #[] := g8Succ.trans f8Succ
  -- Number of results (all one).
  have hNR0 : cast0.getNumResults! rw'.ctx.raw = 1 := g0NR.trans f0NR
  have hNR1 : ext1.getNumResults! rw'.ctx.raw = 1 := g1NR.trans f1NR
  have hNR2 : cast2.getNumResults! rw'.ctx.raw = 1 := g2NR.trans f2NR
  have hNR3 : ext3.getNumResults! rw'.ctx.raw = 1 := g3NR.trans f3NR
  have hNR4 : const4.getNumResults! rw'.ctx.raw = 1 := g4NR.trans f4NR
  have hNR5 : mul5.getNumResults! rw'.ctx.raw = 1 := g5NR.trans f5NR
  have hNR6 : rem6.getNumResults! rw'.ctx.raw = 1 := g6NR.trans f6NR
  have hNR7 : trunc7.getNumResults! rw'.ctx.raw = 1 := g7NR.trans f7NR
  have hNR8 : cast8.getNumResults! rw'.ctx.raw = 1 := g8NR.trans f8NR
  -- Result types.
  have hRT0 : cast0.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g0RT.trans f0RT
  have hRT1 : ext1.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr)] := by rw [g1RT, f1RT]; rfl
  have hRT2 : cast2.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g2RT.trans f2RT
  have hRT3 : ext3.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr)] := by rw [g3RT, f3RT]; rfl
  have hRT4 : const4.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr)] := by rw [g4RT, f4RT]; rfl
  have hRT5 : mul5.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr)] := by
    rw [g5RT, f5RT, haTyQ]; rfl
  have hRT6 : rem6.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (2 * mt.modulus.type.bitwidth) : TypeAttr)] := by
    rw [g6RT, f6RT, hrBuildTy]; rfl
  have hRT7 : trunc7.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g7RT.trans f7RT
  have hRT8 : cast8.getResultTypes! rw'.ctx.raw = #[⟨.modArithType mt, by rfl⟩] := g8RT.trans f8RT
  -- Properties (only the ones the interpreter reads).
  have hP1 : ext1.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g1P _).trans f1P
  have hP3 : ext3.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g3P _).trans f3P
  have hP4 : const4.getProperties! rw'.ctx.raw (.arith .constant)
      = { value := IntegerAttr.mk mt.modulus.value (IntegerType.mk (2 * mt.modulus.type.bitwidth)) } :=
    (g4P _).trans f4P
  have hP5 : mul5.getProperties! rw'.ctx.raw (.arith .muli) = { attr := { nsw := false, nuw := false } } :=
    (g5P _).trans f5P
  have hP7 : trunc7.getProperties! rw'.ctx.raw (.arith .trunci) = { attr := { nsw := false, nuw := true } } :=
    (g7P _).trans f7P
  -- The new value `cast8.getResult 0` is in bounds of `rw'.ctx`.
  have hNewValIn : (cast8.getResult 0 : ValuePtr).InBounds rw'.ctx.raw := by
    have : (OpResultPtr.mk cast8 0).InBounds rw'.ctx.raw :=
      OpResultPtr.inBounds_of g8In (by simp only [hNR8]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have seqFull : WfCreatedSeq rw.ctx rwPack.ctx := p8.snoc hC8
  -- `op`'s number of results is preserved into `rwPack.ctx`.
  have hOpNRPack : op.getNumResults! rwPack.ctx.raw = 1 := by
    rw [seqFull.getNumResults!_eq opInBounds]; exact hNumResults
  -- # Provide `newOps`, `newValue`, freshness, mapping in-bounds.
  refine ⟨[cast0, ext1, cast2, ext3, const4, mul5, rem6, trunc7, cast8],
    (cast8.getResult 0 : ValuePtr), ?_, hNewValIn, ⟨?_, hNewValIn⟩, ?_⟩
  · -- freshness of every new op
    intro o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨g0In, n0⟩ | exact ⟨g1In, n1⟩ | exact ⟨g2In, n2⟩ | exact ⟨g3In, n3⟩
        | exact ⟨g4In, n4⟩ | exact ⟨g5In, n5⟩ | exact ⟨g6In, n6⟩ | exact ⟨g7In, n7⟩
        | exact ⟨g8In, n8⟩
  · -- in-bounds-preservation of the identity-on-non-results part of the mapping
    intro v hvIn hvNotRes
    have hvPack : v.InBounds rwPack.ctx.raw := seqFull.inBounds_mono (GenericPtr.value v) hvIn
    -- `v` is not a result of `op` in `rwPack.ctx` either (results depend only on numResults).
    have hvNotResPack : v ∉ op.getResults! rwPack.ctx.raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      rintro ⟨i, hi, heqv⟩
      apply hvNotRes
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      exact ⟨i, by rw [hNumResults]; rw [hOpNRPack] at hi; exact hi, heqv⟩
    have hvR : v.InBounds (WfRewriter.replaceValue rwPack.ctx (op.getResult 0) (cast8.getResult 0)
        hRne hRold hRnew).raw := by
      have := (WfRewriter.replaceValue_inBounds (ptr := GenericPtr.value v)
        (ne := hRne) (oldIn := hRold) (newIn := hRnew)).mpr
        (by simpa [GenericPtr.InBounds] using hvPack)
      simpa [GenericPtr.InBounds] using this
    have hvNotResR : v ∉ op.getResults! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
        (cast8.getResult 0) hRne hRold hRnew).raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index] at hvNotResPack ⊢
      simp only [OperationPtr.getNumResults!_WfRewriter_replaceValue] at *
      exact hvNotResPack
    rw [hfinal]
    exact ModArithToArithOriginal.valueSurvivesErase hvR hvNotResR
  -- # The semantics replay.
  intro state newState cf hinterp srcVal hsrcVal state' hrefines
  -- ## Source interpretation of `mod_arith.add`.
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := hOpArr
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) ∧ (x.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) ∧ (y.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mt.modulus.type.bitwidth (.val x),
      RuntimeValue.int mt.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  have hSrcNumRes : (op.getResultTypes! rw.ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! rw.ctx.raw)[0]? = some ⟨.modArithType mt, by rfl⟩ := by
    have h0 : (op.getResultTypes! rw.ctx.raw)[0]?
        = some ((op.getResultTypes! rw.ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  have hSrcEval' : interpretOp' (.mod_arith .mul)
      (op.getProperties! rw.ctx.raw (.mod_arith .mul)) (op.getResultTypes! rw.ctx.raw) srcOperandVals
      (op.getSuccessors! rw.ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.mul mt.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.mul mt.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  -- The single source result value.
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.mul mt.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hsrcVal' : srcVal = RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.mul mt.modulus.value x y)) := by
    rw [hvSrc] at hsrcVal; exact (Option.some.injEq _ _).mp hsrcVal.symm
  subst hsrcVal'
  -- ## Refinement transfer: operands take the same concrete value in `state'`.
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  have hLhsNotRes' : operands[0]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes' : operands[1]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hTLhs : state'.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    simp only [ImperativeMapping, dif_neg hLhsNotRes'] at htv
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
  have hTRhs : state'.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    simp only [ImperativeMapping, dif_neg hRhsNotRes'] at htv
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
  obtain ⟨hqsq, hqm2⟩ : mt.modulus.value * mt.modulus.value ≤ 2 ^ (2 * mt.modulus.type.bitwidth) ∧
      mt.modulus.value < 2 ^ (2 * mt.modulus.type.bitwidth) :=
    Data.ModArith.modulus_sq_lt_two_pow_two_mul hN1 (by omega) hQwidth
  have hnm : mt.modulus.type.bitwidth ≤ 2 * mt.modulus.type.bitwidth := by omega
  have hQle : mt.modulus.value ≤ 2 ^ mt.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  have hPipeEq : ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
        * y.zeroExtend (2 * mt.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
        mt.modulus.type.bitwidth = Data.ModArith.mul mt.modulus.value x y :=
    Data.ModArith.mulPipeline_eq_mul hQpos hqsq hqm2 hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
        * y.zeroExtend (2 * mt.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).toNat : Int)
        < mt.modulus.value :=
    Data.ModArith.toNat_mulPipeline_lt hQpos hqsq hqm2 hnm hxlt hylt
  -- ## Target interpretation: step through the nine created operations.
  -- Step cast₀: cast `lhs : iN`.
  have hOpVals0 : state'.variables.getOperandValues cast0
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands0 hTLhs
  have hEval0 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast0.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast0.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (cast0.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT0]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf0 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] (cast0.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT0 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs1, hSet0, hStep0⟩ := interpretOp_step (inB := g0In) hTy0 hOpVals0 hEval0 hConf0
  have hv1_0 : vs1.getVar? (cast0.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet0]; simp [hNR0]
  have hv1_rhs : vs1.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n0 hSet0]; exact hTRhs
  -- Step ext₁: `extui` of `x` to width `N+1`.
  have hOpVals1 : (InterpreterState.mk vs1 state'.memory).variables.getOperandValues ext1
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands1 hv1_0
  have hEval1 : interpretOp' (.arith .extui) (ext1.getProperties! rw'.ctx.raw (.arith .extui))
      (ext1.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (ext1.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT1, hP1]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (2 * mt.modulus.type.bitwidth ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf1 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)))]
      (ext1.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT1 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs2, hSet1, hStep1⟩ := interpretOp_step (inB := g1In) hTy1 hOpVals1 hEval1 hConf1
  -- Step cast₂: cast `rhs : iN`.
  have hv2_rhs : vs2.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n1 hSet1]; exact hv1_rhs
  have hOpVals2 : (InterpreterState.mk vs2 state'.memory).variables.getOperandValues cast2
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands2 hv2_rhs
  have hEval2 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast2.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast2.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (cast2.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT2]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf2 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] (cast2.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT2 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs3, hSet2, hStep2⟩ := interpretOp_step (inB := g2In) hTy2 hOpVals2 hEval2 hConf2
  -- Step ext₃: `extui` of `y` to width `N+1`.
  have hv3_2 : vs3.getVar? (cast2.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet2]; simp [hNR2]
  have hOpVals3 : (InterpreterState.mk vs3 state'.memory).variables.getOperandValues ext3
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands3 hv3_2
  have hEval3 : interpretOp' (.arith .extui) (ext3.getProperties! rw'.ctx.raw (.arith .extui))
      (ext3.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (ext3.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT3, hP3]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (2 * mt.modulus.type.bitwidth ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf3 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))]
      (ext3.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT3 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs4, hSet3, hStep3⟩ := interpretOp_step (inB := g3In) hTy3 hOpVals3 hEval3 hConf3
  -- Step const₄: the modulus constant `q : i(N+1)`.
  have hOpVals4 : (InterpreterState.mk vs4 state'.memory).variables.getOperandValues const4
      = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands4, Array.mapM_eq_mapM_toList]; simp
  have hEval4 : interpretOp' (.arith .constant) (const4.getProperties! rw'.ctx.raw (.arith .constant))
      (const4.getResultTypes! rw'.ctx.raw) #[] (const4.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))],
          state'.memory, none)) := by
    rw [hRT4, hP4]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf4 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))]
      (const4.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT4 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs5, hSet4, hStep4⟩ := interpretOp_step (inB := g4In) hTy4 hOpVals4 hEval4 hConf4
  -- Step add₅.
  have hv2_1 : vs2.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet1]; simp [hNR1]
  have hv4_3 : vs4.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet3]; simp [hNR3]
  -- Distinctness of the created ops we thread operands through.
  -- `o₁` is in bounds at `o₂`'s creation context (a fresh `o₂` is not), so `o₁ ≠ o₂`.
  have d12 : ext1 ≠ cast2 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC2) (h ▸ WfRewriter.createOp_new_inBounds _ hC1)
  have d13 : ext1 ≠ ext3 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC3)
      (h ▸ ((WfCreatedSeq.single hC2).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d14 : ext1 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4)
      (h ▸ (((WfCreatedSeq.single hC2).snoc hC3).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d34 : ext3 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4) (h ▸ WfRewriter.createOp_new_inBounds _ hC3)
  have d45 : const4 ≠ mul5 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC5) (h ▸ WfRewriter.createOp_new_inBounds _ hC4)
  have hv5_1 : vs5.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d14 hSet4, ModArithToArith.getVar?_setResultValues?_ne d13 hSet3,
      ModArithToArith.getVar?_setResultValues?_ne d12 hSet2]; exact hv2_1
  have hv5_3 : vs5.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d34 hSet4]; exact hv4_3
  have hOpVals5 : (InterpreterState.mk vs5 state'.memory).variables.getOperandValues mul5
      = some #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))] :=
    ModArithToArith.getOperandValues_two hOperands5 hv5_1 hv5_3
  have hEval5 : interpretOp' (.arith .muli) (mul5.getProperties! rw'.ctx.raw (.arith .muli))
      (mul5.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (y.zeroExtend (2 * mt.modulus.type.bitwidth)))]
      (mul5.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hP5]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.mul, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf5 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth)))]
      (mul5.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT5 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs6, hSet5, hStep5⟩ := interpretOp_step (inB := g5In) hTy5 hOpVals5 hEval5 hConf5
  -- Step rem₆: `remui` modulo `q`.
  have hv5_4 : vs5.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet4]; simp [hNR4]
  have hv6_5 : vs6.getVar? (mul5.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth)))) := by
    rw [VariableState.getVar?_setResultValues? hSet5]; simp [hNR5]
  have hv6_4 : vs6.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d45 hSet5]; exact hv5_4
  have hOpVals6 : (InterpreterState.mk vs6 state'.memory).variables.getOperandValues rem6
      = some #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)
              * y.zeroExtend (2 * mt.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_two hOperands6 hv6_5 hv6_4
  have hEval6 : interpretOp' (.arith .remui) (rem6.getProperties! rw'.ctx.raw (.arith .remui))
      (rem6.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (x.zeroExtend (2 * mt.modulus.type.bitwidth)
              * y.zeroExtend (2 * mt.modulus.type.bitwidth))),
          RuntimeValue.int (2 * mt.modulus.type.bitwidth)
            (.val (BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))]
      (rem6.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))],
          state'.memory, none)) := by
    have hqne : BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value
        ≠ 0#(2 * mt.modulus.type.bitwidth) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := 2 * mt.modulus.type.bitwidth) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf6 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))]
      (rem6.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT6 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs7, hSet6, hStep6⟩ := interpretOp_step (inB := g6In) hTy6 hOpVals6 hEval6 hConf6
  -- Step trunc₇: `trunci` (nuw) back to width `N`.
  have hv7_6 : vs7.getVar? (rem6.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet6]; simp [hNR6]
  have hOpVals7 : (InterpreterState.mk vs7 state'.memory).variables.getOperandValues trunc7
      = some #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_one hOperands7 hv7_6
  have hNoPoison : (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
        * y.zeroExtend (2 * mt.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
        mt.modulus.type.bitwidth).zeroExtend (2 * mt.modulus.type.bitwidth)
        = (x.zeroExtend (2 * mt.modulus.type.bitwidth)
        * y.zeroExtend (2 * mt.modulus.type.bitwidth))
        % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    have hcast : (2:Int)^mt.modulus.type.bitwidth = ((2^mt.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval7 : interpretOp' (.arith .trunci) (trunc7.getProperties! rw'.ctx.raw (.arith .trunci))
      (trunc7.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (2 * mt.modulus.type.bitwidth)
          (.val ((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value))]
      (trunc7.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT7, hP7]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mt.modulus.type.bitwidth ≥ 2 * mt.modulus.type.bitwidth) from by omega)]
  have hConf7 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (trunc7.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT7 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs8, hSet7, hStep7⟩ := interpretOp_step (inB := g7In) hTy7 hOpVals7 hEval7 hConf7
  -- Step cast₈: cast back to `!mod_arith.int`.
  have hv8_7 : vs8.getVar? (trunc7.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet7]; simp [hNR7]
  have hOpVals8 : (InterpreterState.mk vs8 state'.memory).variables.getOperandValues cast8
      = some #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))] :=
    ModArithToArith.getOperandValues_one hOperands8 hv8_7
  have hEval8 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast8.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast8.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (2 * mt.modulus.type.bitwidth)
            * y.zeroExtend (2 * mt.modulus.type.bitwidth))
            % BitVec.ofInt (2 * mt.modulus.type.bitwidth) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (cast8.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.mul mt.modulus.value x y))], state'.memory, none)) := by
    rw [hRT8, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf8 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val (Data.ModArith.mul mt.modulus.value x y))]
      (cast8.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT8 ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_mul hQpos hQle⟩
  obtain ⟨vs9, hSet8, hStep8⟩ := interpretOp_step (inB := g8In) hTy8 hOpVals8 hEval8 hConf8
  -- ## Assemble the nine steps.
  refine ⟨⟨vs9, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [cast0, ext1, cast2, ext3, const4, mul5, rem6, trunc7, cast8] state' _
      = some (.ok (⟨vs9, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep0]
    rw [interpretOpList_cons]; simp only [hStep1]
    rw [interpretOpList_cons]; simp only [hStep2]
    rw [interpretOpList_cons]; simp only [hStep3]
    rw [interpretOpList_cons]; simp only [hStep4]
    rw [interpretOpList_cons]; simp only [hStep5]
    rw [interpretOpList_cons]; simp only [hStep6]
    rw [interpretOpList_cons]; simp only [hStep7]
    rw [interpretOpList_cons]; simp only [hStep8]
    rfl
  · -- memory unchanged
    simpa using hMemEq
  · -- target value refines the source result
    refine ⟨RuntimeValue.int mt.modulus.type.bitwidth
        (.val (Data.ModArith.mul mt.modulus.value x y)), ?_, ?_⟩
    · rw [VariableState.getVar?_setResultValues? hSet8]; simp [hNR8]
    · simp [RuntimeValue.isRefinedBy]


set_option maxHeartbeats 2000000 in
/-- Direct semantics correctness of the imperative `mod_arith.sub` lowering. -/
theorem lowerModArithSubOp_correct :
    ImperativePatternCorrect ModArithToArithOriginal.lowerModArithSubOp := by
  intro rw op rw' ctxDom ctxVerif opInBounds hpat hctxne
  -- Inversion of the imperative pattern into its ten helper-emitted ops.
  obtain ⟨operands, mt, rwA, a, rwB, b, rwQ, q, rwBuild, rBuild, rwRem, rRem, rwPack, rPack,
      hmatch, hmt, hunpA, hunpB, hconst, hbuild, hrem, hpack, herase⟩ :=
    ModArithToArithOriginal.lowerModArithBinOp_fired_inv hpat hctxne
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, hProps⟩ := matchOp_some_inv hmatch
  -- Verifier facts: operand/result types are the modulus type, modulus is valid.
  have hVerified : op.Verified rw.ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, _, _, _, mtv, hResTy, hOp0Ty, hOp1Ty, hValid⟩ :=
    hVerified.mod_arith_binop hOpType (Or.inr (Or.inl rfl))
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by
    rw [ValuePtr.getType!_opResult, hResTy] at hmt
    simp only [Attribute.modArithType.injEq] at hmt
    exact hmt
  subst mtv
  -- N ≥ 1 from a valid modulus, so the widen width N+1 > N: the ext/trunc branches fire.
  have hN1 : 1 ≤ mt.modulus.type.bitwidth := by
    rcases Nat.eq_zero_or_pos mt.modulus.type.bitwidth with h0 | h0
    · rw [h0] at hQwidth
      simp only [Nat.zero_sub, Int.pow_zero] at hQwidth
      omega
    · omega
  -- Operands of `op` are in bounds.
  have hFields : rw.ctx.raw.FieldsInBounds := (WfIRContext_raw_wellFormed rw.ctx).inBounds
  have hOpSize : (op.getOperands! rw.ctx.raw).size = 2 := by grind
  have hlhsIn : operands[0]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 0 (by omega)]; exact Array.getElem_mem _
  have hrhsIn : operands[1]!.InBounds rw.ctx.raw := by
    rw [hOperands]
    apply OperationPtr.getOperands!_inBounds hFields opInBounds
    rw [getElem!_pos _ 1 (by omega)]; exact Array.getElem_mem _
  -- The two operands carry the modulus type.
  have hLhsTy : operands[0]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! rw.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
  -- The result of a freshly created cast-to-storage op has the storage integer type `iN`.
  have castResTy : ∀ (c c' : PatternRewriter OpCode) (v : ValuePtr) (castOp : OperationPtr) h1 h2 h3 h4,
      WfRewriter.createOp c.ctx (.builtin .unrealized_conversion_cast) #[mt.modulus.type] #[v]
        #[] #[] () (some (InsertPoint.before op)) h1 h2 h3 h4 = some (c'.ctx, castOp) →
      ((castOp.getResult 0 : ValuePtr).getType! c'.ctx.raw).val = .integerType mt.modulus.type := by
    intro c c' v castOp h1 h2 h3 h4 hC
    have := ValuePtr.getType!_WfRewriter_createOp hC (value := (castOp.getResult 0 : ValuePtr))
    simp only [OperationPtr.getResult] at this ⊢
    rw [this]
    simp
  -- # Extract the nine created operations.
  -- unpack lhs: cast₀ (iN), then ext₁ (iN → iN+1).
  obtain ⟨mt0, rwCastA, cast0, st0, hlhsTy0, hcast0Ty, ⟨_, _, _, _, hC0⟩, hbranchA⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpA
  have hmt0 : mt0 = mt := by
    have := hlhsTy0; rw [hLhsTy] at this; simpa using this.symm
  subst mt0
  -- The stored type is iN, so width N+1 > N: the ext branch must have fired.
  have hst0 : st0 = mt.modulus.type := by
    have h := castResTy rw rwCastA operands[0]! cast0 _ _ _ _ hC0
    rw [hcast0Ty] at h
    simp only [Attribute.integerType.injEq] at h
    exact h
  subst hst0
  obtain ⟨_, ext1, ha_eq, _, _, _, _, hC1⟩ | ⟨hbad, _, _⟩ := hbranchA
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- unpack rhs: cast₂ (iN), then ext₃.
  -- `WfCreatedSeq` from `rw.ctx` up to `rwA.ctx` (cast₀ then ext₁), to transfer the rhs type.
  have seq_rwA : WfCreatedSeq rw.ctx rwA.ctx := (WfCreatedSeq.single hC0).snoc hC1
  have hRhsTyA : operands[1]!.getType! rwA.ctx.raw = ⟨.modArithType mt, by rfl⟩ := by
    rw [seq_rwA.getType!_eq hrhsIn]; exact hRhsTy
  obtain ⟨mt2, rwCastB, cast2, st2, hrhsTy2, hcast2Ty, ⟨_, _, _, _, hC2⟩, hbranchB⟩ :=
    ModArithToArithOriginal.unpackValue_inv hunpB
  have hmt2 : mt2 = mt := by
    have := hrhsTy2; rw [hRhsTyA] at this; simpa using this.symm
  subst mt2
  have hst2 : st2 = mt.modulus.type := by
    have h := castResTy rwA rwCastB operands[1]! cast2 _ _ _ _ hC2
    rw [hcast2Ty] at h; simp only [Attribute.integerType.injEq] at h; exact h
  subst hst2
  obtain ⟨_, ext3, hb_eq, _, _, _, _, hC3⟩ | ⟨hbad, _, _⟩ := hbranchB
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad; omega
  -- constant q : i(N+1).
  obtain ⟨const4, hq_eq, _, _, _, _, hC4⟩ := ModArithToArithOriginal.emitArithConstant_inv hconst
  -- addi₅ (a+q) then subi₆ (aq-b), both i(N+1).
  obtain ⟨rwAdd, addi5, subi6, hrBuild_eq, ⟨_, _, _, _, hC5⟩, ⟨_, _, _, _, hC6⟩⟩ :=
    ModArithToArithOriginal.buildSub_inv hbuild
  -- rem₆ : i(N+1).
  obtain ⟨rem7, hrRem_eq, _, _, _, _, hC7⟩ := ModArithToArithOriginal.emitArithBinOp_inv hrem
  -- ## The intermediate-value width is N+1 along the add → remui chain.
  -- `a` (ext₁'s result) has type i(N+1).
  have haTyA : (ext1.getResult 0 : ValuePtr).getType! rwA.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := createOp_result0_type hC1
  -- Transfer `a`'s type along cast₂, ext₃, const₄ to `rwQ.ctx`.
  have seq_AtoQ : WfCreatedSeq rwA.ctx rwQ.ctx :=
    (((WfCreatedSeq.single hC2).snoc hC3).snoc hC4)
  have hExt1InA : (ext1.getResult 0 : ValuePtr).InBounds rwA.ctx.raw := by
    have hfr := WfRewriter.createOp_new_inBounds _ hC1
    have hnr : ext1.getNumResults! rwA.ctx.raw = 1 := by
      rw [OperationPtr.getNumResults!_WfRewriter_createOp hC1, if_pos rfl]; rfl
    have : (OpResultPtr.mk ext1 0).InBounds rwA.ctx.raw :=
      OpResultPtr.inBounds_of hfr (by simp only [hnr]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have haTyQ : (ext1.getResult 0 : ValuePtr).getType! rwQ.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    rw [seq_AtoQ.getType!_eq hExt1InA]; exact haTyA
  -- addi₅'s result has type i(N+1): its result type is `a`'s type in `rwQ.ctx`.
  have haddiTy : (addi5.getResult 0 : ValuePtr).getType! rwAdd.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    have h := createOp_result0_type hC5
    rw [ha_eq, haTyQ] at h; exact h
  -- subi₆'s result (`rBuild`) has type i(N+1): its result type is `addi₅`'s type in `rwAdd.ctx`.
  have hrBuildTy : (subi6.getResult 0 : ValuePtr).getType! rwBuild.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    have h := createOp_result0_type hC6
    rw [haddiTy] at h; exact h
  -- rem₇'s result (`rRem`) has type i(N+1): its result type is `rBuild`'s type in `rwBuild.ctx`.
  have hrRemTy : (rem7.getResult 0 : ValuePtr).getType! rwRem.ctx.raw
      = (IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr) := by
    have h := createOp_result0_type hC7
    rw [hrBuild_eq, hrBuildTy] at h; exact h
  -- pack: trunc₇ (i(N+1) → iN), cast₈ (iN → modArith).
  obtain ⟨it7, hrRemTy7, hbranchP⟩ := ModArithToArithOriginal.packValue_inv hpack
  -- `it7 = i(N+1)`, so the trunc branch fired.
  have hit7 : it7 = IntegerType.mk (mt.modulus.type.bitwidth + 1) := by
    have := hrRemTy7
    rw [hrRem_eq, hrRemTy] at this
    simp only [Attribute.integerType.injEq] at this
    exact this.symm
  subst hit7
  obtain ⟨hgt7, rwTrunc, trunc8, cast9, hrPack_eq, ⟨_, _, _, _, hC8⟩, ⟨_, _, _, _, hC9⟩⟩
    | ⟨hbad7, _⟩ := hbranchP
  rotate_left
  · exfalso; simp only [IntegerType.bitwidth] at hbad7; omega
  -- Result-value abbreviations.
  subst ha_eq hb_eq hq_eq hrBuild_eq hrRem_eq hrPack_eq
  -- # `WfCreatedSeq` suffix chains from each creation context up to `rwPack.ctx`.
  have s9 : WfCreatedSeq rwPack.ctx rwPack.ctx := .nil
  have s8 : WfCreatedSeq rwTrunc.ctx rwPack.ctx := .single hC9
  have s7 : WfCreatedSeq rwRem.ctx rwPack.ctx := (WfCreatedSeq.single hC8).snoc hC9
  have s6 : WfCreatedSeq rwBuild.ctx rwPack.ctx := ((WfCreatedSeq.single hC7).snoc hC8).snoc hC9
  have s5 : WfCreatedSeq rwAdd.ctx rwPack.ctx := (((WfCreatedSeq.single hC6).snoc hC7).snoc hC8).snoc hC9
  have s4 : WfCreatedSeq rwQ.ctx rwPack.ctx :=
    ((((WfCreatedSeq.single hC5).snoc hC6).snoc hC7).snoc hC8).snoc hC9
  have s3 : WfCreatedSeq rwB.ctx rwPack.ctx :=
    (((((WfCreatedSeq.single hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8).snoc hC9
  have s2 : WfCreatedSeq rwCastB.ctx rwPack.ctx :=
    ((((((WfCreatedSeq.single hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8).snoc hC9
  have s1 : WfCreatedSeq rwA.ctx rwPack.ctx :=
    (((((((WfCreatedSeq.single hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8).snoc hC9
  have s0 : WfCreatedSeq rwCastA.ctx rwPack.ctx :=
    ((((((((WfCreatedSeq.single hC1).snoc hC2).snoc hC3).snoc hC4).snoc hC5).snoc hC6).snoc hC7).snoc hC8).snoc
      hC9
  -- # Per-op shape facts in `rwPack.ctx` (where all ten ops exist).
  obtain ⟨f0In, f0Ty, f0Ops, f0RT, f0NR, f0Succ, f0P⟩ := newOpFactsAtPack hC0 s0
  obtain ⟨f1In, f1Ty, f1Ops, f1RT, f1NR, f1Succ, f1P⟩ := newOpFactsAtPack hC1 s1
  obtain ⟨f2In, f2Ty, f2Ops, f2RT, f2NR, f2Succ, f2P⟩ := newOpFactsAtPack hC2 s2
  obtain ⟨f3In, f3Ty, f3Ops, f3RT, f3NR, f3Succ, f3P⟩ := newOpFactsAtPack hC3 s3
  obtain ⟨f4In, f4Ty, f4Ops, f4RT, f4NR, f4Succ, f4P⟩ := newOpFactsAtPack hC4 s4
  obtain ⟨f5In, f5Ty, f5Ops, f5RT, f5NR, f5Succ, f5P⟩ := newOpFactsAtPack hC5 s5
  obtain ⟨f6In, f6Ty, f6Ops, f6RT, f6NR, f6Succ, f6P⟩ := newOpFactsAtPack hC6 s6
  obtain ⟨f7In, f7Ty, f7Ops, f7RT, f7NR, f7Succ, f7P⟩ := newOpFactsAtPack hC7 s7
  obtain ⟨f8In, f8Ty, f8Ops, f8RT, f8NR, f8Succ, f8P⟩ := newOpFactsAtPack hC8 s8
  obtain ⟨f9In, f9Ty, f9Ops, f9RT, f9NR, f9Succ, f9P⟩ := newOpFactsAtPack hC9 s9
  -- # The final rewiring: replaceValue (op's result → rPack) then eraseOp op.
  obtain ⟨ctxR, hRne, hRold, hRnew, hctxR, hRregions, hRuses, hRop, hfinal⟩ :=
    ModArithToArithOriginal.replaceAndErase_inv herase
  -- Each new op is distinct from `op` (it is fresh, `op` is not).
  have freshNe : ∀ {o : OperationPtr}, o.InBounds rwPack.ctx.raw →
      ¬ o.InBounds rw.ctx.raw → o ≠ op := by
    intro o hPack hNotRw heq; subst heq; exact hNotRw opInBounds
  -- All nine ops are fresh w.r.t. `rw.ctx`.
  have notRw : ∀ {cM cN : WfIRContext OpCode} {T rt ops bo rg} {p : propertiesOf T} {ipx ha hb hc hd}
      {o : OperationPtr},
      WfRewriter.createOp cM T rt ops bo rg p ipx ha hb hc hd = some (cN, o) →
      WfCreatedSeq rw.ctx cM → ¬ o.InBounds rw.ctx.raw := by
    intro cM cN T rt ops bo rg p ipx ha hb hc hd o hCo seqPre hin
    exact (WfRewriter.createOp_new_not_inBounds _ hCo) (seqPre.inBounds_mono (.operation o) hin)
  -- Prefix chains `rw.ctx → <creation ctx>` for each op, giving freshness.
  have p1 : WfCreatedSeq rw.ctx rwCastA.ctx := .single hC0
  have p2 : WfCreatedSeq rw.ctx rwA.ctx := p1.snoc hC1
  have p3 : WfCreatedSeq rw.ctx rwCastB.ctx := p2.snoc hC2
  have p4 : WfCreatedSeq rw.ctx rwB.ctx := p3.snoc hC3
  have p5 : WfCreatedSeq rw.ctx rwQ.ctx := p4.snoc hC4
  have p6 : WfCreatedSeq rw.ctx rwAdd.ctx := p5.snoc hC5
  have p7 : WfCreatedSeq rw.ctx rwBuild.ctx := p6.snoc hC6
  have p8 : WfCreatedSeq rw.ctx rwRem.ctx := p7.snoc hC7
  have p9 : WfCreatedSeq rw.ctx rwTrunc.ctx := p8.snoc hC8
  have n0 : ¬ cast0.InBounds rw.ctx.raw := notRw hC0 .nil
  have n1 : ¬ ext1.InBounds rw.ctx.raw := notRw hC1 p1
  have n2 : ¬ cast2.InBounds rw.ctx.raw := notRw hC2 p2
  have n3 : ¬ ext3.InBounds rw.ctx.raw := notRw hC3 p3
  have n4 : ¬ const4.InBounds rw.ctx.raw := notRw hC4 p4
  have n5 : ¬ addi5.InBounds rw.ctx.raw := notRw hC5 p5
  have n6 : ¬ subi6.InBounds rw.ctx.raw := notRw hC6 p6
  have n7 : ¬ rem7.InBounds rw.ctx.raw := notRw hC7 p7
  have n8 : ¬ trunc8.InBounds rw.ctx.raw := notRw hC8 p8
  have n9 : ¬ cast9.InBounds rw.ctx.raw := notRw hC9 p9
  -- `op`'s result differs from any other op's result, and from `lhs`/`rhs` (dominance).
  have resNe : ∀ {o' : OperationPtr}, o' ≠ op →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hne heq
    apply hne
    simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at heq
    exact heq.1.symm
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := by
    subst hOperands
    apply Array.ext
    · rw [hOpSize]; rfl
    · intro i h1 h2
      rw [hOpSize] at h1
      match i, h1 with
      | 0, _ => rw [getElem!_pos _ 0 (by rw [hOpSize]; omega)]; rfl
      | 1, _ => rw [getElem!_pos _ 1 (by rw [hOpSize]; omega)]; rfl
  have hLhsMem : operands[0]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hRhsMem : operands[1]! ∈ op.getOperands! rw.ctx.raw := by rw [hOpArr]; simp
  have hLhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[0]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  have hRhsNeRes : (op.getResult 0 : ValuePtr) ≠ operands[1]! := by
    have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
    intro heq
    apply this
    rw [← heq]
    rw [OperationPtr.getResults!.mem_iff_exists_index]
    exact ⟨0, by rw [hNumResults]; omega, rfl⟩
  subst hctxR
  have hRuses' : (!op.hasUses! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
      (cast9.getResult 0) hRne hRold hRnew).raw) = true := by simpa using hRuses
  -- `opSurvives` packaged for our fixed replace/erase, transferring `rwPack.ctx` facts to `rw'.ctx`.
  have surv : ∀ (o : OperationPtr), o ≠ op → o.InBounds rwPack.ctx.raw →
      (op.getResult 0 : ValuePtr) ∉ o.getOperands! rwPack.ctx.raw →
      o.InBounds rw'.ctx.raw ∧
      o.getOpType! rw'.ctx.raw = o.getOpType! rwPack.ctx.raw ∧
      o.getOperands! rw'.ctx.raw = o.getOperands! rwPack.ctx.raw ∧
      o.getResultTypes! rw'.ctx.raw = o.getResultTypes! rwPack.ctx.raw ∧
      o.getNumResults! rw'.ctx.raw = o.getNumResults! rwPack.ctx.raw ∧
      o.getSuccessors! rw'.ctx.raw = o.getSuccessors! rwPack.ctx.raw ∧
      (∀ T, o.getProperties! rw'.ctx.raw T = o.getProperties! rwPack.ctx.raw T) := by
    intro o hne hin hnm
    have := ModArithToArithOriginal.opSurvives (op := op) (o := o) hRne hRold hRnew hRregions
      hRuses' hRop hne hin hnm
    rw [hfinal]; exact this
  -- `op`'s result differs from each fresh op's result.
  have neNew : ∀ {o' : OperationPtr}, ¬ o'.InBounds rw.ctx.raw →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hfr
    exact resNe (fun heq => hfr (heq ▸ opInBounds))
  -- The replaced value is not among any new op's operands (in `rwPack.ctx`).
  have nm0 : (op.getResult 0 : ValuePtr) ∉ cast0.getOperands! rwPack.ctx.raw := by
    rw [f0Ops]; simp only [Array.mem_singleton]; exact hLhsNeRes
  have nm1 : (op.getResult 0 : ValuePtr) ∉ ext1.getOperands! rwPack.ctx.raw := by
    rw [f1Ops]; simp only [Array.mem_singleton]; exact neNew n0
  have nm2 : (op.getResult 0 : ValuePtr) ∉ cast2.getOperands! rwPack.ctx.raw := by
    rw [f2Ops]; simp only [Array.mem_singleton]; exact hRhsNeRes
  have nm3 : (op.getResult 0 : ValuePtr) ∉ ext3.getOperands! rwPack.ctx.raw := by
    rw [f3Ops]; simp only [Array.mem_singleton]; exact neNew n2
  have nm4 : (op.getResult 0 : ValuePtr) ∉ const4.getOperands! rwPack.ctx.raw := by
    rw [f4Ops]; simp
  have nm5 : (op.getResult 0 : ValuePtr) ∉ addi5.getOperands! rwPack.ctx.raw := by
    rw [f5Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n1 h
    · exact neNew n4 h
  have nm6 : (op.getResult 0 : ValuePtr) ∉ subi6.getOperands! rwPack.ctx.raw := by
    rw [f6Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n5 h
    · exact neNew n3 h
  have nm7 : (op.getResult 0 : ValuePtr) ∉ rem7.getOperands! rwPack.ctx.raw := by
    rw [f7Ops, Array.mem_def]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact neNew n6 h
    · exact neNew n4 h
  have nm8 : (op.getResult 0 : ValuePtr) ∉ trunc8.getOperands! rwPack.ctx.raw := by
    rw [f8Ops]; simp only [Array.mem_singleton]; exact neNew n7
  have nm9 : (op.getResult 0 : ValuePtr) ∉ cast9.getOperands! rwPack.ctx.raw := by
    rw [f9Ops]; simp only [Array.mem_singleton]; exact neNew n8
  -- # Survive to `rw'.ctx`.
  obtain ⟨g0In, g0Ty, g0Ops, g0RT, g0NR, g0Succ, g0P⟩ := surv cast0 (freshNe f0In n0) f0In nm0
  obtain ⟨g1In, g1Ty, g1Ops, g1RT, g1NR, g1Succ, g1P⟩ := surv ext1 (freshNe f1In n1) f1In nm1
  obtain ⟨g2In, g2Ty, g2Ops, g2RT, g2NR, g2Succ, g2P⟩ := surv cast2 (freshNe f2In n2) f2In nm2
  obtain ⟨g3In, g3Ty, g3Ops, g3RT, g3NR, g3Succ, g3P⟩ := surv ext3 (freshNe f3In n3) f3In nm3
  obtain ⟨g4In, g4Ty, g4Ops, g4RT, g4NR, g4Succ, g4P⟩ := surv const4 (freshNe f4In n4) f4In nm4
  obtain ⟨g5In, g5Ty, g5Ops, g5RT, g5NR, g5Succ, g5P⟩ := surv addi5 (freshNe f5In n5) f5In nm5
  obtain ⟨g6In, g6Ty, g6Ops, g6RT, g6NR, g6Succ, g6P⟩ := surv subi6 (freshNe f6In n6) f6In nm6
  obtain ⟨g7In, g7Ty, g7Ops, g7RT, g7NR, g7Succ, g7P⟩ := surv rem7 (freshNe f7In n7) f7In nm7
  obtain ⟨g8In, g8Ty, g8Ops, g8RT, g8NR, g8Succ, g8P⟩ := surv trunc8 (freshNe f8In n8) f8In nm8
  obtain ⟨g9In, g9Ty, g9Ops, g9RT, g9NR, g9Succ, g9P⟩ := surv cast9 (freshNe f9In n9) f9In nm9
  -- # Combined op facts in `rw'.ctx`.
  -- Opcodes.
  have hTy0 : cast0.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g0Ty.trans f0Ty
  have hTy1 : ext1.getOpType! rw'.ctx.raw = .arith .extui := g1Ty.trans f1Ty
  have hTy2 : cast2.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g2Ty.trans f2Ty
  have hTy3 : ext3.getOpType! rw'.ctx.raw = .arith .extui := g3Ty.trans f3Ty
  have hTy4 : const4.getOpType! rw'.ctx.raw = .arith .constant := g4Ty.trans f4Ty
  have hTy5 : addi5.getOpType! rw'.ctx.raw = .arith .addi := g5Ty.trans f5Ty
  have hTy6 : subi6.getOpType! rw'.ctx.raw = .arith .subi := g6Ty.trans f6Ty
  have hTy7 : rem7.getOpType! rw'.ctx.raw = .arith .remui := g7Ty.trans f7Ty
  have hTy8 : trunc8.getOpType! rw'.ctx.raw = .arith .trunci := g8Ty.trans f8Ty
  have hTy9 : cast9.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g9Ty.trans f9Ty
  -- Operands.
  have hOperands0 : cast0.getOperands! rw'.ctx.raw = #[operands[0]!] := g0Ops.trans f0Ops
  have hOperands1 : ext1.getOperands! rw'.ctx.raw = #[(cast0.getResult 0 : ValuePtr)] :=
    g1Ops.trans f1Ops
  have hOperands2 : cast2.getOperands! rw'.ctx.raw = #[operands[1]!] := g2Ops.trans f2Ops
  have hOperands3 : ext3.getOperands! rw'.ctx.raw = #[(cast2.getResult 0 : ValuePtr)] :=
    g3Ops.trans f3Ops
  have hOperands4 : const4.getOperands! rw'.ctx.raw = #[] := g4Ops.trans f4Ops
  have hOperands5 : addi5.getOperands! rw'.ctx.raw
      = #[(ext1.getResult 0 : ValuePtr), (const4.getResult 0 : ValuePtr)] := g5Ops.trans f5Ops
  have hOperands6 : subi6.getOperands! rw'.ctx.raw
      = #[(addi5.getResult 0 : ValuePtr), (ext3.getResult 0 : ValuePtr)] := g6Ops.trans f6Ops
  have hOperands7 : rem7.getOperands! rw'.ctx.raw
      = #[(subi6.getResult 0 : ValuePtr), (const4.getResult 0 : ValuePtr)] := g7Ops.trans f7Ops
  have hOperands8 : trunc8.getOperands! rw'.ctx.raw = #[(rem7.getResult 0 : ValuePtr)] :=
    g8Ops.trans f8Ops
  have hOperands9 : cast9.getOperands! rw'.ctx.raw = #[(trunc8.getResult 0 : ValuePtr)] :=
    g9Ops.trans f9Ops
  -- Successors (all empty).
  have hSucc0 : cast0.getSuccessors! rw'.ctx.raw = #[] := g0Succ.trans f0Succ
  have hSucc1 : ext1.getSuccessors! rw'.ctx.raw = #[] := g1Succ.trans f1Succ
  have hSucc2 : cast2.getSuccessors! rw'.ctx.raw = #[] := g2Succ.trans f2Succ
  have hSucc3 : ext3.getSuccessors! rw'.ctx.raw = #[] := g3Succ.trans f3Succ
  have hSucc4 : const4.getSuccessors! rw'.ctx.raw = #[] := g4Succ.trans f4Succ
  have hSucc5 : addi5.getSuccessors! rw'.ctx.raw = #[] := g5Succ.trans f5Succ
  have hSucc6 : subi6.getSuccessors! rw'.ctx.raw = #[] := g6Succ.trans f6Succ
  have hSucc7 : rem7.getSuccessors! rw'.ctx.raw = #[] := g7Succ.trans f7Succ
  have hSucc8 : trunc8.getSuccessors! rw'.ctx.raw = #[] := g8Succ.trans f8Succ
  have hSucc9 : cast9.getSuccessors! rw'.ctx.raw = #[] := g9Succ.trans f9Succ
  -- Number of results (all one).
  have hNR0 : cast0.getNumResults! rw'.ctx.raw = 1 := g0NR.trans f0NR
  have hNR1 : ext1.getNumResults! rw'.ctx.raw = 1 := g1NR.trans f1NR
  have hNR2 : cast2.getNumResults! rw'.ctx.raw = 1 := g2NR.trans f2NR
  have hNR3 : ext3.getNumResults! rw'.ctx.raw = 1 := g3NR.trans f3NR
  have hNR4 : const4.getNumResults! rw'.ctx.raw = 1 := g4NR.trans f4NR
  have hNR5 : addi5.getNumResults! rw'.ctx.raw = 1 := g5NR.trans f5NR
  have hNR6 : subi6.getNumResults! rw'.ctx.raw = 1 := g6NR.trans f6NR
  have hNR7 : rem7.getNumResults! rw'.ctx.raw = 1 := g7NR.trans f7NR
  have hNR8 : trunc8.getNumResults! rw'.ctx.raw = 1 := g8NR.trans f8NR
  have hNR9 : cast9.getNumResults! rw'.ctx.raw = 1 := g9NR.trans f9NR
  -- Result types.
  have hRT0 : cast0.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g0RT.trans f0RT
  have hRT1 : ext1.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g1RT, f1RT]; rfl
  have hRT2 : cast2.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g2RT.trans f2RT
  have hRT3 : ext3.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g3RT, f3RT]; rfl
  have hRT4 : const4.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by rw [g4RT, f4RT]; rfl
  have hRT5 : addi5.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [g5RT, f5RT, haTyQ]; rfl
  have hRT6 : subi6.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [g6RT, f6RT, haddiTy]; rfl
  have hRT7 : rem7.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk (mt.modulus.type.bitwidth + 1) : TypeAttr)] := by
    rw [g7RT, f7RT, hrBuildTy]; rfl
  have hRT8 : trunc8.getResultTypes! rw'.ctx.raw = #[(mt.modulus.type : TypeAttr)] := g8RT.trans f8RT
  have hRT9 : cast9.getResultTypes! rw'.ctx.raw = #[⟨.modArithType mt, by rfl⟩] := g9RT.trans f9RT
  -- Properties (only the ones the interpreter reads).
  have hP1 : ext1.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g1P _).trans f1P
  have hP3 : ext3.getProperties! rw'.ctx.raw (.arith .extui) = { nneg := false } :=
    (g3P _).trans f3P
  have hP4 : const4.getProperties! rw'.ctx.raw (.arith .constant)
      = { value := IntegerAttr.mk mt.modulus.value (IntegerType.mk (mt.modulus.type.bitwidth + 1)) } :=
    (g4P _).trans f4P
  have hP5 : addi5.getProperties! rw'.ctx.raw (.arith .addi) = { attr := { nsw := false, nuw := false } } :=
    (g5P _).trans f5P
  have hP6 : subi6.getProperties! rw'.ctx.raw (.arith .subi) = { attr := { nsw := false, nuw := false } } :=
    (g6P _).trans f6P
  have hP8 : trunc8.getProperties! rw'.ctx.raw (.arith .trunci) = { attr := { nsw := false, nuw := true } } :=
    (g8P _).trans f8P
  -- The new value `cast9.getResult 0` is in bounds of `rw'.ctx`.
  have hNewValIn : (cast9.getResult 0 : ValuePtr).InBounds rw'.ctx.raw := by
    have : (OpResultPtr.mk cast9 0).InBounds rw'.ctx.raw :=
      OpResultPtr.inBounds_of g9In (by simp only [hNR9]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have seqFull : WfCreatedSeq rw.ctx rwPack.ctx := p9.snoc hC9
  -- `op`'s number of results is preserved into `rwPack.ctx`.
  have hOpNRPack : op.getNumResults! rwPack.ctx.raw = 1 := by
    rw [seqFull.getNumResults!_eq opInBounds]; exact hNumResults
  -- # Provide `newOps`, `newValue`, freshness, mapping in-bounds.
  refine ⟨[cast0, ext1, cast2, ext3, const4, addi5, subi6, rem7, trunc8, cast9],
    (cast9.getResult 0 : ValuePtr), ?_, hNewValIn, ⟨?_, hNewValIn⟩, ?_⟩
  · -- freshness of every new op
    intro o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨g0In, n0⟩ | exact ⟨g1In, n1⟩ | exact ⟨g2In, n2⟩ | exact ⟨g3In, n3⟩
        | exact ⟨g4In, n4⟩ | exact ⟨g5In, n5⟩ | exact ⟨g6In, n6⟩ | exact ⟨g7In, n7⟩
        | exact ⟨g8In, n8⟩ | exact ⟨g9In, n9⟩
  · -- in-bounds-preservation of the identity-on-non-results part of the mapping
    intro v hvIn hvNotRes
    have hvPack : v.InBounds rwPack.ctx.raw := seqFull.inBounds_mono (GenericPtr.value v) hvIn
    -- `v` is not a result of `op` in `rwPack.ctx` either (results depend only on numResults).
    have hvNotResPack : v ∉ op.getResults! rwPack.ctx.raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      rintro ⟨i, hi, heqv⟩
      apply hvNotRes
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      exact ⟨i, by rw [hNumResults]; rw [hOpNRPack] at hi; exact hi, heqv⟩
    have hvR : v.InBounds (WfRewriter.replaceValue rwPack.ctx (op.getResult 0) (cast9.getResult 0)
        hRne hRold hRnew).raw := by
      have := (WfRewriter.replaceValue_inBounds (ptr := GenericPtr.value v)
        (ne := hRne) (oldIn := hRold) (newIn := hRnew)).mpr
        (by simpa [GenericPtr.InBounds] using hvPack)
      simpa [GenericPtr.InBounds] using this
    have hvNotResR : v ∉ op.getResults! (WfRewriter.replaceValue rwPack.ctx (op.getResult 0)
        (cast9.getResult 0) hRne hRold hRnew).raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index] at hvNotResPack ⊢
      simp only [OperationPtr.getNumResults!_WfRewriter_replaceValue] at *
      exact hvNotResPack
    rw [hfinal]
    exact ModArithToArithOriginal.valueSurvivesErase hvR hvNotResR
  -- # The semantics replay.
  intro state newState cf hinterp srcVal hsrcVal state' hrefines
  -- ## Source interpretation of `mod_arith.add`.
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp
  have hOpArr : op.getOperands! rw.ctx.raw = #[operands[0]!, operands[1]!] := hOpArr
  have hMapM : #[operands[0]!, operands[1]!].mapM (state.variables.getVar? ·) = some srcOperandVals := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr] at hSrcOpVals; exact hSrcOpVals
  have hsz : srcOperandVals.size = 2 := by
    have := Array.size_eq_of_mapM_eq_some hMapM; simpa using this.symm
  have hLk0 := Array.mapM_option_eq_some_implies hMapM 0 (by omega)
  have hLk1 := Array.mapM_option_eq_some_implies hMapM 1 (by omega)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hLk0 hLk1
  obtain ⟨x, hx, hxlt⟩ : ∃ x, state.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) ∧ (x.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk0
    rw [hLhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk0, hv], hvlt⟩
  obtain ⟨y, hy, hylt⟩ : ∃ y, state.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) ∧ (y.toNat : Int) < mt.modulus.value := by
    have hconf := ModArithToArithOriginal.getVar?_conforms hLk1
    rw [hRhsTy] at hconf
    obtain ⟨v, hv, hvlt⟩ := RuntimeValue.Conforms.modArithType hconf
    exact ⟨v, by rw [hLk1, hv], hvlt⟩
  have hSrcOps : srcOperandVals = #[RuntimeValue.int mt.modulus.type.bitwidth (.val x),
      RuntimeValue.int mt.modulus.type.bitwidth (.val y)] := by
    apply Array.ext
    · rw [hsz]; rfl
    · intro i h1 h2
      rw [hsz] at h1
      match i, h1 with
      | 0, _ => rw [hx] at hLk0; simpa using hLk0.symm
      | 1, _ => rw [hy] at hLk1; simpa using hLk1.symm
  have hSrcNumRes : (op.getResultTypes! rw.ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! rw.ctx.raw)[0]? = some ⟨.modArithType mt, by rfl⟩ := by
    have h0 : (op.getResultTypes! rw.ctx.raw)[0]?
        = some ((op.getResultTypes! rw.ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  have hSrcEval' : interpretOp' (.mod_arith .sub)
      (op.getProperties! rw.ctx.raw (.mod_arith .sub)) (op.getResultTypes! rw.ctx.raw) srcOperandVals
      (op.getSuccessors! rw.ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.sub mt.modulus.value x y))], state.memory, none)) := by
    rw [hSrcOps]
    simp only [interpretOp', ModArith.interpretOp', hResTy0]
    rw [dif_neg (by simp), dif_neg (by simp)]
    simp only [BitVec.cast_eq, bind, pure]
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.sub mt.modulus.value x y))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  -- The single source result value.
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.sub mt.modulus.value x y))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]
    simp [hNumResults, hSrcResVals]
  have hsrcVal' : srcVal = RuntimeValue.int mt.modulus.type.bitwidth
      (.val (Data.ModArith.sub mt.modulus.value x y)) := by
    rw [hvSrc] at hsrcVal; exact (Option.some.injEq _ _).mp hsrcVal.symm
  subst hsrcVal'
  -- ## Refinement transfer: operands take the same concrete value in `state'`.
  obtain ⟨hMemEq, hVarRef⟩ := hrefines
  have hLhsNotRes' : operands[0]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[0]! hLhsMem
  have hRhsNotRes' : operands[1]! ∉ op.getResults! rw.ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl operands[1]! hRhsMem
  have hTLhs : state'.variables.getVar? operands[0]!
      = some (.int mt.modulus.type.bitwidth (.val x)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[0]! hlhsIn _ hx
    simp only [ImperativeMapping, dif_neg hLhsNotRes'] at htv
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
  have hTRhs : state'.variables.getVar? operands[1]!
      = some (.int mt.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    simp only [ImperativeMapping, dif_neg hRhsNotRes'] at htv
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
  have hqm : 2 * mt.modulus.value ≤ 2 ^ (mt.modulus.type.bitwidth + 1) :=
    Data.ModArith.two_mul_modulus_le_two_pow_succ hN1 hQwidth
  have hnm : mt.modulus.type.bitwidth ≤ mt.modulus.type.bitwidth + 1 := by omega
  have hQle : mt.modulus.value ≤ 2 ^ mt.modulus.type.bitwidth :=
    Data.ModArith.modulus_le_two_pow hN1 hQwidth
  have hPipeEq : ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
        mt.modulus.type.bitwidth = Data.ModArith.sub mt.modulus.value x y :=
    Data.ModArith.subPipeline_eq_sub hQpos hqm hnm hxlt hylt
  have hRemLt : (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).toNat : Int)
        < mt.modulus.value :=
    Data.ModArith.toNat_subPipeline_lt hQpos hqm hnm hxlt hylt
  -- ## Target interpretation: step through the nine created operations.
  -- Step cast₀: cast `lhs : iN`.
  have hOpVals0 : state'.variables.getOperandValues cast0
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands0 hTLhs
  have hEval0 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast0.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast0.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (cast0.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT0]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf0 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] (cast0.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT0 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs1, hSet0, hStep0⟩ := interpretOp_step (inB := g0In) hTy0 hOpVals0 hEval0 hConf0
  have hv1_0 : vs1.getVar? (cast0.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet0]; simp [hNR0]
  have hv1_rhs : vs1.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n0 hSet0]; exact hTRhs
  -- Step ext₁: `extui` of `x` to width `N+1`.
  have hOpVals1 : (InterpreterState.mk vs1 state'.memory).variables.getOperandValues ext1
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)] :=
    ModArithToArith.getOperandValues_one hOperands1 hv1_0
  have hEval1 : interpretOp' (.arith .extui) (ext1.getProperties! rw'.ctx.raw (.arith .extui))
      (ext1.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val x)]
      (ext1.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT1, hP1]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mt.modulus.type.bitwidth + 1 ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf1 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (ext1.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT1 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs2, hSet1, hStep1⟩ := interpretOp_step (inB := g1In) hTy1 hOpVals1 hEval1 hConf1
  -- Step cast₂: cast `rhs : iN`.
  have hv2_rhs : vs2.getVar? operands[1]! = some (.int mt.modulus.type.bitwidth (.val y)) := by
    rw [ModArithToArith.getVar?_setResultValues?_outer hrhsIn n1 hSet1]; exact hv1_rhs
  have hOpVals2 : (InterpreterState.mk vs2 state'.memory).variables.getOperandValues cast2
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands2 hv2_rhs
  have hEval2 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast2.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast2.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (cast2.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT2]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf2 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] (cast2.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT2 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs3, hSet2, hStep2⟩ := interpretOp_step (inB := g2In) hTy2 hOpVals2 hEval2 hConf2
  -- Step ext₃: `extui` of `y` to width `N+1`.
  have hv3_2 : vs3.getVar? (cast2.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet2]; simp [hNR2]
  have hOpVals3 : (InterpreterState.mk vs3 state'.memory).variables.getOperandValues ext3
      = some #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)] :=
    ModArithToArith.getOperandValues_one hOperands3 hv3_2
  have hEval3 : interpretOp' (.arith .extui) (ext3.getProperties! rw'.ctx.raw (.arith .extui))
      (ext3.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val y)]
      (ext3.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hRT3, hP3]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (mt.modulus.type.bitwidth + 1 ≤ mt.modulus.type.bitwidth) from by omega)]
  have hConf3 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (ext3.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT3 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs4, hSet3, hStep3⟩ := interpretOp_step (inB := g3In) hTy3 hOpVals3 hEval3 hConf3
  -- Step const₄: the modulus constant `q : i(N+1)`.
  have hOpVals4 : (InterpreterState.mk vs4 state'.memory).variables.getOperandValues const4
      = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands4, Array.mapM_eq_mapM_toList]; simp
  have hEval4 : interpretOp' (.arith .constant) (const4.getProperties! rw'.ctx.raw (.arith .constant))
      (const4.getResultTypes! rw'.ctx.raw) #[] (const4.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))],
          state'.memory, none)) := by
    rw [hRT4, hP4]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf4 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (const4.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT4 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs5, hSet4, hStep4⟩ := interpretOp_step (inB := g4In) hTy4 hOpVals4 hEval4 hConf4
  -- Step add₅.
  have hv2_1 : vs2.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet1]; simp [hNR1]
  have hv4_3 : vs4.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet3]; simp [hNR3]
  -- Distinctness of the created ops we thread operands through.
  -- `o₁` is in bounds at `o₂`'s creation context (a fresh `o₂` is not), so `o₁ ≠ o₂`.
  have d12 : ext1 ≠ cast2 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC2) (h ▸ WfRewriter.createOp_new_inBounds _ hC1)
  have d13 : ext1 ≠ ext3 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC3)
      (h ▸ ((WfCreatedSeq.single hC2).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d14 : ext1 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4)
      (h ▸ (((WfCreatedSeq.single hC2).snoc hC3).inBounds_mono (.operation ext1)
        (WfRewriter.createOp_new_inBounds _ hC1)))
  have d34 : ext3 ≠ const4 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC4) (h ▸ WfRewriter.createOp_new_inBounds _ hC3)
  have d45 : const4 ≠ addi5 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC5) (h ▸ WfRewriter.createOp_new_inBounds _ hC4)
  have d56 : addi5 ≠ subi6 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC6) (h ▸ WfRewriter.createOp_new_inBounds _ hC5)
  have d35 : ext3 ≠ addi5 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC5)
      (h ▸ ((WfCreatedSeq.single hC4).inBounds_mono (.operation ext3)
        (WfRewriter.createOp_new_inBounds _ hC3)))
  have d46 : const4 ≠ subi6 := fun h =>
    (WfRewriter.createOp_new_not_inBounds _ hC6)
      ((h ▸ (WfCreatedSeq.single hC5).inBounds_mono (.operation const4)
        (WfRewriter.createOp_new_inBounds _ hC4)))
  -- Step addi₅: `a + q`, i.e. `x.ze + ofInt q`.
  have hv5_1 : vs5.getVar? (ext1.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d14 hSet4,
      ModArithToArith.getVar?_setResultValues?_ne d13 hSet3,
      ModArithToArith.getVar?_setResultValues?_ne d12 hSet2]; exact hv2_1
  have hv5_q : vs5.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet4]; simp [hNR4]
  have hOpVals5 : (InterpreterState.mk vs5 state'.memory).variables.getOperandValues addi5
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_two hOperands5 hv5_1 hv5_q
  have hEval5 : interpretOp' (.arith .addi) (addi5.getProperties! rw'.ctx.raw (.arith .addi))
      (addi5.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (addi5.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))], state'.memory, none)) := by
    rw [hP5]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf5 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (addi5.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT5 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs6, hSet5, hStep5⟩ := interpretOp_step (inB := g5In) hTy5 hOpVals5 hEval5 hConf5
  -- Step subi₆: `aq - b`, i.e. `(x.ze + ofInt q) - y.ze`.
  have hv4_3 : vs4.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet3]; simp [hNR3]
  have hv6_5 : vs6.getVar? (addi5.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet5]; simp [hNR5]
  have hv6_3 : vs6.getVar? (ext3.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d35 hSet5,
      ModArithToArith.getVar?_setResultValues?_ne d34 hSet4]; exact hv4_3
  have hOpVals6 : (InterpreterState.mk vs6 state'.memory).variables.getOperandValues subi6
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value)),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))] :=
    ModArithToArith.getOperandValues_two hOperands6 hv6_5 hv6_3
  have hEval6 : interpretOp' (.arith .subi) (subi6.getProperties! rw'.ctx.raw (.arith .subi))
      (subi6.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value)),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (subi6.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value
            - y.zeroExtend (mt.modulus.type.bitwidth + 1)))], state'.memory, none)) := by
    rw [hP6]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf6 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1)))]
      (subi6.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT6 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs7, hSet6, hStep6⟩ := interpretOp_step (inB := g6In) hTy6 hOpVals6 hEval6 hConf6
  -- Step rem₇: `remui` modulo `q`.
  have hv6_q : vs6.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d45 hSet5]; exact hv5_q
  have hv7_6 : vs7.getVar? (subi6.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1)))) := by
    rw [VariableState.getVar?_setResultValues? hSet6]; simp [hNR6]
  have hv7_q : vs7.getVar? (const4.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [ModArithToArith.getVar?_setResultValues?_ne d46 hSet6]; exact hv6_q
  have hOpVals7 : (InterpreterState.mk vs7 state'.memory).variables.getOperandValues rem7
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_two hOperands7 hv7_6 hv7_q
  have hEval7 : interpretOp' (.arith .remui) (rem7.getProperties! rw'.ctx.raw (.arith .remui))
      (rem7.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
            (.val (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))),
          RuntimeValue.int (mt.modulus.type.bitwidth + 1) (.val (BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (rem7.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))], state'.memory, none)) := by
    have hqne : BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value ≠ 0#(mt.modulus.type.bitwidth + 1) :=
      Data.ModArith.ofInt_modulus_ne_zero (m := (mt.modulus.type.bitwidth + 1)) hQpos (by omega)
    simp only [interpretOp', Arith.interpretOp']
    rw [dif_neg (by simp)]
    simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
    rw [if_neg (by simpa using hqne)]
    simp [Data.LLVM.Int.urem, BitVec.cast_eq, hqne, Id.run, pure, bind]
  have hConf7 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (rem7.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT7 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs8, hSet7, hStep7⟩ := interpretOp_step (inB := g7In) hTy7 hOpVals7 hEval7 hConf7
  -- Step trunc₇: `trunci` (nuw) back to width `N`.
  have hv8_7 : vs8.getVar? (rem7.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet7]; simp [hNR7]
  have hOpVals8 : (InterpreterState.mk vs8 state'.memory).variables.getOperandValues trunc8
      = some #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))] :=
    ModArithToArith.getOperandValues_one hOperands8 hv8_7
  have hNoPoison : (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
        mt.modulus.type.bitwidth).zeroExtend (mt.modulus.type.bitwidth + 1)
        = (x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
        % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    have hcast : (2:Int)^mt.modulus.type.bitwidth = ((2^mt.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  have hEval8 : interpretOp' (.arith .trunci) (trunc8.getProperties! rw'.ctx.raw (.arith .trunci))
      (trunc8.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int (mt.modulus.type.bitwidth + 1)
          (.val ((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value))]
      (trunc8.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT8, hP8]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mt.modulus.type.bitwidth ≥ mt.modulus.type.bitwidth + 1) from by omega)]
  have hConf8 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (trunc8.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT8 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs9, hSet8, hStep8⟩ := interpretOp_step (inB := g8In) hTy8 hOpVals8 hEval8 hConf8
  -- Step cast₈: cast back to `!mod_arith.int`.
  have hv9_8 : vs9.getVar? (trunc8.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet8]; simp [hNR8]
  have hOpVals9 : (InterpreterState.mk vs9 state'.memory).variables.getOperandValues cast9
      = some #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))] :=
    ModArithToArith.getOperandValues_one hOperands9 hv9_8
  have hEval9 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast9.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast9.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (((x.zeroExtend (mt.modulus.type.bitwidth + 1) + BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value - y.zeroExtend (mt.modulus.type.bitwidth + 1))
            % BitVec.ofInt (mt.modulus.type.bitwidth + 1) mt.modulus.value).truncate
            mt.modulus.type.bitwidth))]
      (cast9.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (Data.ModArith.sub mt.modulus.value x y))], state'.memory, none)) := by
    rw [hRT9, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf9 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth (.val (Data.ModArith.sub mt.modulus.value x y))]
      (cast9.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT9 ⟨rfl, by
      simp only [Data.ModArith.isCanonical_val]; exact Data.ModArith.isCanonical_sub hQpos hQle⟩
  obtain ⟨vs10, hSet9, hStep9⟩ := interpretOp_step (inB := g9In) hTy9 hOpVals9 hEval9 hConf9
  -- ## Assemble the ten steps.
  refine ⟨⟨vs10, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [cast0, ext1, cast2, ext3, const4, addi5, subi6, rem7, trunc8, cast9] state' _
      = some (.ok (⟨vs10, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep0]
    rw [interpretOpList_cons]; simp only [hStep1]
    rw [interpretOpList_cons]; simp only [hStep2]
    rw [interpretOpList_cons]; simp only [hStep3]
    rw [interpretOpList_cons]; simp only [hStep4]
    rw [interpretOpList_cons]; simp only [hStep5]
    rw [interpretOpList_cons]; simp only [hStep6]
    rw [interpretOpList_cons]; simp only [hStep7]
    rw [interpretOpList_cons]; simp only [hStep8]
    rw [interpretOpList_cons]; simp only [hStep9]
    rfl
  · -- memory unchanged
    simpa using hMemEq
  · -- target value refines the source result
    refine ⟨RuntimeValue.int mt.modulus.type.bitwidth
        (.val (Data.ModArith.sub mt.modulus.value x y)), ?_, ?_⟩
    · rw [VariableState.getVar?_setResultValues? hSet9]; simp [hNR9]
    · simp [RuntimeValue.isRefinedBy]

namespace ModArithToArithOriginal

/-- Inversion of a fired `lowerModArithConstant`: it matched `mod_arith.constant`, emitted an
`arith.constant` and a cast, and finished with `replaceAndErase`. -/
theorem lowerModArithConstant_fired_inv {rw : PatternRewriter OpCode} {op : OperationPtr}
    {rw' : PatternRewriter OpCode}
    (h : lowerModArithConstant rw op = some rw') (hne : rw'.ctx ≠ rw.ctx) :
    ∃ (props : ModArithConstantProperties) (mt : ModArithType)
      (rwC : PatternRewriter OpCode) (cv : ValuePtr) (rwOut : PatternRewriter OpCode) (out : ValuePtr),
      matchOp op rw.ctx.raw (.mod_arith .constant) 0
        = some (op.getOperands! rw.ctx.raw, props) ∧
      ((op.getResult 0 : ValuePtr).getType! rw.ctx.raw).val = .modArithType mt ∧
      props = op.getProperties! rw.ctx.raw (.mod_arith .constant) ∧
      emitArithConstant rw props.value.value mt.modulus.type.bitwidth (InsertPoint.before op)
        = some (rwC, cv) ∧
      castToModArith rwC cv mt (InsertPoint.before op) = some (rwOut, out) ∧
      replaceAndErase rwOut op out = some rw' := by
  unfold lowerModArithConstant at h
  split at h
  · rename_i operands props hmatch
    simp only at h
    split at h
    · rename_i mt hmt
      simp only [bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwC, cv⟩, hconst, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rwOut, out⟩, hcast, h⟩ := h
      obtain ⟨_, hNumOperands, _, hopr, hprops⟩ := matchOp_some_inv hmatch
      refine ⟨props, mt, rwC, cv, rwOut, out, ?_, hmt, hprops, hconst, hcast, h⟩
      rw [hopr] at hmatch; exact hmatch
    · rename_i hnotmod
      simp only [pure, Option.some.injEq] at h
      exact absurd (by rw [← h]) hne
  · rename_i hnomatch
    simp only [pure, Option.some.injEq] at h
    exact absurd (by rw [← h]) hne

end ModArithToArithOriginal

set_option maxHeartbeats 2000000 in
/-- Direct semantics correctness of the imperative `mod_arith.constant` lowering. -/
theorem lowerModArithConstant_correct :
    ImperativePatternCorrect ModArithToArithOriginal.lowerModArithConstant := by
  intro rw op rw' ctxDom ctxVerif opInBounds hpat hctxne
  obtain ⟨props, mt, rwC, cv, rwOut, out, hmatch, hmt, hprops, hconst, hcast, herase⟩ :=
    ModArithToArithOriginal.lowerModArithConstant_fired_inv hpat hctxne
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperands, _⟩ := matchOp_some_inv hmatch
  -- Verifier facts.
  have hVerified : op.Verified rw.ctx opInBounds :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif
  obtain ⟨_, hNumOperandsV, _, _, mtv, hResTy, hValTy, hValNonneg, hValLt, hValid⟩ :=
    hVerified.mod_arith_constant hOpType
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by
    rw [ValuePtr.getType!_opResult, hResTy] at hmt
    simp only [Attribute.modArithType.injEq] at hmt
    exact hmt
  subst mtv
  rw [← hprops] at hValTy hValNonneg hValLt
  -- Width: N ≥ 1.
  have hN1 : 1 ≤ mt.modulus.type.bitwidth := by
    rcases Nat.eq_zero_or_pos mt.modulus.type.bitwidth with h0 | h0
    · rw [h0] at hQwidth
      simp only [Nat.zero_sub, Int.pow_zero] at hQwidth
      omega
    · omega
  -- Extract the two created ops.
  obtain ⟨cst0, hcv_eq, _, _, _, _, hC0⟩ := ModArithToArithOriginal.emitArithConstant_inv hconst
  obtain ⟨cast1, hout_eq, _, _, _, _, hC1⟩ := ModArithToArithOriginal.castToModArith_inv hcast
  subst hcv_eq hout_eq
  -- Chains.
  have s1 : WfCreatedSeq rwOut.ctx rwOut.ctx := .nil
  have s0 : WfCreatedSeq rwC.ctx rwOut.ctx := .single hC1
  obtain ⟨f0In, f0Ty, f0Ops, f0RT, f0NR, f0Succ, f0P⟩ := newOpFactsAtPack hC0 s0
  obtain ⟨f1In, f1Ty, f1Ops, f1RT, f1NR, f1Succ, f1P⟩ := newOpFactsAtPack hC1 s1
  obtain ⟨ctxR, hRne, hRold, hRnew, hctxR, hRregions, hRuses, hRop, hfinal⟩ :=
    ModArithToArithOriginal.replaceAndErase_inv herase
  have freshNe : ∀ {o : OperationPtr}, ¬ o.InBounds rw.ctx.raw → o ≠ op := by
    intro o hNotRw heq; subst heq; exact hNotRw opInBounds
  have notRw : ∀ {cM cN : WfIRContext OpCode} {T rt ops bo rg} {p : propertiesOf T}
      {ipx ha hb hc hd} {o : OperationPtr},
      WfRewriter.createOp cM T rt ops bo rg p ipx ha hb hc hd = some (cN, o) →
      WfCreatedSeq rw.ctx cM → ¬ o.InBounds rw.ctx.raw := by
    intro cM cN T rt ops bo rg p ipx ha hb hc hd o hCo seqPre hin
    exact (WfRewriter.createOp_new_not_inBounds _ hCo) (seqPre.inBounds_mono (.operation o) hin)
  have n0 : ¬ cst0.InBounds rw.ctx.raw := notRw hC0 .nil
  have p1 : WfCreatedSeq rw.ctx rwC.ctx := .single hC0
  have n1 : ¬ cast1.InBounds rw.ctx.raw := notRw hC1 p1
  -- `op`'s result differs from each fresh op's result.
  have resNe : ∀ {o' : OperationPtr}, ¬ o'.InBounds rw.ctx.raw →
      (op.getResult 0 : ValuePtr) ≠ (o'.getResult 0 : ValuePtr) := by
    intro o' hfr heq
    apply hfr
    rw [show o' = op from by
      simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at heq
      exact heq.1.symm]
    exact opInBounds
  subst hctxR
  have hRuses' : (!op.hasUses! (WfRewriter.replaceValue rwOut.ctx (op.getResult 0)
      (cast1.getResult 0) hRne hRold hRnew).raw) = true := by simpa using hRuses
  have surv : ∀ (o : OperationPtr), o ≠ op → o.InBounds rwOut.ctx.raw →
      (op.getResult 0 : ValuePtr) ∉ o.getOperands! rwOut.ctx.raw →
      o.InBounds rw'.ctx.raw ∧
      o.getOpType! rw'.ctx.raw = o.getOpType! rwOut.ctx.raw ∧
      o.getOperands! rw'.ctx.raw = o.getOperands! rwOut.ctx.raw ∧
      o.getResultTypes! rw'.ctx.raw = o.getResultTypes! rwOut.ctx.raw ∧
      o.getNumResults! rw'.ctx.raw = o.getNumResults! rwOut.ctx.raw ∧
      o.getSuccessors! rw'.ctx.raw = o.getSuccessors! rwOut.ctx.raw ∧
      (∀ T, o.getProperties! rw'.ctx.raw T = o.getProperties! rwOut.ctx.raw T) := by
    intro o hne hin hnm
    have := ModArithToArithOriginal.opSurvives (op := op) (o := o) hRne hRold hRnew hRregions
      hRuses' hRop hne hin hnm
    rw [hfinal]; exact this
  have nm0 : (op.getResult 0 : ValuePtr) ∉ cst0.getOperands! rwOut.ctx.raw := by
    rw [f0Ops]; simp
  have nm1 : (op.getResult 0 : ValuePtr) ∉ cast1.getOperands! rwOut.ctx.raw := by
    rw [f1Ops]; simp only [Array.mem_singleton]; exact resNe n0
  obtain ⟨g0In, g0Ty, g0Ops, g0RT, g0NR, g0Succ, g0P⟩ := surv cst0 (freshNe n0) f0In nm0
  obtain ⟨g1In, g1Ty, g1Ops, g1RT, g1NR, g1Succ, g1P⟩ := surv cast1 (freshNe n1) f1In nm1
  -- Combined facts in `rw'.ctx`.
  have hTy0 : cst0.getOpType! rw'.ctx.raw = .arith .constant := g0Ty.trans f0Ty
  have hTy1 : cast1.getOpType! rw'.ctx.raw = .builtin .unrealized_conversion_cast := g1Ty.trans f1Ty
  have hOperands0 : cst0.getOperands! rw'.ctx.raw = #[] := g0Ops.trans f0Ops
  have hOperands1 : cast1.getOperands! rw'.ctx.raw = #[(cst0.getResult 0 : ValuePtr)] :=
    g1Ops.trans f1Ops
  have hSucc0 : cst0.getSuccessors! rw'.ctx.raw = #[] := g0Succ.trans f0Succ
  have hSucc1 : cast1.getSuccessors! rw'.ctx.raw = #[] := g1Succ.trans f1Succ
  have hNR0 : cst0.getNumResults! rw'.ctx.raw = 1 := g0NR.trans f0NR
  have hNR1 : cast1.getNumResults! rw'.ctx.raw = 1 := g1NR.trans f1NR
  have hRT0 : cst0.getResultTypes! rw'.ctx.raw
      = #[(IntegerType.mk mt.modulus.type.bitwidth : TypeAttr)] := g0RT.trans f0RT
  have hRT1 : cast1.getResultTypes! rw'.ctx.raw = #[⟨.modArithType mt, by rfl⟩] := g1RT.trans f1RT
  have hP0 : cst0.getProperties! rw'.ctx.raw (.arith .constant)
      = { value := IntegerAttr.mk props.value.value (IntegerType.mk mt.modulus.type.bitwidth) } :=
    (g0P _).trans f0P
  -- The new value is in bounds.
  have hNewValIn : (cast1.getResult 0 : ValuePtr).InBounds rw'.ctx.raw := by
    have : (OpResultPtr.mk cast1 0).InBounds rw'.ctx.raw :=
      OpResultPtr.inBounds_of g1In (by simp only [hNR1]; omega)
    simpa [ValuePtr.InBounds, OperationPtr.getResult] using this
  have seqFull : WfCreatedSeq rw.ctx rwOut.ctx := p1.snoc hC1
  have hOpNRPack : op.getNumResults! rwOut.ctx.raw = 1 := by
    rw [seqFull.getNumResults!_eq opInBounds]; exact hNumResults
  refine ⟨[cst0, cast1], (cast1.getResult 0 : ValuePtr), ?_, hNewValIn, ⟨?_, hNewValIn⟩, ?_⟩
  · intro o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨g0In, n0⟩
    · exact ⟨g1In, n1⟩
  · intro v hvIn hvNotRes
    have hvPack : v.InBounds rwOut.ctx.raw := seqFull.inBounds_mono (GenericPtr.value v) hvIn
    have hvNotResPack : v ∉ op.getResults! rwOut.ctx.raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      rintro ⟨i, hi, heqv⟩
      apply hvNotRes
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      exact ⟨i, by rw [hNumResults]; rw [hOpNRPack] at hi; exact hi, heqv⟩
    have hvR : v.InBounds (WfRewriter.replaceValue rwOut.ctx (op.getResult 0) (cast1.getResult 0)
        hRne hRold hRnew).raw := by
      have := (WfRewriter.replaceValue_inBounds (ptr := GenericPtr.value v)
        (ne := hRne) (oldIn := hRold) (newIn := hRnew)).mpr
        (by simpa [GenericPtr.InBounds] using hvPack)
      simpa [GenericPtr.InBounds] using this
    have hvNotResR : v ∉ op.getResults! (WfRewriter.replaceValue rwOut.ctx (op.getResult 0)
        (cast1.getResult 0) hRne hRold hRnew).raw := by
      rw [OperationPtr.getResults!.mem_iff_exists_index] at hvNotResPack ⊢
      simp only [OperationPtr.getNumResults!_WfRewriter_replaceValue] at *
      exact hvNotResPack
    rw [hfinal]
    exact ModArithToArithOriginal.valueSurvivesErase hvR hvNotResR
  -- The semantics replay.
  intro state newState cf hinterp srcVal hsrcVal state' hrefines
  obtain ⟨srcOperandVals, srcResVals, srcMem, srcVarState, hSrcOpVals, hSrcEval, hSrcSet,
    hSrcState⟩ := interpretOp_some_inv hOpType hinterp
  -- The constant has no operands.
  have hOpArr0 : op.getOperands! rw.ctx.raw = #[] := by
    have hsz : (op.getOperands! rw.ctx.raw).size = 0 := by
      rw [OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    exact Array.eq_empty_of_size_eq_zero hsz
  have hSrcOps0 : srcOperandVals = #[] := by
    unfold VariableState.getOperandValues at hSrcOpVals
    rw [hOpArr0] at hSrcOpVals
    simpa using hSrcOpVals.symm
  subst hSrcOps0
  -- The source result type is the modulus type.
  have hSrcNumRes : (op.getResultTypes! rw.ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
  have hResTy0 : (op.getResultTypes! rw.ctx.raw)[0]? = some ⟨.modArithType mt, by rfl⟩ := by
    have h0 : (op.getResultTypes! rw.ctx.raw)[0]?
        = some ((op.getResultTypes! rw.ctx.raw)[0]'(by omega)) := by simp [hSrcNumRes]
    rw [h0]; congr 1; apply Subtype.ext
    rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
  have hSrcEval' : interpretOp' (.mod_arith .constant)
      (op.getProperties! rw.ctx.raw (.mod_arith .constant)) (op.getResultTypes! rw.ctx.raw) #[]
      (op.getSuccessors! rw.ctx.raw) state.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))],
          state.memory, none)) := by
    simp only [interpretOp', ModArith.interpretOp', hResTy0, ← hprops]
    rfl
  rw [hSrcEval'] at hSrcEval
  have hSrcResVals : srcResVals = #[RuntimeValue.int mt.modulus.type.bitwidth
      (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))] := by grind
  have hSrcMemEq : srcMem = state.memory := by grind
  have hcf : cf = none := by grind
  subst hcf; subst hSrcMemEq; subst hSrcState
  have hvSrc : srcVarState.getVar? (op.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))) := by
    rw [VariableState.getVar?_setResultValues? hSrcSet]; simp [hNumResults, hSrcResVals]
  have hsrcVal' : srcVal = RuntimeValue.int mt.modulus.type.bitwidth
      (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value)) := by
    rw [hvSrc] at hsrcVal; exact (Option.some.injEq _ _).mp hsrcVal.symm
  subst hsrcVal'
  obtain ⟨hMemEq, _⟩ := hrefines
  -- Canonicity of the constant value.
  have hCanon : ((BitVec.ofInt mt.modulus.type.bitwidth props.value.value).toNat : Int)
      < mt.modulus.value := by
    have hPowLe : ((2 : Int) ^ (mt.modulus.type.bitwidth - 1)) ≤ 2 ^ mt.modulus.type.bitwidth := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.sub_le mt.modulus.type.bitwidth 1)
      exact_mod_cast this
    have hofInt := Data.ModArith.toNat_ofInt_modulus (m := mt.modulus.type.bitwidth) hValNonneg
      (by omega)
    omega
  -- Step cst₀: the `arith.constant`.
  have hOpVals0 : state'.variables.getOperandValues cst0 = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands0, Array.mapM_eq_mapM_toList]; simp
  have hEval0 : interpretOp' (.arith .constant) (cst0.getProperties! rw'.ctx.raw (.arith .constant))
      (cst0.getResultTypes! rw'.ctx.raw) #[] (cst0.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))],
          state'.memory, none)) := by
    rw [hRT0, hP0]; rfl
  have hConf0 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))]
      (cst0.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT0 (by simp [RuntimeValue.Conforms])
  obtain ⟨vs1, hSet0, hStep0⟩ := interpretOp_step (inB := g0In) hTy0 hOpVals0 hEval0 hConf0
  have hv1 : vs1.getVar? (cst0.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet0]; simp [hNR0]
  -- Step cast₁: cast to `!mod_arith.int`.
  have hOpVals1 : (InterpreterState.mk vs1 state'.memory).variables.getOperandValues cast1
      = some #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))] :=
    ModArithToArith.getOperandValues_one hOperands1 hv1
  have hEval1 : interpretOp' (.builtin .unrealized_conversion_cast)
      (cast1.getProperties! rw'.ctx.raw (.builtin .unrealized_conversion_cast))
      (cast1.getResultTypes! rw'.ctx.raw)
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))]
      (cast1.getSuccessors! rw'.ctx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))],
          state'.memory, none)) := by
    rw [hRT1]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf1 : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mt.modulus.type.bitwidth
          (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value))]
      (cast1.getResultTypes! rw'.ctx.raw) :=
    arrayConforms_singleton hRT1 ⟨rfl, by simp only [Data.ModArith.isCanonical_val]; exact hCanon⟩
  obtain ⟨vs2, hSet1, hStep1⟩ := interpretOp_step (inB := g1In) hTy1 hOpVals1 hEval1 hConf1
  refine ⟨⟨vs2, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [cst0, cast1] state' _ = some (.ok (⟨vs2, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep0]
    rw [interpretOpList_cons]; simp only [hStep1]
    rfl
  · simpa using hMemEq
  · refine ⟨RuntimeValue.int mt.modulus.type.bitwidth
        (.val (BitVec.ofInt mt.modulus.type.bitwidth props.value.value)), ?_, ?_⟩
    · rw [VariableState.getVar?_setResultValues? hSet1]; simp [hNR1]
    · simp [RuntimeValue.isRefinedBy]

end Veir
