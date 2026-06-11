import Veir.Passes.ModArithToArithBarrett
import Veir.Passes.ModArithToArith.Proofs
import Veir.Data.ModArith.Barrett

/-!
# Correctness of the Barrett-based ModArithToArith lowering patterns

The structural properties (`ReturnOps`, `ReturnCtxChanges`, ...) hold for the Barrett
patterns directly, since they are proven parametrically in the recipe
(`lowerBinop_returnOps` etc. in `Veir.Passes.ModArithToArith.Proofs`).

This file proves `PreservesSemantics` for the three Barrett recipes: interpreting the
operations they create computes the reference semantics `(x ⊙ y) mod q`, with the
arithmetic correctness supplied by `Veir.Data.ModArith.Barrett.barrett_core` and
`subifge_eq_mod`.
-/

namespace Veir

namespace ModArithToArith

set_option maxHeartbeats 2000000 in
theorem lowerAddBarrett_preservesSemantics :
    (lowerBinop .add addBarrettRecipe).PreservesSemantics
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
    hVerified.mod_arith_binop hOpType (Or.inl rfl)
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by have := hResTy; grind [ValuePtr.getType!]
  subst hmtv
  -- Unpack the eight operations created by the recipe.
  rw [addBarrettRecipe] at hbuild
  obtain ⟨res₀, ctx₁, op₀, _, _, _, _, hres₀, hC₀, hbuild₁⟩ := buildOps_cons_inv hbuild
  obtain ⟨res₁, ctx₂, op₁, _, _, _, _, hres₁, hC₁, hbuild₂⟩ := buildOps_cons_inv hbuild₁
  obtain ⟨res₂, ctx₃, op₂, _, _, _, _, hres₂, hC₂, hbuild₃⟩ := buildOps_cons_inv hbuild₂
  obtain ⟨res₃, ctx₄, op₃, _, _, _, _, hres₃, hC₃, hbuild₄⟩ := buildOps_cons_inv hbuild₃
  obtain ⟨res₄, ctx₅, op₄, _, _, _, _, hres₄, hC₄, hbuild₅⟩ := buildOps_cons_inv hbuild₄
  obtain ⟨res₅, ctx₆, op₅, _, _, _, _, hres₅, hC₅, hbuild₆⟩ := buildOps_cons_inv hbuild₅
  obtain ⟨res₆, ctx₇, op₆, _, _, _, _, hres₆, hC₆, hbuild₇⟩ := buildOps_cons_inv hbuild₆
  obtain ⟨res₇, ctx₈, op₇, _, _, _, _, hres₇, hC₇, hbuild₈⟩ := buildOps_cons_inv hbuild₇
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₈
  have hresult : op₇ = result := by simpa using hback
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
  -- Resolve the `.outer` operand arrays of ops 0 and 1 (the casts of `lhs` and `rhs`).
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
  have hres₁' : res₁.map (·.val) = #[operands[1]!] := by
    have hsize : res₁.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₁; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₁ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  -- Resolve the `.created` operand arrays.
  have hres₂' : res₂.map (·.val) = #[(op₀.getResult 0 : ValuePtr), (op₁.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 0) (j := 1) (by simp [binopDescr]) (by simp) (by simp) hres₂
  have hres₄' : res₄.map (·.val) = #[(op₂.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 2) (j := 3) (by simp [cmpiUgeDescr]) (by simp) (by simp) hres₄
  have hres₅' : res₅.map (·.val) = #[(op₂.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 2) (j := 3) (by simp [binopDescr]) (by simp) (by simp) hres₅
  -- the select op has three created operands; resolve it directly.
  have hres₆' : res₆.map (·.val)
      = #[(op₄.getResult 0 : ValuePtr), (op₅.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] := by
    have hd : (selectDescr (.created 4 0) (.created 5 0) (.created 2 0) mtv.modulus.type.bitwidth).operands
        = #[.created 4 0, .created 5 0, .created 2 0] := by simp [selectDescr]
    rw [hd] at hres₆
    have hsize : res₆.size = 3 := by
      have := Array.size_eq_of_mapM_eq_some hres₆; simpa using this.symm
    have hidx0 := Array.mapM_option_eq_some_implies hres₆ 0 (by omega)
    have hidx1 := Array.mapM_option_eq_some_implies hres₆ 1 (by omega)
    have hidx2 := Array.mapM_option_eq_some_implies hres₆ 2 (by omega)
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hidx0 hidx1 hidx2
    obtain ⟨a0, ha0, hval0⟩ := resolve_created_inv (by simpa using hidx0)
    obtain ⟨a1, ha1, hval1⟩ := resolve_created_inv (by simpa using hidx1)
    obtain ⟨a2, ha2, hval2⟩ := resolve_created_inv (by simpa using hidx2)
    have e0 : op₄ = a0 := by simpa using ha0
    have e1 : op₅ = a1 := by simpa using ha1
    have e2 : op₂ = a2 := by simpa using ha2
    subst e0; subst e1; subst e2
    apply Array.ext
    · simpa using hsize
    · intro k h1 h2
      simp only [Array.size_map, hsize] at h1
      match k, h1 with
      | 0, _ => simpa using hval0
      | 1, _ => simpa using hval1
      | 2, _ => simpa using hval2
  have hres₇' : res₇.map (·.val) = #[(op₆.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 6) (by simp [castDescr]) (by simp) hres₇
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
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  have hnfc₀ : ¬ op₀.InBounds ctx.raw := hnf₀
  have hnfc₁ : ¬ op₁.InBounds ctx.raw := fun h => hnf₁ (mono hC₀ h)
  have hnfc₂ : ¬ op₂.InBounds ctx.raw := fun h => hnf₂ (mono hC₁ (mono hC₀ h))
  have hnfc₃ : ¬ op₃.InBounds ctx.raw := fun h => hnf₃ (mono hC₂ (mono hC₁ (mono hC₀ h)))
  have hnfc₄ : ¬ op₄.InBounds ctx.raw := fun h => hnf₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h))))
  have hnfc₅ : ¬ op₅.InBounds ctx.raw :=
    fun h => hnf₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h)))))
  have hnfc₆ : ¬ op₆.InBounds ctx.raw :=
    fun h => hnf₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h))))))
  have hInB₀ : op₀.InBounds newCtx.raw :=
    mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀))))))
  have hInB₁ : op₁.InBounds newCtx.raw :=
    mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁)))))
  have hInB₂ : op₂.InBounds newCtx.raw :=
    mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂))))
  have hInB₃ : op₃.InBounds newCtx.raw :=
    mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃)))
  have hInB₄ : op₄.InBounds newCtx.raw := mono hC₇ (mono hC₆ (mono hC₅ hfresh₄))
  have hInB₅ : op₅.InBounds newCtx.raw := mono hC₇ (mono hC₆ hfresh₅)
  have hInB₆ : op₆.InBounds newCtx.raw := mono hC₇ hfresh₆
  have hInB₇ : op₇.InBounds newCtx.raw := hfresh₇
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  have i01 : op₀.InBounds ctx₁.raw := hfresh₀
  have i02 : op₀.InBounds ctx₂.raw := mono hC₁ i01
  have i03 : op₀.InBounds ctx₃.raw := mono hC₂ i02
  have i04 : op₀.InBounds ctx₄.raw := mono hC₃ i03
  have i05 : op₀.InBounds ctx₅.raw := mono hC₄ i04
  have i06 : op₀.InBounds ctx₆.raw := mono hC₅ i05
  have i07 : op₀.InBounds ctx₇.raw := mono hC₆ i06
  have i12 : op₁.InBounds ctx₂.raw := hfresh₁
  have i13 : op₁.InBounds ctx₃.raw := mono hC₂ i12
  have i14 : op₁.InBounds ctx₄.raw := mono hC₃ i13
  have i15 : op₁.InBounds ctx₅.raw := mono hC₄ i14
  have i16 : op₁.InBounds ctx₆.raw := mono hC₅ i15
  have i17 : op₁.InBounds ctx₇.raw := mono hC₆ i16
  have i23 : op₂.InBounds ctx₃.raw := hfresh₂
  have i24 : op₂.InBounds ctx₄.raw := mono hC₃ i23
  have i25 : op₂.InBounds ctx₅.raw := mono hC₄ i24
  have i26 : op₂.InBounds ctx₆.raw := mono hC₅ i25
  have i27 : op₂.InBounds ctx₇.raw := mono hC₆ i26
  have i34 : op₃.InBounds ctx₄.raw := hfresh₃
  have i35 : op₃.InBounds ctx₅.raw := mono hC₄ i34
  have i36 : op₃.InBounds ctx₆.raw := mono hC₅ i35
  have i37 : op₃.InBounds ctx₇.raw := mono hC₆ i36
  have i45 : op₄.InBounds ctx₅.raw := hfresh₄
  have i46 : op₄.InBounds ctx₆.raw := mono hC₅ i45
  have i47 : op₄.InBounds ctx₇.raw := mono hC₆ i46
  have i56 : op₅.InBounds ctx₆.raw := hfresh₅
  have i57 : op₅.InBounds ctx₇.raw := mono hC₆ i56
  have i67 : op₆.InBounds ctx₇.raw := hfresh₆
  have d01 : op₀ ≠ op₁ := ne i01 hnf₁
  have d02 : op₀ ≠ op₂ := ne i02 hnf₂
  have d03 : op₀ ≠ op₃ := ne i03 hnf₃
  have d04 : op₀ ≠ op₄ := ne i04 hnf₄
  have d05 : op₀ ≠ op₅ := ne i05 hnf₅
  have d06 : op₀ ≠ op₆ := ne i06 hnf₆
  have d07 : op₀ ≠ op₇ := ne i07 hnf₇
  have d12 : op₁ ≠ op₂ := ne i12 hnf₂
  have d13 : op₁ ≠ op₃ := ne i13 hnf₃
  have d14 : op₁ ≠ op₄ := ne i14 hnf₄
  have d15 : op₁ ≠ op₅ := ne i15 hnf₅
  have d16 : op₁ ≠ op₆ := ne i16 hnf₆
  have d17 : op₁ ≠ op₇ := ne i17 hnf₇
  have d23 : op₂ ≠ op₃ := ne i23 hnf₃
  have d24 : op₂ ≠ op₄ := ne i24 hnf₄
  have d25 : op₂ ≠ op₅ := ne i25 hnf₅
  have d26 : op₂ ≠ op₆ := ne i26 hnf₆
  have d27 : op₂ ≠ op₇ := ne i27 hnf₇
  have d34 : op₃ ≠ op₄ := ne i34 hnf₄
  have d35 : op₃ ≠ op₅ := ne i35 hnf₅
  have d36 : op₃ ≠ op₆ := ne i36 hnf₆
  have d37 : op₃ ≠ op₇ := ne i37 hnf₇
  have d45 : op₄ ≠ op₅ := ne i45 hnf₅
  have d46 : op₄ ≠ op₆ := ne i46 hnf₆
  have d47 : op₄ ≠ op₇ := ne i47 hnf₇
  have d56 : op₅ ≠ op₆ := ne i56 hnf₆
  have d57 : op₅ ≠ op₇ := ne i57 hnf₇
  have d67 : op₆ ≠ op₇ := ne i67 hnf₇
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  -- Op types.
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .arith .addi := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .cmpi := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .select := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  -- Operands.
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀,
      if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁,
      if_pos rfl, hres₁']
  have hOperands₂ : op₂.getOperands! newCtx.raw
      = #[(op₀.getResult 0 : ValuePtr), (op₁.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂,
      if_pos rfl, hres₂']
  have hres₃' : res₃.map (·.val) = #[] := by
    have hsz : res₃.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₃; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₃ : op₃.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃,
      if_pos rfl, hres₃']
  have hOperands₄ : op₄.getOperands! newCtx.raw
      = #[(op₂.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄,
      if_pos rfl, hres₄']
  have hOperands₅ : op₅.getOperands! newCtx.raw
      = #[(op₂.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅,
      if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₄.getResult 0 : ValuePtr), (op₅.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆,
      if_pos rfl, hres₆']
  have hOperands₇ : op₇.getOperands! newCtx.raw = #[(op₆.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₇, if_pos rfl, hres₇']
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
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  -- Result types.
  have hRT₀ : op₀.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w1 hfresh₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk 1 : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  -- Properties (only the ones we need to evaluate the interpreter).
  have hP₂ : op₂.getProperties! newCtx.raw (.arith .addi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w3 hfresh₂]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₂ (operation := op₂)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk mtv.modulus.type.bitwidth) } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .cmpi) = { predicate := .uge } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  -- ## Source interpretation
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
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
  -- ## Refinement transfer.
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
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val x) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val y) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  -- ## Width side conditions and the pipeline arithmetic core.
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  have hqm : 2 * mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth := by
    have hnat : (2:Nat)^(mtv.modulus.type.bitwidth - 1) * 2 = 2^(mtv.modulus.type.bitwidth) := by
      rw [← Nat.pow_succ]
      congr 1; omega
    have hcast : (2:Int)^(mtv.modulus.type.bitwidth)
        = ((2^(mtv.modulus.type.bitwidth) : Nat) : Int) := by push_cast; rfl
    have hcast2 : (2:Int)^(mtv.modulus.type.bitwidth - 1)
        = ((2^(mtv.modulus.type.bitwidth - 1) : Nat) : Int) := by push_cast; rfl
    rw [hcast]; rw [hcast2] at hQwidth
    have hnat' : ((2^(mtv.modulus.type.bitwidth - 1):Nat):Int) * 2 = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      exact_mod_cast hnat
    omega
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth := by omega
  -- The pipeline result and its canonicity.
  have hPipeEq : (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
      then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y))
      = Data.ModArith.add mtv.modulus.value x y :=
    Data.ModArith.addSubifge_eq_add hQpos hqm hxlt hylt
  -- ## Target interpretation: step through the eight created operations.
  -- Step op₀: cast `lhs : iN`.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₀, Array.mapM_eq_mapM_toList]; simp [hTLhs]
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) := by
    rw [hRT₀]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnf₀ hSet₀]; exact hTRhs
  -- Step op₁: cast `rhs : iN`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁, Array.mapM_eq_mapM_toList]; simp [hv₁_rhs]
  have hEval₁ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₁.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₁]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₁.getResultTypes! newCtx.raw) := by
    rw [hRT₁]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  have hv₂_0 : vs₂.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [getVar?_setResultValues?_ne d01 hSet₁]; exact hv₁_0
  have hv₂_1 : vs₂.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  -- Step op₂: addi (t = x + y).
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₂, Array.mapM_eq_mapM_toList]; simp [hv₂_0, hv₂_1]
  have hEval₂ : interpretOp' (.arith .addi) (op₂.getProperties! newCtx.raw (.arith .addi))
      (op₂.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))], state'.memory, none)) := by
    rw [hP₂]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))] (op₂.getResultTypes! newCtx.raw) := by
    rw [hRT₂]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  -- Step op₃: const q : iN.
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₃, Array.mapM_eq_mapM_toList]; simp
  have hEval₃ : interpretOp' (.arith .constant) (op₃.getProperties! newCtx.raw (.arith .constant))
      (op₃.getResultTypes! newCtx.raw) #[] (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))], state'.memory, none)) := by
    rw [hRT₃, hP₃]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₃.getResultTypes! newCtx.raw) := by
    rw [hRT₃]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  have hv₄_2 : vs₄.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))) := by
    rw [getVar?_setResultValues?_ne d23 hSet₃]; exact hv₃_2
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  -- Step op₄: cmpi uge t q → i1.
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp [hv₄_2, hv₄_3]
  have hEval₄ : interpretOp' (.arith .cmpi) (op₄.getProperties! newCtx.raw (.arith .cmpi))
      (op₄.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y))))],
          state'.memory, none)) := by
    rw [hP₄]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.icmp, Data.LLVM.Int.cast, Id.run, pure, bind,
      Data.LLVM.IntPred.eval]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y))))]
      (op₄.getResultTypes! newCtx.raw) := by
    rw [hRT₄]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  have hv₅_2 : vs₅.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))) := by
    rw [getVar?_setResultValues?_ne d24 hSet₄]; exact hv₄_2
  have hv₅_3 : vs₅.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d34 hSet₄]; exact hv₄_3
  have hv₅_4 : vs₅.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y))))) := by
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  -- Step op₅: subi (t - q).
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₅, Array.mapM_eq_mapM_toList]; simp [hv₅_2, hv₅_3]
  have hEval₅ : interpretOp' (.arith .subi) (op₅.getProperties! newCtx.raw (.arith .subi))
      (op₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))],
          state'.memory, none)) := by
    rw [hP₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₅.getResultTypes! newCtx.raw) := by
    rw [hRT₅]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  have hv₆_2 : vs₆.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))) := by
    rw [getVar?_setResultValues?_ne d25 hSet₅]; exact hv₅_2
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y))))) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]; exact hv₅_4
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  -- Step op₆: select cond (t-q) t.
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int 1
            (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)))),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₆, Array.mapM_eq_mapM_toList]; simp [hv₆_4, hv₆_5, hv₆_2]
  have hEval₆ : interpretOp' (.arith .select) (op₆.getProperties! newCtx.raw (.arith .select))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int 1
            (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)))),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val (x + y))]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
            then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y)))],
          state'.memory, none)) := by
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.select, Data.LLVM.Int.cast, Id.run, pure,
      bind, apply_ite]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
            then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y)))]
      (op₆.getResultTypes! newCtx.raw) := by
    rw [hRT₆]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  have hv₇_6 : vs₇.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
            then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  -- Step op₇: cast back to !mod_arith.int.
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
            then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y)))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₇, Array.mapM_eq_mapM_toList]; simp [hv₇_6]
  have hEval₇ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₇.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₇.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule (x + y)) == 1#1)
            then (x + y - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value) else (x + y)))]
      (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.add mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₇, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.add mtv.modulus.value x y))]
      (op₇.getResultTypes! newCtx.raw) := by
    rw [hRT₇]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this
    refine ⟨rfl, ?_⟩
    simp only [Data.ModArith.isCanonical_val]
    exact Data.ModArith.isCanonical_add hQpos hQle
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  -- ## Assemble the eight steps.
  refine ⟨⟨vs₈, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁, op₂, op₃, op₄, op₅, op₆, op₇] state' _
      = liftM (some (⟨vs₈, state'.memory⟩, none))
    rw [interpretOpList_cons]; simp only [hStep₀]
    rw [interpretOpList_cons]; simp only [hStep₁]
    rw [interpretOpList_cons]; simp only [hStep₂]
    rw [interpretOpList_cons]; simp only [hStep₃]
    rw [interpretOpList_cons]; simp only [hStep₄]
    rw [interpretOpList_cons]; simp only [hStep₅]
    rw [interpretOpList_cons]; simp only [hStep₆]
    rw [interpretOpList_cons]; simp only [hStep₇]
    simp [liftM, monadLift, MonadLift.monadLift]
  · simpa using hMemEq
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (Data.ModArith.add mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₈ : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.add mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₈]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]

set_option maxHeartbeats 2000000 in
theorem lowerSubBarrett_preservesSemantics :
    (lowerBinop .sub subBarrettRecipe).PreservesSemantics
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
  -- Unpack the nine operations created by the recipe.
  rw [subBarrettRecipe] at hbuild
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
  have hresult : op₈ = result := by simpa using hback
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
  -- Resolve the `.outer` operand arrays of ops 0 and 1.
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
  have hres₁' : res₁.map (·.val) = #[operands[1]!] := by
    have hsize : res₁.size = 1 := by
      have := Array.size_eq_of_mapM_eq_some hres₁; simpa [castDescr] using this.symm
    have hidx := Array.mapM_option_eq_some_implies hres₁ 0 (by omega)
    obtain ⟨hin, hval⟩ := resolve_outer_inv (by simpa [castDescr] using hidx)
    apply Array.ext
    · simpa using hsize
    · intro i h1 h2
      have hi : i = 0 := by simp only [Array.size_map, hsize] at h1; omega
      subst hi; simpa using hval
  -- Resolve the `.created` operand arrays.
  -- op₃ = addi (.created 0 0) (.created 2 0) ;  op₄ = subi (.created 3 0) (.created 1 0)
  have hres₃' : res₃.map (·.val) = #[(op₀.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 0) (j := 2) (by simp [binopDescr]) (by simp) (by simp) hres₃
  have hres₄' : res₄.map (·.val) = #[(op₃.getResult 0 : ValuePtr), (op₁.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 3) (j := 1) (by simp [binopDescr]) (by simp) (by simp) hres₄
  have hres₅' : res₅.map (·.val) = #[(op₄.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 4) (j := 2) (by simp [cmpiUgeDescr]) (by simp) (by simp) hres₅
  have hres₆' : res₆.map (·.val) = #[(op₄.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 4) (j := 2) (by simp [binopDescr]) (by simp) (by simp) hres₆
  -- op₇ = select (.created 5 0) (.created 6 0) (.created 4 0) : three created operands.
  have hres₇' : res₇.map (·.val)
      = #[(op₅.getResult 0 : ValuePtr), (op₆.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    have hd : (selectDescr (.created 5 0) (.created 6 0) (.created 4 0) mtv.modulus.type.bitwidth).operands
        = #[.created 5 0, .created 6 0, .created 4 0] := by simp [selectDescr]
    rw [hd] at hres₇
    have hsize : res₇.size = 3 := by
      have := Array.size_eq_of_mapM_eq_some hres₇; simpa using this.symm
    have hidx0 := Array.mapM_option_eq_some_implies hres₇ 0 (by omega)
    have hidx1 := Array.mapM_option_eq_some_implies hres₇ 1 (by omega)
    have hidx2 := Array.mapM_option_eq_some_implies hres₇ 2 (by omega)
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hidx0 hidx1 hidx2
    obtain ⟨a0, ha0, hval0⟩ := resolve_created_inv (by simpa using hidx0)
    obtain ⟨a1, ha1, hval1⟩ := resolve_created_inv (by simpa using hidx1)
    obtain ⟨a2, ha2, hval2⟩ := resolve_created_inv (by simpa using hidx2)
    have e0 : op₅ = a0 := by simpa using ha0
    have e1 : op₆ = a1 := by simpa using ha1
    have e2 : op₄ = a2 := by simpa using ha2
    subst e0; subst e1; subst e2
    apply Array.ext
    · simpa using hsize
    · intro k h1 h2
      simp only [Array.size_map, hsize] at h1
      match k, h1 with
      | 0, _ => simpa using hval0
      | 1, _ => simpa using hval1
      | 2, _ => simpa using hval2
  have hres₈' : res₈.map (·.val) = #[(op₇.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 7) (by simp [castDescr]) (by simp) hres₈
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
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  have hnfc₀ : ¬ op₀.InBounds ctx.raw := hnf₀
  have hnfc₁ : ¬ op₁.InBounds ctx.raw := fun h => hnf₁ (mono hC₀ h)
  have hnfc₂ : ¬ op₂.InBounds ctx.raw := fun h => hnf₂ (mono hC₁ (mono hC₀ h))
  have hnfc₃ : ¬ op₃.InBounds ctx.raw := fun h => hnf₃ (mono hC₂ (mono hC₁ (mono hC₀ h)))
  have hnfc₄ : ¬ op₄.InBounds ctx.raw := fun h => hnf₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h))))
  have hnfc₅ : ¬ op₅.InBounds ctx.raw :=
    fun h => hnf₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h)))))
  have hnfc₆ : ¬ op₆.InBounds ctx.raw :=
    fun h => hnf₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h))))))
  have hnfc₇ : ¬ op₇.InBounds ctx.raw :=
    fun h => hnf₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ (mono hC₀ h)))))))
  have hInB₀ : op₀.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀)))))))
  have hInB₁ : op₁.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁))))))
  have hInB₂ : op₂.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂)))))
  have hInB₃ : op₃.InBounds newCtx.raw :=
    mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃))))
  have hInB₄ : op₄.InBounds newCtx.raw := mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ hfresh₄)))
  have hInB₅ : op₅.InBounds newCtx.raw := mono hC₈ (mono hC₇ (mono hC₆ hfresh₅))
  have hInB₆ : op₆.InBounds newCtx.raw := mono hC₈ (mono hC₇ hfresh₆)
  have hInB₇ : op₇.InBounds newCtx.raw := mono hC₈ hfresh₇
  have hInB₈ : op₈.InBounds newCtx.raw := hfresh₈
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  have i01 : op₀.InBounds ctx₁.raw := hfresh₀
  have i02 : op₀.InBounds ctx₂.raw := mono hC₁ i01
  have i03 : op₀.InBounds ctx₃.raw := mono hC₂ i02
  have i04 : op₀.InBounds ctx₄.raw := mono hC₃ i03
  have i05 : op₀.InBounds ctx₅.raw := mono hC₄ i04
  have i06 : op₀.InBounds ctx₆.raw := mono hC₅ i05
  have i07 : op₀.InBounds ctx₇.raw := mono hC₆ i06
  have i08 : op₀.InBounds ctx₈.raw := mono hC₇ i07
  have i12 : op₁.InBounds ctx₂.raw := hfresh₁
  have i13 : op₁.InBounds ctx₃.raw := mono hC₂ i12
  have i14 : op₁.InBounds ctx₄.raw := mono hC₃ i13
  have i15 : op₁.InBounds ctx₅.raw := mono hC₄ i14
  have i16 : op₁.InBounds ctx₆.raw := mono hC₅ i15
  have i17 : op₁.InBounds ctx₇.raw := mono hC₆ i16
  have i18 : op₁.InBounds ctx₈.raw := mono hC₇ i17
  have i23 : op₂.InBounds ctx₃.raw := hfresh₂
  have i24 : op₂.InBounds ctx₄.raw := mono hC₃ i23
  have i25 : op₂.InBounds ctx₅.raw := mono hC₄ i24
  have i26 : op₂.InBounds ctx₆.raw := mono hC₅ i25
  have i27 : op₂.InBounds ctx₇.raw := mono hC₆ i26
  have i28 : op₂.InBounds ctx₈.raw := mono hC₇ i27
  have i34 : op₃.InBounds ctx₄.raw := hfresh₃
  have i35 : op₃.InBounds ctx₅.raw := mono hC₄ i34
  have i36 : op₃.InBounds ctx₆.raw := mono hC₅ i35
  have i37 : op₃.InBounds ctx₇.raw := mono hC₆ i36
  have i38 : op₃.InBounds ctx₈.raw := mono hC₇ i37
  have i45 : op₄.InBounds ctx₅.raw := hfresh₄
  have i46 : op₄.InBounds ctx₆.raw := mono hC₅ i45
  have i47 : op₄.InBounds ctx₇.raw := mono hC₆ i46
  have i48 : op₄.InBounds ctx₈.raw := mono hC₇ i47
  have i56 : op₅.InBounds ctx₆.raw := hfresh₅
  have i57 : op₅.InBounds ctx₇.raw := mono hC₆ i56
  have i58 : op₅.InBounds ctx₈.raw := mono hC₇ i57
  have i67 : op₆.InBounds ctx₇.raw := hfresh₆
  have i68 : op₆.InBounds ctx₈.raw := mono hC₇ i67
  have i78 : op₇.InBounds ctx₈.raw := hfresh₇
  have d01 : op₀ ≠ op₁ := ne i01 hnf₁
  have d02 : op₀ ≠ op₂ := ne i02 hnf₂
  have d03 : op₀ ≠ op₃ := ne i03 hnf₃
  have d04 : op₀ ≠ op₄ := ne i04 hnf₄
  have d05 : op₀ ≠ op₅ := ne i05 hnf₅
  have d06 : op₀ ≠ op₆ := ne i06 hnf₆
  have d07 : op₀ ≠ op₇ := ne i07 hnf₇
  have d08 : op₀ ≠ op₈ := ne i08 hnf₈
  have d12 : op₁ ≠ op₂ := ne i12 hnf₂
  have d13 : op₁ ≠ op₃ := ne i13 hnf₃
  have d14 : op₁ ≠ op₄ := ne i14 hnf₄
  have d15 : op₁ ≠ op₅ := ne i15 hnf₅
  have d16 : op₁ ≠ op₆ := ne i16 hnf₆
  have d17 : op₁ ≠ op₇ := ne i17 hnf₇
  have d18 : op₁ ≠ op₈ := ne i18 hnf₈
  have d23 : op₂ ≠ op₃ := ne i23 hnf₃
  have d24 : op₂ ≠ op₄ := ne i24 hnf₄
  have d25 : op₂ ≠ op₅ := ne i25 hnf₅
  have d26 : op₂ ≠ op₆ := ne i26 hnf₆
  have d27 : op₂ ≠ op₇ := ne i27 hnf₇
  have d28 : op₂ ≠ op₈ := ne i28 hnf₈
  have d34 : op₃ ≠ op₄ := ne i34 hnf₄
  have d35 : op₃ ≠ op₅ := ne i35 hnf₅
  have d36 : op₃ ≠ op₆ := ne i36 hnf₆
  have d37 : op₃ ≠ op₇ := ne i37 hnf₇
  have d38 : op₃ ≠ op₈ := ne i38 hnf₈
  have d45 : op₄ ≠ op₅ := ne i45 hnf₅
  have d46 : op₄ ≠ op₆ := ne i46 hnf₆
  have d47 : op₄ ≠ op₇ := ne i47 hnf₇
  have d48 : op₄ ≠ op₈ := ne i48 hnf₈
  have d56 : op₅ ≠ op₆ := ne i56 hnf₆
  have d57 : op₅ ≠ op₇ := ne i57 hnf₇
  have d58 : op₅ ≠ op₈ := ne i58 hnf₈
  have d67 : op₆ ≠ op₇ := ne i67 hnf₇
  have d68 : op₆ ≠ op₈ := ne i68 hnf₈
  have d78 : op₇ ≠ op₈ := ne i78 hnf₈
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  have w8 : WfIRContext.WithCreatedOps ctx₈ newCtx := buildOps_withCreatedOps hbuild₈
  -- Op types.
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀,
      if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .addi := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .cmpi := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .arith .select := by
    rw [WithCreatedOps.getOpType!_eq w8 hfresh₇, OperationPtr.getOpType!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hTy₈ : op₈.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Operands.
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀,
      if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁,
      if_pos rfl, hres₁']
  have hres₂' : res₂.map (·.val) = #[] := by
    have hsz : res₂.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₂; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₂ : op₂.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂,
      if_pos rfl, hres₂']
  have hOperands₃ : op₃.getOperands! newCtx.raw
      = #[(op₀.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃,
      if_pos rfl, hres₃']
  have hOperands₄ : op₄.getOperands! newCtx.raw
      = #[(op₃.getResult 0 : ValuePtr), (op₁.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄,
      if_pos rfl, hres₄']
  have hOperands₅ : op₅.getOperands! newCtx.raw
      = #[(op₄.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅,
      if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₄.getResult 0 : ValuePtr), (op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆,
      if_pos rfl, hres₆']
  have hOperands₇ : op₇.getOperands! newCtx.raw
      = #[(op₅.getResult 0 : ValuePtr), (op₆.getResult 0 : ValuePtr), (op₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w8 hfresh₇, OperationPtr.getOperands!_WfRewriter_createOp hC₇,
      if_pos rfl, hres₇']
  have hOperands₈ : op₈.getOperands! newCtx.raw = #[(op₇.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₈, if_pos rfl, hres₈']
  -- Number of results.
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
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁,
      if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂,
      if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃,
      if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄,
      if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk 1 : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅,
      if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆,
      if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w8 hfresh₇, OperationPtr.getResultTypes!_WfRewriter_createOp hC₇,
      if_pos rfl]; rfl
  have hRT₈ : op₈.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  -- Properties.
  have hP₂ : op₂.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk mtv.modulus.type.bitwidth) } := by
    rw [WithCreatedOps.getProperties!_eq w3 hfresh₂]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₂ (operation := op₂)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .addi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .cmpi) = { predicate := .uge } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  have hP₆ : op₆.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w7 hfresh₆]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₆ (operation := op₆)
    rw [if_pos rfl] at h2; exact h2
  -- ## Source interpretation
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
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
  -- ## Refinement transfer.
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
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val x) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val y) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  -- ## Width side conditions and the pipeline arithmetic core.
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  have hqm : 2 * mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth := by
    have hnat : (2:Nat)^(mtv.modulus.type.bitwidth - 1) * 2 = 2^(mtv.modulus.type.bitwidth) := by
      rw [← Nat.pow_succ]
      congr 1; omega
    have hcast : (2:Int)^(mtv.modulus.type.bitwidth)
        = ((2^(mtv.modulus.type.bitwidth) : Nat) : Int) := by push_cast; rfl
    have hcast2 : (2:Int)^(mtv.modulus.type.bitwidth - 1)
        = ((2^(mtv.modulus.type.bitwidth - 1) : Nat) : Int) := by push_cast; rfl
    rw [hcast]; rw [hcast2] at hQwidth
    have hnat' : ((2^(mtv.modulus.type.bitwidth - 1):Nat):Int) * 2 = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      exact_mod_cast hnat
    omega
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth := by omega
  -- The pipeline result and its canonicity.
  have hPipeEq : (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
        (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
      then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
        - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
      else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))
      = Data.ModArith.sub mtv.modulus.value x y :=
    Data.ModArith.subSubifge_eq_sub hQpos hqm hxlt hylt
  -- ## Target interpretation.
  -- Step op₀: cast `lhs : iN`.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₀, Array.mapM_eq_mapM_toList]; simp [hTLhs]
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) := by
    rw [hRT₀]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnf₀ hSet₀]; exact hTRhs
  -- Step op₁: cast `rhs : iN`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁, Array.mapM_eq_mapM_toList]; simp [hv₁_rhs]
  have hEval₁ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₁.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₁]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₁.getResultTypes! newCtx.raw) := by
    rw [hRT₁]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  have hv₂_0 : vs₂.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [getVar?_setResultValues?_ne d01 hSet₁]; exact hv₁_0
  have hv₂_1 : vs₂.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  -- Step op₂: const q.
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₂, Array.mapM_eq_mapM_toList]; simp
  have hEval₂ : interpretOp' (.arith .constant) (op₂.getProperties! newCtx.raw (.arith .constant))
      (op₂.getResultTypes! newCtx.raw) #[] (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))], state'.memory, none)) := by
    rw [hRT₂, hP₂]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₂.getResultTypes! newCtx.raw) := by
    rw [hRT₂]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  have hv₃_0 : vs₃.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [getVar?_setResultValues?_ne d02 hSet₂]; exact hv₂_0
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  -- Step op₃: addi (x + q).
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₃, Array.mapM_eq_mapM_toList]; simp [hv₃_0, hv₃_2]
  have hEval₃ : interpretOp' (.arith .addi) (op₃.getProperties! newCtx.raw (.arith .addi))
      (op₃.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))], state'.memory, none)) := by
    rw [hP₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.add, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₃.getResultTypes! newCtx.raw) := by
    rw [hRT₃]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  have hv₄_1 : vs₄.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_ne d13 hSet₃,
      getVar?_setResultValues?_ne d12 hSet₂]; exact hv₂_1
  have hv₄_2 : vs₄.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d23 hSet₃]; exact hv₃_2
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  -- Step op₄: subi ((x+q) - y) = t.
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp [hv₄_3, hv₄_1]
  have hEval₄ : interpretOp' (.arith .subi) (op₄.getProperties! newCtx.raw (.arith .subi))
      (op₄.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))],
          state'.memory, none)) := by
    rw [hP₄]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))]
      (op₄.getResultTypes! newCtx.raw) := by
    rw [hRT₄]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  have hv₅_2 : vs₅.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d24 hSet₄]; exact hv₄_2
  have hv₅_4 : vs₅.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))) := by
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  -- Step op₅: cmpi uge t q → i1.
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₅, Array.mapM_eq_mapM_toList]; simp [hv₅_4, hv₅_2]
  have hEval₅ : interpretOp' (.arith .cmpi) (op₅.getProperties! newCtx.raw (.arith .cmpi))
      (op₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))))],
          state'.memory, none)) := by
    rw [hP₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.icmp, Data.LLVM.Int.cast, Id.run, pure, bind,
      Data.LLVM.IntPred.eval]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))))]
      (op₅.getResultTypes! newCtx.raw) := by
    rw [hRT₅]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  have hv₆_2 : vs₆.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [getVar?_setResultValues?_ne d25 hSet₅]; exact hv₅_2
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]; exact hv₅_4
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))))) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  -- Step op₆: subi (t - q).
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₆, Array.mapM_eq_mapM_toList]; simp [hv₆_4, hv₆_2]
  have hEval₆ : interpretOp' (.arith .subi) (op₆.getProperties! newCtx.raw (.arith .subi))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
            - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))], state'.memory, none)) := by
    rw [hP₆]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
            - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))]
      (op₆.getResultTypes! newCtx.raw) := by
    rw [hRT₆]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  have hv₇_4 : vs₇.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))) := by
    rw [getVar?_setResultValues?_ne d46 hSet₆]; exact hv₆_4
  have hv₇_5 : vs₇.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int 1
          (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))))) := by
    rw [getVar?_setResultValues?_ne d56 hSet₆]; exact hv₆_5
  have hv₇_6 : vs₇.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
            - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value))) := by
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  -- Step op₇: select cond (t-q) t.
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇
      = some #[RuntimeValue.int 1
            (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
              (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₇, Array.mapM_eq_mapM_toList]; simp [hv₇_5, hv₇_6, hv₇_4]
  have hEval₇ : interpretOp' (.arith .select) (op₇.getProperties! newCtx.raw (.arith .select))
      (op₇.getResultTypes! newCtx.raw)
      #[RuntimeValue.int 1
            (.val (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
              (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)),
          RuntimeValue.int mtv.modulus.type.bitwidth
            (.val (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y))]
      (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
            then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
            else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))],
          state'.memory, none)) := by
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.select, Data.LLVM.Int.cast, Id.run, pure,
      bind, apply_ite]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
            then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
            else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))]
      (op₇.getResultTypes! newCtx.raw) := by
    rw [hRT₇]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  have hv₈_7 : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
            then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
            else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))) := by
    rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
  -- Step op₈: cast back to !mod_arith.int.
  have hOpVals₈ : (InterpreterState.mk vs₈ state'.memory).variables.getOperandValues op₈
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
            then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
            else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₈, Array.mapM_eq_mapM_toList]; simp [hv₈_7]
  have hEval₈ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₈.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₈.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (if (BitVec.ofBool ((BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value).ule
            (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)) == 1#1)
            then (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y
              - BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value)
            else (x + BitVec.ofInt mtv.modulus.type.bitwidth mtv.modulus.value - y)))]
      (op₈.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.sub mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₈, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₈ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.sub mtv.modulus.value x y))]
      (op₈.getResultTypes! newCtx.raw) := by
    rw [hRT₈]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this
    refine ⟨rfl, ?_⟩
    simp only [Data.ModArith.isCanonical_val]
    exact Data.ModArith.isCanonical_sub hQpos hQle
  obtain ⟨vs₉, hSet₈, hStep₈⟩ := interpretOp_step (inB := hInB₈) hTy₈ hOpVals₈ hEval₈ hConf₈
  -- ## Assemble.
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
        (.val (Data.ModArith.sub mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₉ : vs₉.getVar? (op₈.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.sub mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₈]; simp [hNumRes₈]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₉]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]

set_option maxHeartbeats 800000 in
theorem lowerMulBarrett_preservesSemantics :
    (lowerBinop .mul mulBarrettRecipe).PreservesSemantics
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
    hVerified.mod_arith_binop hOpType (Or.inr (Or.inr rfl))
  obtain ⟨hQpos, hQwidth⟩ := hValid
  have hmtv : mtv = mt := by have := hResTy; grind [ValuePtr.getType!]
  subst hmtv
  -- Abbreviations.  N := bitwidth, W := 4N, ratio := 2^(2N)/q.
  have hN1 : 1 ≤ mtv.modulus.type.bitwidth := by omega
  -- Unpack the seventeen operations created by the recipe.
  rw [mulBarrettRecipe] at hbuild
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
  obtain ⟨res₁₀, ctx₁₁, op₁₀, _, _, _, _, hres₁₀, hC₁₀, hbuild₁₁⟩ := buildOps_cons_inv hbuild₁₀
  obtain ⟨res₁₁, ctx₁₂, op₁₁, _, _, _, _, hres₁₁, hC₁₁, hbuild₁₂⟩ := buildOps_cons_inv hbuild₁₁
  obtain ⟨res₁₂, ctx₁₃, op₁₂, _, _, _, _, hres₁₂, hC₁₂, hbuild₁₃⟩ := buildOps_cons_inv hbuild₁₂
  obtain ⟨res₁₃, ctx₁₄, op₁₃, _, _, _, _, hres₁₃, hC₁₃, hbuild₁₄⟩ := buildOps_cons_inv hbuild₁₃
  obtain ⟨res₁₄, ctx₁₅, op₁₄, _, _, _, _, hres₁₄, hC₁₄, hbuild₁₅⟩ := buildOps_cons_inv hbuild₁₄
  obtain ⟨res₁₅, ctx₁₆, op₁₅, _, _, _, _, hres₁₅, hC₁₅, hbuild₁₆⟩ := buildOps_cons_inv hbuild₁₅
  obtain ⟨res₁₆, ctx₁₇, op₁₆, _, _, _, _, hres₁₆, hC₁₆, hbuild₁₇⟩ := buildOps_cons_inv hbuild₁₆
  obtain ⟨rfl, rfl⟩ := buildOps_nil_inv hbuild₁₇
  have hresult : op₁₆ = result := by simpa using hback
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
  -- Resolve operand arrays.
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
  have hres₄' : res₄.map (·.val) = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 1) (j := 3) (by simp [binopDescr]) (by simp) (by simp) hres₄
  have hres₆' : res₆.map (·.val) = #[(op₄.getResult 0 : ValuePtr), (op₅.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 4) (j := 5) (by simp [binopDescr]) (by simp) (by simp) hres₆
  have hres₈' : res₈.map (·.val) = #[(op₆.getResult 0 : ValuePtr), (op₇.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 6) (j := 7) (by simp [binopDescr]) (by simp) (by simp) hres₈
  have hres₁₀' : res₁₀.map (·.val) = #[(op₈.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 8) (j := 9) (by simp [binopDescr]) (by simp) (by simp) hres₁₀
  have hres₁₁' : res₁₁.map (·.val) = #[(op₄.getResult 0 : ValuePtr), (op₁₀.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 4) (j := 10) (by simp [binopDescr]) (by simp) (by simp) hres₁₁
  have hres₁₂' : res₁₂.map (·.val) = #[(op₁₁.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 11) (j := 9) (by simp [cmpiUgeDescr]) (by simp) (by simp) hres₁₂
  have hres₁₃' : res₁₃.map (·.val) = #[(op₁₁.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] :=
    resolve_two_created (i := 11) (j := 9) (by simp [binopDescr]) (by simp) (by simp) hres₁₃
  -- the select op (op₁₄) has three created operands.
  have hres₁₄' : res₁₄.map (·.val)
      = #[(op₁₂.getResult 0 : ValuePtr), (op₁₃.getResult 0 : ValuePtr), (op₁₁.getResult 0 : ValuePtr)] := by
    have hd : (selectDescr (.created 12 0) (.created 13 0) (.created 11 0) (4*mtv.modulus.type.bitwidth)).operands
        = #[.created 12 0, .created 13 0, .created 11 0] := by simp [selectDescr]
    rw [hd] at hres₁₄
    have hsize : res₁₄.size = 3 := by
      have := Array.size_eq_of_mapM_eq_some hres₁₄; simpa using this.symm
    have hidx0 := Array.mapM_option_eq_some_implies hres₁₄ 0 (by omega)
    have hidx1 := Array.mapM_option_eq_some_implies hres₁₄ 1 (by omega)
    have hidx2 := Array.mapM_option_eq_some_implies hres₁₄ 2 (by omega)
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hidx0 hidx1 hidx2
    obtain ⟨a0, ha0, hval0⟩ := resolve_created_inv (by simpa using hidx0)
    obtain ⟨a1, ha1, hval1⟩ := resolve_created_inv (by simpa using hidx1)
    obtain ⟨a2, ha2, hval2⟩ := resolve_created_inv (by simpa using hidx2)
    have e0 : op₁₂ = a0 := by simpa using ha0
    have e1 : op₁₃ = a1 := by simpa using ha1
    have e2 : op₁₁ = a2 := by simpa using ha2
    subst e0; subst e1; subst e2
    apply Array.ext
    · simpa using hsize
    · intro k h1 h2
      simp only [Array.size_map, hsize] at h1
      match k, h1 with
      | 0, _ => simpa using hval0
      | 1, _ => simpa using hval1
      | 2, _ => simpa using hval2
  have hres₁₅' : res₁₅.map (·.val) = #[(op₁₄.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 14) (by simp [trunciNuwDescr]) (by simp) hres₁₅
  have hres₁₆' : res₁₆.map (·.val) = #[(op₁₅.getResult 0 : ValuePtr)] :=
    resolve_one_created (i := 15) (by simp [castDescr]) (by simp) hres₁₆
  -- Freshness facts for the 17 created ops.
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
  have hfresh₁₀ := WfRewriter.createOp_new_inBounds _ hC₁₀
  have hnf₁₀ := WfRewriter.createOp_new_not_inBounds _ hC₁₀
  have hfresh₁₁ := WfRewriter.createOp_new_inBounds _ hC₁₁
  have hnf₁₁ := WfRewriter.createOp_new_not_inBounds _ hC₁₁
  have hfresh₁₂ := WfRewriter.createOp_new_inBounds _ hC₁₂
  have hnf₁₂ := WfRewriter.createOp_new_not_inBounds _ hC₁₂
  have hfresh₁₃ := WfRewriter.createOp_new_inBounds _ hC₁₃
  have hnf₁₃ := WfRewriter.createOp_new_not_inBounds _ hC₁₃
  have hfresh₁₄ := WfRewriter.createOp_new_inBounds _ hC₁₄
  have hnf₁₄ := WfRewriter.createOp_new_not_inBounds _ hC₁₄
  have hfresh₁₅ := WfRewriter.createOp_new_inBounds _ hC₁₅
  have hnf₁₅ := WfRewriter.createOp_new_not_inBounds _ hC₁₅
  have hfresh₁₆ := WfRewriter.createOp_new_inBounds _ hC₁₆
  have hnf₁₆ := WfRewriter.createOp_new_not_inBounds _ hC₁₆
  have mono : ∀ {p : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', nO) →
      p.InBounds c.raw → p.InBounds c'.raw := by
    intro p c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ nO hC hin
    exact (WfRewriter.createOp_operation_inBounds_iff hC p).mpr (Or.inl hin)
  -- In-bounds in the final context (push each fresh op forward through all later creations).
  have hInB₀ : op₀.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ (mono hC₁ hfresh₀)))))))))))))))
  have hInB₁ : op₁.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ (mono hC₂ hfresh₁))))))))))))))
  have hInB₂ : op₂.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ (mono hC₃ hfresh₂)))))))))))))
  have hInB₃ : op₃.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ (mono hC₄ hfresh₃))))))))))))
  have hInB₄ : op₄.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ (mono hC₅ hfresh₄)))))))))))
  have hInB₅ : op₅.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ (mono hC₆ hfresh₅))))))))))
  have hInB₆ : op₆.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ (mono hC₇ hfresh₆)))))))))
  have hInB₇ : op₇.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ (mono hC₈ hfresh₇))))))))
  have hInB₈ : op₈.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ (mono hC₉ hfresh₈)))))))
  have hInB₉ : op₉.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ (mono hC₁₀ hfresh₉))))))
  have hInB₁₀ : op₁₀.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ (mono hC₁₁ hfresh₁₀)))))
  have hInB₁₁ : op₁₁.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ (mono hC₁₂ hfresh₁₁))))
  have hInB₁₂ : op₁₂.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ (mono hC₁₃ hfresh₁₂)))
  have hInB₁₃ : op₁₃.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ (mono hC₁₄ hfresh₁₃))
  have hInB₁₄ : op₁₄.InBounds newCtx.raw := mono hC₁₆ (mono hC₁₅ hfresh₁₄)
  have hInB₁₅ : op₁₅.InBounds newCtx.raw := mono hC₁₆ hfresh₁₅
  have hInB₁₆ : op₁₆.InBounds newCtx.raw := hfresh₁₆
  have ne : ∀ {a b : OperationPtr} {c : WfIRContext OpCode},
      a.InBounds c.raw → ¬ b.InBounds c.raw → a ≠ b := by
    intro a b c ha hb heq; subst heq; exact hb ha
  -- `WithCreatedOps` chains.
  have w1 : WfIRContext.WithCreatedOps ctx₁ newCtx := buildOps_withCreatedOps hbuild₁
  have w2 : WfIRContext.WithCreatedOps ctx₂ newCtx := buildOps_withCreatedOps hbuild₂
  have w3 : WfIRContext.WithCreatedOps ctx₃ newCtx := buildOps_withCreatedOps hbuild₃
  have w4 : WfIRContext.WithCreatedOps ctx₄ newCtx := buildOps_withCreatedOps hbuild₄
  have w5 : WfIRContext.WithCreatedOps ctx₅ newCtx := buildOps_withCreatedOps hbuild₅
  have w6 : WfIRContext.WithCreatedOps ctx₆ newCtx := buildOps_withCreatedOps hbuild₆
  have w7 : WfIRContext.WithCreatedOps ctx₇ newCtx := buildOps_withCreatedOps hbuild₇
  have w8 : WfIRContext.WithCreatedOps ctx₈ newCtx := buildOps_withCreatedOps hbuild₈
  have w9 : WfIRContext.WithCreatedOps ctx₉ newCtx := buildOps_withCreatedOps hbuild₉
  have w10 : WfIRContext.WithCreatedOps ctx₁₀ newCtx := buildOps_withCreatedOps hbuild₁₀
  have w11 : WfIRContext.WithCreatedOps ctx₁₁ newCtx := buildOps_withCreatedOps hbuild₁₁
  have w12 : WfIRContext.WithCreatedOps ctx₁₂ newCtx := buildOps_withCreatedOps hbuild₁₂
  have w13 : WfIRContext.WithCreatedOps ctx₁₃ newCtx := buildOps_withCreatedOps hbuild₁₃
  have w14 : WfIRContext.WithCreatedOps ctx₁₄ newCtx := buildOps_withCreatedOps hbuild₁₄
  have w15 : WfIRContext.WithCreatedOps ctx₁₅ newCtx := buildOps_withCreatedOps hbuild₁₅
  have w16 : WfIRContext.WithCreatedOps ctx₁₆ newCtx := buildOps_withCreatedOps hbuild₁₆
  -- Forward in-bounds: `opᵢ` is in bounds of the context where `opⱼ` (j > i) is freshly created,
  -- hence `opᵢ ≠ opⱼ`.  We only build the (few) distinctness facts the lookups need.
  -- `opⱼ` is fresh in `ctx_{j+1}`; pushing `opᵢ` forward to that same context proves the inequality.
  have fib : ∀ {a b : OperationPtr} {c c' : WfIRContext OpCode} {oT rT ops bo rg pr ip h₁ h₂ h₃ h₄},
      WfRewriter.createOp c oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ = some (c', a) →
      b.InBounds c.raw → b ≠ a := by
    intro a b c c' oT rT ops bo rg pr ip h₁ h₂ h₃ h₄ hC hin heq
    subst heq; exact (WfRewriter.createOp_new_not_inBounds _ hC) hin
  -- Forward in-bounds of `op_i` up to each later creation context, then distinctness.
  -- op₀
  have i0_1 : op₀.InBounds ctx₁.raw := hfresh₀
  have i0_2 : op₀.InBounds ctx₂.raw := mono hC₁ i0_1
  have i0_3 : op₀.InBounds ctx₃.raw := mono hC₂ i0_2
  have i0_4 : op₀.InBounds ctx₄.raw := mono hC₃ i0_3
  have i0_5 : op₀.InBounds ctx₅.raw := mono hC₄ i0_4
  -- op₁
  have i1_2 : op₁.InBounds ctx₂.raw := hfresh₁
  have i1_3 : op₁.InBounds ctx₃.raw := mono hC₂ i1_2
  have i1_4 : op₁.InBounds ctx₄.raw := mono hC₃ i1_3
  -- op₂
  have i2_3 : op₂.InBounds ctx₃.raw := hfresh₂
  have i2_4 : op₂.InBounds ctx₄.raw := mono hC₃ i2_3
  -- op₃
  have i3_4 : op₃.InBounds ctx₄.raw := hfresh₃
  -- op₄ forward to ctx₁₁ (for op₁₁ lookups) and ctx₆ etc.
  have i4_5 : op₄.InBounds ctx₅.raw := hfresh₄
  have i4_6 : op₄.InBounds ctx₆.raw := mono hC₅ i4_5
  have i4_7 : op₄.InBounds ctx₇.raw := mono hC₆ i4_6
  have i4_8 : op₄.InBounds ctx₈.raw := mono hC₇ i4_7
  have i4_9 : op₄.InBounds ctx₉.raw := mono hC₈ i4_8
  have i4_10 : op₄.InBounds ctx₁₀.raw := mono hC₉ i4_9
  have i4_11 : op₄.InBounds ctx₁₁.raw := mono hC₁₀ i4_10
  -- op₅
  have i5_6 : op₅.InBounds ctx₆.raw := hfresh₅
  -- op₆
  have i6_7 : op₆.InBounds ctx₇.raw := hfresh₆
  have i6_8 : op₆.InBounds ctx₈.raw := mono hC₇ i6_7
  -- op₇
  have i7_8 : op₇.InBounds ctx₈.raw := hfresh₇
  -- op₈
  have i8_9 : op₈.InBounds ctx₉.raw := hfresh₈
  have i8_10 : op₈.InBounds ctx₁₀.raw := mono hC₉ i8_9
  -- op₉ forward to ctx₁₃ (for op₁₂/op₁₃ lookups)
  have i9_10 : op₉.InBounds ctx₁₀.raw := hfresh₉
  have i9_11 : op₉.InBounds ctx₁₁.raw := mono hC₁₀ i9_10
  have i9_12 : op₉.InBounds ctx₁₂.raw := mono hC₁₁ i9_11
  have i9_13 : op₉.InBounds ctx₁₃.raw := mono hC₁₂ i9_12
  -- op₁₀
  have i10_11 : op₁₀.InBounds ctx₁₁.raw := hfresh₁₀
  -- op₁₁ forward to ctx₁₄ (for op₁₂/op₁₃/op₁₄ lookups)
  have i11_12 : op₁₁.InBounds ctx₁₂.raw := hfresh₁₁
  have i11_13 : op₁₁.InBounds ctx₁₃.raw := mono hC₁₂ i11_12
  have i11_14 : op₁₁.InBounds ctx₁₄.raw := mono hC₁₃ i11_13
  -- op₁₂
  have i12_13 : op₁₂.InBounds ctx₁₃.raw := hfresh₁₂
  have i12_14 : op₁₂.InBounds ctx₁₄.raw := mono hC₁₃ i12_13
  -- op₁₃
  have i13_14 : op₁₃.InBounds ctx₁₄.raw := hfresh₁₃
  -- op₁₄, op₁₅
  have i14_15 : op₁₄.InBounds ctx₁₅.raw := hfresh₁₄
  have i15_16 : op₁₅.InBounds ctx₁₆.raw := hfresh₁₅
  -- Distinctness facts used by the value lookups.
  have d01 : op₀ ≠ op₁ := ne i0_1 hnf₁
  have d23 : op₂ ≠ op₃ := ne i2_3 hnf₃
  have d02 : op₀ ≠ op₂ := ne i0_2 hnf₂
  have d12 : op₁ ≠ op₂ := ne i1_2 hnf₂
  have d13 : op₁ ≠ op₃ := ne i1_3 hnf₃
  have d45 : op₄ ≠ op₅ := ne i4_5 hnf₅
  have d46 : op₄ ≠ op₆ := ne i4_6 hnf₆
  have d56 : op₅ ≠ op₆ := ne i5_6 hnf₆
  have d67 : op₆ ≠ op₇ := ne i6_7 hnf₇
  have d68 : op₆ ≠ op₈ := ne i6_8 hnf₈
  have d78 : op₇ ≠ op₈ := ne i7_8 hnf₈
  have d89 : op₈ ≠ op₉ := ne i8_9 hnf₉
  have d8_10 : op₈ ≠ op₁₀ := ne i8_10 hnf₁₀
  have d9_10 : op₉ ≠ op₁₀ := ne i9_10 hnf₁₀
  have d4_10 : op₄ ≠ op₁₀ := ne i4_10 hnf₁₀
  have d4_11 : op₄ ≠ op₁₁ := ne i4_11 hnf₁₁
  have d10_11 : op₁₀ ≠ op₁₁ := ne i10_11 hnf₁₁
  have d9_11 : op₉ ≠ op₁₁ := ne i9_11 hnf₁₁
  have d9_12 : op₉ ≠ op₁₂ := ne i9_12 hnf₁₂
  have d11_12 : op₁₁ ≠ op₁₂ := ne i11_12 hnf₁₂
  have d9_13 : op₉ ≠ op₁₃ := ne i9_13 hnf₁₃
  have d11_13 : op₁₁ ≠ op₁₃ := ne i11_13 hnf₁₃
  have d12_13 : op₁₂ ≠ op₁₃ := ne i12_13 hnf₁₃
  have d11_14 : op₁₁ ≠ op₁₄ := ne i11_14 hnf₁₄
  have d12_14 : op₁₂ ≠ op₁₄ := ne i12_14 hnf₁₄
  have d13_14 : op₁₃ ≠ op₁₄ := ne i13_14 hnf₁₄
  have d14_15 : op₁₄ ≠ op₁₅ := ne i14_15 hnf₁₅
  have d15_16 : op₁₅ ≠ op₁₆ := ne i15_16 hnf₁₆
  -- ## Operation shapes in the final context.
  have hTy₀ : op₀.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w1 hfresh₀, OperationPtr.getOpType!_WfRewriter_createOp hC₀, if_pos rfl]; rfl
  have hTy₁ : op₁.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w2 hfresh₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁, if_pos rfl]; rfl
  have hTy₂ : op₂.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [WithCreatedOps.getOpType!_eq w3 hfresh₂, OperationPtr.getOpType!_WfRewriter_createOp hC₂, if_pos rfl]; rfl
  have hTy₃ : op₃.getOpType! newCtx.raw = .arith .extui := by
    rw [WithCreatedOps.getOpType!_eq w4 hfresh₃, OperationPtr.getOpType!_WfRewriter_createOp hC₃, if_pos rfl]; rfl
  have hTy₄ : op₄.getOpType! newCtx.raw = .arith .muli := by
    rw [WithCreatedOps.getOpType!_eq w5 hfresh₄, OperationPtr.getOpType!_WfRewriter_createOp hC₄, if_pos rfl]; rfl
  have hTy₅ : op₅.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w6 hfresh₅, OperationPtr.getOpType!_WfRewriter_createOp hC₅, if_pos rfl]; rfl
  have hTy₆ : op₆.getOpType! newCtx.raw = .arith .muli := by
    rw [WithCreatedOps.getOpType!_eq w7 hfresh₆, OperationPtr.getOpType!_WfRewriter_createOp hC₆, if_pos rfl]; rfl
  have hTy₇ : op₇.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w8 hfresh₇, OperationPtr.getOpType!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  have hTy₈ : op₈.getOpType! newCtx.raw = .arith .shrui := by
    rw [WithCreatedOps.getOpType!_eq w9 hfresh₈, OperationPtr.getOpType!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  have hTy₉ : op₉.getOpType! newCtx.raw = .arith .constant := by
    rw [WithCreatedOps.getOpType!_eq w10 hfresh₉, OperationPtr.getOpType!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hTy₁₀ : op₁₀.getOpType! newCtx.raw = .arith .muli := by
    rw [WithCreatedOps.getOpType!_eq w11 hfresh₁₀, OperationPtr.getOpType!_WfRewriter_createOp hC₁₀, if_pos rfl]; rfl
  have hTy₁₁ : op₁₁.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w12 hfresh₁₁, OperationPtr.getOpType!_WfRewriter_createOp hC₁₁, if_pos rfl]; rfl
  have hTy₁₂ : op₁₂.getOpType! newCtx.raw = .arith .cmpi := by
    rw [WithCreatedOps.getOpType!_eq w13 hfresh₁₂, OperationPtr.getOpType!_WfRewriter_createOp hC₁₂, if_pos rfl]; rfl
  have hTy₁₃ : op₁₃.getOpType! newCtx.raw = .arith .subi := by
    rw [WithCreatedOps.getOpType!_eq w14 hfresh₁₃, OperationPtr.getOpType!_WfRewriter_createOp hC₁₃, if_pos rfl]; rfl
  have hTy₁₄ : op₁₄.getOpType! newCtx.raw = .arith .select := by
    rw [WithCreatedOps.getOpType!_eq w15 hfresh₁₄, OperationPtr.getOpType!_WfRewriter_createOp hC₁₄, if_pos rfl]; rfl
  have hTy₁₅ : op₁₅.getOpType! newCtx.raw = .arith .trunci := by
    rw [WithCreatedOps.getOpType!_eq w16 hfresh₁₅, OperationPtr.getOpType!_WfRewriter_createOp hC₁₅, if_pos rfl]; rfl
  have hTy₁₆ : op₁₆.getOpType! newCtx.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hC₁₆, if_pos rfl]; rfl
  -- Operands.
  have hOperands₀ : op₀.getOperands! newCtx.raw = #[operands[0]!] := by
    rw [WithCreatedOps.getOperands!_eq w1 hfresh₀, OperationPtr.getOperands!_WfRewriter_createOp hC₀, if_pos rfl, hres₀']
  have hOperands₁ : op₁.getOperands! newCtx.raw = #[(op₀.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w2 hfresh₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁, if_pos rfl, hres₁']
  have hOperands₂ : op₂.getOperands! newCtx.raw = #[operands[1]!] := by
    rw [WithCreatedOps.getOperands!_eq w3 hfresh₂, OperationPtr.getOperands!_WfRewriter_createOp hC₂, if_pos rfl, hres₂']
  have hOperands₃ : op₃.getOperands! newCtx.raw = #[(op₂.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w4 hfresh₃, OperationPtr.getOperands!_WfRewriter_createOp hC₃, if_pos rfl, hres₃']
  have hOperands₄ : op₄.getOperands! newCtx.raw
      = #[(op₁.getResult 0 : ValuePtr), (op₃.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w5 hfresh₄, OperationPtr.getOperands!_WfRewriter_createOp hC₄, if_pos rfl, hres₄']
  have hres₅' : res₅.map (·.val) = #[] := by
    have hsz : res₅.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₅; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₅ : op₅.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w6 hfresh₅, OperationPtr.getOperands!_WfRewriter_createOp hC₅, if_pos rfl, hres₅']
  have hOperands₆ : op₆.getOperands! newCtx.raw
      = #[(op₄.getResult 0 : ValuePtr), (op₅.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w7 hfresh₆, OperationPtr.getOperands!_WfRewriter_createOp hC₆, if_pos rfl, hres₆']
  have hres₇' : res₇.map (·.val) = #[] := by
    have hsz : res₇.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₇; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₇ : op₇.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w8 hfresh₇, OperationPtr.getOperands!_WfRewriter_createOp hC₇, if_pos rfl, hres₇']
  have hOperands₈ : op₈.getOperands! newCtx.raw
      = #[(op₆.getResult 0 : ValuePtr), (op₇.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w9 hfresh₈, OperationPtr.getOperands!_WfRewriter_createOp hC₈, if_pos rfl, hres₈']
  have hres₉' : res₉.map (·.val) = #[] := by
    have hsz : res₉.size = 0 := by
      have := Array.size_eq_of_mapM_eq_some hres₉; simpa [constantDescr] using this.symm
    apply Array.ext
    · simp only [Array.size_map]; simpa using hsz
    · intro i h1 h2; simp only [Array.size_map, hsz] at h1; omega
  have hOperands₉ : op₉.getOperands! newCtx.raw = #[] := by
    rw [WithCreatedOps.getOperands!_eq w10 hfresh₉, OperationPtr.getOperands!_WfRewriter_createOp hC₉, if_pos rfl, hres₉']
  have hOperands₁₀ : op₁₀.getOperands! newCtx.raw
      = #[(op₈.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w11 hfresh₁₀, OperationPtr.getOperands!_WfRewriter_createOp hC₁₀, if_pos rfl, hres₁₀']
  have hOperands₁₁ : op₁₁.getOperands! newCtx.raw
      = #[(op₄.getResult 0 : ValuePtr), (op₁₀.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w12 hfresh₁₁, OperationPtr.getOperands!_WfRewriter_createOp hC₁₁, if_pos rfl, hres₁₁']
  have hOperands₁₂ : op₁₂.getOperands! newCtx.raw
      = #[(op₁₁.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w13 hfresh₁₂, OperationPtr.getOperands!_WfRewriter_createOp hC₁₂, if_pos rfl, hres₁₂']
  have hOperands₁₃ : op₁₃.getOperands! newCtx.raw
      = #[(op₁₁.getResult 0 : ValuePtr), (op₉.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w14 hfresh₁₃, OperationPtr.getOperands!_WfRewriter_createOp hC₁₃, if_pos rfl, hres₁₃']
  have hOperands₁₄ : op₁₄.getOperands! newCtx.raw
      = #[(op₁₂.getResult 0 : ValuePtr), (op₁₃.getResult 0 : ValuePtr), (op₁₁.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w15 hfresh₁₄, OperationPtr.getOperands!_WfRewriter_createOp hC₁₄, if_pos rfl, hres₁₄']
  have hOperands₁₅ : op₁₅.getOperands! newCtx.raw = #[(op₁₄.getResult 0 : ValuePtr)] := by
    rw [WithCreatedOps.getOperands!_eq w16 hfresh₁₅, OperationPtr.getOperands!_WfRewriter_createOp hC₁₅, if_pos rfl, hres₁₅']
  have hOperands₁₆ : op₁₆.getOperands! newCtx.raw = #[(op₁₅.getResult 0 : ValuePtr)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hC₁₆, if_pos rfl, hres₁₆']
  -- Number of results (all one).
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
    rw [WithCreatedOps.getNumResults!_eq w10 hfresh₉, OperationPtr.getNumResults!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hNumRes₁₀ : op₁₀.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w11 hfresh₁₀, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₀, if_pos rfl]; rfl
  have hNumRes₁₁ : op₁₁.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w12 hfresh₁₁, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₁, if_pos rfl]; rfl
  have hNumRes₁₂ : op₁₂.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w13 hfresh₁₂, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₂, if_pos rfl]; rfl
  have hNumRes₁₃ : op₁₃.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w14 hfresh₁₃, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₃, if_pos rfl]; rfl
  have hNumRes₁₄ : op₁₄.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w15 hfresh₁₄, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₄, if_pos rfl]; rfl
  have hNumRes₁₅ : op₁₅.getNumResults! newCtx.raw = 1 := by
    rw [WithCreatedOps.getNumResults!_eq w16 hfresh₁₅, OperationPtr.getNumResults!_WfRewriter_createOp hC₁₅, if_pos rfl]; rfl
  have hNumRes₁₆ : op₁₆.getNumResults! newCtx.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hC₁₆, if_pos rfl]; rfl
  -- Result types.  W := 4N.
  have hRT₀ : op₀.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w1 hfresh₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₀, if_pos rfl]; rfl
  have hRT₁ : op₁.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w2 hfresh₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁, if_pos rfl]; rfl
  have hRT₂ : op₂.getResultTypes! newCtx.raw = #[(mtv.modulus.type : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w3 hfresh₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₂, if_pos rfl]; rfl
  have hRT₃ : op₃.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w4 hfresh₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₃, if_pos rfl]; rfl
  have hRT₄ : op₄.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w5 hfresh₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₄, if_pos rfl]; rfl
  have hRT₅ : op₅.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w6 hfresh₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₅, if_pos rfl]; rfl
  have hRT₆ : op₆.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w7 hfresh₆, OperationPtr.getResultTypes!_WfRewriter_createOp hC₆, if_pos rfl]; rfl
  have hRT₇ : op₇.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w8 hfresh₇, OperationPtr.getResultTypes!_WfRewriter_createOp hC₇, if_pos rfl]; rfl
  have hRT₈ : op₈.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w9 hfresh₈, OperationPtr.getResultTypes!_WfRewriter_createOp hC₈, if_pos rfl]; rfl
  have hRT₉ : op₉.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w10 hfresh₉, OperationPtr.getResultTypes!_WfRewriter_createOp hC₉, if_pos rfl]; rfl
  have hRT₁₀ : op₁₀.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w11 hfresh₁₀, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₀, if_pos rfl]; rfl
  have hRT₁₁ : op₁₁.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w12 hfresh₁₁, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₁, if_pos rfl]; rfl
  have hRT₁₂ : op₁₂.getResultTypes! newCtx.raw = #[(IntegerType.mk 1 : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w13 hfresh₁₂, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₂, if_pos rfl]; rfl
  have hRT₁₃ : op₁₃.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w14 hfresh₁₃, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₃, if_pos rfl]; rfl
  have hRT₁₄ : op₁₄.getResultTypes! newCtx.raw = #[(IntegerType.mk (4*mtv.modulus.type.bitwidth) : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w15 hfresh₁₄, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₄, if_pos rfl]; rfl
  have hRT₁₅ : op₁₅.getResultTypes! newCtx.raw = #[(IntegerType.mk mtv.modulus.type.bitwidth : TypeAttr)] := by
    rw [WithCreatedOps.getResultTypes!_eq w16 hfresh₁₅, OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₅, if_pos rfl]; rfl
  have hRT₁₆ : op₁₆.getResultTypes! newCtx.raw = #[⟨.modArithType mtv, by rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hC₁₆, if_pos rfl]; rfl
  -- Properties.
  have hP₁ : op₁.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w2 hfresh₁]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁ (operation := op₁)
    rw [if_pos rfl] at h2; exact h2
  have hP₃ : op₃.getProperties! newCtx.raw (.arith .extui) = { nneg := false } := by
    rw [WithCreatedOps.getProperties!_eq w4 hfresh₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₃ (operation := op₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₄ : op₄.getProperties! newCtx.raw (.arith .muli) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w5 hfresh₄]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₄ (operation := op₄)
    rw [if_pos rfl] at h2; exact h2
  have hP₅ : op₅.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk ((2:Int)^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value)
            (IntegerType.mk (4*mtv.modulus.type.bitwidth)) } := by
    rw [WithCreatedOps.getProperties!_eq w6 hfresh₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₅ (operation := op₅)
    rw [if_pos rfl] at h2; exact h2
  have hP₆ : op₆.getProperties! newCtx.raw (.arith .muli) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w7 hfresh₆]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₆ (operation := op₆)
    rw [if_pos rfl] at h2; exact h2
  have hP₇ : op₇.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk (2*mtv.modulus.type.bitwidth : Int)
            (IntegerType.mk (4*mtv.modulus.type.bitwidth)) } := by
    rw [WithCreatedOps.getProperties!_eq w8 hfresh₇]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₇ (operation := op₇)
    rw [if_pos rfl] at h2; exact h2
  have hP₈ : op₈.getProperties! newCtx.raw (.arith .shrui) = { exact := false } := by
    rw [WithCreatedOps.getProperties!_eq w9 hfresh₈]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₈ (operation := op₈)
    rw [if_pos rfl] at h2; exact h2
  have hP₉ : op₉.getProperties! newCtx.raw (.arith .constant)
      = { value := IntegerAttr.mk mtv.modulus.value (IntegerType.mk (4*mtv.modulus.type.bitwidth)) } := by
    rw [WithCreatedOps.getProperties!_eq w10 hfresh₉]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₉ (operation := op₉)
    rw [if_pos rfl] at h2; exact h2
  have hP₁₀ : op₁₀.getProperties! newCtx.raw (.arith .muli) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w11 hfresh₁₀]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁₀ (operation := op₁₀)
    rw [if_pos rfl] at h2; exact h2
  have hP₁₁ : op₁₁.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w12 hfresh₁₁]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁₁ (operation := op₁₁)
    rw [if_pos rfl] at h2; exact h2
  have hP₁₂ : op₁₂.getProperties! newCtx.raw (.arith .cmpi) = { predicate := .uge } := by
    rw [WithCreatedOps.getProperties!_eq w13 hfresh₁₂]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁₂ (operation := op₁₂)
    rw [if_pos rfl] at h2; exact h2
  have hP₁₃ : op₁₃.getProperties! newCtx.raw (.arith .subi) = { nsw := false, nuw := false } := by
    rw [WithCreatedOps.getProperties!_eq w14 hfresh₁₃]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁₃ (operation := op₁₃)
    rw [if_pos rfl] at h2; exact h2
  have hP₁₅ : op₁₅.getProperties! newCtx.raw (.arith .trunci) = { nsw := false, nuw := true } := by
    rw [WithCreatedOps.getProperties!_eq w16 hfresh₁₅]
    have h2 := OperationPtr.getProperties!_WfRewriter_createOp hC₁₅ (operation := op₁₅)
    rw [if_pos rfl] at h2; exact h2
  -- ## Source interpretation
  have hLhsTy : operands[0]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp0Ty
  have hRhsTy : operands[1]!.getType! ctx.raw = ⟨.modArithType mtv, by rfl⟩ := by
    rw [hOperands, OperationPtr.getOperands!.getElem!_eq_getOperand!]; exact hOp1Ty
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
    have helem : (op.getResultTypes! ctx.raw)[0]'(by omega) = ⟨.modArithType mtv, by rfl⟩ := by
      apply Subtype.ext
      rw [OperationPtr.getResultTypes!.getElem_eq, hResTy]
    rw [h0, helem]
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
  -- ## Refinement transfer.
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
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val x) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  have hTRhs : state'.variables.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    obtain ⟨tv, htv, href⟩ := hVarRef operands[1]! hrhsIn _ hy
    rw [hMapRhs] at htv
    have htv' : tv = .int mtv.modulus.type.bitwidth (.val y) := by
      cases tv with
      | int bw t =>
        simp only [RuntimeValue.isRefinedBy] at href
        obtain ⟨hbweq, href⟩ := href
        subst hbweq
        cases t with
        | poison => simp [Data.LLVM.Int.cast, isRefinedBy] at href
        | val tval => simp [Data.LLVM.Int.cast, isRefinedBy] at href; rw [href]
      | _ => simp [RuntimeValue.isRefinedBy] at href
    rw [htv, htv']
  -- ## The Barrett pipeline arithmetic core and canonicity.
  have hPipeEq := Data.ModArith.mulBarrettPipeline_eq_mul (n := mtv.modulus.type.bitwidth)
    (q := mtv.modulus.value) hQpos hQwidth hN1 hxlt hylt
  have hQle : mtv.modulus.value ≤ 2 ^ mtv.modulus.type.bitwidth := by
    have hle : (2:Nat)^(mtv.modulus.type.bitwidth-1) ≤ 2^mtv.modulus.type.bitwidth :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hcast : (2:Int)^mtv.modulus.type.bitwidth = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    have hcast2 : (2:Int)^(mtv.modulus.type.bitwidth-1)
        = ((2^(mtv.modulus.type.bitwidth-1):Nat):Int) := by push_cast; rfl
    rw [hcast2] at hQwidth; rw [hcast]
    have : ((2^(mtv.modulus.type.bitwidth-1):Nat):Int) ≤ ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      exact_mod_cast hle
    omega
  -- Canonicity of the final pre-truncation value `u` (the conditional subtraction result),
  -- needed for the `trunci nuw` no-poison condition and the final cast's conformance.
  have hUcanon : (((if (BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value).ule
        (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      then (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value
          - BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      else (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)).truncate
        mtv.modulus.type.bitwidth).toNat : Int) < mtv.modulus.value := by
    rw [hPipeEq]
    simp only [Data.ModArith.isCanonical_val]
    exact Data.ModArith.isCanonical_mul hQpos hQle
  -- The no-poison side condition for the final `trunci nuw`: the (canonical) value fits in `N` bits.
  have hNoPoison : (((if (BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value).ule
        (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      then (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value
          - BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      else (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)).truncate
        mtv.modulus.type.bitwidth).zeroExtend (4*mtv.modulus.type.bitwidth))
      = (if (BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value).ule
        (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      then (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value
          - BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)
      else (x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
          - ((x.zeroExtend (4*mtv.modulus.type.bitwidth) * y.zeroExtend (4*mtv.modulus.type.bitwidth)
              * BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value))
              >>> BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int))
            * BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value)) := by
    apply Data.ModArith.zeroExtend_truncate_eq_self
    have hcast : (2:Int)^mtv.modulus.type.bitwidth = ((2^mtv.modulus.type.bitwidth:Nat):Int) := by
      push_cast; rfl
    rw [hcast] at hQle
    omega
  -- Shift amount `2N < 4N = W`, needed for `shrui` to be non-poison (concrete).
  have hShiftLt : ¬ ((BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int)).toNat
      ≥ 4*mtv.modulus.type.bitwidth) := by
    have hP : ∀ m : Nat, (2:Int)^m = ((2^m:Nat):Int) := fun m => by push_cast; rfl
    have h1 : (2:Nat) * mtv.modulus.type.bitwidth < 2 ^ (2 * mtv.modulus.type.bitwidth) :=
      Nat.lt_two_pow_self
    have h2 : (2:Nat)^(2*mtv.modulus.type.bitwidth) ≤ 2^(4*mtv.modulus.type.bitwidth) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hlt : (2*(mtv.modulus.type.bitwidth:Int)) < 2 ^ (4*mtv.modulus.type.bitwidth) := by
      have hh : ((2*mtv.modulus.type.bitwidth:Nat):Int) < ((2^(4*mtv.modulus.type.bitwidth):Nat):Int) := by
        exact_mod_cast (by omega : 2*mtv.modulus.type.bitwidth < 2^(4*mtv.modulus.type.bitwidth))
      push_cast at hh; exact_mod_cast hh
    have hkey := Data.ModArith.toNat_ofInt_modulus (m := 4*mtv.modulus.type.bitwidth)
      (q := (2*(mtv.modulus.type.bitwidth:Int))) (by omega) hlt
    rw [hkey]; omega
  -- ## Target interpretation: 17 steps.  To keep terms small, each freshly produced bitvector
  -- value is `generalize`d to an atom right after its step (also in the arithmetic facts).
  -- Step op₀: cast lhs : iN.
  have hOpVals₀ : state'.variables.getOperandValues op₀
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₀, Array.mapM_eq_mapM_toList]; simp [hTLhs]
  have hEval₀ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₀.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)], state'.memory, none)) := by
    rw [hRT₀]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] (op₀.getResultTypes! newCtx.raw) := by
    rw [hRT₀]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁, hSet₀, hStep₀⟩ := interpretOp_step (inB := hInB₀) hTy₀ hOpVals₀ hEval₀ hConf₀
  have hv₁_0 : vs₁.getVar? (op₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val x)) := by
    rw [VariableState.getVar?_setResultValues? hSet₀]; simp [hNumRes₀]
  have hv₁_rhs : vs₁.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnf₀ hSet₀]; exact hTRhs
  -- Step op₁: extui x → iW, then abstract `xe := x.zeroExtend W`.
  have hOpVals₁ : (InterpreterState.mk vs₁ state'.memory).variables.getOperandValues op₁
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁, Array.mapM_eq_mapM_toList]; simp [hv₁_0]
  have hEval₁ : interpretOp' (.arith .extui) (op₁.getProperties! newCtx.raw (.arith .extui))
      (op₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val x)]
      (op₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (x.zeroExtend (4*mtv.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT₁, hP₁]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (4*mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (x.zeroExtend (4*mtv.modulus.type.bitwidth)))]
      (op₁.getResultTypes! newCtx.raw) := by
    rw [hRT₁]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₂, hSet₁, hStep₁⟩ := interpretOp_step (inB := hInB₁) hTy₁ hOpVals₁ hEval₁ hConf₁
  generalize hxe : x.zeroExtend (4*mtv.modulus.type.bitwidth) = xe at hStep₁ hSet₁ hPipeEq hUcanon hNoPoison
  -- Step op₂: cast rhs : iN.
  have hv₂_rhs : vs₂.getVar? operands[1]! = some (.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [getVar?_setResultValues?_outer hrhsIn hnfc₁ hSet₁]; exact hv₁_rhs
  have hOpVals₂ : (InterpreterState.mk vs₂ state'.memory).variables.getOperandValues op₂
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₂, Array.mapM_eq_mapM_toList]; simp [hv₂_rhs]
  have hEval₂ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₂.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₂.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)], state'.memory, none)) := by
    rw [hRT₂]; simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] (op₂.getResultTypes! newCtx.raw) := by
    rw [hRT₂]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₃, hSet₂, hStep₂⟩ := interpretOp_step (inB := hInB₂) hTy₂ hOpVals₂ hEval₂ hConf₂
  have hv₃_2 : vs₃.getVar? (op₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val y)) := by
    rw [VariableState.getVar?_setResultValues? hSet₂]; simp [hNumRes₂]
  -- Step op₃: extui y → iW, then abstract `ye := y.zeroExtend W`.
  have hOpVals₃ : (InterpreterState.mk vs₃ state'.memory).variables.getOperandValues op₃
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₃, Array.mapM_eq_mapM_toList]; simp [hv₃_2]
  have hEval₃ : interpretOp' (.arith .extui) (op₃.getProperties! newCtx.raw (.arith .extui))
      (op₃.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val y)]
      (op₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (y.zeroExtend (4*mtv.modulus.type.bitwidth)))], state'.memory, none)) := by
    rw [hRT₃, hP₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.zext, Id.run, pure, bind,
      dif_neg (show ¬ (4*mtv.modulus.type.bitwidth ≤ mtv.modulus.type.bitwidth) from by omega)]
  have hConf₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (y.zeroExtend (4*mtv.modulus.type.bitwidth)))]
      (op₃.getResultTypes! newCtx.raw) := by
    rw [hRT₃]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₄, hSet₃, hStep₃⟩ := interpretOp_step (inB := hInB₃) hTy₃ hOpVals₃ hEval₃ hConf₃
  generalize hye : y.zeroExtend (4*mtv.modulus.type.bitwidth) = ye at hStep₃ hSet₃ hPipeEq hUcanon hNoPoison
  -- Step op₄: muli (p = xe * ye), then abstract `p`.
  have hv₄_1 : vs₄.getVar? (op₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val xe)) := by
    rw [getVar?_setResultValues?_ne d13 hSet₃, getVar?_setResultValues?_ne d12 hSet₂]
    rw [VariableState.getVar?_setResultValues? hSet₁]; simp [hNumRes₁]
  have hv₄_3 : vs₄.getVar? (op₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val ye)) := by
    rw [VariableState.getVar?_setResultValues? hSet₃]; simp [hNumRes₃]
  have hOpVals₄ : (InterpreterState.mk vs₄ state'.memory).variables.getOperandValues op₄
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val xe),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val ye)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₄, Array.mapM_eq_mapM_toList]; simp [hv₄_1, hv₄_3]
  have hEval₄ : interpretOp' (.arith .muli) (op₄.getProperties! newCtx.raw (.arith .muli))
      (op₄.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val xe),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val ye)]
      (op₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (xe * ye))],
          state'.memory, none)) := by
    rw [hP₄]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.mul, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (xe * ye))]
      (op₄.getResultTypes! newCtx.raw) := by
    rw [hRT₄]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₅, hSet₄, hStep₄⟩ := interpretOp_step (inB := hInB₄) hTy₄ hOpVals₄ hEval₄ hConf₄
  generalize hp : xe * ye = p at hStep₄ hSet₄ hPipeEq hUcanon hNoPoison
  -- Step op₅: const ratio : iW, then abstract `rBV`.
  have hOpVals₅ : (InterpreterState.mk vs₅ state'.memory).variables.getOperandValues op₅ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₅, Array.mapM_eq_mapM_toList]; simp
  have hEval₅ : interpretOp' (.arith .constant) (op₅.getProperties! newCtx.raw (.arith .constant))
      (op₅.getResultTypes! newCtx.raw) #[] (op₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth)
            ((2:Int)^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value)))], state'.memory, none)) := by
    rw [hRT₅, hP₅]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth)
            ((2:Int)^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value)))]
      (op₅.getResultTypes! newCtx.raw) := by
    rw [hRT₅]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₆, hSet₅, hStep₅⟩ := interpretOp_step (inB := hInB₅) hTy₅ hOpVals₅ hEval₅ hConf₅
  generalize hrBV : BitVec.ofInt (4*mtv.modulus.type.bitwidth)
      ((2:Int)^(2*mtv.modulus.type.bitwidth)/mtv.modulus.value) = rBV at hStep₅ hSet₅ hPipeEq hUcanon hNoPoison
  -- Step op₆: muli (pr = p * rBV), then abstract `pr`.
  have hv₆_4 : vs₆.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p)) := by
    rw [getVar?_setResultValues?_ne d45 hSet₅]
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  have hv₆_5 : vs₆.getVar? (op₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val rBV)) := by
    rw [VariableState.getVar?_setResultValues? hSet₅]; simp [hNumRes₅]
  have hOpVals₆ : (InterpreterState.mk vs₆ state'.memory).variables.getOperandValues op₆
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val rBV)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₆, Array.mapM_eq_mapM_toList]; simp [hv₆_4, hv₆_5]
  have hEval₆ : interpretOp' (.arith .muli) (op₆.getProperties! newCtx.raw (.arith .muli))
      (op₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val rBV)]
      (op₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (p * rBV))],
          state'.memory, none)) := by
    rw [hP₆]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.mul, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (p * rBV))]
      (op₆.getResultTypes! newCtx.raw) := by
    rw [hRT₆]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₇, hSet₆, hStep₆⟩ := interpretOp_step (inB := hInB₆) hTy₆ hOpVals₆ hEval₆ hConf₆
  generalize hpr : p * rBV = pr at hStep₆ hSet₆ hPipeEq hUcanon hNoPoison
  -- Step op₇: const 2N : iW, then abstract `shBV`.
  have hOpVals₇ : (InterpreterState.mk vs₇ state'.memory).variables.getOperandValues op₇ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₇, Array.mapM_eq_mapM_toList]; simp
  have hEval₇ : interpretOp' (.arith .constant) (op₇.getProperties! newCtx.raw (.arith .constant))
      (op₇.getResultTypes! newCtx.raw) #[] (op₇.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int)))],
          state'.memory, none)) := by
    rw [hRT₇, hP₇]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₇ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int)))]
      (op₇.getResultTypes! newCtx.raw) := by
    rw [hRT₇]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₈, hSet₇, hStep₇⟩ := interpretOp_step (inB := hInB₇) hTy₇ hOpVals₇ hEval₇ hConf₇
  generalize hshBV : BitVec.ofInt (4*mtv.modulus.type.bitwidth) (2*mtv.modulus.type.bitwidth : Int)
      = shBV at hStep₇ hSet₇ hPipeEq hUcanon hNoPoison hShiftLt
  -- Step op₈: shrui (s = pr >>> shBV), then abstract `s`.
  have hv₈_6 : vs₈.getVar? (op₆.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val pr)) := by
    rw [getVar?_setResultValues?_ne d67 hSet₇]
    rw [VariableState.getVar?_setResultValues? hSet₆]; simp [hNumRes₆]
  have hv₈_7 : vs₈.getVar? (op₇.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val shBV)) := by
    rw [VariableState.getVar?_setResultValues? hSet₇]; simp [hNumRes₇]
  have hOpVals₈ : (InterpreterState.mk vs₈ state'.memory).variables.getOperandValues op₈
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val pr),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val shBV)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₈, Array.mapM_eq_mapM_toList]; simp [hv₈_6, hv₈_7]
  have hEval₈ : interpretOp' (.arith .shrui) (op₈.getProperties! newCtx.raw (.arith .shrui))
      (op₈.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val pr),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val shBV)]
      (op₈.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (pr >>> shBV))],
          state'.memory, none)) := by
    rw [hP₈]
    simp only [interpretOp', Arith.interpretOp', List.toArray_cons, List.toArray_nil,
      List.cons.injEq, ne_eq, reduceCtorEq, not_false_eq_true, and_self, ↓reduceDIte,
      BitVec.cast_eq, Data.LLVM.Int.lshr, Id.run, pure, bind]
    rw [if_neg hShiftLt]
  have hConf₈ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (pr >>> shBV))]
      (op₈.getResultTypes! newCtx.raw) := by
    rw [hRT₈]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₉, hSet₈, hStep₈⟩ := interpretOp_step (inB := hInB₈) hTy₈ hOpVals₈ hEval₈ hConf₈
  generalize hs : pr >>> shBV = s at hStep₈ hSet₈ hPipeEq hUcanon hNoPoison
  -- Step op₉: const q : iW, then abstract `qBV`.
  have hOpVals₉ : (InterpreterState.mk vs₉ state'.memory).variables.getOperandValues op₉ = some #[] := by
    unfold VariableState.getOperandValues
    rw [hOperands₉, Array.mapM_eq_mapM_toList]; simp
  have hEval₉ : interpretOp' (.arith .constant) (op₉.getProperties! newCtx.raw (.arith .constant))
      (op₉.getResultTypes! newCtx.raw) #[] (op₉.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value))], state'.memory, none)) := by
    rw [hRT₉, hP₉]; simp [interpretOp', Arith.interpretOp', pure, bind]
  have hConf₉ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value))]
      (op₉.getResultTypes! newCtx.raw) := by
    rw [hRT₉]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₀, hSet₉, hStep₉⟩ := interpretOp_step (inB := hInB₉) hTy₉ hOpVals₉ hEval₉ hConf₉
  generalize hqBV : BitVec.ofInt (4*mtv.modulus.type.bitwidth) mtv.modulus.value
      = qBV at hStep₉ hSet₉ hPipeEq hUcanon hNoPoison
  -- Step op₁₀: muli (sq = s * qBV), then abstract `sq`.
  have hv₁₀_8 : vs₁₀.getVar? (op₈.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val s)) := by
    rw [getVar?_setResultValues?_ne d89 hSet₉]
    rw [VariableState.getVar?_setResultValues? hSet₈]; simp [hNumRes₈]
  have hv₁₀_9 : vs₁₀.getVar? (op₉.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)) := by
    rw [VariableState.getVar?_setResultValues? hSet₉]; simp [hNumRes₉]
  have hOpVals₁₀ : (InterpreterState.mk vs₁₀ state'.memory).variables.getOperandValues op₁₀
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val s),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₀, Array.mapM_eq_mapM_toList]; simp [hv₁₀_8, hv₁₀_9]
  have hEval₁₀ : interpretOp' (.arith .muli) (op₁₀.getProperties! newCtx.raw (.arith .muli))
      (op₁₀.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val s),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)]
      (op₁₀.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (s * qBV))],
          state'.memory, none)) := by
    rw [hP₁₀]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.mul, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₁₀ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (s * qBV))]
      (op₁₀.getResultTypes! newCtx.raw) := by
    rw [hRT₁₀]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₁, hSet₁₀, hStep₁₀⟩ := interpretOp_step (inB := hInB₁₀) hTy₁₀ hOpVals₁₀ hEval₁₀ hConf₁₀
  generalize hsq : s * qBV = sq at hStep₁₀ hSet₁₀
  -- Step op₁₁: subi (t = p - sq), then abstract `t`.
  have hv₁₁_4 : vs₁₁.getVar? (op₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p)) := by
    rw [getVar?_setResultValues?_ne d4_10 hSet₁₀, getVar?_setResultValues?_ne d49 hSet₉,
      getVar?_setResultValues?_ne d48 hSet₈, getVar?_setResultValues?_ne d47 hSet₇,
      getVar?_setResultValues?_ne d46 hSet₆, getVar?_setResultValues?_ne d45 hSet₅]
    rw [VariableState.getVar?_setResultValues? hSet₄]; simp [hNumRes₄]
  have hv₁₁_10 : vs₁₁.getVar? (op₁₀.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val sq)) := by
    rw [VariableState.getVar?_setResultValues? hSet₁₀]; simp [hNumRes₁₀]
  have hOpVals₁₁ : (InterpreterState.mk vs₁₁ state'.memory).variables.getOperandValues op₁₁
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val sq)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₁, Array.mapM_eq_mapM_toList]; simp [hv₁₁_4, hv₁₁_10]
  have hEval₁₁ : interpretOp' (.arith .subi) (op₁₁.getProperties! newCtx.raw (.arith .subi))
      (op₁₁.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val p),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val sq)]
      (op₁₁.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (p - sq))],
          state'.memory, none)) := by
    rw [hP₁₁]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₁₁ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (p - sq))]
      (op₁₁.getResultTypes! newCtx.raw) := by
    rw [hRT₁₁]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₂, hSet₁₁, hStep₁₁⟩ := interpretOp_step (inB := hInB₁₁) hTy₁₁ hOpVals₁₁ hEval₁₁ hConf₁₁
  -- `p - sq` is exactly the Barrett `t` appearing in `hPipeEq`; abstract it everywhere.
  generalize ht : p - sq = t at hStep₁₁ hSet₁₁ hPipeEq hUcanon hNoPoison
  -- Step op₁₂: cmpi uge t q → i1, then abstract `cond`.
  have hv₁₂_11 : vs₁₂.getVar? (op₁₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t)) := by
    rw [VariableState.getVar?_setResultValues? hSet₁₁]; simp [hNumRes₁₁]
  have hv₁₂_9 : vs₁₂.getVar? (op₉.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)) := by
    rw [getVar?_setResultValues?_ne d9_11 hSet₁₁, getVar?_setResultValues?_ne d9_10 hSet₁₀]
    rw [VariableState.getVar?_setResultValues? hSet₉]; simp [hNumRes₉]
  have hOpVals₁₂ : (InterpreterState.mk vs₁₂ state'.memory).variables.getOperandValues op₁₂
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₂, Array.mapM_eq_mapM_toList]; simp [hv₁₂_11, hv₁₂_9]
  have hEval₁₂ : interpretOp' (.arith .cmpi) (op₁₂.getProperties! newCtx.raw (.arith .cmpi))
      (op₁₂.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)]
      (op₁₂.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int 1 (.val (BitVec.ofBool (qBV.ule t)))], state'.memory, none)) := by
    rw [hP₁₂]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.icmp, Data.LLVM.Int.cast, Id.run, pure, bind,
      Data.LLVM.IntPred.eval]
  have hConf₁₂ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int 1 (.val (BitVec.ofBool (qBV.ule t)))] (op₁₂.getResultTypes! newCtx.raw) := by
    rw [hRT₁₂]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₃, hSet₁₂, hStep₁₂⟩ := interpretOp_step (inB := hInB₁₂) hTy₁₂ hOpVals₁₂ hEval₁₂ hConf₁₂
  -- Step op₁₃: subi (t - q), then abstract `tmq`.
  have hv₁₃_11 : vs₁₃.getVar? (op₁₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t)) := by
    rw [getVar?_setResultValues?_ne d11_12 hSet₁₂]
    rw [VariableState.getVar?_setResultValues? hSet₁₁]; simp [hNumRes₁₁]
  have hv₁₃_9 : vs₁₃.getVar? (op₉.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)) := by
    rw [getVar?_setResultValues?_ne d9_12 hSet₁₂]; exact hv₁₂_9
  have hOpVals₁₃ : (InterpreterState.mk vs₁₃ state'.memory).variables.getOperandValues op₁₃
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₃, Array.mapM_eq_mapM_toList]; simp [hv₁₃_11, hv₁₃_9]
  have hEval₁₃ : interpretOp' (.arith .subi) (op₁₃.getProperties! newCtx.raw (.arith .subi))
      (op₁₃.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val qBV)]
      (op₁₃.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (t - qBV))],
          state'.memory, none)) := by
    rw [hP₁₃]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.sub, Data.LLVM.Int.cast, Id.run, pure, bind]
  have hConf₁₃ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (t - qBV))]
      (op₁₃.getResultTypes! newCtx.raw) := by
    rw [hRT₁₃]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₄, hSet₁₃, hStep₁₃⟩ := interpretOp_step (inB := hInB₁₃) hTy₁₃ hOpVals₁₃ hEval₁₃ hConf₁₃
  -- Step op₁₄: select cond (t-q) t.
  have hv₁₄_12 : vs₁₄.getVar? (op₁₂.getResult 0 : ValuePtr)
      = some (RuntimeValue.int 1 (.val (BitVec.ofBool (qBV.ule t)))) := by
    rw [getVar?_setResultValues?_ne d12_13 hSet₁₃]
    rw [VariableState.getVar?_setResultValues? hSet₁₂]; simp [hNumRes₁₂]
  have hv₁₄_13 : vs₁₄.getVar? (op₁₃.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (t - qBV))) := by
    rw [VariableState.getVar?_setResultValues? hSet₁₃]; simp [hNumRes₁₃]
  have hv₁₄_11 : vs₁₄.getVar? (op₁₁.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t)) := by
    rw [getVar?_setResultValues?_ne d11_13 hSet₁₃, getVar?_setResultValues?_ne d11_12 hSet₁₂]
    rw [VariableState.getVar?_setResultValues? hSet₁₁]; simp [hNumRes₁₁]
  have hOpVals₁₄ : (InterpreterState.mk vs₁₄ state'.memory).variables.getOperandValues op₁₄
      = some #[RuntimeValue.int 1 (.val (BitVec.ofBool (qBV.ule t))),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (t - qBV)),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₄, Array.mapM_eq_mapM_toList]; simp [hv₁₄_12, hv₁₄_13, hv₁₄_11]
  have hEval₁₄ : interpretOp' (.arith .select) (op₁₄.getProperties! newCtx.raw (.arith .select))
      (op₁₄.getResultTypes! newCtx.raw)
      #[RuntimeValue.int 1 (.val (BitVec.ofBool (qBV.ule t))),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val (t - qBV)),
          RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val t)]
      (op₁₄.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (if (BitVec.ofBool (qBV.ule t) == 1#1) then (t - qBV) else t))],
          state'.memory, none)) := by
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.select, Data.LLVM.Int.cast, Id.run, pure,
      bind, apply_ite]
  have hConf₁₄ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth)
          (.val (if (BitVec.ofBool (qBV.ule t) == 1#1) then (t - qBV) else t))]
      (op₁₄.getResultTypes! newCtx.raw) := by
    rw [hRT₁₄]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₅, hSet₁₄, hStep₁₄⟩ := interpretOp_step (inB := hInB₁₄) hTy₁₄ hOpVals₁₄ hEval₁₄ hConf₁₄
  -- The select result is the Barrett conditional value `u`; rewrite `hPipeEq`/`hUcanon`/`hNoPoison`.
  have hUeq : (if (BitVec.ofBool (qBV.ule t) == 1#1) then (t - qBV) else t)
      = (if qBV.ule t then t - qBV else t) := by
    rw [Data.ModArith.ofBool_beq_one]
  rw [hUeq] at hStep₁₄ hSet₁₄ hConf₁₄
  -- Now `hPipeEq : (if qBV.ule t then t - qBV else t).truncate N = mul`, etc.  Abstract `u`.
  generalize hu : (if qBV.ule t then t - qBV else t) = u at hStep₁₄ hSet₁₄ hPipeEq hUcanon hNoPoison
  -- Step op₁₅: trunci (nuw) → iN.
  have hv₁₅_14 : vs₁₅.getVar? (op₁₄.getResult 0 : ValuePtr)
      = some (RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val u)) := by
    rw [VariableState.getVar?_setResultValues? hSet₁₄]; simp [hNumRes₁₄]
  have hOpVals₁₅ : (InterpreterState.mk vs₁₅ state'.memory).variables.getOperandValues op₁₅
      = some #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val u)] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₅, Array.mapM_eq_mapM_toList]; simp [hv₁₅_14]
  have hEval₁₅ : interpretOp' (.arith .trunci) (op₁₅.getProperties! newCtx.raw (.arith .trunci))
      (op₁₅.getResultTypes! newCtx.raw)
      #[RuntimeValue.int (4*mtv.modulus.type.bitwidth) (.val u)]
      (op₁₅.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (u.truncate mtv.modulus.type.bitwidth))], state'.memory, none)) := by
    rw [hRT₁₅, hP₁₅]
    simp [interpretOp', Arith.interpretOp', Data.LLVM.Int.trunc, Id.run, pure, bind, hNoPoison,
      dif_neg (show ¬ (mtv.modulus.type.bitwidth ≥ 4*mtv.modulus.type.bitwidth) from by omega)]
  have hConf₁₅ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (u.truncate mtv.modulus.type.bitwidth))]
      (op₁₅.getResultTypes! newCtx.raw) := by
    rw [hRT₁₅]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this; rfl
  obtain ⟨vs₁₆, hSet₁₅, hStep₁₅⟩ := interpretOp_step (inB := hInB₁₅) hTy₁₅ hOpVals₁₅ hEval₁₅ hConf₁₅
  -- Step op₁₆: cast back to !mod_arith.int.
  have hv₁₆_15 : vs₁₆.getVar? (op₁₅.getResult 0 : ValuePtr)
      = some (RuntimeValue.int mtv.modulus.type.bitwidth (.val (u.truncate mtv.modulus.type.bitwidth))) := by
    rw [VariableState.getVar?_setResultValues? hSet₁₅]; simp [hNumRes₁₅]
  have hOpVals₁₆ : (InterpreterState.mk vs₁₆ state'.memory).variables.getOperandValues op₁₆
      = some #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (u.truncate mtv.modulus.type.bitwidth))] := by
    unfold VariableState.getOperandValues
    rw [hOperands₁₆, Array.mapM_eq_mapM_toList]; simp [hv₁₆_15]
  have hEval₁₆ : interpretOp' (.builtin .unrealized_conversion_cast)
      (op₁₆.getProperties! newCtx.raw (.builtin .unrealized_conversion_cast))
      (op₁₆.getResultTypes! newCtx.raw)
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (u.truncate mtv.modulus.type.bitwidth))]
      (op₁₆.getSuccessors! newCtx.raw) state'.memory
      = some (.ok (#[RuntimeValue.int mtv.modulus.type.bitwidth
          (.val (Data.ModArith.mul mtv.modulus.value x y))], state'.memory, none)) := by
    rw [hRT₁₆, ← hPipeEq]
    simp [interpretOp', Data.LLVM.Int.cast, pure, bind]
  have hConf₁₆ : RuntimeValue.ArrayConforms
      #[RuntimeValue.int mtv.modulus.type.bitwidth (.val (Data.ModArith.mul mtv.modulus.value x y))]
      (op₁₆.getResultTypes! newCtx.raw) := by
    rw [hRT₁₆]; refine ⟨by rfl, ?_⟩; intro i hi
    have : i = 0 := by simpa using hi
    subst this
    refine ⟨rfl, ?_⟩
    simp only [Data.ModArith.isCanonical_val]
    exact Data.ModArith.isCanonical_mul hQpos hQle
  obtain ⟨vs₁₇, hSet₁₆, hStep₁₆⟩ := interpretOp_step (inB := hInB₁₆) hTy₁₆ hOpVals₁₆ hEval₁₆ hConf₁₆
  -- ## Assemble the seventeen steps.
  refine ⟨⟨vs₁₇, state'.memory⟩, ?_, ?_, ?_⟩
  · show interpretOpList [op₀, op₁, op₂, op₃, op₄, op₅, op₆, op₇, op₈, op₉, op₁₀, op₁₁, op₁₂, op₁₃,
        op₁₄, op₁₅, op₁₆] state' _ = liftM (some (⟨vs₁₇, state'.memory⟩, none))
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
    rw [interpretOpList_cons]; simp only [hStep₁₀]
    rw [interpretOpList_cons]; simp only [hStep₁₁]
    rw [interpretOpList_cons]; simp only [hStep₁₂]
    rw [interpretOpList_cons]; simp only [hStep₁₃]
    rw [interpretOpList_cons]; simp only [hStep₁₄]
    rw [interpretOpList_cons]; simp only [hStep₁₅]
    rw [interpretOpList_cons]; simp only [hStep₁₆]
    simp [liftM, monadLift, MonadLift.monadLift]
  · simpa using hMemEq
  · refine ⟨#[RuntimeValue.int mtv.modulus.type.bitwidth
        (.val (Data.ModArith.mul mtv.modulus.value x y))], ?_, ?_⟩
    · have hv₁₇ : vs₁₇.getVar? (op₁₆.getResult 0 : ValuePtr)
          = some (RuntimeValue.int mtv.modulus.type.bitwidth
              (.val (Data.ModArith.mul mtv.modulus.value x y))) := by
        rw [VariableState.getVar?_setResultValues? hSet₁₆]; simp [hNumRes₁₆]
      rw [Array.mapM_eq_mapM_toList]; simp [hv₁₇]
    · rw [hSourceVals]
      refine ⟨by simp, ?_⟩
      intro i hi
      have : i = 0 := by simpa using hi
      subst this; simp [RuntimeValue.isRefinedBy]
