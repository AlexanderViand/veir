import Veir.Passes.ModArithToArith
import Veir.Passes.ModArithToArith.Proofs
import Veir.Passes.ModArithToArithOriginal

/-!
# Imperative-style lowering vs. the verified recipe-based patterns

This file relates the imperative `PatternRewriter`-style lowering
(`Veir.ModArithToArithOriginal`) to the verified recipe-based lowering
(`Veir.ModArithToArith`).

## Why the agreement is stated *extensionally*

The naive statement would be a per-op *structural* equality

```
ModArithToArithOriginal.lowerModArithAddOp rewriter op = lowerModArithAddOp rewriter op
```

i.e. structural (`Eq`) equality of the `PatternRewriter` record, hence of the underlying
`WfIRContext` / `IRContext`, whose fields are `Std.HashMap`s.

That `Eq` is **not provable**: the two passes insert exactly the same keys with the same
final values into `IRContext.operations`, but in **different orders**:

* the recipe pass (`ModArithToArith.buildOps` + `RewritePattern.fromLocalRewrite`) creates
  *all* new operations detached first (`WfRewriter.createOp ... none`) and only afterwards
  runs the insert-loop that rewires the surrounding linked list
  (`PatternRewriter.insertOp` at `InsertPoint.before op`), then the value replacement and
  the erase;
* the imperative pass interleaves creation and insertion: every helper does
  `PatternRewriter.createOp ... (some (InsertPoint.before op))`, allocating the fresh op
  *and immediately* rewiring the neighbours before allocating the next op.

`Std.HashMap` `Eq` is not insertion-order invariant as an exposed theorem (the public API
only provides the extensional equivalence `~m`; there is no `Eq`-valued `insert_comm`). So
the two passes produce `IRContext`s that are *extensionally equal* — equal under every
`getElem?` / getter, hence denoting the same IR — but not `Eq`.

This is exactly why the existing `ModArithToArith` correctness proof is phrased as
`LocalRewritePattern.PreservesSemantics` (agreement of interpreter results) rather than as
context equality. We therefore introduce a lightweight extensional equivalence
`IRContext.Equiv` and state the agreement modulo it.

## What this file provides

1. `IRContext.Equiv` / `WfIRContext.Equiv`: two contexts agree iff their `operations`,
   `blocks` and `regions` maps agree under `getElem?` and their `nextID` counters are
   equal. This is the smallest getter set that (a) we can prove for the two pipelines and
   (b) determines the entire getter surface used by the rewriter and the interpreter
   (every `get!` / `getOpType!` / `getType!` / `InBounds` / … factors through `getElem?`
   on one of the three maps — see `IRContext.Equiv.op_get!_eq`/`getType!_eq`/… below). It
   is an equivalence relation (`refl`/`symm`/`trans`), and comes with the practical
   introduction form `IRContext.Equiv.of_get!`, which reduces an equivalence goal to
   per-pointer `get!`/`InBounds` agreement so the rewriter's `get!`-level get-set lemma
   library applies.

2. The `createOp`-with-insertion-point decomposition
   (`Rewriter.createOp_some_decompose`, lifted to `WfRewriter`), the reusable structural
   building block: `createOp(some ip) = createOp(none) ; insertOp?`.

3. Semantic transfer (the *meaningful* end of the chain): interpretation reads the context
   only through getters, so `Equiv` contexts yield equal interpretation results.
   Transporting an `InterpreterState` across an `Equiv` (its `variables` field is a plain
   `Std.ExtHashMap`, independent of the context — only the `conforms`/`InBounds` proof
   fields mention the context, and those transfer because `getType!` and `InBounds` agree)
   gives `interpretOp_transport`: on `Equiv` contexts `interpretOp` produces the same
   control-flow action, memory, and variable map. So once the two passes are shown to emit
   `Equiv` contexts, they have identical observable behaviour, and the recipe pass's
   `PreservesSemantics` carries over to the imperative pass. Items 1–3 are complete and
   sorry-free.

4. Per-pattern agreement, stated up to `PatternResultEquiv` (succeed/fail together; on
   success `Equiv` contexts with equal `hasDoneAction`). For `mod_arith.constant`,
   `lowerModArithConstant_equiv` case-splits on the match: the two no-match branches
   (`lowerModArithConstant_matchOp_none`, `lowerModArithConstant_notModArith`) are proved
   in full; the match branch (`lowerModArithConstant_match_equiv`) is reduced to a single
   isolated commutation primitive, the only `sorry` in the file (see its `TODO(BLOCKED)`).
   The binop patterns (add/sub/mul) follow the identical template — they would replicate
   the very same single commutation gap several times over, so they are intentionally not
   spelled out here (one isolated gap rather than many scattered ones).

Note on `sorryAx`: the recipe patterns are built with `RewritePattern.fromLocalRewrite`,
whose framework well-formedness obligations are themselves `sorry` (erased proofs, out of
scope for this task). Any statement mentioning a recipe pattern therefore inherits that
`sorryAx`. The infrastructure in items 1–3 (which does not mention `fromLocalRewrite`) is
fully axiom-clean apart from the standard `propext`/`Classical.choice`/`Quot.sound`.
-/

namespace Veir

open Std

/-! ## Extensional context equivalence -/

/--
Extensional equivalence of IR contexts: the three maps agree under `getElem?` (`get?`) and
the allocation counter agrees. Every getter of the rewriter/interpreter surface
(`get!`, `getOpType!`, `getType!`, `InBounds`, …) factors through these, so `Equiv`
contexts are interchangeable for all observational purposes (see the lemmas below); they
need not be structurally `Eq`.
-/
structure IRContext.Equiv {OpInfo : Type} [HasOpInfo OpInfo] (c c' : IRContext OpInfo) :
    Prop where
  operations : ∀ op, c.operations.get? op = c'.operations.get? op
  blocks : ∀ bl, c.blocks.get? bl = c'.blocks.get? bl
  regions : ∀ rg, c.regions.get? rg = c'.regions.get? rg
  nextID : c.nextID = c'.nextID

namespace IRContext.Equiv

variable {OpInfo : Type} [HasOpInfo OpInfo] {c c' c'' : IRContext OpInfo}

theorem refl (c : IRContext OpInfo) : IRContext.Equiv c c :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem symm (h : IRContext.Equiv c c') : IRContext.Equiv c' c :=
  ⟨fun op => (h.operations op).symm, fun bl => (h.blocks bl).symm,
   fun rg => (h.regions rg).symm, h.nextID.symm⟩

theorem trans (h : IRContext.Equiv c c') (h' : IRContext.Equiv c' c'') :
    IRContext.Equiv c c'' :=
  ⟨fun op => (h.operations op).trans (h'.operations op),
   fun bl => (h.blocks bl).trans (h'.blocks bl),
   fun rg => (h.regions rg).trans (h'.regions rg), h.nextID.trans h'.nextID⟩

/-- `Equiv` contexts agree on the `get!` of any operation pointer. -/
theorem op_get!_eq (h : IRContext.Equiv c c') (op : OperationPtr) : op.get! c = op.get! c' := by
  simp only [OperationPtr.get!, getElem!_def]
  rw [show c.operations[op]? = c'.operations[op]? from h.operations op]

/-- `Equiv` contexts agree on the `get!` of any block pointer. -/
theorem block_get!_eq (h : IRContext.Equiv c c') (bl : BlockPtr) : bl.get! c = bl.get! c' := by
  simp only [BlockPtr.get!, getElem!_def]
  rw [show c.blocks[bl]? = c'.blocks[bl]? from h.blocks bl]

/-- `Equiv` contexts agree on the `get!` of any region pointer. -/
theorem region_get!_eq (h : IRContext.Equiv c c') (rg : RegionPtr) :
    rg.get! c = rg.get! c' := by
  simp only [RegionPtr.get!, getElem!_def]
  rw [show c.regions[rg]? = c'.regions[rg]? from h.regions rg]

/-- `Equiv` contexts agree on operation in-bounds. -/
theorem op_inBounds_iff (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.InBounds c ↔ op.InBounds c' := by
  simp only [OperationPtr.InBounds]
  rw [Std.HashMap.mem_iff_isSome_getElem?, Std.HashMap.mem_iff_isSome_getElem?,
    show c.operations[op]? = c'.operations[op]? from h.operations op]

theorem getOpType!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getOpType! c = op.getOpType! c' := by grind [OperationPtr.getOpType!, op_get!_eq]

theorem getProperties!_eq (h : IRContext.Equiv c c') (op : OperationPtr) (T : OpInfo) :
    op.getProperties! c T = op.getProperties! c' T := by
  grind [OperationPtr.getProperties!, op_get!_eq]

theorem getResultTypes!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getResultTypes! c = op.getResultTypes! c' := by
  have := h.op_get!_eq op
  grind [OperationPtr.getResultTypes!, OperationPtr.getResult, OpResultPtr.get!]

theorem getSuccessors!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getSuccessors! c = op.getSuccessors! c' := by
  have := h.op_get!_eq op; grind [OperationPtr.getSuccessors!]

theorem getOperands!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getOperands! c = op.getOperands! c' := by
  have := h.op_get!_eq op; grind [OperationPtr.getOperands!]

theorem getNumResults!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getNumResults! c = op.getNumResults! c' := by
  have := h.op_get!_eq op; grind [OperationPtr.getNumResults!]

theorem getNumRegions!_eq (h : IRContext.Equiv c c') (op : OperationPtr) :
    op.getNumRegions! c = op.getNumRegions! c' := by
  have := h.op_get!_eq op; grind [OperationPtr.getNumRegions!]

theorem getType!_eq (h : IRContext.Equiv c c') (v : ValuePtr) : v.getType! c = v.getType! c' := by
  cases v with
  | opResult ptr => have := h.op_get!_eq ptr.op; grind [ValuePtr.getType!, OpResultPtr.get!]
  | blockArgument ptr =>
      have := h.block_get!_eq ptr.block; grind [ValuePtr.getType!, BlockArgumentPtr.get!]

/-- `Equiv` contexts agree on block in-bounds. -/
theorem block_inBounds_iff (h : IRContext.Equiv c c') (bl : BlockPtr) :
    bl.InBounds c ↔ bl.InBounds c' := by
  simp only [BlockPtr.InBounds]
  rw [Std.HashMap.mem_iff_isSome_getElem?, Std.HashMap.mem_iff_isSome_getElem?,
    show c.blocks[bl]? = c'.blocks[bl]? from h.blocks bl]

/-- `Equiv` contexts agree on op-result in-bounds. -/
theorem opResult_inBounds_iff (h : IRContext.Equiv c c') (ptr : OpResultPtr) :
    ptr.InBounds c ↔ ptr.InBounds c' := by
  have hg := h.op_get!_eq ptr.op
  have hi := h.op_inBounds_iff ptr.op
  simp only [OpResultPtr.InBounds]
  constructor
  · rintro ⟨hin, hlt⟩; refine ⟨hi.mp hin, ?_⟩
    rwa [← OperationPtr.get!_eq_get (hi.mp hin), ← hg, OperationPtr.get!_eq_get hin]
  · rintro ⟨hin, hlt⟩; refine ⟨hi.mpr hin, ?_⟩
    rwa [← OperationPtr.get!_eq_get (hi.mpr hin), hg, OperationPtr.get!_eq_get hin]

/-- `Equiv` contexts agree on block-argument in-bounds. -/
theorem blockArg_inBounds_iff (h : IRContext.Equiv c c') (ptr : BlockArgumentPtr) :
    ptr.InBounds c ↔ ptr.InBounds c' := by
  have hg := h.block_get!_eq ptr.block
  have hi := h.block_inBounds_iff ptr.block
  simp only [BlockArgumentPtr.InBounds]
  constructor
  · rintro ⟨hin, hlt⟩; refine ⟨hi.mp hin, ?_⟩
    rwa [← BlockPtr.get!_eq_get (hi.mp hin), ← hg, BlockPtr.get!_eq_get hin]
  · rintro ⟨hin, hlt⟩; refine ⟨hi.mpr hin, ?_⟩
    rwa [← BlockPtr.get!_eq_get (hi.mpr hin), hg, BlockPtr.get!_eq_get hin]

/-- `Equiv` contexts agree on value in-bounds. -/
theorem value_inBounds_iff (h : IRContext.Equiv c c') (v : ValuePtr) :
    v.InBounds c ↔ v.InBounds c' := by
  cases v with
  | opResult ptr => simp only [ValuePtr.inBounds_opResult]; exact h.opResult_inBounds_iff ptr
  | blockArgument ptr => simp only [ValuePtr.inBounds_blockArg]; exact h.blockArg_inBounds_iff ptr

/--
Build an `IRContext.Equiv` from `get!`/`InBounds` agreement on each map. This is the
practical introduction form: the rewriter's get-set lemma library is stated at the `get!`
level (`OperationPtr.prev!_createOp`, `…_insertOp?`, …), so equivalence proofs can be
discharged there and packaged here, rather than reasoning about `Std.HashMap.getElem?`
directly. (`InBounds` on a pointer is definitionally membership in the corresponding map,
and `get! = map[·]!`, so this is exactly `getElem?` agreement re-expressed.)
-/
theorem of_get! (hops : ∀ op : OperationPtr, (op.InBounds c ↔ op.InBounds c') ∧
      (op.InBounds c → op.get! c = op.get! c'))
    (hbls : ∀ bl : BlockPtr, (bl.InBounds c ↔ bl.InBounds c') ∧
      (bl.InBounds c → bl.get! c = bl.get! c'))
    (hrgs : ∀ rg : RegionPtr, (rg.InBounds c ↔ rg.InBounds c') ∧
      (rg.InBounds c → rg.get! c = rg.get! c'))
    (hid : c.nextID = c'.nextID) : IRContext.Equiv c c' := by
  refine ⟨fun op => ?_, fun bl => ?_, fun rg => ?_, hid⟩
  · obtain ⟨hiff, hget⟩ := hops op
    show c.operations[op]? = c'.operations[op]?
    by_cases hin : op.InBounds c
    · rw [Std.HashMap.getElem?_eq_some_getElem! hin,
        Std.HashMap.getElem?_eq_some_getElem! (hiff.mp hin)]
      simp only [OperationPtr.get!] at hget; rw [hget hin]
    · rw [Std.HashMap.getElem?_eq_none hin, Std.HashMap.getElem?_eq_none (fun h => hin (hiff.mpr h))]
  · obtain ⟨hiff, hget⟩ := hbls bl
    show c.blocks[bl]? = c'.blocks[bl]?
    by_cases hin : bl.InBounds c
    · rw [Std.HashMap.getElem?_eq_some_getElem! hin,
        Std.HashMap.getElem?_eq_some_getElem! (hiff.mp hin)]
      simp only [BlockPtr.get!] at hget; rw [hget hin]
    · rw [Std.HashMap.getElem?_eq_none hin, Std.HashMap.getElem?_eq_none (fun h => hin (hiff.mpr h))]
  · obtain ⟨hiff, hget⟩ := hrgs rg
    show c.regions[rg]? = c'.regions[rg]?
    by_cases hin : rg.InBounds c
    · rw [Std.HashMap.getElem?_eq_some_getElem! hin,
        Std.HashMap.getElem?_eq_some_getElem! (hiff.mp hin)]
      simp only [RegionPtr.get!] at hget; rw [hget hin]
    · rw [Std.HashMap.getElem?_eq_none hin, Std.HashMap.getElem?_eq_none (fun h => hin (hiff.mpr h))]

end IRContext.Equiv

/-- Extensional equivalence of well-formed contexts: equivalence of the underlying raws. -/
def WfIRContext.Equiv {OpInfo : Type} [HasOpInfo OpInfo] (c c' : WfIRContext OpInfo) : Prop :=
  IRContext.Equiv c.raw c'.raw

namespace WfIRContext.Equiv
variable {OpInfo : Type} [HasOpInfo OpInfo] {c c' c'' : WfIRContext OpInfo}

theorem refl (c : WfIRContext OpInfo) : WfIRContext.Equiv c c := IRContext.Equiv.refl c.raw
theorem symm (h : WfIRContext.Equiv c c') : WfIRContext.Equiv c' c := IRContext.Equiv.symm h
theorem trans (h : WfIRContext.Equiv c c') (h' : WfIRContext.Equiv c' c'') :
    WfIRContext.Equiv c c'' := IRContext.Equiv.trans h h'

theorem getType!_eq (h : WfIRContext.Equiv c c') (v : ValuePtr) :
    v.getType! c.raw = v.getType! c'.raw := IRContext.Equiv.getType!_eq h v
theorem value_inBounds_iff (h : WfIRContext.Equiv c c') (v : ValuePtr) :
    v.InBounds c.raw ↔ v.InBounds c'.raw := IRContext.Equiv.value_inBounds_iff h v
theorem op_inBounds_iff (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.InBounds c.raw ↔ op.InBounds c'.raw := IRContext.Equiv.op_inBounds_iff h op
theorem getOpType!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getOpType! c.raw = op.getOpType! c'.raw := IRContext.Equiv.getOpType!_eq h op
theorem getProperties!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) (T : OpInfo) :
    op.getProperties! c.raw T = op.getProperties! c'.raw T := IRContext.Equiv.getProperties!_eq h op T
theorem getResultTypes!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getResultTypes! c.raw = op.getResultTypes! c'.raw := IRContext.Equiv.getResultTypes!_eq h op
theorem getSuccessors!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getSuccessors! c.raw = op.getSuccessors! c'.raw := IRContext.Equiv.getSuccessors!_eq h op
theorem getOperands!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getOperands! c.raw = op.getOperands! c'.raw := IRContext.Equiv.getOperands!_eq h op
theorem getNumResults!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getNumResults! c.raw = op.getNumResults! c'.raw := IRContext.Equiv.getNumResults!_eq h op
theorem getNumRegions!_eq (h : WfIRContext.Equiv c c') (op : OperationPtr) :
    op.getNumRegions! c.raw = op.getNumRegions! c'.raw := IRContext.Equiv.getNumRegions!_eq h op

end WfIRContext.Equiv

/-! ## The `createOp`-with-insertion-point decomposition -/

/--
`Rewriter.createOp` with an insertion point equals the detached `createOp` (insertion
point `none`) followed by `Rewriter.insertOp?` at that point.

Holds as a structural equality: both sides perform exactly the same allocation and
initialization steps and differ only in whether the final `insertOp?` runs inline, so no
`Std.HashMap` insertions are reordered.
-/
theorem Rewriter.createOp_some_decompose {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx ctx' : IRContext OpInfo} {opType : OpInfo}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr} {blockOperands : Array BlockPtr}
    {regions : Array RegionPtr} {properties : HasOpInfo.propertiesOf opType} {ip : InsertPoint}
    {h₁ h₂ h₃ h₄ h₅} {newOp}
    (heq : Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      (some ip) h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp)) :
    ∃ ctxMid h₄',
      Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
        none h₁ h₂ h₃ h₄' h₅ = some (ctxMid, newOp) ∧
      ∃ hib hb hfb, Rewriter.insertOp? ctxMid newOp ip hib hb hfb = some ctx' := by
  unfold Rewriter.createOp at heq ⊢
  simp only at heq ⊢
  split at heq
  · simp at heq
  next nc np hcreate =>
  split at heq
  · simp at heq
  next ctx3 hregions =>
  split at heq
  · simp at heq
  next ctx6 hins =>
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨_, by simp [Option.maybe], rfl, _, _, _, hins⟩

/-- A `WfIRContext` is determined by its `raw` field (the `wellFormed` field is a proof). -/
theorem WfIRContext.eq_of_raw {OpInfo : Type} [HasOpInfo OpInfo] {c c' : WfIRContext OpInfo}
    (h : c.raw = c'.raw) : c = c' := by
  obtain ⟨r, w⟩ := c; obtain ⟨r', w'⟩ := c'; cases h; rfl

/--
`WfRewriter.createOp` success is exactly `Rewriter.createOp` success on the raw context:
the `wellFormed` proof field is determined by proof irrelevance.
-/
theorem WfRewriter.createOp_eq_some_iff {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx : WfIRContext OpInfo} {c' : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes operands blockOperands regions properties ip h₁ h₂ h₃ h₄ o} :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
        ip h₁ h₂ h₃ h₄ = some (c', o) ↔
    Rewriter.createOp ctx.raw opType resultTypes operands blockOperands regions properties
        ip h₁ h₂ h₃ h₄ (by grind) = some (c'.raw, o) := by
  rw [WfRewriter.createOp]; simp only [pure]
  constructor
  · intro h
    split at h
    · simp at h
    · next rc ro hr =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨he, rfl⟩ := h; rw [hr]; rw [← he]
  · intro h
    split
    · next hnone => rw [h] at hnone; simp at hnone
    · next rc ro hr =>
        rw [h] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨he, rfl⟩ := hr
        exact congrArg (fun w => some (w, o)) (WfIRContext.eq_of_raw he.symm)

/-- `WfRewriter.insertOp?` success is exactly `Rewriter.insertOp?` success on the raw context. -/
theorem WfRewriter.insertOp?_eq_some_iff {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx : WfIRContext OpInfo} {c' : WfIRContext OpInfo} {op ip h₁ h₂} :
    WfRewriter.insertOp? ctx op ip h₁ h₂ = some c' ↔
    Rewriter.insertOp? ctx.raw op ip h₁ h₂ (by grind) = some c'.raw := by
  rw [WfRewriter.insertOp?]; simp only [pure]
  constructor
  · intro h
    split at h
    · simp at h
    · next rc hr => simp only [Option.some.injEq] at h; rw [hr, ← h]
  · intro h
    split
    · next hnone => rw [h] at hnone; simp at hnone
    · next rc hr =>
        rw [h] at hr; simp only [Option.some.injEq] at hr
        exact congrArg some (WfIRContext.eq_of_raw hr.symm)

/--
Lifted decomposition at the `WfRewriter` level: `WfRewriter.createOp` with an insertion
point is the detached `WfRewriter.createOp` followed by `WfRewriter.insertOp?`.
-/
theorem WfRewriter.createOp_some_decompose {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx ctx' : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr} {blockOperands : Array BlockPtr}
    {regions : Array RegionPtr} {properties : HasOpInfo.propertiesOf opType} {ip : InsertPoint}
    {h₁ h₂ h₃ h₄} {newOp}
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      (some ip) h₁ h₂ h₃ h₄ = some (ctx', newOp)) :
    ∃ ctxMid h₄',
      WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
        none h₁ h₂ h₃ h₄' = some (ctxMid, newOp) ∧
      ∃ hib hb, WfRewriter.insertOp? ctxMid newOp ip hib hb = some ctx' := by
  rw [WfRewriter.createOp_eq_some_iff] at heq
  obtain ⟨ctxMidRaw, h₄', hnone, hib, hb, hfb, hins⟩ := Rewriter.createOp_some_decompose heq
  have hwf : ctxMidRaw.WellFormed := by grind [Rewriter.createOp_WellFormed]
  refine ⟨⟨ctxMidRaw, hwf⟩, h₄', ?_, hib, hb, ?_⟩
  · rw [WfRewriter.createOp_eq_some_iff]; exact hnone
  · rw [WfRewriter.insertOp?_eq_some_iff]; exact hins

/-! ## Semantic transfer across `Equiv`

Interpretation reads the context only through getters that agree on `Equiv` contexts.
An interpreter state is a `Std.ExtHashMap ValuePtr RuntimeValue` together with proof fields
(`conforms`, `variablesIn`) that mention the context only through `getType!` / `InBounds`,
both of which agree under `Equiv`. So a state transports across an `Equiv` keeping the same
underlying map, and `interpretOp` produces equal results (up to transporting the output
state). This is the formal core of "the imperative pass's output interprets identically to
the recipe pass's output". -/

/-- Transport a variable state across an `Equiv`: the underlying map is unchanged; the
`conforms` / `variablesIn` proof fields transfer because `getType!` and `InBounds` agree. -/
def VariableState.transport {c c' : WfIRContext OpCode} (h : WfIRContext.Equiv c c')
    (vs : VariableState c) : VariableState c' where
  variables := vs.variables
  conforms := by
    intro val var hmem hget
    have := vs.conforms val var hmem hget
    rwa [show val.getType! c'.raw = val.getType! c.raw from (h.getType!_eq val).symm]
  variablesIn := fun val hmem => (h.value_inBounds_iff val).mp (vs.variablesIn val hmem)

@[simp] theorem VariableState.transport_variables {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (vs : VariableState c) :
    (vs.transport h).variables = vs.variables := rfl

@[simp] theorem VariableState.getVar?_transport {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (vs : VariableState c) (v : ValuePtr) :
    (vs.transport h).getVar? v = vs.getVar? v := rfl

theorem VariableState.getOperandValues_transport {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (vs : VariableState c) (op : OperationPtr) :
    (vs.transport h).getOperandValues op = vs.getOperandValues op := by
  unfold VariableState.getOperandValues
  rw [show op.getOperands! c'.raw = op.getOperands! c.raw from (h.getOperands!_eq op).symm]
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]; congr 1

/-- Transport an interpreter state across an `Equiv` (same variable map, same memory). -/
def InterpreterState.transport {c c' : WfIRContext OpCode} (h : WfIRContext.Equiv c c')
    (st : InterpreterState c) : InterpreterState c' :=
  ⟨st.variables.transport h, st.memory⟩

@[simp] theorem InterpreterState.transport_memory {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (st : InterpreterState c) : (st.transport h).memory = st.memory :=
  rfl

@[simp] theorem InterpreterState.transport_variables {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (st : InterpreterState c) :
    (st.transport h).variables = st.variables.transport h := rfl

/-- `setResultValues?` agrees across a transport: the resulting variable maps coincide. -/
theorem VariableState.setResultValues?_transport {c c' : WfIRContext OpCode}
    (h : WfIRContext.Equiv c c') (vs : VariableState c) (op : OperationPtr)
    (rv : Array RuntimeValue) (hin : op.InBounds c.raw) (hin' : op.InBounds c'.raw)
    {vs' : VariableState c} (hset : vs.setResultValues? op rv hin = some vs') :
    ∃ vs'', (vs.transport h).setResultValues? op rv hin' = some vs'' ∧
      vs''.variables = vs'.variables := by
  have hconf : RuntimeValue.ArrayConforms rv (op.getResultTypes! c.raw) :=
    RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hset
  have hconf' : RuntimeValue.ArrayConforms rv (op.getResultTypes! c'.raw) := by
    rwa [show op.getResultTypes! c'.raw = op.getResultTypes! c.raw from (h.getResultTypes!_eq op).symm]
  obtain ⟨vs'', hset''⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms (varState := vs.transport h)
      (inBounds := hin')).mp hconf'
  refine ⟨vs'', hset'', ?_⟩
  apply Std.ExtHashMap.ext_getElem?
  intro var
  show vs''.getVar? var = vs'.getVar? var
  rw [VariableState.getVar?_setResultValues? hset'', VariableState.getVar?_setResultValues? hset]
  rw [show op.getNumResults! c'.raw = op.getNumResults! c.raw from (h.getNumResults!_eq op).symm]
  cases var with
  | opResult ptr => simp [VariableState.getVar?_transport]
  | blockArgument ptr => simp [VariableState.getVar?_transport]

/--
**Semantic transfer (single op).** On `Equiv` contexts, `interpretOp` agrees: a successful
interpretation on `state` transports to a successful interpretation on `state.transport h`
producing the same control-flow action, the same memory, and the same variable map.

This is the key lemma making the extensional agreement *meaningful*: the imperative and
recipe passes produce `Equiv` contexts, so they have identical observable interpreter
behaviour even though their `Std.HashMap`s are not structurally `Eq`.
-/
theorem interpretOp_transport {c c' : WfIRContext OpCode} (h : WfIRContext.Equiv c c')
    (op : OperationPtr) (state : InterpreterState c) (hin : op.InBounds c.raw)
    (hin' : op.InBounds c'.raw) {state' : InterpreterState c} {cf}
    (hinterp : interpretOp op state hin = some (.ok (state', cf))) :
    ∃ state'', interpretOp op (state.transport h) hin' = some (.ok (state'', cf)) ∧
      state''.variables.variables = state'.variables.variables ∧
      state''.memory = state'.memory := by
  obtain ⟨ov, rv, mem', vs', hov, heval, hset, hst⟩ := interpretOp_some_iff.mp hinterp
  subst hst
  obtain ⟨vs'', hset'', hvarseq⟩ :=
    VariableState.setResultValues?_transport h state.variables op rv hin hin' hset
  refine ⟨⟨vs'', mem'⟩, ?_, hvarseq, rfl⟩
  rw [interpretOp_some_iff]
  refine ⟨ov, rv, mem', vs'', ?_, ?_, hset'', rfl⟩
  · rw [InterpreterState.transport_variables, VariableState.getOperandValues_transport]; exact hov
  · rw [show op.getOpType! c'.raw = op.getOpType! c.raw from (h.getOpType!_eq op).symm,
        show op.getProperties! c'.raw (op.getOpType! c.raw)
           = op.getProperties! c.raw (op.getOpType! c.raw) from (h.getProperties!_eq op _).symm,
        show op.getResultTypes! c'.raw = op.getResultTypes! c.raw from (h.getResultTypes!_eq op).symm,
        show op.getSuccessors! c'.raw = op.getSuccessors! c.raw from (h.getSuccessors!_eq op).symm,
        InterpreterState.transport_memory]
    exact heval

/-! ## Per-pattern agreement (imperative vs. recipe)

For each of the four patterns we relate the imperative pattern from
`ModArithToArithOriginal` to the recipe pattern from `ModArithToArith`. Two
`PatternRewriter` results agree up to `PatternResultEquiv`: they succeed/fail together and,
on success, their output contexts are `Equiv` and their `hasDoneAction` flags are equal.

We deliberately do **not** require worklist agreement in the conclusion. The worklist
(`PatternRewriter.worklist`) is itself backed by a `Std.HashMap` (`indexInStack`) and only
governs the *traversal order* of the greedy driver, never the IR content or its
interpretation; including it would re-introduce exactly the `Std.HashMap`-order obstruction
that motivates the extensional treatment in the first place. Both passes push precisely the
created ops (in creation order) and then remove `op`, so the worklists are extensionally
equal, but we omit that from the statement.
-/

/-- Agreement of two optional `PatternRewriter` results up to context `Equiv`: both fail, or
both succeed with `Equiv` contexts and equal `hasDoneAction`. -/
def PatternResultEquiv (r₁ r₂ : Option (PatternRewriter OpCode)) : Prop :=
  match r₁, r₂ with
  | none, none => True
  | some a, some b => WfIRContext.Equiv a.ctx b.ctx ∧ a.hasDoneAction = b.hasDoneAction
  | _, _ => False

theorem PatternResultEquiv.some {a b : PatternRewriter OpCode}
    (hctx : WfIRContext.Equiv a.ctx b.ctx) (hda : a.hasDoneAction = b.hasDoneAction) :
    PatternResultEquiv (some a) (some b) := ⟨hctx, hda⟩

/-- Both constant patterns no-op when `matchOp` fails. -/
theorem lowerModArithConstant_matchOp_none (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (hda : rewriter.hasDoneAction = false)
    (hm : matchOp op rewriter.ctx.raw (.mod_arith .constant) 0 = none) :
    ModArithToArithOriginal.lowerModArithConstant rewriter op = some rewriter ∧
    lowerModArithConstant rewriter op = some rewriter := by
  refine ⟨?_, ?_⟩
  · unfold ModArithToArithOriginal.lowerModArithConstant; simp only [pure, hm]
  · unfold lowerModArithConstant RewritePattern.fromLocalRewrite ModArithToArith.lowerConstant
    simp only [pure, hm]; obtain ⟨ctx, hda', wl⟩ := rewriter; simp_all

/-- Both constant patterns no-op when the matched op's result type is not a `mod_arith` type. -/
theorem lowerModArithConstant_notModArith (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    {operands props} (hda : rewriter.hasDoneAction = false)
    (hm : matchOp op rewriter.ctx.raw (.mod_arith .constant) 0 = some (operands, props))
    (hty : ∀ mt, ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val ≠ .modArithType mt) :
    ModArithToArithOriginal.lowerModArithConstant rewriter op = some rewriter ∧
    lowerModArithConstant rewriter op = some rewriter := by
  refine ⟨?_, ?_⟩
  · unfold ModArithToArithOriginal.lowerModArithConstant
    simp only [pure, hm, hty]
  · unfold lowerModArithConstant RewritePattern.fromLocalRewrite ModArithToArith.lowerConstant
    simp only [pure, hm, hty]
    obtain ⟨ctx, hda', wl⟩ := rewriter; simp_all

/--
**Match-case agreement for `mod_arith.constant`** (the one remaining gap).

When `op` is a `mod_arith.constant` with `mod_arith` result type, the imperative pattern
`ModArithToArithOriginal.lowerModArithConstant` and the recipe pattern
`lowerModArithConstant` produce contexts that are `Equiv` and equal `hasDoneAction`.

Both pipelines create the same two operations (`arith.constant` then
`builtin.unrealized_conversion_cast`) and then run the same `replaceValue` / `eraseOp`. By
`Rewriter.createOp_some_decompose` the imperative pipeline is
`createConst(none); insertConst; createCast(none); insertCast; replace; erase`, while the
recipe pipeline is `createConst(none); createCast(none); insertConst; insertCast; replace;
erase`. They differ only in the order of the single pair `insertConst ; createCast(none)`,
which commutes *up to `Equiv`*: `createConst` produces a fresh op `C` with no uses, so the
`createCast`'s `insertIntoCurrent` (which links the cast's operand onto `C`'s result use
chain, `OpOperandPtr.insertIntoCurrent`) only sets `C`'s result `firstUse` (the
`newNextUse = none` branch fires, since `C` has no prior uses) and the fresh cast operand's
own back/nextUse; whereas `insertConst` (`linkBetweenWithParent`) only sets `C`'s
`prev`/`next`/`parent` and the parent block's `firstOp`/`lastOp`. These are *disjoint
fields* of `C`'s `Operation` record (and disjoint keys otherwise), so the two orders yield
`Equiv` contexts. The intended on-ramp is `IRContext.Equiv.of_get!`, reducing the goal to
`get!`/`InBounds` agreement on each pointer, dischargeable with the `…_createOp` /
`…_insertOp?` get-set lemma families.

-- TODO(BLOCKED): the single remaining gap is the up-to-`Equiv` commutation
--   `insertOp? A ip ; createOp B none  ≃  createOp B none ; insertOp? A ip`   (B fresh).
-- With `IRContext.Equiv.of_get!` the goal is per-pointer `get!`/`InBounds` agreement. The
-- structural setters (`linkBetweenWithParent`) have full `get!`-level get-set lemmas
-- (`OperationPtr.prev!_createOp`/`…_insertOp?`, etc.), but `createOp`'s effect on an
-- operand owner's *use chain* — `value.setFirstUse` inside `OpOperandPtr.insertIntoCurrent`
-- on the freshly created op's result — is not exposed as a `get!`-level lemma (several
-- operand-record `get!_createOp` lemmas in `Veir/Rewriter/GetSet/CreateOp.lean` are marked
-- "too complex to be expressed"). Closing this needs a `firstUse!`/`results`-projection
-- frame lemma for `createOp`, built from the `.set`/`insertIntoCurrent` primitives, then a
-- field-disjointness argument that `setFirstUse` (on `C`'s result) commutes with
-- `setPrev`/`setNext`/`setParent` (on `C`). That frame layer is the only piece not yet
-- discharged; everything it feeds (no-match cases, the decomposition, `Equiv` + `of_get!`,
-- and the semantic transfer `interpretOp_transport`) is complete and sorry-free.
-/
set_option warn.sorry false in
theorem lowerModArithConstant_match_equiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    {operands props mt} (hda : rewriter.hasDoneAction = false)
    (hop : op.InBounds rewriter.ctx.raw)
    (hparent : (op.get! rewriter.ctx.raw).parent.isSome)
    (hregions : op.getNumRegions! rewriter.ctx.raw = 0)
    (hm : matchOp op rewriter.ctx.raw (.mod_arith .constant) 0 = some (operands, props))
    (hty : ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val = .modArithType mt) :
    PatternResultEquiv
      (ModArithToArithOriginal.lowerModArithConstant rewriter op)
      (lowerModArithConstant rewriter op) := by
  -- TODO(BLOCKED): needs the `insertOp? ; createOp(none) ≃ createOp(none) ; insertOp?`
  -- commutation (up to `IRContext.Equiv`), which in turn needs `get!`-level frame lemmas
  -- for `createOp`'s effect on use chains — the lemma family the get-set library marks
  -- "too complex to be expressed". See the docstring above for the full analysis.
  sorry

/--
**Agreement of the `mod_arith.constant` lowerings.** On a well-formed rewriter
(`hasDoneAction = false`, `op` in bounds with a parent and no regions), the imperative
pattern `ModArithToArithOriginal.lowerModArithConstant` and the recipe pattern
`lowerModArithConstant` agree up to `PatternResultEquiv`: they succeed/fail together and,
on success, produce `Equiv` contexts with equal `hasDoneAction`.

The `hop`/`hparent`/`hregions` hypotheses are exactly the invariants the greedy driver
maintains when it invokes a pattern on an operation drawn from its worklist: the op is a
real, in-bounds op (`hop`) sitting inside a block (`hparent`), and `mod_arith.constant`
takes no regions (`hregions`). They feed the dynamic `dite` checks of the imperative
helpers and the `eraseOp` side conditions.
-/
theorem lowerModArithConstant_equiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (hda : rewriter.hasDoneAction = false)
    (hop : op.InBounds rewriter.ctx.raw)
    (hparent : (op.get! rewriter.ctx.raw).parent.isSome)
    (hregions : op.getNumRegions! rewriter.ctx.raw = 0) :
    PatternResultEquiv
      (ModArithToArithOriginal.lowerModArithConstant rewriter op)
      (lowerModArithConstant rewriter op) := by
  rcases hm : matchOp op rewriter.ctx.raw (.mod_arith .constant) 0 with _ | ⟨operands, props⟩
  · obtain ⟨ho, hr⟩ := lowerModArithConstant_matchOp_none rewriter op hda hm
    rw [ho, hr]; exact PatternResultEquiv.some (WfIRContext.Equiv.refl _) rfl
  · by_cases hty : ∃ mt, ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
        = .modArithType mt
    · obtain ⟨mt, hmt⟩ := hty
      exact lowerModArithConstant_match_equiv rewriter op hda hop hparent hregions hm hmt
    · have hty' : ∀ mt, ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
          ≠ .modArithType mt := fun mt heq => hty ⟨mt, heq⟩
      obtain ⟨ho, hr⟩ := lowerModArithConstant_notModArith rewriter op hda hm hty'
      rw [ho, hr]; exact PatternResultEquiv.some (WfIRContext.Equiv.refl _) rfl

end Veir
