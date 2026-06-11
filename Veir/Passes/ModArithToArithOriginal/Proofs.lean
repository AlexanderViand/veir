import Veir.Passes.ModArithToArith
import Veir.Passes.ModArithToArith.Proofs
import Veir.Passes.ModArithToArithOriginal

/-!
# Imperative-style lowering vs. the verified recipe-based patterns

This file relates the imperative `PatternRewriter`-style lowering
(`Veir.ModArithToArithOriginal`) to the verified recipe-based lowering
(`Veir.ModArithToArith`).

## Status: blocked on a statement-level (data-structure) issue

The intended deliverable was a per-op *structural* equality

```
ModArithToArithOriginal.lowerModArithAddOp rewriter op = lowerModArithAddOp rewriter op
```

(and likewise for Sub / Mul / Constant), where equality is structural (`Eq`) equality of
the `PatternRewriter` record — in particular structural equality of the underlying
`WfIRContext` / `IRContext`, whose fields are `Std.HashMap`s.

That equality is **not provable as stated** for a fundamental data-structure reason.
The two passes insert exactly the same keys with the same final values into
`IRContext.operations`, but in **different orders**:

* the recipe pass (`ModArithToArith.buildOps` + `RewritePattern.fromLocalRewrite`)
  creates *all* new operations detached first (`WfRewriter.createOp ... none`), and only
  afterwards runs the insert-loop that rewires the surrounding linked list
  (`PatternRewriter.insertOp` at `InsertPoint.before op`), the value replacement and the
  erase;
* the imperative pass interleaves creation and insertion: every helper does
  `PatternRewriter.createOp ... (some (InsertPoint.before op))`, i.e. it allocates the
  fresh op *and immediately* rewires the neighbours, before allocating the next op.

`Std.HashMap` equality is **not** insertion-order invariant up to `Eq` *as a theorem the
library exposes*: the public API only provides an *extensional equivalence* relation
(`Std.HashMap.Equiv`, notation `~m`) plus `Decidable`/lemma support for it. There is no
`Eq`-valued `insert_comm` / `insert_insert` reordering lemma — proving one for arbitrary
keys would require reasoning about `reinsertAux` and the concrete bucket layout, i.e. the
internal representation, which the library deliberately keeps opaque. (Empirically the two
resulting maps *do* coincide structurally on concrete inputs, because every interleaved
re-insert touches an already-present key and so preserves the bucket layout; but there is
no `Eq`-level lemma to discharge this, so the structural equality is — at best —
true-but-not-provable with the available infrastructure, and unprovable in general for the
HashMap API as exposed.) The two passes therefore produce `IRContext`s that are
`~m`-equivalent (equal under every `getElem?` and every getter, so they denote the very
same IR) but cannot be shown `Eq`.

This is the same reason the existing `ModArithToArith` correctness proof is phrased as
`LocalRewritePattern.PreservesSemantics` (agreement of interpreter results) rather than
as context equality: structural ctx equality is the wrong — and here unprovable —
notion.

### What a correct statement needs (out of scope: header-fenced)

A provable "the two passes agree" statement requires one of:

1. an *extensional* `IRContext` equivalence (agreement of all getters / `getElem?`), used
   in place of `Eq` in the theorem statements; or
2. switching the IR's `Std.HashMap`s to `Std.ExtHashMap` (which is extensional and has
   `insert_comm`), after which the operation-commutation argument sketched below closes.

Either is a statement / architecture change, so this file records the genuinely reusable
building block the alignment proof is built on — the `createOp`-with-insertion-point
decomposition, which *is* a structural equality — and documents the blocker for a future
redraft.

## The reusable building block

`Rewriter.createOp` with an insertion point is, by construction (see
`Veir/Rewriter/Basic.lean`), the detached `createOp` (insertion point `none`) followed by
`Rewriter.insertOp?` at that point. This is the decomposition that turns the imperative
"create-then-insert inline" shape into the recipe "create-all-then-insert-all" shape, and
it holds as a structural equality (no `Std.HashMap` reordering is involved — it is the
same computation split at the final `match insertionPoint`).
-/

namespace Veir

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

end Veir
