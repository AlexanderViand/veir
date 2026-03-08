import Veir.Interpreter

namespace Veir.Dialects.ModArith

/--
  Barrett reduction requires that the input value is less than `m^2` and that `m > 0`.
-/
def BarretPrecondition (m x : Nat) : Prop :=
  0 < m ∧ x < m * m

/--
  Barrett-reducing a value in [0, m^2) should yield a value in [0, 2m)
   that is either `x mod m` or `x mod m + m`.
-/
def BarrettReduceSpec (m x r : Nat) : Prop :=
    BarretPrecondition m x →
    (r = x % m ∨ r = x % m + m)

/--
  If a value is Barrett-reduced,
  the result is less than twice the modulus.
-/
theorem BarretReduceSpecImpliesLt2q (m x r : Nat) :
  (BarretPrecondition m x ∧
  BarrettReduceSpec m x r ) →
    r < 2 * m := by
    rintro ⟨hBounds, hSpec⟩
    have hOr := hSpec hBounds
    have hlt := Nat.mod_lt x hBounds.left
    grind

-- theorem AssumingQ (m x r : Nat) :
--   ∀ m x:
--   let bitWidth := natBitLength (m - 1)
--   let k := 2 * bitWidth
--   let mu := ((1 : Nat) <<< k) / m
--   let q := (a * mu) >>> k
--   BarretPrecondition m x → ((q = x / m) ∨ (q = x/m)) := by
--   sorry

theorem barrettReduceStepNatCorrect (m x output : Nat) :
    barrettReduceStepNat m x = output  →
    BarrettReduceSpec m x output := by
    intro h
    simp [BarrettReduceSpec, BarretPrecondition]
    intro h0 hmm
    unfold barrettReduceStepNat at h
    /- We need to show that the weird shift division hack is the same. -/
    /- lets focus first on the precomputed constant, mu? -/
    /- we have mu = 2^(2w) / m which is what?  -/
    /- if m = 222 and bw=8, then we have 2^16/222 = 65k/222 = 295.something ??-/
    /- Now we take x*295 and shift down by 2w? -/
    /- effectively, we divide by 2^2w = 2^16 again?-/
    /- lets say x = 333 --> 98235/2^15 i.e. 65536 gives 1.49 for q?-/
    /- now we compute x - 1 * m and oh boy, it worked! -/
    /- so when do we end up in +m range? -/
    /- basically, in the nice case, q is exactly x/m floordiv? -/
    /- and in the not so nice case, x/m floordiv + 1 ? -/
    /- Basically, we look at 2^(log2(m)/m) basically,  -/
    sorry

theorem barretReduceFullCorrect (m x : Nat) :
∀ output : Nat, ∀ y : Nat,
  (BarretPrecondition m x ∧ barrettReduceStepNat m x = y ∧ subifgeNat m y = output) →
  output = x % m := by
  intro output y h
  have hPre := h.left
  have hStep := h.right.left
  have hSubIfge := h.right.right
  sorry
