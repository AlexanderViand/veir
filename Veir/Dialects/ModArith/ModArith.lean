import Veir.Interpreter

namespace Veir.Dialects.ModArith

/--
  Barrett reduction requires that the input value is less than `m^2` and that `m > 0`.
-/
def BarretPrecondition (m x k : Nat) : Prop :=
  0 < m ∧ x < m * m ∧ 2 ^ k > m

/--
  Barrett-reducing a value in [0, m^2) should yield a value in [0, 2m)
   that is either `x mod m` or `x mod m + m`.
-/
def BarrettReduceSpec (m x k r : Nat) : Prop :=
    BarretPrecondition m x k →
    (r = x % m ∨ r = x % m + m)

/--
  If a value is Barrett-reduced,
  the result is less than twice the modulus.
-/
theorem BarretReduceSpecImpliesLt2q (m x k r : Nat) :
  (BarretPrecondition m x k ∧
  BarrettReduceSpec m x k r ) →
    r < 2 * m := by
    rintro ⟨hBounds, hSpec⟩
    have hOr := hSpec hBounds
    have hlt := Nat.mod_lt x hBounds.left
    omega

theorem barrettReduceStepNatCorrect (m x k : Nat) :
  ∀ output, barrettReduceStepNat m x k = output  →
    BarrettReduceSpec m x k output := by
    -- intro output hOutput
    -- simp [BarrettReduceSpec, BarretPrecondition]
    -- intro h0 hmm
    -- unfold barrettReduceStepNat at hOutput
    unfold barrettReduceStepNat BarrettReduceSpec BarretPrecondition
    simp
    -- grind [Nat.mod_def, Nat.div_eq_sub_mod_div]
    sorry
