import Ginzburg333.Bar.SimpleCoordinates

/-! The differential in scalar coordinates for the actual simple-row bar. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem tensorWords_scalar (x : WordSpace k) (a : k) : tensorWords x a = a • x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add]
  | single gs b => simp [Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem simple_bar_differential_coordinates (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (x : Ambient (D.QuotientRow i ⊤)) :
    coefficientMap (simpleCoefficient D hD i) (ambientDifferential (quotientRightAction D i ⊤) x) =
      innerDifferential D (coefficientMap (simpleCoefficient D hD i) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs m =>
      rw [ambientDifferential_single, coefficientMap_single]
      cases gs with
      | nil => simp [onWord, innerDifferential, innerBasisDifferential]
      | cons g gs =>
          change coefficientMap (simpleCoefficient D hD i)
            (-Finsupp.single gs (D.quotientAction i ⊤ (positiveBasis g) m) +
              tensorWords (innerBasisDifferential D (g :: gs)) m) = _
          rw [simpleRow_positive_action D hD, Finsupp.single_zero, neg_zero, zero_add,
            coefficientMap_tensorWords, tensorWords_scalar]
          simp [innerDifferential]

theorem simpleScalarMap_differential (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (r n : ℕ) (x : internallyNormalizedTerm D i ⊤ (r + 1) n) :
    (simpleScalarMap D hD i r n (internallyNormalizedDifferential D i ⊤ r n x)).val =
      innerDifferential D (simpleScalarMap D hD i (r + 1) n x).val :=
  simple_bar_differential_coordinates D hD i x.val
end
end Ginzburg333.Bar
