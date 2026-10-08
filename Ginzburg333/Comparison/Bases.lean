import Ginzburg333.Comparison.Primitives
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Ginzburg333.Comparison
variable {k : Type*} [Field k]
variable {X Y Z : Type*} [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
noncomputable section

def tripleFunctionEquiv : ((((Fin 3 × Fin 3) × Fin 3) → k)) ≃ₗ[k] Tensor k where
  toFun f a b c := f ((a, b), c)
  invFun f abc := f abc.1.1 abc.1.2 abc.2
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; rfl
  map_smul' := by intro a f; rfl

/-- The three factors remain independent modules with independent bases. -/
def tensorCoordinatesEquiv (bx : Basis (Fin 3) k X) (by_ : Basis (Fin 3) k Y)
    (bz : Basis (Fin 3) k Z) :
    TensorProduct k (TensorProduct k X Y) Z ≃ₗ[k] Tensor k :=
  ((bx.tensorProduct by_).tensorProduct bz).repr.trans
    ((Finsupp.linearEquivFunOnFinite k k ((Fin 3 × Fin 3) × Fin 3)).trans tripleFunctionEquiv)

theorem tensorCoordinatesEquiv_apply (bx : Basis (Fin 3) k X) (by_ : Basis (Fin 3) k Y)
    (bz : Basis (Fin 3) k Z) (w : TensorProduct k (TensorProduct k X Y) Z)
    (a b c : Fin 3) :
    tensorCoordinatesEquiv bx by_ bz w a b c =
      ((bx.tensorProduct by_).tensorProduct bz).repr w ((a, b), c) := rfl

theorem tensorRegular_ginzburgRegular_in_bases [IsAlgClosed k] [CharZero k]
    (bx : Basis (Fin 3) k X) (by_ : Basis (Fin 3) k Y) (bz : Basis (Fin 3) k Z)
    (w : TensorProduct k (TensorProduct k X Y) Z)
    (hw : TensorRegular (tensorCoordinatesEquiv bx by_ bz w)) :
    Ginzburg.GinzburgRegular (tensorCoordinatesEquiv bx by_ bz w) :=
  Ginzburg333.tensorRegular_ginzburgRegular _ hw

variable [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]

def chosenTensorCoordinates (hx : Module.finrank k X = 3) (hy : Module.finrank k Y = 3)
    (hz : Module.finrank k Z = 3) :
    TensorProduct k (TensorProduct k X Y) Z ≃ₗ[k] Tensor k :=
  tensorCoordinatesEquiv (Module.finBasisOfFinrankEq k X hx)
    (Module.finBasisOfFinrankEq k Y hy) (Module.finBasisOfFinrankEq k Z hz)
theorem tensorRegular_ginzburgRegular_chosen_bases [IsAlgClosed k] [CharZero k]
    (hx : Module.finrank k X = 3) (hy : Module.finrank k Y = 3) (hz : Module.finrank k Z = 3)
    (w : TensorProduct k (TensorProduct k X Y) Z)
    (hw : TensorRegular (chosenTensorCoordinates hx hy hz w)) :
    Ginzburg.GinzburgRegular (chosenTensorCoordinates hx hy hz w) :=
  Ginzburg333.tensorRegular_ginzburgRegular _ hw

end
end Ginzburg333.Comparison
