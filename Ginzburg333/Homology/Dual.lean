import Ginzburg333.Homology.Exact
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exactness of the algebraic dual maps, used separately in each internal degree. -/
namespace Ginzburg333.Homology
variable {k A B C : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

theorem exactAt_dual (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : ExactAt f g) :
    ExactAt g.dualMap f.dualMap := by
  apply (exactAt_iff_range_eq_ker _ _).mpr
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    (exactAt_iff_range_eq_ker f g).mp h]

end Ginzburg333.Homology
