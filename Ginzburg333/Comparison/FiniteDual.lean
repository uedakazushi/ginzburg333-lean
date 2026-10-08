import Ginzburg333.Bar.SimpleCoordinates
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Finite internal-degree duals of the actual simple-row normalized terms. -/
namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

abbrev SimpleRowBasis (i : Vertex) (r n : ℕ) :=
  {gs : List Generator // startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}

instance finite_simpleRowBasis (i : Vertex) (r n : ℕ) : Finite (SimpleRowBasis i r n) := by
  let f : SimpleRowBasis i r n → {gs : List Generator // gs.length = r} :=
    fun gs => ⟨gs.val, gs.property.2.1⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : {gs : List Generator // gs.length = r} => z.val) h

@[irreducible] def simpleBarLinearBasis (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    Basis (SimpleRowBasis i r n) k (internallyNormalizedTerm D i ⊤ r n) :=
  Finsupp.basisSingleOne.map
    ((Finsupp.supportedEquivFinsupp {gs : List Generator | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm.trans
      (simpleBarCoordinatesEquiv D hD i r n).symm)

def basisDualCoordinates {ι M : Type*} [AddCommGroup M] [Module k M] [Finite ι]
    (b : Basis ι k M) : Module.Dual k M ≃ₗ[k] (ι →₀ k) := by
  classical
  exact (Basis.dualBasis (R := k) (M := M) b).repr

theorem basisDualCoordinates_apply {ι M : Type*} [AddCommGroup M] [Module k M] [Finite ι]
    (b : Basis ι k M) (f : Module.Dual k M) (j : ι) : basisDualCoordinates b f j = f (b j) := by
  classical
  exact Basis.dualBasis_repr (R := k) (M := M) b f j

/-- Duals are taken for fixed (r,n), never for the unrestricted bar direct sum. -/
def simpleBarDualCoordinates (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    Module.Dual k (internallyNormalizedTerm D i ⊤ r n) ≃ₗ[k] (SimpleRowBasis i r n →₀ k) :=
  basisDualCoordinates (k := k) (M := internallyNormalizedTerm D i ⊤ r n)
    (simpleBarLinearBasis D hD i r n)

theorem simpleBarDualCoordinates_apply (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (f : Module.Dual k (internallyNormalizedTerm D i ⊤ r n)) (gs : SimpleRowBasis i r n) :
    simpleBarDualCoordinates D hD i r n f gs = f (simpleBarLinearBasis D hD i r n gs) := by
  simp only [simpleBarDualCoordinates, basisDualCoordinates_apply]
end
end Ginzburg333.Comparison
