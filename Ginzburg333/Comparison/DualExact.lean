import Ginzburg333.Bar.SimpleDifferential
import Ginzburg333.Homology.Dual

/-! Off-diagonal exactness for actual finite internal-degree dual bar terms. -/
namespace Ginzburg333.Comparison
open Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

set_option maxHeartbeats 2000000 in
theorem simple_dual_bar_off_diagonal [IsAlgClosed k] (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (r n : ℕ) (hne : n ≠ r + 1) :
    Homology.ExactAt (k := k)
      (A := Module.Dual k (internallyNormalizedTerm D i ⊤ r n))
      (B := Module.Dual k (internallyNormalizedTerm D i ⊤ (r + 1) n))
      (C := Module.Dual k (internallyNormalizedTerm D i ⊤ (r + 1 + 1) n))
      (internallyNormalizedDifferential D i ⊤ r n).dualMap
      (internallyNormalizedDifferential D i ⊤ (r + 1) n).dualMap := by
  have h := simple_normalized_bar_off_diagonal D hD i (r + 1) n hne
  simp only [BarExact, chainDifferential_succ] at h
  exact Homology.exactAt_dual (k := k)
    (A := internallyNormalizedTerm D i ⊤ (r + 1 + 1) n)
    (B := internallyNormalizedTerm D i ⊤ (r + 1) n)
    (C := internallyNormalizedTerm D i ⊤ r n)
    (internallyNormalizedDifferential D i ⊤ (r + 1) n)
    (internallyNormalizedDifferential D i ⊤ r n)
    h
end
end Ginzburg333.Comparison
