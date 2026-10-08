import Ginzburg333.Comparison.Primitives
import Mathlib.LinearAlgebra.Pi

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem vertexProjection_row (i j : Vertex) (r n : ℕ) (x : rowPathComponent (k := k) j r n) :
    vertexProjection i x.val = if j = i then x.val else 0 := by
  classical
  by_cases he : j = i
  · rw [if_pos he]
    ext p
    by_cases hp : p ∈ x.val.support
    · have hs := (x.property hp).1
      simp [vertexProjection_apply, hs, he]
    · simp [vertexProjection_apply, Finsupp.not_mem_support_iff.mp hp]
  · rw [if_neg he]
    ext p
    by_cases hp : p ∈ x.val.support
    · have hs := (x.property hp).1
      simp [vertexProjection_apply, hs, he]
    · simp [vertexProjection_apply, Finsupp.not_mem_support_iff.mp hp]

def vertexDecompositionEquiv (r n : ℕ) :
    bigradedComponent (k := k) n ((r : ℤ) - (n : ℤ)) ≃ₗ[k]
      ((i : Vertex) → rowPathComponent (k := k) i r n) where
  toFun x i := ⟨vertexProjection i x.val, vertexProjection_row_mem i r n x.val x.property⟩
  invFun y := ⟨∑ i, (y i).val, by
    apply Submodule.sum_mem
    intro i hi
    exact rowPathComponent_bigraded i r n (y i)⟩
  left_inv := by intro x; apply Subtype.ext; exact sum_vertexProjection x.val
  right_inv := by
    intro y
    funext i
    apply Subtype.ext
    change vertexProjection i (∑ j, (y j).val) = (y i).val
    rw [map_sum]
    simp [vertexProjection_row]
  map_add' := by
    intro x y
    funext i
    apply Subtype.ext
    exact map_add (vertexProjection i) x.val y.val
  map_smul' := by
    intro a x
    funext i
    apply Subtype.ext
    exact map_smul (vertexProjection i) a x.val

/-- The finite direct sum of the vertex dual bar terms. -/
abbrev TotalSimpleDual (D : CyclicData k) (r n : ℕ) :=
  (i : Vertex) → Module.Dual k (internallyNormalizedTerm D i ⊤ r n)

/-- Actual fixed-internal-degree term isomorphism with the whole Ginzburg component. -/
def totalDualReversal (D : CyclicData k) (hD : D.Regular) (r n : ℕ) :
    TotalSimpleDual D r n ≃ₗ[k] bigradedComponent (k := k) n ((r : ℤ) - (n : ℤ)) :=
  (LinearEquiv.piCongrRight fun i => finiteDualReversal D hD i r n).trans
    (vertexDecompositionEquiv r n).symm

theorem totalDualReversal_val (D : CyclicData k) (hD : D.Regular) (r n : ℕ)
    (f : TotalSimpleDual D r n) :
    (totalDualReversal D hD r n f).val = ∑ i, (finiteDualReversal D hD i r n (f i)).val := rfl

/-- The term isomorphisms commute with the actual finite-support Ginzburg differential. -/
theorem totalDualReversal_differential (w : Tensor k) (hD : (ofTensor w).Regular) (r n : ℕ)
    (f : TotalSimpleDual (ofTensor w) r n) :
    (totalDualReversal (ofTensor w) hD (r + 1) n
      (fun i => (internallyNormalizedDifferential (ofTensor w) i ⊤ r n).dualMap (f i))).val =
      differential w (totalDualReversal (ofTensor w) hD r n f).val := by
  rw [totalDualReversal_val, totalDualReversal_val, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteDualReversal_differential w hD i r n (f i)
end
end Ginzburg333.Comparison
