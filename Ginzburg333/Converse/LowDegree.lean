import Ginzburg333.Comparison.Generators
import Ginzburg333.Ginzburg.Complex

namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

/-- A nonempty path has strictly more internal weight than negative degree. -/
theorem homogeneous_eq_zero_of_internal_bound (n : ℕ) (hn : 0 < n) (q : ℤ)
    (hq : q + (n : ℤ) ≤ 0) (x : PathSpace k)
    (hi : InternallyHomogeneous n x) (hc : Homogeneous q x) : x = 0 := by
  classical
  ext p
  by_cases hp : p ∈ x.support
  · have hn0 := hi p hp
    have hq0 := hc p hp
    rw [cohomologicalDegree_eq_length_sub_weight, hn0] at hq0
    have hl : p.val.2.length = 0 := by omega
    have he := List.length_eq_zero_iff.mp hl
    simp [internalDegree, he] at hn0
    omega
  · exact Finsupp.not_mem_support_iff.mp hp

def reversePath (i : Vertex) (a : Fin 3) : BasisPath :=
  ⟨(next i, [.reverse i a]), by simp [ValidPath, endpoint?, Generator.source]⟩

theorem reversePath_injective (i : Vertex) : Function.Injective (reversePath i) := by
  intro a b h
  have he := congrArg (fun p : BasisPath => p.val.2) h
  simpa [reversePath] using he

def reverseEmbedding (i : Vertex) : Vec k →ₗ[k] PathSpace k where
  toFun a := ∑ j, a j • Finsupp.single (reversePath i j) 1
  map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro t a; simp [Finset.smul_sum, smul_smul]

theorem reverseEmbedding_coefficient (i : Vertex) (a : Vec k) (j : Fin 3) :
    reverseEmbedding i a (reversePath i j) = a j := by
  classical
  simp [reverseEmbedding, Finsupp.single_apply, (reversePath_injective i).eq_iff]

theorem reverseEmbedding_injective (i : Vertex) : Function.Injective (reverseEmbedding (k := k) i) := by
  intro a b h
  funext j
  simpa only [reverseEmbedding_coefficient] using congrArg (fun x : PathSpace k => x (reversePath i j)) h

theorem reverseEmbedding_homogeneous (i : Vertex) (a : Vec k) :
    InternallyHomogeneous 2 (reverseEmbedding i a) ∧ Homogeneous (-1) (reverseEmbedding i a) := by
  classical
  have hmem : reverseEmbedding i a ∈ bigradedComponent (k := k) 2 (-1) := by
    change (∑ j, a j • Finsupp.single (reversePath i j) 1) ∈ bigradedComponent (k := k) 2 (-1)
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Finsupp.single_mem_supported
    simp [reversePath, internalDegree, cohomologicalDegree, Generator.weight, Generator.negativeDegree]
  exact (mem_bigradedComponent _ _ _).mp hmem

theorem contraction_zero_coefficients (w : Tensor k) (i : Vertex) (a : Vec k)
    (h : (ofTensor w).mul i a = 0) (b c : Fin 3) :
    (∑ j, a j * coeff w i j b c) = 0 := by
  have he := congrArg (fun f : Vec k →ₗ[k] Vec k => f (unitVec b) c) h
  simpa [ofTensor, contraction, contract, unitVec, mul_comm] using he

theorem reverseEmbedding_closed (w : Tensor k) (i : Vertex) (a : Vec k)
    (h : (ofTensor w).mul i a = 0) : differential w (reverseEmbedding i a) = 0 := by
  classical
  apply forgetPathValidity_injective
  rw [forgetPathValidity_differential, map_zero]
  change locatedDifferential w (forgetPathValidity (∑ j, a j • Finsupp.single (reversePath i j) 1)) = 0
  simp only [map_sum, map_smul, forgetPathValidity_single, locatedDifferential_single,
    reversePath, one_smul, Comparison.reverse_generator_vector]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c hc
  rw [← Finset.sum_smul]
  rw [contraction_zero_coefficients w i a h b c, zero_smul]

/-- This excludes rank zero, but does not yet exclude rank one. -/
theorem ginzburgRegular_contraction_ne_zero (w : Tensor k) (hw : GinzburgRegular w)
    (i : Vertex) (a : Vec k) (ha : a ≠ 0) : (ofTensor w).mul i a ≠ 0 := by
  intro hz
  let x := reverseEmbedding i a
  obtain ⟨y, hyq, hdy⟩ := hw (-1) (by omega) x
    (reverseEmbedding_homogeneous i a).2 (reverseEmbedding_closed w i a hz)
  have hpy : internalProjection 2 y = 0 :=
    homogeneous_eq_zero_of_internal_bound 2 (by omega) (-2) (by omega) _
      (internalProjection_internal 2 y) (internalProjection_cohomological 2 (-2) y hyq)
  have hx : x = 0 := by
    have hxproj : internalProjection 2 x = x :=
      internalProjection_eq_self 2 x (reverseEmbedding_homogeneous i a).1
    rw [← hxproj, ← hdy, internalProjection_differential, hpy, map_zero]
  apply ha
  exact reverseEmbedding_injective i (hx.trans (map_zero (reverseEmbedding i)).symm)
end
end Ginzburg333.Ginzburg
