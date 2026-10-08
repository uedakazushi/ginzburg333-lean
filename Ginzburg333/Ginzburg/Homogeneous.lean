import Ginzburg333.Ginzburg.Words

/-! Homogeneity of the finite-support differential, on actual path vectors. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem pathTerm_mem_supported (S : Set BasisPath) (start : Vertex)
    (t : k × List Generator)
    (hS : ∀ h : ValidPath (start, t.2), (⟨(start, t.2), h⟩ : BasisPath) ∈ S) :
    pathTerm start t ∈ Finsupp.supported k k S := by
  classical
  unfold pathTerm
  split_ifs with h
  · exact Finsupp.single_mem_supported k t.1 (hS h)
  · exact Submodule.zero_mem _

theorem list_sum_mem_submodule (H : Submodule k (PathSpace k)) (xs : List (PathSpace k))
    (h : ∀ x ∈ xs, x ∈ H) : xs.sum ∈ H := by
  induction xs with
  | nil => exact H.zero_mem
  | cons x xs ih =>
      exact H.add_mem (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem basisDifferential_mem_supported (w : Tensor k) (p : BasisPath) (S : Set BasisPath)
    (hS : ∀ t ∈ wordDifferential w p.val.2, ∀ h : ValidPath (p.val.1, t.2),
      (⟨(p.val.1, t.2), h⟩ : BasisPath) ∈ S) :
    basisDifferential w p ∈ Finsupp.supported k k S := by
  apply list_sum_mem_submodule
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact pathTerm_mem_supported S p.val.1 t (hS t ht)

theorem basisDifferential_internal (w : Tensor k) (p : BasisPath) :
    InternallyHomogeneous (internalDegree p) (basisDifferential w p) := by
  change basisDifferential w p ∈ Finsupp.supported k k {a | internalDegree a = internalDegree p}
  apply basisDifferential_mem_supported
  intro t ht h
  exact (wordDifferential_degrees w p.val.2 ht).1

theorem basisDifferential_cohomological (w : Tensor k) (p : BasisPath) :
    Homogeneous (cohomologicalDegree p + 1) (basisDifferential w p) := by
  change basisDifferential w p ∈ Finsupp.supported k k {a | cohomologicalDegree a = cohomologicalDegree p + 1}
  apply basisDifferential_mem_supported
  intro t ht h
  have hn := (wordDifferential_degrees w p.val.2 ht).2
  change -(wordNegative t.2 : ℤ) = -(wordNegative p.val.2 : ℤ) + 1
  omega

theorem differential_internal (w : Tensor k) (n : ℕ) (x : PathSpace k)
    (hx : InternallyHomogeneous n x) : InternallyHomogeneous n (differential w x) := by
  classical
  let H : Submodule k (PathSpace k) := Finsupp.supported k k {a | internalDegree a = n}
  change x.support.sum (fun p => x p • basisDifferential w p) ∈ H
  apply H.sum_mem
  intro p hp
  apply H.smul_mem
  have h := basisDifferential_internal w p
  rw [hx p hp] at h
  exact h

theorem differential_cohomological (w : Tensor k) (q : ℤ) (x : PathSpace k)
    (hx : Homogeneous q x) : Homogeneous (q + 1) (differential w x) := by
  classical
  let H : Submodule k (PathSpace k) := Finsupp.supported k k {a | cohomologicalDegree a = q + 1}
  change x.support.sum (fun p => x p • basisDifferential w p) ∈ H
  apply H.sum_mem
  intro p hp
  apply H.smul_mem
  have h := basisDifferential_cohomological w p
  rw [hx p hp] at h
  exact h

end
end Ginzburg333.Ginzburg
