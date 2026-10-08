import Ginzburg333.Comparison.Reversal

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

def vertexProjection (i : Vertex) : PathSpace k →ₗ[k] PathSpace k where
  toFun := Finsupp.filter (fun p => p.val.1 = i)
  map_add' := by intro x y; exact Finsupp.filter_add
  map_smul' := by
    intro a x
    ext p
    by_cases hp : p.val.1 = i <;> simp [Finsupp.filter_apply, hp]

@[simp] theorem vertexProjection_apply (i : Vertex) (x : PathSpace k) (p : BasisPath) :
    vertexProjection i x p = if p.val.1 = i then x p else 0 := rfl

@[simp] theorem vertexProjection_single (i : Vertex) (p : BasisPath) (a : k) :
    vertexProjection i (Finsupp.single p a) = if p.val.1 = i then Finsupp.single p a else 0 := by
  classical
  by_cases hp : p.val.1 = i <;> simp [vertexProjection, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg, hp]

theorem vertexProjection_pathTerm (i start : Vertex) (t : k × List Generator)
    (ht : ValidPath (start, t.2)) :
    vertexProjection i (pathTerm start t) = if start = i then pathTerm start t else 0 := by
  classical
  simp [pathTerm, ht]

theorem vertexProjection_basisDifferential (w : Tensor k) (i : Vertex) (p : BasisPath) :
    vertexProjection i (basisDifferential w p) = if p.val.1 = i then basisDifferential w p else 0 := by
  unfold basisDifferential
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  have he : (wordDifferential w p.val.2).map (fun t => vertexProjection i (pathTerm p.val.1 t)) =
      (wordDifferential w p.val.2).map (fun t => if p.val.1 = i then pathTerm p.val.1 t else 0) := by
    apply List.map_congr_left
    intro t ht
    exact vertexProjection_pathTerm i p.val.1 t (differential_term_valid w p ht)
  rw [he]
  by_cases hp : p.val.1 = i <;> simp [hp]

theorem vertexProjection_differential (w : Tensor k) (i : Vertex) (x : PathSpace k) :
    vertexProjection i (differential w x) = differential w (vertexProjection i x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a =>
      by_cases hp : p.val.1 = i <;>
        simp [differential, vertexProjection_basisDifferential, hp]

theorem sum_vertexProjection (x : PathSpace k) : (∑ i, vertexProjection i x) = x := by
  classical
  ext p
  simp [vertexProjection_apply, Finset.sum_apply, eq_comm]

theorem vertexProjection_row_mem (i : Vertex) (r n : ℕ) (x : PathSpace k)
    (hx : x ∈ bigradedComponent (k := k) n ((r : ℤ) - (n : ℤ))) :
    vertexProjection i x ∈ rowPathComponent (k := k) i r n := by
  intro p hp
  have hz : vertexProjection i x p ≠ 0 := Finsupp.mem_support_iff.mp hp
  rw [vertexProjection_apply] at hz
  have hi : p.val.1 = i := by by_contra h; exact hz (if_neg h)
  rw [if_pos hi] at hz
  obtain ⟨hn, hq⟩ := hx (Finsupp.mem_support_iff.mpr hz)
  have he := cohomologicalDegree_eq_length_sub_weight p
  refine ⟨hi, ?_, hn⟩
  omega

theorem rowPath_zero_length (i : Vertex) (n : ℕ) (hn : 0 < n)
    (x : rowPathComponent (k := k) i 0 n) : x.val = 0 := by
  ext p
  by_contra hp
  obtain ⟨hi, hl, hw⟩ := x.property (Finsupp.mem_support_iff.mpr hp)
  have he : p.val.2 = [] := List.length_eq_zero_iff.mp hl
  simp [internalDegree, he] at hw
  omega
end
end Ginzburg333.Comparison
