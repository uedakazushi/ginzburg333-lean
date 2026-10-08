import Ginzburg333.Converse.Representation

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 4000000


theorem sum_cycle_three {A B C M : Type*} [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) : (∑ x, ∑ y, ∑ z, f x y z) = ∑ z, ∑ x, ∑ y, f x y z := by
  calc
    _ = ∑ x, ∑ z, ∑ y, f x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem sum_reverse_three {A B C M : Type*} [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) : (∑ x, ∑ y, ∑ z, f x y z) = ∑ z, ∑ y, ∑ x, f x y z := by
  rw [sum_cycle_three]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_comm]

def reverseMatrixSum (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (j : Vertex) (b : Fin 3) : CornerMatrix k :=
  ∑ x, ∑ y, coeff w j b x y •
    (forwardMatrix w i a d (next (next j)) y * forwardMatrix w i a d (next j) x)

theorem reverseMatrixSum_same (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) : reverseMatrixSum w i a d i b = 0 := by
  simp only [reverseMatrixSum, forwardMatrix_prev, forwardMatrix_next, zMatrix_mul_yMatrix,
    ← tensorOutput_expand]
  have hz := congrArg (fun v => matrixUnit (k := k) 3 0 (freeLetterMap v)) (d.first_relations b)
  simpa only [map_sum, map_smul, map_zero] using hz

theorem reverseMatrixSum_next (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) : reverseMatrixSum w i a d (next i) b = 0 := by
  simp only [reverseMatrixSum, next_three, forwardMatrix_same, forwardMatrix_prev, coeff_next,
    xMatrix_mul_zMatrix]
  have he : (∑ x : Fin 3, ∑ y : Fin 3, coeff w i y b x •
      (∑ h : Fin 2, a y • matrixUnit (k := k) 0 (smallIndex h)
        (freeLetterMap (d.output (smallUnit h ⊗ₜ[k] d.right (unitVec x)))))) =
      ∑ h : Fin 2, matrixUnit (k := k) 0 (smallIndex h)
        (freeLetterMap (∑ y : Fin 3, ∑ x : Fin 3,
          (a y * coeff w i y b x) • d.output (smallUnit h ⊗ₜ[k] d.right (unitVec x)))) := by
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [sum_reverse_three]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm]
  rw [he]
  simp only [d.second_relations, map_zero, Finset.sum_const_zero]

theorem reverseMatrixSum_prev (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) : reverseMatrixSum w i a d (next (next i)) b = 0 := by
  simp only [reverseMatrixSum, next_three, forwardMatrix_same, forwardMatrix_next, coeff_prev,
    yMatrix_mul_xMatrix]
  have he : (∑ x : Fin 3, ∑ y : Fin 3, coeff w i x y b •
      (∑ h : Fin 2, (a x * d.left (unitVec y) h) • matrixUnit (k := k) (smallIndex h) 3 1)) =
      ∑ h : Fin 2, (∑ x : Fin 3, ∑ y : Fin 3,
        (a x * coeff w i x y b) * d.left (unitVec y) h) • matrixUnit (k := k) (smallIndex h) 3 1 := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [sum_cycle_three]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    ring
  rw [he]
  apply Finset.sum_eq_zero
  intro h hh
  have hz := congrArg (fun v : SmallVec k => v h) (d.third_relations b)
  have hc : (∑ x : Fin 3, ∑ y : Fin 3, (a x * coeff w i x y b) * d.left (unitVec y) h) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hz
  rw [hc, zero_smul]

theorem reverseMatrixSum_zero (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (j : Vertex) (b : Fin 3) : reverseMatrixSum w i a d j b = 0 := by
  have hj : j = i ∨ j = next i ∨ j = next (next i) := by fin_cases i <;> fin_cases j <;> decide
  rcases hj with hj | hj | hj
  · rw [hj]; exact reverseMatrixSum_same w i a d b
  · rw [hj]; exact reverseMatrixSum_next w i a d b
  · rw [hj]; exact reverseMatrixSum_prev w i a d b

theorem matrixEvaluation_generator_differential (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (g : Generator) :
    matrixEvaluation w i a d (wordVectorDifferential w [g]) = 0 := by
  cases g with
  | forward j b => rw [Comparison.forward_generator_vector, map_zero]
  | reverse j b =>
      rw [Comparison.reverse_generator_vector]
      simp only [map_sum, map_smul, matrixEvaluation_single, matrixWord, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, generatorMatrix, one_smul, mul_one]
      exact reverseMatrixSum_zero w i a d j b
  | loop j =>
      rw [Comparison.loop_generator_vector]
      simp [map_sum, matrixEvaluation_single, matrixWord, generatorMatrix]
end
end Ginzburg333.Converse
