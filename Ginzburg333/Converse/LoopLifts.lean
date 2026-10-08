import Ginzburg333.Converse.WordMap

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 4000000

theorem vecTensor_expansion (t : TensorProduct k (Vec k) (Vec k)) :
    ∃ r : Fin 3 → Fin 3 → k, (∑ b, ∑ c, r b c • (unitVec b ⊗ₜ[k] unitVec c)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v u =>
      refine ⟨fun b c => v b * u c, ?_⟩
      conv_rhs => rw [← sum_unitVec v, ← sum_unitVec u, TensorProduct.sum_tmul]
      simp only [TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      refine ⟨r + s, ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hr, hs]

def originalOutput (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) :
    TensorProduct k (Vec k) (Vec k) →ₗ[k] SmallVec k :=
  d.output.comp (TensorProduct.map d.left d.right)

theorem originalOutput_surjective (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) :
    Function.Surjective (originalOutput w i a d) :=
  d.output_surjective.comp (TensorProduct.map_surjective d.left_surjective d.right_surjective)

theorem outputCoefficients_exists (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (j : Fin 2) : ∃ r : Fin 3 → Fin 3 → k,
    (∑ b, ∑ c, r b c • d.output (d.left (unitVec b) ⊗ₜ[k] d.right (unitVec c))) = smallUnit j := by
  obtain ⟨t, ht⟩ := originalOutput_surjective w i a d (smallUnit j)
  obtain ⟨r, hr⟩ := vecTensor_expansion t
  refine ⟨r, ?_⟩
  have he := congrArg (originalOutput w i a d) hr
  rw [ht] at he
  simpa only [map_sum, map_smul, originalOutput, LinearMap.comp_apply, TensorProduct.map_tmul] using he

def loopTriple (i : Vertex) (a0 b c : Fin 3) : List Generator :=
  [.forward i a0, .forward (next (next i)) c, .forward (next i) b]

theorem loopTriple_closed (i : Vertex) (a0 b c : Fin 3) :
    endpoint? (next i) (loopTriple i a0 b c) = some (next i) ∧
      wordWeight (loopTriple i a0 b c) = 3 ∧ wordNegative (loopTriple i a0 b c) = 0 := by
  simp [loopTriple, endpoint?, Generator.source, Generator.target, wordWeight, wordNegative,
    Generator.weight, Generator.negativeDegree]

theorem loopTriple_matrix (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (a0 b c : Fin 3) : matrixWord w i a d (loopTriple i a0 b c) =
      a a0 • matrixUnit 0 0 (freeLetterMap (d.output (d.left (unitVec b) ⊗ₜ[k] d.right (unitVec c)))) := by
  simp only [loopTriple, matrixWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    generatorMatrix, mul_one, forwardMatrix_same, forwardMatrix_prev, forwardMatrix_next,
    zMatrix_mul_yMatrix, ← tensorOutput_expand]
  simp [xMatrix, smul_mul_assoc, matrixUnit_mul]

def loopWordVector (i : Vertex) (a0 : Fin 3) (r : Fin 3 → Fin 3 → k) : WordSpace k :=
  ∑ b, ∑ c, r b c • Finsupp.single (loopTriple i a0 b c) 1

theorem loopWordVector_closed (i : Vertex) (a0 : Fin 3) (r : Fin 3 → Fin 3 → k) :
    loopWordVector i a0 r ∈ closedWords (next i) 3 := by
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported k 1 (loopTriple_closed i a0 b c)

theorem loopWordVector_matrix (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (a0 : Fin 3) (r : Fin 3 → Fin 3 → k) : matrixEvaluation w i a d (loopWordVector i a0 r) =
      a a0 • matrixUnit 0 0 (freeLetterMap (∑ b, ∑ c, r b c • d.output
        (d.left (unitVec b) ⊗ₜ[k] d.right (unitVec c)))) := by
  simp only [loopWordVector, map_sum, map_smul, matrixEvaluation_single, one_smul,
    loopTriple_matrix, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  ring

theorem freeLetterMap_smallUnit (j : Fin 2) :
    freeLetterMap (smallUnit (k := k) j) = MonoidAlgebra.single (FreeMonoid.of j) 1 := by
  fin_cases j <;> simp [freeLetterMap, smallUnit]

theorem liftLoop_exists (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (a0 : Fin 3) (ha0 : a a0 ≠ 0) (j : Fin 2) : ∃ x : WordSpace k,
    x ∈ closedWords (next i) 3 ∧
      matrixEvaluation w i a d x = matrixUnit 0 0 (MonoidAlgebra.single (FreeMonoid.of j) 1) := by
  obtain ⟨r, hr⟩ := outputCoefficients_exists w i a d j
  refine ⟨(a a0)⁻¹ • loopWordVector i a0 r, (closedWords (next i) 3).smul_mem _ (loopWordVector_closed i a0 r), ?_⟩
  rw [map_smul, loopWordVector_matrix, hr, freeLetterMap_smallUnit, smul_smul, inv_mul_cancel₀ ha0, one_smul]

structure LoopLiftData (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) where
  word : Fin 2 → WordSpace k
  closed : ∀ j, word j ∈ closedWords (next i) 3
  matrix : ∀ j, matrixEvaluation w i a d (word j) = matrixUnit 0 0 (MonoidAlgebra.single (FreeMonoid.of j) 1)

theorem loopLiftData_exists (w : Tensor k) (i : Vertex) (a : Vec k) (ha : a ≠ 0)
    (d : FreeCornerData w i a) : Nonempty (LoopLiftData w i a d) := by
  classical
  have hex : ∃ a0, a a0 ≠ 0 := by
    by_contra! hh
    exact ha (funext hh)
  obtain ⟨a0, ha0⟩ := hex
  have hl (j : Fin 2) := liftLoop_exists w i a d a0 ha0 j
  choose x hx hm using hl
  exact ⟨⟨x, hx, hm⟩⟩

def liftFreeWord {w : Tensor k} {i : Vertex} {a : Vec k} {d : FreeCornerData w i a}
    (L : LoopLiftData w i a d) : List (Fin 2) → WordSpace k
  | [] => Finsupp.single [] 1
  | j :: js => concatenate (L.word j) (liftFreeWord L js)

theorem liftFreeWord_closed {w : Tensor k} {i : Vertex} {a : Vec k} {d : FreeCornerData w i a}
    (L : LoopLiftData w i a d) (js : List (Fin 2)) :
    liftFreeWord L js ∈ closedWords (next i) (3 * js.length) := by
  induction js with
  | nil => exact closedWords_nil (next i)
  | cons j js ih =>
      have h := closedWords_concatenate (next i) 3 (3 * js.length) _ _ (L.closed j) ih
      simpa only [liftFreeWord, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h

theorem liftFreeWord_matrix {w : Tensor k} {i : Vertex} {a : Vec k} {d : FreeCornerData w i a}
    (L : LoopLiftData w i a d) (js : List (Fin 2)) :
    matrixEvaluation w i a d (liftFreeWord L js) = if js = [] then 1 else
      matrixUnit 0 0 (MonoidAlgebra.single (FreeMonoid.ofList js) 1) := by
  induction js with
  | nil => simp [liftFreeWord, matrixWord]
  | cons j js ih =>
      rw [liftFreeWord, matrixEvaluation_concatenate, L.matrix, ih]
      cases js with
      | nil => simp [FreeMonoid.ofList_singleton]
      | cons h hs => simp [matrixUnit_mul, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_cons]
theorem liftFreeWord_entry00 {w : Tensor k} {i : Vertex} {a : Vec k} {d : FreeCornerData w i a}
    (L : LoopLiftData w i a d) (js : List (Fin 2)) :
    matrixEvaluation w i a d (liftFreeWord L js) 0 0 = MonoidAlgebra.single (FreeMonoid.ofList js) 1 := by
  rw [liftFreeWord_matrix]
  cases js with
  | nil => simp [MonoidAlgebra.one_def, FreeMonoid.ofList_nil]
  | cons j js => simp [matrixUnit, Matrix.stdBasisMatrix]

end
end Ginzburg333.Converse
