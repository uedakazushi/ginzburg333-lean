import Ginzburg333.Converse.Quotient
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

abbrev LoopWords (k : Type*) [Field k] := MonoidAlgebra k (FreeMonoid (Fin 2))
abbrev CornerMatrix (k : Type*) [Field k] := Matrix (Fin 4) (Fin 4) (LoopWords k)

def freeLetterMap : SmallVec k →ₗ[k] LoopWords k where
  toFun v := ∑ j, v j • MonoidAlgebra.single (FreeMonoid.of j) 1
  map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro a x; simp [Finset.smul_sum, smul_smul]

def matrixUnit (r c : Fin 4) : LoopWords k →ₗ[k] CornerMatrix k where
  toFun v := Matrix.stdBasisMatrix r c v
  map_add' := by intro x y; ext a b l; by_cases hr : r = a <;> by_cases hc : c = b <;> simp [Matrix.stdBasisMatrix, hr, hc]
  map_smul' := by intro t x; ext a b l; by_cases hr : r = a <;> by_cases hc : c = b <;> simp [Matrix.stdBasisMatrix, hr, hc]

theorem matrixUnit_mul (r s t u : Fin 4) (x y : LoopWords k) :
    matrixUnit r s x * matrixUnit t u y = if s = t then matrixUnit r u (x * y) else 0 := by
  by_cases h : s = t
  · subst t
    exact (Matrix.StdBasisMatrix.mul_same x r s u y).trans (if_pos rfl).symm
  · exact (Matrix.StdBasisMatrix.mul_of_ne x r s t h y).trans (if_neg h).symm

def smallIndex (j : Fin 2) : Fin 4 := ⟨j.val + 1, by omega⟩

def xMatrix (a : k) : CornerMatrix k := a • matrixUnit 0 3 1
def yMatrix (v : SmallVec k) : CornerMatrix k := ∑ j, v j • matrixUnit (smallIndex j) 0 1
def zMatrix (v : Fin 2 → SmallVec k) : CornerMatrix k :=
  ∑ j, matrixUnit 3 (smallIndex j) (freeLetterMap (v j))

theorem tensorOutput_expand (f : SmallTensor k →ₗ[k] SmallVec k) (v z : SmallVec k) :
    f (v ⊗ₜ[k] z) = ∑ j, v j • f (smallUnit j ⊗ₜ[k] z) := by
  conv_lhs => rw [← sum_smallUnit v, TensorProduct.sum_tmul]
  simp [TensorProduct.smul_tmul, map_sum, map_smul]

theorem zMatrix_mul_yMatrix (v : Fin 2 → SmallVec k) (p : SmallVec k) :
    zMatrix v * yMatrix p = matrixUnit 3 0 (freeLetterMap (∑ j, p j • v j)) := by
  simp only [zMatrix, yMatrix, Fin.sum_univ_succ]
  simp [add_mul, mul_add, mul_smul_comm, matrixUnit_mul, smallIndex,
    map_add, map_smul]

theorem xMatrix_mul_zMatrix (a : k) (v : Fin 2 → SmallVec k) :
    xMatrix a * zMatrix v = ∑ j, a • matrixUnit 0 (smallIndex j) (freeLetterMap (v j)) := by
  simp only [xMatrix, zMatrix, Fin.sum_univ_succ]
  simp [mul_add, smul_mul_assoc, matrixUnit_mul, smallIndex]

theorem yMatrix_mul_xMatrix (p : SmallVec k) (a : k) :
    yMatrix p * xMatrix a = ∑ j, (a * p j) • matrixUnit (smallIndex j) 3 1 := by
  simp only [xMatrix, yMatrix, Fin.sum_univ_succ]
  simp [add_mul, smul_mul_smul_comm, matrixUnit_mul, smallIndex, mul_comm, smul_smul, smul_eq_mul]

def forwardMatrix (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (j : Vertex) (b : Fin 3) : CornerMatrix k :=
  if j = i then xMatrix (a b)
  else if j = next i then yMatrix (d.left (unitVec b))
  else zMatrix (fun h => d.output (smallUnit h ⊗ₜ[k] d.right (unitVec b)))

@[simp] theorem forwardMatrix_same (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) : forwardMatrix w i a d i b = xMatrix (a b) := by
  simp [forwardMatrix]

@[simp] theorem forwardMatrix_next (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) : forwardMatrix w i a d (next i) b = yMatrix (d.left (unitVec b)) := by
  fin_cases i <;> simp [forwardMatrix, next]

@[simp] theorem forwardMatrix_prev (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (b : Fin 3) :
    forwardMatrix w i a d (next (next i)) b = zMatrix (fun h => d.output (smallUnit h ⊗ₜ[k] d.right (unitVec b))) := by
  fin_cases i <;> simp [forwardMatrix, next]

theorem coeff_next (w : Tensor k) (i : Vertex) (a b c : Fin 3) :
    coeff w (next i) a b c = coeff w i c a b := by fin_cases i <;> rfl
theorem coeff_prev (w : Tensor k) (i : Vertex) (a b c : Fin 3) :
    coeff w (next (next i)) a b c = coeff w i b c a := by fin_cases i <;> rfl

def generatorMatrix (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) : Generator → CornerMatrix k
  | .forward j b => forwardMatrix w i a d j b
  | .reverse _ _ => 0
  | .loop _ => 0

def matrixWord (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (gs : List Generator) : CornerMatrix k := (gs.map (generatorMatrix w i a d)).prod

def matrixEvaluation (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) :
    WordSpace k →ₗ[k] CornerMatrix k := Finsupp.linearCombination k (matrixWord w i a d)

@[simp] theorem matrixEvaluation_single (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (gs : List Generator) (t : k) :
    matrixEvaluation w i a d (Finsupp.single gs t) = t • matrixWord w i a d gs := by
  simp [matrixEvaluation]
end
end Ginzburg333.Converse
