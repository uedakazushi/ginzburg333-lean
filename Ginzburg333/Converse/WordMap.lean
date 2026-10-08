import Ginzburg333.Converse.Representation

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 4000000

theorem matrixWord_append (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (gs hs : List Generator) : matrixWord w i a d (gs ++ hs) = matrixWord w i a d gs * matrixWord w i a d hs := by
  simp [matrixWord, List.map_append, List.prod_append]

theorem matrixEvaluation_prepend (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (gs : List Generator) (x : WordSpace k) :
    matrixEvaluation w i a d (prependWords gs x) = matrixWord w i a d gs * matrixEvaluation w i a d x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, mul_add]
  | single hs t => simp [matrixWord_append, mul_smul_comm]

theorem matrixEvaluation_append (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (gs : List Generator) (x : WordSpace k) :
    matrixEvaluation w i a d (appendWords gs x) = matrixEvaluation w i a d x * matrixWord w i a d gs := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | single hs t => simp [matrixWord_append, smul_mul_assoc]

theorem matrixEvaluation_concatenate (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (x y : WordSpace k) :
    matrixEvaluation w i a d (concatenate x y) = matrixEvaluation w i a d x * matrixEvaluation w i a d y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [concatenate_add_left, hx, hz, add_mul]
  | single gs t => simp [matrixEvaluation_prepend, smul_mul_assoc]

def locatedMatrixEvaluation (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) :
    LocatedWordSpace k →ₗ[k] CornerMatrix k := Finsupp.linearCombination k (fun p => matrixWord w i a d p.2)

theorem locatedMatrixEvaluation_locate (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (v : Vertex) (x : WordSpace k) :
    locatedMatrixEvaluation w i a d (locateWords v x) = matrixEvaluation w i a d x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs t => simp [locatedMatrixEvaluation]

def pathMatrixEvaluation (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a) :
    PathSpace k →ₗ[k] CornerMatrix k := (locatedMatrixEvaluation w i a d).comp forgetPathValidity

theorem pathMatrixEvaluation_term (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (v : Vertex) (gs : List Generator) (hv : ValidPath (v, gs)) :
    pathMatrixEvaluation w i a d (pathTerm v ((1 : k), gs)) = matrixWord w i a d gs := by
  simp [pathMatrixEvaluation, forgetPathValidity_pathTerm v ((1 : k), gs) hv, locatedMatrixEvaluation]

def closedWords (v : Vertex) (n : ℕ) : Submodule k (WordSpace k) :=
  Finsupp.supported k k {gs | endpoint? v gs = some v ∧ wordWeight gs = n ∧ wordNegative gs = 0}

theorem closedWords_nil (v : Vertex) : (Finsupp.single [] 1 : WordSpace k) ∈ closedWords v 0 := by
  apply Finsupp.single_mem_supported
  simp [endpoint?, wordWeight, wordNegative]

theorem closedWords_concatenate (v : Vertex) (m n : ℕ) (x y : WordSpace k)
    (hx : x ∈ closedWords v m) (hy : y ∈ closedWords v n) : concatenate x y ∈ closedWords v (m + n) := by
  classical
  change x.support.sum (fun gs => x gs • prependWords gs y) ∈ closedWords v (m + n)
  apply Submodule.sum_mem
  intro gs hgs
  apply Submodule.smul_mem
  change (y.support.sum (fun hs => Finsupp.single (gs ++ hs) (y hs))) ∈ closedWords v (m + n)
  apply Submodule.sum_mem
  intro hs hhs
  apply Finsupp.single_mem_supported
  obtain ⟨he, hw, hn⟩ := hx hgs
  obtain ⟨he', hw', hn'⟩ := hy hhs
  exact ⟨by rw [endpoint_append, he']; exact he, by rw [wordWeight_append, hw, hw'],
    by rw [wordNegative_append, hn, hn']⟩

def wordToPaths (v : Vertex) : WordSpace k →ₗ[k] PathSpace k :=
  Finsupp.linearCombination k (fun gs => pathTerm v ((1 : k), gs))

theorem wordToPaths_bigraded (v : Vertex) (n : ℕ) (x : WordSpace k)
    (hx : x ∈ closedWords v n) : wordToPaths v x ∈ bigradedComponent (k := k) n 0 := by
  classical
  change x.support.sum (fun gs => x gs • pathTerm v ((1 : k), gs)) ∈ bigradedComponent (k := k) n 0
  apply Submodule.sum_mem
  intro gs hgs
  apply Submodule.smul_mem
  apply pathTerm_mem_supported
  intro hp
  obtain ⟨he, hw, hn⟩ := hx hgs
  exact ⟨hw, by change -(wordNegative gs : ℤ) = 0; rw [hn]; rfl⟩

theorem wordToPaths_matrix (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (v : Vertex) (n : ℕ) (x : WordSpace k) (hx : x ∈ closedWords v n) :
    pathMatrixEvaluation w i a d (wordToPaths v x) = matrixEvaluation w i a d x := by
  classical
  change pathMatrixEvaluation w i a d (x.support.sum (fun gs => x gs • pathTerm v ((1 : k), gs))) =
    x.support.sum (fun gs => x gs • matrixWord w i a d gs)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro gs hgs
  have hv : ValidPath (v, gs) := by
    have he := (hx hgs).1
    simp [ValidPath, he]
  rw [map_smul, pathMatrixEvaluation_term w i a d v gs hv]
end
end Ginzburg333.Converse
