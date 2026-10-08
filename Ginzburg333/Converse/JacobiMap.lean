import Ginzburg333.Converse.Euler
import Ginzburg333.Converse.MatrixRelations
import Ginzburg333.Converse.WordMap

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 4000000

theorem matrixEvaluation_word_differential (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (gs : List Generator) :
    matrixEvaluation w i a d (wordVectorDifferential w gs) = 0 := by
  induction gs with
  | nil => rw [wordVectorDifferential_nil, map_zero]
  | cons g gs ih =>
      rw [wordVectorDifferential_cons, map_add, matrixEvaluation_append, map_smul,
        matrixEvaluation_prepend, matrixEvaluation_generator_differential, ih]
      simp

theorem locatedMatrixEvaluation_differential (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (x : LocatedWordSpace k) :
    locatedMatrixEvaluation w i a d (locatedDifferential w x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p t =>
      rw [locatedDifferential_single, map_smul, locatedMatrixEvaluation_locate,
        matrixEvaluation_word_differential, smul_zero]

/-- The representation annihilates the actual finite-support differential. -/
theorem pathMatrixEvaluation_differential (w : Tensor k) (i : Vertex) (a : Vec k)
    (d : FreeCornerData w i a) (x : PathSpace k) : pathMatrixEvaluation w i a d (differential w x) = 0 := by
  change locatedMatrixEvaluation w i a d (forgetPathValidity (differential w x)) = 0
  rw [forgetPathValidity_differential, locatedMatrixEvaluation_differential]

def jacobiMatrixEvaluation (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (n : ℕ) : internalJacobi w n →ₗ[k] CornerMatrix k :=
  (LinearMap.range (negativeDifferential w n 0)).liftQ
    ((pathMatrixEvaluation w i a d).comp (negativeTerm (k := k) n 0).subtype) (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      change pathMatrixEvaluation w i a d (differential w y.val) = 0
      exact pathMatrixEvaluation_differential w i a d y.val)

theorem jacobiMatrixEvaluation_mk (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (n : ℕ) (x : negativeTerm (k := k) n 0) :
    jacobiMatrixEvaluation w i a d n ((LinearMap.range (negativeDifferential w n 0)).mkQ x) =
      pathMatrixEvaluation w i a d x.val := rfl

def matrixEntry00 : CornerMatrix k →ₗ[k] LoopWords k where
  toFun x := x 0 0
  map_add' := by intro x y; rfl
  map_smul' := by intro t x; rfl

def jacobiEvaluation (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (n : ℕ) : internalJacobi w n →ₗ[k] LoopWords k :=
  matrixEntry00.comp (jacobiMatrixEvaluation w i a d n)

theorem jacobiEvaluation_wordToPaths (w : Tensor k) (i : Vertex) (a : Vec k) (d : FreeCornerData w i a)
    (v : Vertex) (n : ℕ) (x : WordSpace k) (hx : x ∈ closedWords v n) :
    jacobiEvaluation w i a d n ((LinearMap.range (negativeDifferential w n 0)).mkQ
      ⟨wordToPaths v x, wordToPaths_bigraded v n x hx⟩) = matrixEvaluation w i a d x 0 0 := by
  dsimp only [jacobiEvaluation, LinearMap.comp_apply, matrixEntry00]
  rw [jacobiMatrixEvaluation_mk, wordToPaths_matrix w i a d v n x hx]
  rfl
end
end Ginzburg333.Converse
