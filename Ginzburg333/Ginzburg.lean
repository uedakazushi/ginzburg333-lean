import Ginzburg333.Finite.Coordinates
import Mathlib.Tactic.DeriveFintype

/-!
# An explicit finite-support model of the Ginzburg differential

Words are stored in algebra multiplication order: [b,a] means the path first
a, then b. Empty paths retain a vertex. This is the convention of equation
(1.5) in the original paper. Invalid words are not basis elements.

This file defines the actual target predicate. Square-zero is proved in Ginzburg/SquareZero.lean. The bar-comparison
and tensor-regularity implication theorems remain absent.
Those are explicit unfinished obligations in GAPS.md.

Status: compiled with Lean 4.19.0; negative acyclicity remains unfinished.
-/

namespace Ginzburg333.Ginzburg

inductive Generator
  | forward (i : Vertex) (a : Fin 3)
  | reverse (i : Vertex) (a : Fin 3)
  | loop (i : Vertex)
  deriving DecidableEq, Fintype

namespace Generator

def source : Generator → Vertex
  | .forward i _ => i
  | .reverse i _ => next i
  | .loop i => i

def target : Generator → Vertex
  | .forward i _ => next i
  | .reverse i _ => i
  | .loop i => i

def weight : Generator → ℕ
  | .forward _ _ => 1
  | .reverse _ _ => 2
  | .loop _ => 3

def negativeDegree : Generator → ℕ
  | .forward _ _ => 0
  | .reverse _ _ => 1
  | .loop _ => 2

theorem weight_eq_negativeDegree_add_one (g : Generator) :
    g.weight = g.negativeDegree + 1 := by cases g <;> rfl

end Generator

/-- Read the rightmost generator first, as required by the path convention. -/
def endpoint? (start : Vertex) : List Generator → Option Vertex
  | [] => some start
  | g :: gs => do
      let v ← endpoint? start gs
      if g.source = v then some g.target else none

def ValidPath (p : Vertex × List Generator) : Prop :=
  (endpoint? p.1 p.2).isSome = true

abbrev BasisPath := {p : Vertex × List Generator // ValidPath p}

/-- Direct sum, not a product/completion. -/
abbrev PathSpace (k : Type*) [Zero k] := BasisPath →₀ k

def internalDegree (p : BasisPath) : ℕ := (p.val.2.map Generator.weight).sum

def cohomologicalDegree (p : BasisPath) : ℤ :=
  -((p.val.2.map Generator.negativeDegree).sum : ℤ)

theorem word_degree (gs : List Generator) :
    ((gs.map Generator.weight).sum : ℤ) =
      (gs.length : ℤ) + ((gs.map Generator.negativeDegree).sum : ℤ) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, Generator.weight_eq_negativeDegree_add_one]
      omega

/-- The r-n degree relation used in the final comparison. -/
theorem cohomologicalDegree_eq_length_sub_weight (p : BasisPath) :
    cohomologicalDegree p = (p.val.2.length : ℤ) - (internalDegree p : ℤ) := by
  have h := word_degree p.val.2
  unfold cohomologicalDegree internalDegree
  omega

def coordinates : List (Fin 3) := [0, 1, 2]

section Differential
variable {k : Type*} [Field k]

/-- Differential of one generator, using the tensor coefficient convention. -/
def generatorDifferential (w : Tensor k) : Generator → List (k × List Generator)
  | .forward _ _ => []
  | .reverse i a =>
      coordinates.flatMap fun b => coordinates.map fun c =>
        (coeff w i a b c,
          [.forward (next (next i)) c, .forward (next i) b])
  | .loop i =>
      (coordinates.map fun a => ((1 : k), [.reverse i a, .forward i a])) ++
      (coordinates.map fun a => ((-1 : k),
        [.forward (next (next i)) a, .reverse (next (next i)) a]))

/-- Graded derivation in algebra word order. Negative degrees have the same
parity as their absolute values. -/
def wordDifferential (w : Tensor k) : List Generator → List (k × List Generator)
  | [] => []
  | g :: gs =>
      ((generatorDifferential w g).map fun p => (p.1, p.2 ++ gs)) ++
      ((wordDifferential w gs).map fun p =>
        (((-1 : k) ^ g.negativeDegree) * p.1, g :: p.2))

noncomputable section

/-- Embed a valid word, keeping the starting vertex of the original path. -/
def pathTerm (start : Vertex) (t : k × List Generator) : PathSpace k := by
  classical
  exact if h : ValidPath (start, t.2) then Finsupp.single ⟨(start, t.2), h⟩ t.1 else 0

def basisDifferential (w : Tensor k) (p : BasisPath) : PathSpace k :=
  ((wordDifferential w p.val.2).map (pathTerm p.val.1)).sum

/-- The differential on finite linear combinations of paths. -/
def differential (w : Tensor k) : PathSpace k →ₗ[k] PathSpace k :=
  Finsupp.linearCombination k (basisDifferential w)

def Homogeneous (q : ℤ) (x : PathSpace k) : Prop :=
  ∀ p ∈ x.support, cohomologicalDegree p = q

def InternallyHomogeneous (n : ℕ) (x : PathSpace k) : Prop :=
  ∀ p ∈ x.support, internalDegree p = n

/-- Negative acyclicity expressed without quotienting cycles by boundaries.
No bar vanishing, avatar or finite-degree cutoff occurs in this definition. -/
def GinzburgRegular (w : Tensor k) : Prop :=
  ∀ q : ℤ, q < 0 → ∀ x : PathSpace k,
    Homogeneous q x → differential w x = 0 →
      ∃ y : PathSpace k, Homogeneous (q - 1) y ∧ differential w y = x

/-
Target (NOT declared as a theorem, and NOT supplied as an axiom):

  [IsAlgClosed k] [CharZero k] : TensorRegular w → GinzburgRegular w.

Square-zero and homogeneity of `differential` are proved, and normalized bar
terms and their differential are constructed. Internal grading, contraction,
filtration vanishing and the sign-compatible finite-degree comparison remain.
-/

end
end Differential
end Ginzburg333.Ginzburg
