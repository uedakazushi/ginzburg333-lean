import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Three-dimensional coordinates and cyclic contractions

Source: direct_proof_source.tex, Sections 1--3.
Status: compiled and kernel-checked with Lean 4.19.0.
The coordinate model amounts to choosing bases in the three arrow spaces.
It does not identify their geometric meanings or quotient by cyclic permutation.
-/

namespace Ginzburg333

abbrev Vertex := Fin 3
abbrev Vec (k : Type*) := Fin 3 → k
abbrev Tensor (k : Type*) := Fin 3 → Fin 3 → Fin 3 → k

/-- The cyclic successor on the three labelled vertices. -/
def next : Vertex → Vertex := ![1, 2, 0]

@[simp] theorem next_three (i : Vertex) : next (next (next i)) = i := by
  fin_cases i <;> rfl

section Coordinates
variable {k : Type*} [Field k]

/-- Ordinary bilinear evaluation, not a Hermitian pairing. -/
def dot (a b : Vec k) : k := ∑ j, a j * b j

/-- Coordinate basis vector. -/
def unitVec (j : Fin 3) : Vec k := fun l => if l = j then 1 else 0

@[simp] theorem dot_zero_left (b : Vec k) : dot 0 b = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (a : Vec k) : dot a 0 = 0 := by
  simp [dot]

theorem dot_comm (a b : Vec k) : dot a b = dot b a := by
  simp [dot, mul_comm]

@[simp] theorem dot_add_left (a b c : Vec k) :
    dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_add_right (a b c : Vec k) :
    dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_smul_left (t : k) (a b : Vec k) :
    dot (t • a) b = t * dot a b := by
  simp [dot, Finset.mul_sum, mul_assoc]

@[simp] theorem dot_smul_right (t : k) (a b : Vec k) :
    dot a (t • b) = t * dot a b := by
  simp [dot, Finset.mul_sum, mul_left_comm, mul_assoc]

@[simp] theorem dot_unit_right (a : Vec k) (j : Fin 3) :
    dot a (unitVec j) = a j := by
  classical
  simp [dot, unitVec]

@[simp] theorem dot_unit_left (a : Vec k) (j : Fin 3) :
    dot (unitVec j) a = a j := by
  rw [dot_comm, dot_unit_right]

theorem eq_zero_of_dot_right {a : Vec k} (h : ∀ b, dot a b = 0) : a = 0 := by
  funext j
  simpa using h (unitVec j)

theorem eq_zero_of_dot_left {a : Vec k} (h : ∀ b, dot b a = 0) : a = 0 := by
  apply eq_zero_of_dot_right
  intro b
  rw [dot_comm]
  exact h b

/-- The functional associated to a coordinate covector. -/
def dotMap (a : Vec k) : Vec k →ₗ[k] k where
  toFun := dot a
  map_add' := dot_add_right a
  map_smul' := by
    intro t b
    simpa using dot_smul_right t a b

@[simp] theorem dotMap_apply (a b : Vec k) : dotMap a b = dot a b := rfl

theorem dotMap_surjective {a : Vec k} (ha : a ≠ 0) :
    Function.Surjective (dotMap a) := by
  classical
  have hex : ∃ j, a j ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  obtain ⟨j, hj⟩ := hex
  intro t
  refine ⟨(t / a j) • unitVec j, ?_⟩
  change dot a ((t / a j) • unitVec j) = t
  rw [dot_smul_right, dot_unit_right]
  exact div_mul_cancel₀ t hj

@[simp] theorem finrank_vec : Module.finrank k (Vec k) = 3 := by
  simp [Vec]

theorem finrank_dot_ker {a : Vec k} (ha : a ≠ 0) :
    Module.finrank k (LinearMap.ker (dotMap a)) = 2 := by
  have hr : LinearMap.range (dotMap a) = ⊤ :=
    LinearMap.range_eq_top.mpr (dotMap_surjective ha)
  have hdim := LinearMap.finrank_range_add_finrank_ker (dotMap a)
  rw [hr] at hdim
  have hdim' : 1 + Module.finrank k (LinearMap.ker (dotMap a)) = 3 := by
    simpa [hr] using hdim
  omega

theorem sum_unitVec (a : Vec k) : ∑ j, a j • unitVec j = a := by
  classical
  funext l
  simp [unitVec, Finset.sum_apply]

/-- Every linear functional is dot product with this vector. -/
def vectorOfFunctional (f : Vec k →ₗ[k] k) : Vec k := fun j => f (unitVec j)

theorem dot_vectorOfFunctional (f : Vec k →ₗ[k] k) (a : Vec k) :
    dot (vectorOfFunctional f) a = f a := by
  calc
    dot (vectorOfFunctional f) a = ∑ j, a j * f (unitVec j) := by
      unfold dot vectorOfFunctional
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = f (∑ j, a j • unitVec j) := by simp
    _ = f a := by rw [sum_unitVec]

theorem vectorOfFunctional_ne_zero {f : Vec k →ₗ[k] k} (hf : f ≠ 0) :
    vectorOfFunctional f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro a
  have ha := dot_vectorOfFunctional f a
  rw [h, dot_zero_left] at ha
  exact ha.symm

end Coordinates

section TensorCoordinates
variable {k : Type*} [Field k]

/-- Coefficients in the order `V_i, V_(i+1), V_(i+2)`. -/
def coeff (w : Tensor k) (i : Vertex) : Tensor k :=
  if i = 0 then w
  else if i = 1 then fun a b c => w c a b
  else fun a b c => w b c a

/-- First contraction followed by second contraction, in coordinates. -/
def contract (w : Tensor k) (i : Vertex) (a : Vec k) : Vec k →ₗ[k] Vec k where
  toFun b := fun c => ∑ x, ∑ y, coeff w i x y c * a x * b y
  map_add' := by
    intro b b'
    funext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro t b
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

/-- Bilinear contraction map; no regularity is assumed in its definition. -/
def contraction (w : Tensor k) (i : Vertex) :
    Vec k →ₗ[k] Vec k →ₗ[k] Vec k where
  toFun := contract w i
  map_add' := by
    intro a a'
    ext b c
    simp [contract, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro t a
    apply LinearMap.ext
    intro b
    funext c
    change (∑ x, ∑ y, coeff w i x y c * (t * a x) * b y) =
      t * (∑ x, ∑ y, coeff w i x y c * a x * b y)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

/-- A small interface exposing only the contractions and their cyclic identity. -/
structure CyclicData (k : Type*) [Field k] where
  mul : Vertex → Vec k →ₗ[k] Vec k →ₗ[k] Vec k
  cyclic : ∀ i a b c,
    dot (mul i a b) c = dot a (mul (next i) b c)

/-- The interface is instantiated from arbitrary tensor coefficients. -/
def ofTensor (w : Tensor k) : CyclicData k where
  mul := contraction w
  cyclic := by
    intro i a b c
    fin_cases i <;>
      simp [dot, contraction, contract, coeff, next, Fin.sum_univ_succ] <;> ring

/-- Exactly the three rank conditions in Definition 1.1 of the source paper. -/
def CyclicData.Regular (D : CyclicData k) : Prop :=
  ∀ (i : Vertex) (a : Vec k), a ≠ 0 →
    2 ≤ Module.finrank k (LinearMap.range (D.mul i a))

/-- Tensor regularity in the chosen bases. -/
def TensorRegular (w : Tensor k) : Prop := (ofTensor w).Regular

end TensorCoordinates
end Ginzburg333
