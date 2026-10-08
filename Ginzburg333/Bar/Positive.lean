import Ginzburg333.Finite.Grading
import Ginzburg333.Ginzburg.Words

/-! Coordinates and associative structure constants of the augmentation ideal. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

def positiveBasis : Generator → Auxiliary k
  | .forward i a => embedRow i (0, unitVec a, 0, 0)
  | .reverse i a => embedRow (next i) (0, 0, unitVec a, 0)
  | .loop i => embedRow i (0, 0, 0, 1)
def positiveCoordinate (a : Auxiliary k) : Generator → k
  | .forward i j => (a i).2.1 j
  | .reverse i j => (a (next i)).2.2.1 j
  | .loop i => (a i).2.2.2
def positiveCoordinates : Auxiliary k →ₗ[k] (Generator → k) where
  toFun := positiveCoordinate
  map_add' := by intro a b; funext g; cases g <;> rfl
  map_smul' := by intro a b; funext g; cases g <;> rfl
def positiveExpansion (f : Generator → k) : Auxiliary k :=
  (∑ i, ∑ a, f (.forward i a) • positiveBasis (.forward i a)) +
  (∑ i, ∑ a, f (.reverse i a) • positiveBasis (.reverse i a)) +
  ∑ i, f (.loop i) • positiveBasis (.loop i)

theorem positiveExpansion_coordinates (a : Auxiliary k) :
    positiveExpansion (positiveCoordinate a) = fun i => (0, (a i).2) := by
  classical
  funext i
  fin_cases i <;>
    simp [positiveExpansion, positiveCoordinate, positiveBasis, embedRow, unitVec,
      Fin.sum_univ_succ, next, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    apply Prod.ext
  all_goals
    repeat first
      | apply Prod.ext
      | (funext j; fin_cases j <;> simp [unitVec])
      | rfl
theorem positiveExpansion_of_augmentation_zero (a : Auxiliary k) (ha : augmentation a = 0) :
    positiveExpansion (positiveCoordinate a) = a := by
  rw [positiveExpansion_coordinates]
  funext i
  apply Prod.ext
  · exact (congrFun ha i).symm
  · rfl
@[simp] theorem augmentation_positiveBasis (g : Generator) :
    augmentation (positiveBasis (k := k) g) = 0 := by
  classical
  funext j
  cases g <;> simp [augmentation, positiveBasis, embedRow, apply_ite]
@[simp] theorem positiveCoordinate_basis (g h : Generator) :
    positiveCoordinate (positiveBasis (k := k) g) h = if h = g then 1 else 0 := by
  classical
  have hn : Function.Injective next := by
    intro i j hij
    have e := congrArg (fun v => next (next v)) hij
    simpa using e
  cases g <;> cases h <;>
    simp [positiveCoordinate, positiveBasis, embedRow, unitVec, apply_ite,
      hn.eq_iff, eq_comm, and_comm]
  all_goals
    rename_i i a j b
    by_cases hi : i = j <;> by_cases ha : a = b <;>
      simp_all [unitVec, apply_ite, hn.eq_iff, eq_comm]
def positiveExpansionLinear : (Generator → k) →ₗ[k] Auxiliary k where
  toFun := positiveExpansion
  map_add' := by
    intro f g
    simp only [positiveExpansion, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro a f
    simp [positiveExpansion, Finset.smul_sum, smul_add, smul_smul]
theorem positiveCoordinate_expansion (f : Generator → k) (g : Generator) :
    positiveCoordinate (positiveExpansion f) g = f g := by
  classical
  change positiveCoordinates (positiveExpansion f) g = f g
  simp only [positiveExpansion, map_add, map_sum, map_smul, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [positiveCoordinates]
  cases g <;> simp [positiveCoordinate_basis, ite_and]
def positiveCoefficients : Auxiliary k →ₗ[k] (Generator →₀ k) :=
  (Finsupp.linearEquivFunOnFinite k k Generator).symm.toLinearMap.comp positiveCoordinates
@[simp] theorem positiveCoefficients_apply (a : Auxiliary k) (g : Generator) :
    positiveCoefficients a g = positiveCoordinate a g := rfl
def positiveElement (x : Generator →₀ k) : Auxiliary k := positiveExpansion (fun g => x g)
theorem positiveCoefficients_injective_on_positive (a b : Auxiliary k)
    (ha : augmentation a = 0) (hb : augmentation b = 0)
    (h : positiveCoefficients a = positiveCoefficients b) : a = b := by
  have heq : positiveCoordinate a = positiveCoordinate b := by
    funext g
    exact congrArg (fun x : Generator →₀ k => x g) h
  calc
    a = positiveExpansion (positiveCoordinate a) := (positiveExpansion_of_augmentation_zero a ha).symm
    _ = positiveExpansion (positiveCoordinate b) := congrArg positiveExpansion heq
    _ = b := positiveExpansion_of_augmentation_zero b hb
theorem sum_positive_basis (a : Auxiliary k) (ha : augmentation a = 0) :
    (∑ g, positiveCoordinate a g • positiveBasis g) = a := by
  classical
  have hpos : augmentation (∑ g, positiveCoordinate a g • positiveBasis g : Auxiliary k) = 0 := by
    simp only [map_sum, map_smul, augmentation_positiveBasis, smul_zero, Finset.sum_const_zero]
  apply positiveCoefficients_injective_on_positive _ a hpos ha
  ext g
  change positiveCoordinates (∑ t, positiveCoordinate a t • positiveBasis t) g = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [positiveCoordinates]
  simp [positiveCoordinate_basis]

def positiveMultiplication (D : CyclicData k) (g h : Generator) : Generator → k :=
  positiveCoordinate (D.multiply (positiveBasis g) (positiveBasis h))
theorem sum_positiveMultiplication (D : CyclicData k) (g h : Generator) :
    (∑ t, positiveMultiplication D g h t • positiveBasis t) =
      D.multiply (positiveBasis g) (positiveBasis h) := by
  apply sum_positive_basis
  rw [D.augmentation_multiply, augmentation_positiveBasis, augmentation_positiveBasis]
  simp
def multiplication (D : CyclicData k) : Auxiliary k →ₗ[k] Auxiliary k →ₗ[k] Auxiliary k where
  toFun a :=
    { toFun := D.multiply a
      map_add' := D.multiply_add_right a
      map_smul' := by intro t b; exact D.multiply_smul_right t a b }
  map_add' a b := by
    apply LinearMap.ext; intro c; exact D.multiply_add_left a b c
  map_smul' a b := by
    apply LinearMap.ext; intro c; exact D.multiply_smul_left a b c
theorem multiply_sum_left (D : CyclicData k) (f : Generator → Auxiliary k) (b : Auxiliary k) :
    D.multiply (∑ t, f t) b = ∑ t, D.multiply (f t) b :=
  map_sum ((multiplication D).flip b).toAddMonoidHom f Finset.univ
theorem multiply_sum_right (D : CyclicData k) (a : Auxiliary k) (f : Generator → Auxiliary k) :
    D.multiply a (∑ t, f t) = ∑ t, D.multiply a (f t) :=
  map_sum (multiplication D a).toAddMonoidHom f Finset.univ
theorem positiveMultiplication_assoc (D : CyclicData k) (g h l u : Generator) :
    (∑ t, positiveMultiplication D g h t * positiveMultiplication D t l u) =
      ∑ t, positiveMultiplication D h l t * positiveMultiplication D g t u := by
  classical
  have e := D.multiply_assoc (positiveBasis g) (positiveBasis h) (positiveBasis l)
  rw [← sum_positiveMultiplication D g h, ← sum_positiveMultiplication D h l] at e
  rw [multiply_sum_left, multiply_sum_right] at e
  simp only [CyclicData.multiply_smul_left, CyclicData.multiply_smul_right] at e
  have e' := congrArg positiveCoordinates.toAddMonoidHom e
  simp only [map_sum] at e'
  change (∑ x, positiveCoordinates (positiveMultiplication D g h x •
    D.multiply (positiveBasis x) (positiveBasis l))) =
    ∑ x, positiveCoordinates (positiveMultiplication D h l x •
      D.multiply (positiveBasis g) (positiveBasis x)) at e'
  simp only [map_smul] at e'
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun e' u
theorem positiveMultiplication_reconstruct (D : CyclicData k) (g h : Generator) :
    positiveExpansion (positiveMultiplication D g h) = D.multiply (positiveBasis g) (positiveBasis h) := by
  apply positiveExpansion_of_augmentation_zero
  rw [D.augmentation_multiply, augmentation_positiveBasis, augmentation_positiveBasis]
  simp
end
end Ginzburg333.Bar
