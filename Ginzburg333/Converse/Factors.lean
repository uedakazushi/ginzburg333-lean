import Ginzburg333.Converse.LowDegree
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem contraction_unit_coefficients (w : Tensor k) (i : Vertex) (a : Vec k) (b c : Fin 3) :
    (ofTensor w).mul i a (unitVec b) c = ∑ j, a j * coeff w i j b c := by
  simp [ofTensor, contraction, contract, unitVec, mul_comm]

structure RankOneSlice (w : Tensor k) (i : Vertex) (a : Vec k) where
  left : Vec k
  right : Vec k
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  factor : ∀ b c, (∑ j, a j * coeff w i j b c) = left b * right c

theorem rankOneSlice_exists (w : Tensor k) (i : Vertex) (a : Vec k)
    (h : Module.finrank k (LinearMap.range ((ofTensor w).mul i a)) = 1) :
    Nonempty (RankOneSlice w i a) := by
  classical
  let f := (ofTensor w).mul i a
  change Module.finrank k (LinearMap.range f) = 1 at h
  have hf : f ≠ 0 := by
    intro hz
    have he : Module.finrank k (LinearMap.range f) = 0 := by simp [hz]
    omega
  have hex : ∃ b, f b ≠ 0 := by
    by_contra! hh
    apply hf
    apply LinearMap.ext
    intro b
    exact hh b
  obtain ⟨b0, hb0⟩ := hex
  let u := f b0
  have hr : Submodule.span k {u} = LinearMap.range f := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨b0, rfl⟩
    · rw [finrank_span_singleton hb0, h]
  have hexv (b : Fin 3) : ∃ t : k, t • u = f (unitVec b) := by
    apply Submodule.mem_span_singleton.mp
    rw [hr]
    exact ⟨unitVec b, rfl⟩
  choose v hv using hexv
  have hv0 : v ≠ 0 := by
    intro hz
    apply hf
    apply LinearMap.ext
    intro b
    rw [← sum_unitVec b, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_smul, ← hv j]
    simp [hz]
  refine ⟨⟨v, u, hv0, hb0, ?_⟩⟩
  intro b c
  rw [← contraction_unit_coefficients]
  have he := congrArg (fun x : Vec k => x c) (hv b)
  exact he.symm

theorem rankOneSlice_of_not_regular (w : Tensor k) (hw : GinzburgRegular w)
    (i : Vertex) (a : Vec k) (ha : a ≠ 0)
    (hbad : ¬ 2 ≤ Module.finrank k (LinearMap.range ((ofTensor w).mul i a))) :
    Nonempty (RankOneSlice w i a) := by
  apply rankOneSlice_exists
  have hnz : Module.finrank k (LinearMap.range ((ofTensor w).mul i a)) ≠ 0 := by
    intro hz
    have hr := Submodule.finrank_eq_zero.mp hz
    have hf : (ofTensor w).mul i a = 0 := LinearMap.range_eq_bot.mp hr
    exact ginzburgRegular_contraction_ne_zero w hw i a ha hf
  omega

abbrev SmallVec (k : Type*) := Fin 2 → k
def smallUnit (j : Fin 2) : SmallVec k := fun l => if l = j then 1 else 0

theorem sum_smallUnit (a : SmallVec k) : ∑ j, a j • smallUnit j = a := by
  classical
  funext l
  simp [smallUnit, Finset.sum_apply]

/-- Projection onto two genuine coordinates of a finite-dimensional module. -/
def firstTwoCoordinates {H : Type*} [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    (hH : 2 ≤ Module.finrank k H) : H →ₗ[k] SmallVec k where
  toFun x j := (Module.finBasis k H).repr x (Fin.castLE hH j)
  map_add' := by intro x y; funext j; simp
  map_smul' := by intro a x; funext j; simp

theorem firstTwoCoordinates_surjective {H : Type*} [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] (hH : 2 ≤ Module.finrank k H) :
    Function.Surjective (firstTwoCoordinates (k := k) hH) := by
  classical
  intro a
  refine ⟨∑ j : Fin 2, a j • Module.finBasis k H (Fin.castLE hH j), ?_⟩
  funext l
  fin_cases l <;> simp [firstTwoCoordinates, Basis.repr_self, Finsupp.single_apply, Fin.ext_iff]

abbrev LineQuotient (v : Vec k) := Vec k ⧸ Submodule.span k {v}

theorem lineQuotient_finrank (v : Vec k) (hv : v ≠ 0) : Module.finrank k (LineQuotient v) = 2 := by
  have hd := Submodule.finrank_quotient_add_finrank (Submodule.span k {v})
  rw [finrank_span_singleton hv, finrank_vec] at hd
  change Module.finrank k (LineQuotient v) + 1 = 3 at hd
  omega

def quotientCoordinates (v : Vec k) (hv : v ≠ 0) : LineQuotient v ≃ₗ[k] SmallVec k :=
  (Module.finBasisOfFinrankEq k (LineQuotient v) (lineQuotient_finrank v hv)).equivFun

def killLine (v : Vec k) (hv : v ≠ 0) : Vec k →ₗ[k] SmallVec k :=
  (quotientCoordinates v hv).toLinearMap.comp (Submodule.mkQ (Submodule.span k {v}))

theorem killLine_surjective (v : Vec k) (hv : v ≠ 0) : Function.Surjective (killLine v hv) :=
  (quotientCoordinates v hv).surjective.comp (Submodule.mkQ_surjective _)

theorem killLine_self (v : Vec k) (hv : v ≠ 0) : killLine v hv v = 0 := by
  change quotientCoordinates v hv ((Submodule.span k {v}).mkQ v) = 0
  have hz : (Submodule.span k {v}).mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v)
  rw [hz, map_zero]
end
end Ginzburg333.Converse
