import Ginzburg333.Converse.Factors

namespace Ginzburg333.Converse
variable {k : Type*} [Field k]
noncomputable section
open TensorProduct

abbrev SmallTensor (k : Type*) [Field k] := TensorProduct k (SmallVec k) (SmallVec k)

theorem smallTensor_finrank : Module.finrank k (SmallTensor k) = 4 := by
  simp [SmallTensor, SmallVec, Module.finrank_tensorProduct]

def projectedRelation (w : Tensor k) (i : Vertex) (p z : Vec k →ₗ[k] SmallVec k)
    (j : Fin 3) : SmallTensor k :=
  ∑ b, ∑ c, coeff w i j b c • (p (unitVec b) ⊗ₜ[k] z (unitVec c))

def projectedRelationMap (w : Tensor k) (i : Vertex) (p z : Vec k →ₗ[k] SmallVec k) :
    Vec k →ₗ[k] SmallTensor k where
  toFun a := ∑ j, a j • projectedRelation w i p z j
  map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro t a; simp [Finset.smul_sum, smul_smul]

theorem projectedRelationMap_unit (w : Tensor k) (i : Vertex) (p z : Vec k →ₗ[k] SmallVec k)
    (j : Fin 3) : projectedRelationMap w i p z (unitVec j) = projectedRelation w i p z j := by
  classical
  simp [projectedRelationMap, unitVec]

theorem projected_tmul (p z : Vec k →ₗ[k] SmallVec k) (v u : Vec k) :
    (∑ b, ∑ c, (v b * u c) • (p (unitVec b) ⊗ₜ[k] z (unitVec c))) = p v ⊗ₜ[k] z u := by
  have hp : (∑ b, v b • p (unitVec b)) = p v := by
    calc
      _ = p (∑ b, v b • unitVec b) := by simp only [map_sum, map_smul]
      _ = _ := by rw [sum_unitVec]
  have hz : (∑ c, u c • z (unitVec c)) = z u := by
    calc
      _ = z (∑ c, u c • unitVec c) := by simp only [map_sum, map_smul]
      _ = _ := by rw [sum_unitVec]
  rw [← hp, ← hz]
  rw [TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul]

theorem projectedRelationMap_factor_zero (w : Tensor k) (i : Vertex) (a : Vec k)
    (h : RankOneSlice w i a) :
    projectedRelationMap w i (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero) a = 0 := by
  let p := killLine h.left h.left_ne_zero
  let z := killLine h.right h.right_ne_zero
  change (∑ j, a j • projectedRelation w i p z j) = 0
  simp only [projectedRelation, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have he : (∑ b, ∑ j, ∑ c, (a j * coeff w i j b c) • (p (unitVec b) ⊗ₜ[k] z (unitVec c))) =
      ∑ b, ∑ c, (h.left b * h.right c) • (p (unitVec b) ⊗ₜ[k] z (unitVec c)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_smul, h.factor]
  rw [he, projected_tmul, killLine_self, TensorProduct.zero_tmul]

theorem projectedRelationMap_rank_le_two (w : Tensor k) (i : Vertex) (a : Vec k)
    (ha : a ≠ 0) (h : RankOneSlice w i a) :
    Module.finrank k (LinearMap.range (projectedRelationMap w i
      (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero))) ≤ 2 := by
  let f := projectedRelationMap w i (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero)
  change Module.finrank k (LinearMap.range f) ≤ 2
  have hk : 0 < Module.finrank k (LinearMap.ker f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨a, projectedRelationMap_factor_zero w i a h⟩, ?_⟩
    intro hz
    exact ha (congrArg Subtype.val hz)
  have hd := LinearMap.finrank_range_add_finrank_ker f
  rw [finrank_vec] at hd
  omega

abbrev RelationQuotient (w : Tensor k) (i : Vertex) (p z : Vec k →ₗ[k] SmallVec k) :=
  SmallTensor k ⧸ LinearMap.range (projectedRelationMap w i p z)

theorem relationQuotient_finrank_ge_two (w : Tensor k) (i : Vertex) (a : Vec k)
    (ha : a ≠ 0) (h : RankOneSlice w i a) :
    2 ≤ Module.finrank k (RelationQuotient w i
      (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero)) := by
  have hd := Submodule.finrank_quotient_add_finrank (LinearMap.range (projectedRelationMap w i
    (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero)))
  rw [smallTensor_finrank] at hd
  have hr := projectedRelationMap_rank_le_two w i a ha h
  change Module.finrank k (RelationQuotient w i
      (killLine h.left h.left_ne_zero) (killLine h.right h.right_ne_zero)) + _ = 4 at hd
  omega

structure FreeCornerData (w : Tensor k) (i : Vertex) (a : Vec k) where
  left : Vec k →ₗ[k] SmallVec k
  right : Vec k →ₗ[k] SmallVec k
  output : SmallTensor k →ₗ[k] SmallVec k
  left_surjective : Function.Surjective left
  right_surjective : Function.Surjective right
  output_surjective : Function.Surjective output
  first_relations : ∀ j, (∑ b, ∑ c, coeff w i j b c • output (left (unitVec b) ⊗ₜ[k] right (unitVec c))) = 0
  second_relations : ∀ b y, (∑ j, ∑ c, (a j * coeff w i j b c) • output (y ⊗ₜ[k] right (unitVec c))) = 0
  third_relations : ∀ c, (∑ j, ∑ b, (a j * coeff w i j b c) • left (unitVec b)) = 0

theorem freeCornerData_exists (w : Tensor k) (i : Vertex) (a : Vec k)
    (ha : a ≠ 0) (h : RankOneSlice w i a) : Nonempty (FreeCornerData w i a) := by
  classical
  let p := killLine h.left h.left_ne_zero
  let z := killLine h.right h.right_ne_zero
  let R := LinearMap.range (projectedRelationMap w i p z)
  let H := SmallTensor k ⧸ R
  have hh : 2 ≤ Module.finrank k H := relationQuotient_finrank_ge_two w i a ha h
  let out : SmallTensor k →ₗ[k] SmallVec k := (firstTwoCoordinates hh).comp R.mkQ
  refine ⟨⟨p, z, out, killLine_surjective _ _, killLine_surjective _ _,
    (firstTwoCoordinates_surjective hh).comp R.mkQ_surjective, ?_, ?_, ?_⟩⟩
  · intro j
    have hz : out (projectedRelationMap w i p z (unitVec j)) = 0 := by
      change firstTwoCoordinates hh (R.mkQ _) = 0
      have hq : R.mkQ (projectedRelationMap w i p z (unitVec j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨unitVec j, rfl⟩
      rw [hq, map_zero]
    rw [projectedRelationMap_unit] at hz
    simpa only [projectedRelation, map_sum, map_smul] using hz
  · intro b y
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, h.factor]
    have hsum : (∑ c, (h.left b * h.right c) • out (y ⊗ₜ[k] z (unitVec c))) =
        h.left b • out (y ⊗ₜ[k] z h.right) := by
      conv_rhs => rw [← sum_unitVec h.right, map_sum, TensorProduct.tmul_sum, map_sum, Finset.smul_sum]
      simp [TensorProduct.tmul_smul, map_smul, smul_smul]
    rw [hsum, killLine_self, TensorProduct.tmul_zero, map_zero, smul_zero]
  · intro c
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, h.factor]
    have he : (∑ b, (h.left b * h.right c) • p (unitVec b)) = h.right c • p h.left := by
      conv_rhs => rw [← sum_unitVec h.left, map_sum, Finset.smul_sum]
      simp [map_smul, smul_smul, mul_comm]
    rw [he, killLine_self, smul_zero]
end
end Ginzburg333.Converse
