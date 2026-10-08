import Ginzburg333.Bar.FreeExact

/-! Degree-zero homology vanishes in positive internal degree. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem rowContraction_degree_zero (D : CyclicData k) (i : Vertex) (m : Row k) :
    ambientDifferential (rowRightAction D i) (rowContraction (k := k) i (Finsupp.single [] m)) +
      Finsupp.single [] (degreeProjection 0 m) = Finsupp.single [] m := by
  classical
  have he : degreeProjection 0 m = m.1 • CyclicData.identityRow := by
    simp [degreeProjection, CyclicData.identityRow]
  have h := congrArg (Finsupp.lsingle [] : Row k →ₗ[k] Ambient (Row k)) (row_decomposition i m)
  simp only [map_add, map_sum, map_smul, Finsupp.lsingle_apply] at h
  simp only [rowContraction_single, map_neg, map_sum, map_smul, ambientDifferential_single,
    onWord, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    rowRightAction_apply, rowAction_identity_positive, innerBasisDifferential,
    map_zero, LinearMap.zero_apply, add_zero, smul_neg, neg_neg, he, Finsupp.smul_single]
  simp only [Finset.sum_neg_distrib, neg_neg, ← Finsupp.smul_single]
  exact (add_comm _ _).trans h

theorem length_zero_single {M : Type*} [AddCommGroup M] [Module k M]
    (x : Ambient M) (hx : x ∈ lengthComponent (k := k) 0) :
    x = Finsupp.single [] (x []) := by
  ext gs
  cases gs with
  | nil => simp
  | cons g gs =>
      have hn : g :: gs ∉ x.support := by
        intro h
        have hl := hx h
        change (g :: gs).length = 0 at hl
        simp at hl
      simp [Finsupp.not_mem_support_iff.mp hn]

theorem internallyNormalized_zero_surjective (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (internallyNormalizedDifferential D i U 0 n) := by
  intro x
  obtain ⟨m, hm⟩ := (D.rowGenerated i U).mkQ_surjective (x.val [])
  let f := (D.rowGenerated i U).mkQ
  let A := rowRightAction D i
  let B := quotientRightAction D i U
  let y : normalizedTerm A 0 := ⟨Finsupp.single [] m,
    balanced_single A [] m trivial rfl, Finsupp.single_mem_supported k m rfl⟩
  let z := normalizedMap A B f (row_mkQ_action D i U) 1 (normalizedRowContraction D i 0 y)
  have hzero : D.quotientProjection i U 0 (x.val []) = 0 := by
    apply x.property.2 [] 0
    simp only [Fin.val_zero, wordWeight_nil, zero_add]
    omega
  have hq : f (degreeProjection 0 m) = 0 := by
    rw [← CyclicData.quotientProjection_mkQ, hm, hzero]
  have hz : ambientDifferential B z.val = x.val := by
    have he := congrArg (coefficientMap f) (rowContraction_degree_zero D i m)
    rw [map_add, coefficientMap_single, hq, Finsupp.single_zero, add_zero,
      ambientDifferential_natural A B f (row_mkQ_action D i U), coefficientMap_single, hm] at he
    rw [length_zero_single x.val x.property.1.2]
    exact he
  refine ⟨⟨internalProjection D i U n z.val,
    ⟨internalProjection_balanced _ _ _ _ _ z.property.1,
      internalProjection_length _ _ _ _ _ _ z.property.2⟩,
      internalProjection_mem _ _ _ _ _⟩, ?_⟩
  apply Subtype.ext
  change ambientDifferential B (internalProjection D i U n z.val) = x.val
  rw [← internalProjection_differential, hz, internalProjection_eq_self _ _ _ _ _ x.property.2]
end
end Ginzburg333.Bar
