import Ginzburg333.Bar.FreeHomotopy

/-! Contractibility on the actual normalized free-row terms. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem rowContraction_homotopy_normalized (D : CyclicData k) (i : Vertex) (r : ℕ)
    (x : normalizedTerm (rowRightAction D i) (r + 1)) :
    normalizedDifferential (rowRightAction D i) (r + 1) (normalizedRowContraction D i (r + 1) x) +
      normalizedRowContraction D i r (normalizedDifferential (rowRightAction D i) r x) = x := by
  classical
  have hb := (mem_balancedAmbient_iff _ _).mp x.property.1
  have h : rowHomotopyOperator D i x.val = x.val := by
    calc
      rowHomotopyOperator D i x.val =
          rowHomotopyOperator D i (x.val.support.sum (fun gs => Finsupp.single gs (x.val gs))) :=
        congrArg (rowHomotopyOperator D i) x.val.sum_single.symm
      _ = x.val.support.sum (fun gs => rowHomotopyOperator D i (Finsupp.single gs (x.val gs))) :=
        map_sum _ _ _
      _ = x.val.support.sum (fun gs => Finsupp.single gs (x.val gs)) := by
        apply Finset.sum_congr rfl
        intro gs hgs
        have hl := x.property.2 hgs
        cases gs with
        | nil => simp [lengthComponent] at hl
        | cons g gs =>
            apply rowContraction_homotopy_single
            have he := congrArg (fun y : Ambient (Row k) => y (g :: gs)) hb
            dsimp only at he
            rw [normalization_apply] at he
            by_cases hc : composable (g :: gs)
            · simpa only [if_pos hc] using he
            · rw [if_neg hc] at he
              exact (Finsupp.mem_support_iff.mp hgs he.symm).elim
      _ = x.val := x.val.sum_single
  apply Subtype.ext
  exact h

theorem normalized_free_row_exact (D : CyclicData k) (i : Vertex) (r : ℕ) :
    Homology.ExactAt (k := k)
      (A := normalizedTerm (rowRightAction D i) (r + 1 + 1))
      (B := normalizedTerm (rowRightAction D i) (r + 1))
      (C := normalizedTerm (rowRightAction D i) r)
      (normalizedDifferential (rowRightAction D i) (r + 1))
      (normalizedDifferential (rowRightAction D i) r) := by
  intro x
  constructor
  · intro hx
    refine ⟨normalizedRowContraction D i (r + 1) x, ?_⟩
    have h := rowContraction_homotopy_normalized D i r x
    rwa [hx, map_zero, add_zero] at h
  · rintro ⟨y, rfl⟩
    exact normalizedDifferential_square _ r y

theorem row_mkQ_action (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (a : Auxiliary k) (r : Row k) :
    (D.rowGenerated i U).mkQ ((rowRightAction D i).action a r) =
      (quotientRightAction D i U).action a ((D.rowGenerated i U).mkQ r) := rfl

theorem row_bot_mkQ_injective (D : CyclicData k) (i : Vertex) :
    Function.Injective (D.rowGenerated i ⊥).mkQ := by
  have h := ((D.rowGenerated i ⊥).quotEquivOfEqBot (D.rowGenerated_bot i)).symm.injective
  simpa only [Submodule.quotEquivOfEqBot_symm_apply] using h

theorem normalized_free_quotient_exact (D : CyclicData k) (i : Vertex) (r : ℕ) :
    Homology.ExactAt (k := k)
      (A := normalizedTerm (quotientRightAction D i ⊥) (r + 1 + 1))
      (B := normalizedTerm (quotientRightAction D i ⊥) (r + 1))
      (C := normalizedTerm (quotientRightAction D i ⊥) r)
      (normalizedDifferential (quotientRightAction D i ⊥) (r + 1))
      (normalizedDifferential (quotientRightAction D i ⊥) r) := by
  let f := (D.rowGenerated i ⊥).mkQ
  let hf := row_mkQ_action D i ⊥
  let F := fun j => normalizedMap (rowRightAction D i) (quotientRightAction D i ⊥) f hf j
  have hi (j : ℕ) : Function.Injective (F j) := normalizedMap_injective _ _ f hf j (row_bot_mkQ_injective D i)
  have hs (j : ℕ) : Function.Surjective (F j) := normalizedMap_surjective _ _ f hf j (D.rowGenerated i ⊥).mkQ_surjective
  have hd (j : ℕ) (y : normalizedTerm (rowRightAction D i) (j + 1)) :
      F j (normalizedDifferential (rowRightAction D i) j y) =
        normalizedDifferential (quotientRightAction D i ⊥) j (F (j + 1) y) :=
    normalizedDifferential_natural _ _ f hf j y
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hs (r + 1) x
    have hz : normalizedDifferential (rowRightAction D i) r y = 0 := by
      apply hi r
      rw [map_zero, hd, hy, hx]
    obtain ⟨z, hz⟩ := (normalized_free_row_exact D i r y).mp hz
    refine ⟨F (r + 1 + 1) z, ?_⟩
    rw [← hd, hz, hy]
  · rintro ⟨z, rfl⟩
    exact normalizedDifferential_square _ r z

theorem internally_normalized_free_exact (D : CyclicData k) (i : Vertex) (r n : ℕ) :
    Homology.ExactAt (k := k)
      (A := internallyNormalizedTerm D i ⊥ (r + 1 + 1) n)
      (B := internallyNormalizedTerm D i ⊥ (r + 1) n)
      (C := internallyNormalizedTerm D i ⊥ r n)
      (internallyNormalizedDifferential D i ⊥ (r + 1) n)
      (internallyNormalizedDifferential D i ⊥ r n) := by
  intro x
  constructor
  · intro hx
    have hc : ambientDifferential (quotientRightAction D i ⊥) x.val = 0 :=
      congrArg (fun y : internallyNormalizedTerm D i ⊥ r n => y.val) hx
    obtain ⟨y, hy⟩ := (normalized_free_quotient_exact D i r
      (⟨x.val, x.property.1⟩ : normalizedTerm (quotientRightAction D i ⊥) (r + 1))).mp
      (Subtype.ext hc)
    have hb : ambientDifferential (quotientRightAction D i ⊥) y.val = x.val := congrArg Subtype.val hy
    refine ⟨⟨internalProjection D i ⊥ n y.val,
      ⟨internalProjection_balanced _ _ _ _ _ y.property.1,
        internalProjection_length _ _ _ _ _ _ y.property.2⟩,
        internalProjection_mem _ _ _ _ _⟩, ?_⟩
    apply Subtype.ext
    change ambientDifferential (quotientRightAction D i ⊥) (internalProjection D i ⊥ n y.val) = x.val
    rw [← internalProjection_differential, hb, internalProjection_eq_self _ _ _ _ _ x.property.2]
  · rintro ⟨z, rfl⟩
    exact internallyNormalizedDifferential_square _ _ _ r n z

end
end Ginzburg333.Bar
