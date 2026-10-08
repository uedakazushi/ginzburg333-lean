import Ginzburg333.Bar.Internal

/-! Short exact sequences with the actual +1 internal-degree shift. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
variable {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}

theorem inclusion_top_degree (s : D.FiltrationStep i U) (m : D.QuotientRow (next i) s.colon) :
    s.inclusion (D.quotientProjection (next i) s.colon 3 m) = 0 := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated (next i) s.colon).mkQ_surjective m
  rw [CyclicData.quotientProjection_mkQ, CyclicData.FiltrationStep.inclusion_mkQ]
  simp [degreeProjection, CyclicData.leftOne]

theorem inclusion_coefficientProjection (s : D.FiltrationStep i U)
    (n : ℕ) (gs : List Generator) (m : D.QuotientRow (next i) s.colon) :
    coefficientProjection D i s.smaller (n + 1) gs (s.inclusion m) =
      s.inclusion (coefficientProjection D (next i) s.colon n gs m) := by
  classical
  have h1 : 1 + wordWeight gs = n + 1 ↔ wordWeight gs = n := by omega
  have h2 : 2 + wordWeight gs = n + 1 ↔ 1 + wordWeight gs = n := by omega
  have h3 : 3 + wordWeight gs = n + 1 ↔ 2 + wordWeight gs = n := by omega
  simp only [coefficientProjection, LinearMap.sum_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, zero_add, add_zero, map_add]
  norm_num only at *
  simp only [h1, h2, h3]
  split_ifs <;> simp_all [CyclicData.FiltrationStep.inclusion_degree,
    previousDegree, inclusion_top_degree]

theorem inclusion_internalProjection (s : D.FiltrationStep i U)
    (n : ℕ) (x : Ambient (D.QuotientRow (next i) s.colon)) :
    internalProjection D i s.smaller (n + 1) (coefficientMap s.inclusion x) =
      coefficientMap s.inclusion (internalProjection D (next i) s.colon n x) := by
  ext gs
  simp only [coefficientMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, internalProjection_apply]
  exact inclusion_coefficientProjection s n gs (x gs)

theorem projection_internalProjection (s : D.FiltrationStep i U)
    (n : ℕ) (x : Ambient (D.QuotientRow i s.smaller)) :
    internalProjection D i U n (coefficientMap s.projection x) =
      coefficientMap s.projection (internalProjection D i s.smaller n x) := by
  classical
  ext gs
  simp only [coefficientMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, internalProjection_apply]
  change coefficientProjection D i U n gs (s.projection (x gs)) =
    s.projection (coefficientProjection D i s.smaller n gs (x gs))
  simp only [coefficientProjection, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : d.val + wordWeight gs = n
  · simp only [if_pos hn]; exact s.projection_degree d (x gs)
  · simp only [if_neg hn, LinearMap.zero_apply, map_zero]

def internallyNormalizedRetraction (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) : Ambient (D.QuotientRow i U) →ₗ[k] Ambient (D.QuotientRow i U) :=
  (internalProjection D i U n).comp (normalizedRetraction (quotientRightAction D i U) r)

theorem internallyNormalizedRetraction_mem (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) (x : Ambient (D.QuotientRow i U)) :
    internallyNormalizedRetraction D i U r n x ∈ internallyNormalizedTerm D i U r n :=
  ⟨⟨internalProjection_balanced D i U n _ (normalizedRetraction_mem _ r x).1,
    internalProjection_length D i U n r _ (normalizedRetraction_mem _ r x).2⟩,
    internalProjection_mem D i U n _⟩

theorem internallyNormalizedRetraction_eq_self (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ internallyNormalizedTerm D i U r n) :
    internallyNormalizedRetraction D i U r n x = x := by
  change internalProjection D i U n (normalizedRetraction _ r x) = x
  rw [normalizedRetraction_eq_self _ r x hx.1, internalProjection_eq_self D i U n x hx.2]

theorem inclusion_internal (s : D.FiltrationStep i U) (n : ℕ)
    (x : Ambient (D.QuotientRow (next i) s.colon)) (hx : x ∈ internalComponent D (next i) s.colon n) :
    coefficientMap s.inclusion x ∈ internalComponent D i s.smaller (n + 1) := by
  rw [← internalProjection_eq_self D (next i) s.colon n x hx, ← inclusion_internalProjection]
  exact internalProjection_mem _ _ _ _ _

theorem projection_internal (s : D.FiltrationStep i U) (n : ℕ)
    (x : Ambient (D.QuotientRow i s.smaller)) (hx : x ∈ internalComponent D i s.smaller n) :
    coefficientMap s.projection x ∈ internalComponent D i U n := by
  rw [← internalProjection_eq_self D i s.smaller n x hx, ← projection_internalProjection]
  exact internalProjection_mem _ _ _ _ _

def internalInclusion (s : D.FiltrationStep i U) (r n : ℕ) :
    internallyNormalizedTerm D (next i) s.colon r n →ₗ[k] internallyNormalizedTerm D i s.smaller r (n + 1) where
  toFun x := ⟨coefficientMap s.inclusion x.val,
    ⟨coefficientMap_balanced _ _ _ (fun a m => (s.inclusion_action a m).symm) _ x.property.1.1,
      coefficientMap_length _ r _ x.property.1.2⟩, inclusion_internal s n _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

def internalQuotient (s : D.FiltrationStep i U) (r n : ℕ) :
    internallyNormalizedTerm D i s.smaller r n →ₗ[k] internallyNormalizedTerm D i U r n where
  toFun x := ⟨coefficientMap s.projection x.val,
    ⟨coefficientMap_balanced _ _ _ (fun a m => (s.projection_action a m).symm) _ x.property.1.1,
      coefficientMap_length _ r _ x.property.1.2⟩, projection_internal s n _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

theorem internalInclusion_differential (s : D.FiltrationStep i U) (r n : ℕ)
    (x : internallyNormalizedTerm D (next i) s.colon (r + 1) n) :
    internalInclusion s r n (internallyNormalizedDifferential D (next i) s.colon r n x) =
      internallyNormalizedDifferential D i s.smaller r (n + 1) (internalInclusion s (r + 1) n x) := by
  apply Subtype.ext
  exact filtration_inclusion_natural s x.val

theorem internalQuotient_differential (s : D.FiltrationStep i U) (r n : ℕ)
    (x : internallyNormalizedTerm D i s.smaller (r + 1) n) :
    internalQuotient s r n (internallyNormalizedDifferential D i s.smaller r n x) =
      internallyNormalizedDifferential D i U r n (internalQuotient s (r + 1) n x) := by
  apply Subtype.ext
  exact filtration_projection_natural s x.val

theorem internalInclusion_injective (s : D.FiltrationStep i U) (r n : ℕ) :
    Function.Injective (internalInclusion s r n) := by
  intro x y hxy
  apply Subtype.ext
  apply Homology.finsupp_map_injective s.inclusion s.short_exact.1
  exact congrArg Subtype.val hxy

theorem internalQuotient_surjective (s : D.FiltrationStep i U) (r n : ℕ) :
    Function.Surjective (internalQuotient s r n) := by
  intro y
  obtain ⟨x, hx⟩ := normalizedMap_surjective (quotientRightAction D i s.smaller) (quotientRightAction D i U) s.projection
    (fun a m => (s.projection_action a m).symm) r s.short_exact.2.2
    (⟨y.val, y.property.1⟩ : normalizedTerm (quotientRightAction D i U) r)
  have he : coefficientMap s.projection x.val = y.val := congrArg Subtype.val hx
  refine ⟨⟨internalProjection D i s.smaller n x.val,
    ⟨internalProjection_balanced _ _ _ _ _ x.property.1,
      internalProjection_length _ _ _ _ _ _ x.property.2⟩,
    internalProjection_mem _ _ _ _ _⟩, ?_⟩
  apply Subtype.ext
  change coefficientMap s.projection (internalProjection D i s.smaller n x.val) = y.val
  rw [← projection_internalProjection, he, internalProjection_eq_self _ _ _ _ _ y.property.2]

theorem internalInclusion_exact (s : D.FiltrationStep i U) (r n : ℕ) :
    Homology.ExactAt (k := k)
      (A := internallyNormalizedTerm D (next i) s.colon r n)
      (B := internallyNormalizedTerm D i s.smaller r (n + 1))
      (C := internallyNormalizedTerm D i U r (n + 1)) (internalInclusion s r n) (internalQuotient s r (n + 1)) := by
  intro y
  constructor
  · intro hy
    have hz : coefficientMap s.projection y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (normalizedMap_exact (quotientRightAction D (next i) s.colon) (quotientRightAction D i s.smaller)
      (quotientRightAction D i U) s.inclusion s.projection
      (fun a m => (s.inclusion_action a m).symm) (fun a m => (s.projection_action a m).symm)
      r s.short_exact.2.1 (⟨y.val, y.property.1⟩ : normalizedTerm (quotientRightAction D i s.smaller) r)).mp
      (Subtype.ext hz)
    have he : coefficientMap s.inclusion x.val = y.val := congrArg Subtype.val hx
    refine ⟨⟨internalProjection D (next i) s.colon n x.val,
      ⟨internalProjection_balanced _ _ _ _ _ x.property.1,
        internalProjection_length _ _ _ _ _ _ x.property.2⟩,
      internalProjection_mem _ _ _ _ _⟩, ?_⟩
    apply Subtype.ext
    change coefficientMap s.inclusion (internalProjection D (next i) s.colon n x.val) = y.val
    rw [← inclusion_internalProjection, he, internalProjection_eq_self _ _ _ _ _ y.property.2]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (Homology.exactAt_finsupp (I := List Generator) s.inclusion s.projection s.short_exact.2.1
      (coefficientMap s.inclusion x.val)).mpr ⟨x.val, rfl⟩

/-- B_(r,n)(colon) → B_(r,n+1)(smaller) → B_(r,n+1)(U). -/
theorem filtration_internal_short_exact (s : D.FiltrationStep i U) (r n : ℕ) :
    Function.Injective (internalInclusion s r n) ∧
      Homology.ExactAt (k := k)
      (A := internallyNormalizedTerm D (next i) s.colon r n)
      (B := internallyNormalizedTerm D i s.smaller r (n + 1))
      (C := internallyNormalizedTerm D i U r (n + 1)) (internalInclusion s r n) (internalQuotient s r (n + 1)) ∧
      Function.Surjective (internalQuotient s r (n + 1)) :=
  ⟨internalInclusion_injective s r n, internalInclusion_exact s r n,
    internalQuotient_surjective s r (n + 1)⟩
end
end Ginzburg333.Bar
