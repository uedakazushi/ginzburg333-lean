import Ginzburg333.Bar.Normalized

/-! Degreewise exactness of the normalized bar terms via a natural retraction. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {L M N : Type*} [AddCommGroup L] [Module k L]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
noncomputable section
def lengthProjection (r : ℕ) : Ambient M →ₗ[k] Ambient M where
  toFun := Finsupp.filter (fun gs => gs.length = r)
  map_add' := by intro x y; exact Finsupp.filter_add
  map_smul' := by
    intro a x
    ext gs
    by_cases hg : gs.length = r <;> simp [Finsupp.filter_apply, hg]
theorem lengthProjection_mem (r : ℕ) (x : Ambient M) :
    lengthProjection (k := k) r x ∈ lengthComponent (k := k) r := by
  intro gs hgs
  change gs ∈ x.support.filter (fun gs => gs.length = r) at hgs
  exact (Finset.mem_filter.mp hgs).2
theorem lengthProjection_eq_self (r : ℕ) (x : Ambient M) (hx : x ∈ lengthComponent (k := k) r) :
    lengthProjection (k := k) r x = x := by
  apply (Finsupp.filter_eq_self_iff (fun gs => gs.length = r) x).mpr
  intro gs hgs
  exact hx (Finsupp.mem_support_iff.mpr hgs)
theorem coefficientMap_lengthProjection (f : M →ₗ[k] N) (r : ℕ) (x : Ambient M) :
    coefficientMap f (lengthProjection (k := k) r x) = lengthProjection (k := k) r (coefficientMap f x) := by
  ext gs
  change f (if gs.length = r then x gs else 0) = if gs.length = r then f (x gs) else 0
  by_cases hg : gs.length = r <;> simp [hg]
def normalizedRetraction {D : CyclicData k} (A : RightAction D M) (r : ℕ) : Ambient M →ₗ[k] Ambient M :=
  (normalization A).comp (lengthProjection (k := k) r)
theorem normalizedRetraction_mem {D : CyclicData k} (A : RightAction D M) (r : ℕ) (x : Ambient M) :
    normalizedRetraction A r x ∈ normalizedTerm A r :=
  normalization_mem_normalizedTerm A r _ (lengthProjection_mem r x)
theorem normalizedRetraction_eq_self {D : CyclicData k} (A : RightAction D M) (r : ℕ)
    (x : Ambient M) (hx : x ∈ normalizedTerm A r) : normalizedRetraction A r x = x := by
  change normalization A (lengthProjection (k := k) r x) = x
  rw [lengthProjection_eq_self r x hx.2]
  exact (mem_balancedAmbient_iff A x).mp hx.1
theorem normalizedRetraction_natural {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (r : ℕ) (x : Ambient M) :
    coefficientMap f (normalizedRetraction A r x) = normalizedRetraction B r (coefficientMap f x) := by
  change coefficientMap f (normalization A (lengthProjection (k := k) r x)) =
    normalization B (lengthProjection (k := k) r (coefficientMap f x))
  rw [normalization_natural A B f hf, coefficientMap_lengthProjection]
theorem normalizedMap_injective {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (r : ℕ)
    (hi : Function.Injective f) : Function.Injective (normalizedMap A B f hf r) := by
  intro x y hxy
  apply Subtype.ext
  apply Homology.finsupp_map_injective f hi
  exact congrArg Subtype.val hxy
theorem normalizedMap_surjective {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (r : ℕ)
    (hs : Function.Surjective f) : Function.Surjective (normalizedMap A B f hf r) := by
  intro y
  obtain ⟨x, hx⟩ := Homology.finsupp_map_surjective (I := List Generator) f hs y.val
  change coefficientMap f x = y.val at hx
  refine ⟨⟨normalizedRetraction A r x, normalizedRetraction_mem A r x⟩, ?_⟩
  apply Subtype.ext
  change coefficientMap f (normalizedRetraction A r x) = y.val
  rw [normalizedRetraction_natural A B f hf, hx,
    normalizedRetraction_eq_self B r y.val y.property]
theorem normalizedMap_exact {D : CyclicData k} (A : RightAction D L) (B : RightAction D M)
    (C : RightAction D N) (f : L →ₗ[k] M) (g : M →ₗ[k] N)
    (hf : ∀ a m, f (A.action a m) = B.action a (f m))
    (hg : ∀ a m, g (B.action a m) = C.action a (g m)) (r : ℕ)
    (h : Homology.ExactAt f g) :
    Homology.ExactAt (normalizedMap A B f hf r) (normalizedMap B C g hg r) := by
  intro y
  constructor
  · intro hy
    have hcycle : coefficientMap g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (Homology.exactAt_finsupp (I := List Generator) f g h y.val).mp hcycle
    change coefficientMap f x = y.val at hx
    refine ⟨⟨normalizedRetraction A r x, normalizedRetraction_mem A r x⟩, ?_⟩
    apply Subtype.ext
    change coefficientMap f (normalizedRetraction A r x) = y.val
    rw [normalizedRetraction_natural A B f hf, hx,
      normalizedRetraction_eq_self B r y.val y.property]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (Homology.exactAt_finsupp (I := List Generator) f g h (coefficientMap f x.val)).mpr ⟨x.val, rfl⟩
theorem filtration_normalized_short_exact {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}
    (s : D.FiltrationStep i U) (r : ℕ) :
    Function.Injective (normalizedMap (quotientRightAction D (next i) s.colon)
      (quotientRightAction D i s.smaller) s.inclusion (fun a m => (s.inclusion_action a m).symm) r) ∧
    Homology.ExactAt (normalizedMap (quotientRightAction D (next i) s.colon)
      (quotientRightAction D i s.smaller) s.inclusion (fun a m => (s.inclusion_action a m).symm) r)
      (normalizedMap (quotientRightAction D i s.smaller) (quotientRightAction D i U)
        s.projection (fun a m => (s.projection_action a m).symm) r) ∧
    Function.Surjective (normalizedMap (quotientRightAction D i s.smaller) (quotientRightAction D i U)
      s.projection (fun a m => (s.projection_action a m).symm) r) := by
  obtain ⟨hi, he, hs⟩ := s.short_exact
  exact ⟨normalizedMap_injective _ _ _ _ _ hi,
    normalizedMap_exact _ _ _ _ _ _ _ _ he, normalizedMap_surjective _ _ _ _ _ hs⟩
end
end Ginzburg333.Bar
