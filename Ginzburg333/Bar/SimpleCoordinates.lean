import Ginzburg333.Bar.PathBasis

/-! Scalar coordinates for the actual internally normalized simple-row terms. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

@[simp] theorem coefficientMap_apply {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (f : M →ₗ[k] N) (x : Ambient M) (gs : List Generator) :
    coefficientMap f x gs = f (x gs) := rfl

def scalarSimpleTerm (i : Vertex) (r n : ℕ) : Submodule k (WordSpace k) :=
  Finsupp.supported k k {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}

theorem simpleScalar_mem (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (x : internallyNormalizedTerm D i ⊤ r n) :
    coefficientMap (simpleCoefficient D hD i) x.val ∈ scalarSimpleTerm (k := k) i r n := by
  intro gs hgs
  have hnz : simpleCoefficient D hD i (x.val gs) ≠ 0 := Finsupp.mem_support_iff.mp hgs
  have hxgs : x.val gs ≠ 0 := by intro h; exact hnz (by rw [h, map_zero])
  have hb := congrArg (fun y : Ambient (D.QuotientRow i ⊤) => y gs)
    ((mem_balancedAmbient_iff _ _).mp x.property.1.1)
  dsimp only at hb
  rw [normalization_apply] at hb
  have hc : composable gs := by
    by_contra h; rw [if_neg h] at hb; exact hxgs hb.symm
  rw [if_pos hc] at hb
  have hs : startsAt i gs := by
    refine ⟨hc, ?_⟩
    cases gs with
    | nil => trivial
    | cons g gs =>
        change D.quotientAction i ⊤ (vertexIdempotent g.source) (x.val (g :: gs)) = _ at hb
        rw [simpleRow_corner D hD] at hb
        by_contra hi
        rw [if_neg (Ne.symm hi)] at hb
        exact hxgs hb.symm
  have hl := x.property.1.2 (Finsupp.mem_support_iff.mpr hxgs)
  have hw : wordWeight gs = n := by
    by_contra h
    have hz := x.property.2 gs (0 : Fin 4) (by simpa using h)
    rw [simpleRow_degree D hD] at hz
    simp only [if_pos rfl] at hz
    exact hxgs hz
  exact ⟨hs, hl, hw⟩

def simpleScalarMap (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    internallyNormalizedTerm D i ⊤ r n →ₗ[k] scalarSimpleTerm (k := k) i r n where
  toFun x := ⟨coefficientMap (simpleCoefficient D hD i) x.val, simpleScalar_mem D hD i r n x⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

def simpleUnitMap (D : CyclicData k) (i : Vertex) : k →ₗ[k] D.QuotientRow i ⊤ :=
  LinearMap.toSpanSingleton k _ (simpleUnit D i)

theorem simpleUnit_mem (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (x : scalarSimpleTerm (k := k) i r n) :
    coefficientMap (simpleUnitMap D i) x.val ∈ internallyNormalizedTerm D i ⊤ r n := by
  classical
  have hb : coefficientMap (simpleUnitMap D i) x.val ∈ balancedAmbient (quotientRightAction D i ⊤) := by
    apply (mem_balancedAmbient_iff _ _).mpr
    ext gs
    rw [normalization_apply, coefficientMap_apply]
    by_cases hx : gs ∈ x.val.support
    · obtain ⟨⟨hc, hs⟩, hl, hw⟩ := x.property hx
      rw [if_pos hc]
      cases gs with
      | nil => rfl
      | cons g gs =>
          change D.quotientAction i ⊤ (vertexIdempotent g.source) _ = _
          rw [simpleRow_corner D hD, if_pos hs.symm]
    · rw [Finsupp.not_mem_support_iff.mp hx, map_zero]
      simp
  have hl : coefficientMap (simpleUnitMap D i) x.val ∈ lengthComponent (k := k) r := by
    apply coefficientMap_length
    intro gs hgs
    exact (x.property hgs).2.1
  refine ⟨⟨hb, hl⟩, ?_⟩
  intro gs d hn
  rw [coefficientMap_apply, simpleRow_degree D hD]
  by_cases hx : gs ∈ x.val.support
  · have hw := (x.property hx).2.2
    have hd : d ≠ 0 := by intro h; subst d; exact hn (by simpa using hw)
    rw [if_neg hd]
  · rw [Finsupp.not_mem_support_iff.mp hx, map_zero]
    split_ifs <;> rfl

def simpleUnitBarMap (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    scalarSimpleTerm (k := k) i r n →ₗ[k] internallyNormalizedTerm D i ⊤ r n where
  toFun x := ⟨coefficientMap (simpleUnitMap D i) x.val, simpleUnit_mem D hD i r n x⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

/-- This identifies actual normalized terms, including their coefficient vertex condition. -/
def simpleBarCoordinatesEquiv (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    internallyNormalizedTerm D i ⊤ r n ≃ₗ[k] scalarSimpleTerm (k := k) i r n where
  toLinearMap := simpleScalarMap D hD i r n
  invFun := simpleUnitBarMap D hD i r n
  left_inv := by
    intro x
    apply Subtype.ext
    ext gs
    change simpleCoefficient D hD i (x.val gs) • simpleUnit D i = x.val gs
    exact (simpleRow_expand D hD i _).symm
  right_inv := by
    intro x
    apply Subtype.ext
    ext gs
    change simpleCoefficient D hD i (x.val gs • simpleUnit D i) = x.val gs
    simp
end
end Ginzburg333.Bar
