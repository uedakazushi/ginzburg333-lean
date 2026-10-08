import Ginzburg333.Bar.SquareZero
import Ginzburg333.Ginzburg.FiniteDegree
import Ginzburg333.Homology.Finsupp

namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {M : Type*} [AddCommGroup M] [Module k M]
noncomputable section
def lengthComponent (r : ℕ) : Submodule k (Ambient M) :=
  Finsupp.supported M k {gs | gs.length = r}
theorem tensorWords_mem_supported (S : Set (List Generator)) (x : WordSpace k)
    (hx : x ∈ Finsupp.supported k k S) (m : M) :
    tensorWords x m ∈ Finsupp.supported M k S := by
  classical
  change (x.support.sum (fun gs => x gs • (Finsupp.lsingle gs : M →ₗ[k] Ambient M))) m ∈ _
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro gs hgs
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported k m (hx hgs)
theorem innerBasisDifferential_homological (D : CyclicData k) (gs : List Generator) :
    innerBasisDifferential D gs ∈ Finsupp.supported k k {cs | cs.length + 1 = gs.length} := by
  classical
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      cases gs with
      | nil => exact Submodule.zero_mem _
      | cons h cs =>
          apply Submodule.sub_mem
          · apply Submodule.sum_mem
            intro t ht
            apply Submodule.smul_mem
            exact Finsupp.single_mem_supported k 1 (by simp)
          · apply Finsupp.supported_comap_lmapDomain k k
            intro as has
            have hi := ih has
            simp only [Set.mem_preimage, Set.mem_setOf_eq, List.length_append,
              List.length_singleton, List.length_cons, List.length_nil] at hi ⊢
            omega
theorem onWord_homological {D : CyclicData k} (A : RightAction D M) (gs : List Generator) (m : M) :
    onWord A gs m ∈ Finsupp.supported M k {cs | cs.length + 1 = gs.length} := by
  cases gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs =>
      apply Submodule.add_mem
      · apply Submodule.neg_mem
        exact Finsupp.single_mem_supported k _ (by simp)
      · exact tensorWords_mem_supported _ _ (innerBasisDifferential_homological D _) m
theorem ambientDifferential_homological {D : CyclicData k} (A : RightAction D M)
    (r : ℕ) (x : Ambient M) (hx : x ∈ lengthComponent (k := k) (r + 1)) :
    ambientDifferential A x ∈ lengthComponent (k := k) r := by
  classical
  change x.support.sum (fun gs => onWord A gs (x gs)) ∈ _
  apply Submodule.sum_mem
  intro gs hgs
  have h := onWord_homological A gs (x gs)
  intro cs hcs
  have he := h hcs
  have hg := hx hgs
  simp only [Set.mem_setOf_eq] at he hg ⊢
  omega
def homologicalDifferential {D : CyclicData k} (A : RightAction D M) (r : ℕ) :
    lengthComponent (k := k) (M := M) (r + 1) →ₗ[k] lengthComponent (k := k) (M := M) r where
  toFun x := ⟨ambientDifferential A x.val, ambientDifferential_homological A r _ x.property⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _
theorem homologicalDifferential_square {D : CyclicData k} (A : RightAction D M) (r : ℕ)
    (x : lengthComponent (k := k) (M := M) (r + 1 + 1)) :
    homologicalDifferential A r (homologicalDifferential A (r + 1) x) = 0 := by
  apply Subtype.ext
  exact ambientDifferential_square A x.val
instance finite_length_basis (r : ℕ) : Finite {gs : List Generator // gs.length = r} :=
  (List.finite_length_eq Generator r).to_subtype
instance finiteDimensional_lengthComponent [FiniteDimensional k M] (r : ℕ) :
    FiniteDimensional k (lengthComponent (k := k) (M := M) r) := by
  classical
  let e : lengthComponent (k := k) (M := M) r ≃ₗ[k] ({gs : List Generator // gs.length = r} →₀ M) :=
    Finsupp.supportedEquivFinsupp {gs : List Generator | gs.length = r}
  exact FiniteDimensional.of_injective e.toLinearMap e.injective
theorem filtration_ambient_short_exact {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}
    (s : D.FiltrationStep i U) :
    Function.Injective (coefficientMap s.inclusion : Ambient (D.QuotientRow (next i) s.colon) →ₗ[k] _) ∧
      Homology.ExactAt (coefficientMap s.inclusion : Ambient (D.QuotientRow (next i) s.colon) →ₗ[k] _)
        (coefficientMap s.projection) ∧ Function.Surjective
          (coefficientMap s.projection : Ambient (D.QuotientRow i s.smaller) →ₗ[k] _) :=
  Homology.short_exact_finsupp _ _ s.short_exact
end
end Ginzburg333.Bar
