import Ginzburg333.Bar.Corners
import Ginzburg333.Bar.Support

/-! The normalized bar differential and coefficient maps as actual linear maps. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
noncomputable section
def firstSource : List Generator → Option Vertex
  | [] => none
  | g :: _ => some g.source
theorem innerBasisDifferential_composable (D : CyclicData k) (gs : List Generator) (hc : composable gs) :
    innerBasisDifferential D gs ∈ Finsupp.supported k k
      {as | composable as ∧ firstSource as = firstSource gs} := by
  classical
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      cases gs with
      | nil => exact Submodule.zero_mem _
      | cons h cs =>
          obtain ⟨hgh, hcs⟩ := hc
          apply Submodule.sub_mem
          · apply Submodule.sum_mem
            intro t ht
            by_cases hm : positiveMultiplication D g h t = 0
            · simp [hm]
            · obtain ⟨_, hsource, htarget, _⟩ := positiveMultiplication_support D g h t hm
              apply Submodule.smul_mem
              apply Finsupp.single_mem_supported k 1
              constructor
              · cases cs with
                | nil => trivial
                | cons l ds => exact ⟨htarget.trans hcs.1, hcs.2⟩
              · exact congrArg some hsource
          · apply Finsupp.supported_comap_lmapDomain k k
            intro as has
            obtain ⟨hca, hfa⟩ := ih hcs has
            cases as with
            | nil => simp [firstSource] at hfa
            | cons l ds =>
                have heq : l.source = h.source := Option.some.inj hfa
                exact ⟨⟨hgh.trans heq.symm, hca⟩, rfl⟩
theorem initialProjection_eq_of_firstSource {D : CyclicData k} (A : RightAction D M)
    (as bs : List Generator) (hf : firstSource as = firstSource bs) :
    initialProjection A as = initialProjection A bs := by
  cases as with
  | nil => cases bs <;> simp [firstSource] at hf ⊢
  | cons g gs =>
      cases bs with
      | nil => simp [firstSource] at hf
      | cons h hs => exact congrArg (cornerProjection A) (Option.some.inj hf)
theorem balanced_single {D : CyclicData k} (A : RightAction D M) (gs : List Generator) (m : M)
    (hc : composable gs) (hm : initialProjection A gs m = m) :
    Finsupp.single gs m ∈ balancedAmbient A := by
  apply (mem_balancedAmbient_iff _ _).mpr
  simp [normalization_single, hc, hm]
theorem tensorWords_balanced {D : CyclicData k} (A : RightAction D M) (gs : List Generator)
    (x : WordSpace k)
    (hx : x ∈ Finsupp.supported k k {as | composable as ∧ firstSource as = firstSource gs})
    (m : M) (hm : initialProjection A gs m = m) :
    tensorWords x m ∈ balancedAmbient A := by
  classical
  change (x.support.sum (fun as => x as • (Finsupp.lsingle as : M →ₗ[k] Ambient M))) m ∈ _
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro as has
  apply Submodule.smul_mem
  obtain ⟨hc, hf⟩ := hx has
  apply balanced_single A as m hc
  rw [initialProjection_eq_of_firstSource A as gs hf]
  exact hm
theorem onWord_balanced {D : CyclicData k} (A : RightAction D M)
    (gs : List Generator) (m : M) (hc : composable gs) (hm : initialProjection A gs m = m) :
    onWord A gs m ∈ balancedAmbient A := by
  cases gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs =>
      apply Submodule.add_mem
      · apply Submodule.neg_mem
        apply balanced_single A gs (A.action (positiveBasis g) m)
        · cases gs with
          | nil => trivial
          | cons h cs => exact hc.2
        · cases gs with
          | nil => rfl
          | cons h cs =>
              change A.action (vertexIdempotent h.source) (A.action (positiveBasis g) m) = _
              rw [A.assoc, ← hc.1, positiveBasis_right_corner]
      · exact tensorWords_balanced A _ _ (innerBasisDifferential_composable D _ hc) m hm
theorem ambientDifferential_balanced {D : CyclicData k} (A : RightAction D M)
    (x : Ambient M) (hx : x ∈ balancedAmbient A) :
    ambientDifferential A x ∈ balancedAmbient A := by
  rw [← (mem_balancedAmbient_iff A x).mp hx]
  suffices h : ∀ y : Ambient M, ambientDifferential A (normalization A y) ∈ balancedAmbient A from h x
  intro y
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  | single gs m =>
      rw [normalization_single]
      by_cases hc : composable gs
      · rw [if_pos hc, ambientDifferential_single]
        exact onWord_balanced A gs _ hc (initialProjection_idempotent A gs m)
      · simp [hc]
def normalizedDifferential {D : CyclicData k} (A : RightAction D M) (r : ℕ) :
    normalizedTerm A (r + 1) →ₗ[k] normalizedTerm A r where
  toFun x := ⟨ambientDifferential A x.val,
    ambientDifferential_balanced A _ x.property.1,
    ambientDifferential_homological A r _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _
theorem normalizedDifferential_square {D : CyclicData k} (A : RightAction D M) (r : ℕ)
    (x : normalizedTerm A (r + 1 + 1)) :
    normalizedDifferential A r (normalizedDifferential A (r + 1) x) = 0 := by
  apply Subtype.ext
  exact ambientDifferential_square A x.val
theorem coefficientMap_length (f : M →ₗ[k] N) (r : ℕ) (x : Ambient M)
    (hx : x ∈ lengthComponent (k := k) r) :
    coefficientMap f x ∈ lengthComponent (k := k) r := by
  intro gs hgs
  apply hx
  change gs ∈ (coefficientMap f x).support at hgs
  change gs ∈ x.support
  rw [Finsupp.mem_support_iff] at hgs ⊢
  intro heq
  apply hgs
  change f (x gs) = 0
  rw [heq, map_zero]
theorem coefficientMap_balanced {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m))
    (x : Ambient M) (hx : x ∈ balancedAmbient A) : coefficientMap f x ∈ balancedAmbient B := by
  apply (mem_balancedAmbient_iff _ _).mpr
  rw [← normalization_natural A B f hf, (mem_balancedAmbient_iff _ _).mp hx]
def normalizedMap {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (r : ℕ) :
    normalizedTerm A r →ₗ[k] normalizedTerm B r where
  toFun x := ⟨coefficientMap f x.val,
    coefficientMap_balanced A B f hf _ x.property.1, coefficientMap_length f r _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _
theorem normalizedDifferential_natural {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (r : ℕ)
    (x : normalizedTerm A (r + 1)) :
    normalizedMap A B f hf r (normalizedDifferential A r x) =
      normalizedDifferential B r (normalizedMap A B f hf (r + 1) x) := by
  apply Subtype.ext
  exact ambientDifferential_natural A B f hf x.val
end
end Ginzburg333.Bar
