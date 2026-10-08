import Ginzburg333.Finite.RowIdeals
import Ginzburg333.Finite.Pencil

/-!
# The closed family and its concrete quotient short exact sequences

The family is not enumerated. A step decreases the dimension by one and
identifies the colon with another member. All quotient maps are induced by
the actual degree-one multiplication and identity maps on eight-dimensional rows.
-/
namespace Ginzburg333
open Module
variable {k : Type*} [Field k]

theorem finrank_sup_span_gt (U : Submodule k (Vec k)) {g : Vec k} (hg : g ∉ U) :
    finrank k U < finrank k (U ⊔ Submodule.span k {g} : Submodule k (Vec k)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne le_sup_left
  intro h
  have hm : g ∈ U ⊔ Submodule.span k {g} :=
    (show Submodule.span k {g} ≤ U ⊔ Submodule.span k {g} from le_sup_right)
      (Submodule.subset_span (by simp))
  rw [← h] at hm
  exact hg hm

theorem split_plane (U : Submodule k (Vec k)) (hU : finrank k U = 2)
    {a : Vec k} (haU : a ∈ U) (ha : a ≠ 0) :
    ∃ g : Vec k, g ∉ Submodule.span k {a} ∧
      U = Submodule.span k {a} ⊔ Submodule.span k {g} := by
  classical
  have hle : Submodule.span k {a} ≤ U := by
    apply Submodule.span_le.mpr
    simpa using haU
  have hne : Submodule.span k {a} ≠ U := by
    intro h
    have hh := congrArg (fun P : Submodule k (Vec k) => finrank k P) h
    change finrank k (Submodule.span k {a}) = finrank k U at hh
    rw [finrank_span_singleton ha, hU] at hh
    omega
  obtain ⟨g, hgU, hga⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hle' : Submodule.span k {a} ⊔ Submodule.span k {g} ≤ U := by
    apply sup_le hle
    apply Submodule.span_le.mpr
    simpa using hgU
  have hdim := finrank_sup_span_gt (Submodule.span k {a}) hga
  rw [finrank_span_singleton ha] at hdim
  have heq := Submodule.eq_of_le_of_finrank_le hle' (by rw [hU]; omega)
  exact ⟨g, hga, heq.symm⟩

theorem plane_sup_span_eq_top (U : Submodule k (Vec k)) (hU : finrank k U = 2)
    {g : Vec k} (hg : g ∉ U) : U ⊔ Submodule.span k {g} = ⊤ := by
  have hdim := finrank_sup_span_gt U hg
  rw [hU] at hdim
  apply Submodule.eq_of_le_of_finrank_le le_top
  simpa only [finrank_top, finrank_vec] using Nat.succ_le_of_lt hdim

namespace CyclicData

def Allowed (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) : Prop :=
  U = ⊥ ∨ (∃ a : Vec k, U = Submodule.span k {a} ∧ a ≠ 0 ∧
    finrank k (LinearMap.range (D.mul i a)) = 2) ∨ finrank k U = 2 ∨ U = ⊤

structure FiltrationStep (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) where
  smaller : Submodule k (Vec k)
  colon : Submodule k (Vec k)
  generator : Vec k
  smaller_allowed : D.Allowed i smaller
  colon_allowed : D.Allowed (next i) colon
  generator_outside : generator ∉ smaller
  decomposition : U = smaller ⊔ Submodule.span k {generator}
  size_drop : finrank k smaller + 1 = finrank k U
  colon_eq : (D.rowGenerated i smaller).comap (D.leftOne i generator) =
    D.rowGenerated (next i) colon

/-- Every nonzero member has a one-generator reduction within the same family. -/
theorem exists_filtrationStep [IsAlgClosed k] (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (U : Submodule k (Vec k)) (hU : D.Allowed i U) (hne : U ≠ ⊥) :
    Nonempty (D.FiltrationStep i U) := by
  classical
  rcases hU with hzero | ⟨a, rfl, ha, hr⟩ | hplane | rfl
  · exact (hne hzero).elim
  · have hkerdim := D.finrank_kernel_of_rank_two i a hr
    have hkerne : LinearMap.ker (D.mul i a) ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hkerdim
      omega
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).mp hkerne
    refine ⟨{
      smaller := ⊥
      colon := Submodule.span k {b}
      generator := a
      smaller_allowed := Or.inl rfl
      colon_allowed := Or.inr (Or.inl ⟨b, rfl, hb0, D.adjacent_rank_two hD i ha hb0 hb⟩)
      generator_outside := by simpa using ha
      decomposition := by simp
      size_drop := by simp [finrank_span_singleton ha]
      colon_eq := ?_ }⟩
    rw [D.rowGenerated_bot, Submodule.comap_bot, D.rowGenerated_span]
    exact D.annihilator_eq_adjacent_image hD i ha hb0 hr hb
  · obtain ⟨a, haU, ha, hr⟩ := D.plane_contains_rank_two hD i U hplane
    obtain ⟨g, hg, hsplit⟩ := split_plane U hplane haU ha
    have hpair : finrank k (Submodule.span k ({a, g} : Set (Vec k))) = 2 := by
      rw [Submodule.span_insert, ← hsplit]
      exact hplane
    refine ⟨{
      smaller := Submodule.span k {a}
      colon := D.colonPlane i a g
      generator := g
      smaller_allowed := Or.inr (Or.inl ⟨a, rfl, ha, hr⟩)
      colon_allowed := Or.inr (Or.inr (Or.inl (D.finrank_colonPlane hD i a g hr hpair)))
      generator_outside := hg
      decomposition := hsplit
      size_drop := by rw [finrank_span_singleton ha, hplane]
      colon_eq := ?_ }⟩
    rw [D.rowGenerated_span]
    exact D.plane_colon_closed hD i ha hg hr hpair
  · let a : Vec k := unitVec 0
    have ha : a ≠ 0 := by
      intro h
      have hh := congrFun h 0
      simp [a, unitVec] at hh
    let P : Submodule k (Vec k) := LinearMap.ker (dotMap a)
    have hP : finrank k P = 2 := finrank_dot_ker ha
    have haP : a ∉ P := by
      change ¬ dot a a = 0
      simp [a, unitVec]
    exact ⟨{
      smaller := P
      colon := ⊤
      generator := a
      smaller_allowed := Or.inr (Or.inr (Or.inl hP))
      colon_allowed := Or.inr (Or.inr (Or.inr rfl))
      generator_outside := haP
      decomposition := (plane_sup_span_eq_top P hP haP).symm
      size_drop := by rw [hP, finrank_top, finrank_vec]
      colon_eq := D.full_colon_closed hD i P hP haP }⟩

abbrev QuotientRow (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) :=
  Row k ⧸ D.rowGenerated i U

namespace FiltrationStep
variable {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}

theorem ideal_decomposition (s : D.FiltrationStep i U) :
    D.rowGenerated i U = D.rowGenerated i s.smaller ⊔ LinearMap.range (D.leftOne i s.generator) := by
  calc
    D.rowGenerated i U = D.rowGenerated i (s.smaller ⊔ Submodule.span k {s.generator}) :=
      congrArg (D.rowGenerated i) s.decomposition
    _ = D.rowGenerated i s.smaller ⊔ LinearMap.range (D.leftOne i s.generator) := by
      rw [D.rowGenerated_sup, D.rowGenerated_span]

theorem smaller_ideal_le (s : D.FiltrationStep i U) :
    D.rowGenerated i s.smaller ≤ D.rowGenerated i U := by
  rw [s.ideal_decomposition]
  exact le_sup_left

def inclusion (s : D.FiltrationStep i U) :
    D.QuotientRow (next i) s.colon →ₗ[k] D.QuotientRow i s.smaller :=
  (D.rowGenerated (next i) s.colon).mapQ (D.rowGenerated i s.smaller)
    (D.leftOne i s.generator) (by rw [s.colon_eq])

def projection (s : D.FiltrationStep i U) :
    D.QuotientRow i s.smaller →ₗ[k] D.QuotientRow i U :=
  (D.rowGenerated i s.smaller).mapQ (D.rowGenerated i U) LinearMap.id
    (by simpa using s.smaller_ideal_le)

@[simp] theorem inclusion_mkQ (s : D.FiltrationStep i U) (r : Row k) :
    s.inclusion ((D.rowGenerated (next i) s.colon).mkQ r) =
      (D.rowGenerated i s.smaller).mkQ (D.leftOne i s.generator r) := rfl

@[simp] theorem projection_mkQ (s : D.FiltrationStep i U) (r : Row k) :
    s.projection ((D.rowGenerated i s.smaller).mkQ r) =
      (D.rowGenerated i U).mkQ r := rfl

theorem short_exact (s : D.FiltrationStep i U) :
    Function.Injective s.inclusion ∧ Homology.ExactAt s.inclusion s.projection ∧
      Function.Surjective s.projection := by
  exact Homology.quotient_maps_short_exact _ _ _ _ _ s.smaller_ideal_le
    s.colon_eq s.ideal_decomposition

end FiltrationStep
end CyclicData
end Ginzburg333
