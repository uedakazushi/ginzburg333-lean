import Ginzburg333.Bar.Internal

/-! Orthogonal internal-degree projections commute with the actual differential. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

theorem internalProjection_on_component (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n t : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ internalComponent D i U t) :
    internalProjection D i U n x = if n = t then x else 0 := by
  classical
  by_cases h : n = t
  · subst n; simp [internalProjection_eq_self D i U t x hx]
  · rw [if_neg h]
    ext gs
    rw [internalProjection_apply]
    simp only [coefficientProjection, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hn : d.val + wordWeight gs = n
    · have ht : d.val + wordWeight gs ≠ t := by omega
      simpa only [if_pos hn] using hx gs d ht
    · simp only [if_neg hn, LinearMap.zero_apply]

theorem internalProjection_differential (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U)) :
    internalProjection D i U n (ambientDifferential (quotientRightAction D i U) x) =
      ambientDifferential (quotientRightAction D i U) (internalProjection D i U n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs m =>
      rw [← D.quotientProjection_sum i U m]
      have heq : Finsupp.single gs (∑ d : Fin 4, D.quotientProjection i U d m) =
          ∑ d : Fin 4, Finsupp.single gs (D.quotientProjection i U d m) :=
        map_sum (Finsupp.lsingle gs : D.QuotientRow i U →ₗ[k] Ambient (D.QuotientRow i U)).toAddMonoidHom _ _
      rw [heq]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hx := internal_single_projected D i U gs e m
      rw [internalProjection_on_component D i U n _ _ hx,
        internalProjection_on_component D i U n _ _ (ambientDifferential_internal D i U _ _ hx)]
      split_ifs <;> simp

theorem internallyNormalizedTerm_eq_bot (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) (hn : n < r) :
    internallyNormalizedTerm D i U r n = ⊥ := by
  classical
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  ext gs
  by_cases hg : gs ∈ x.support
  · have hl := hx.1.2 hg
    have hw := word_length_le_weight gs
    change gs.length = r at hl
    have he : ∀ d : Fin 4, D.quotientProjection i U d (x gs) = 0 := by
      intro d
      apply hx.2 gs d
      omega
    have hs := D.quotientProjection_sum i U (x gs)
    simpa only [he, Finset.sum_const_zero] using hs.symm
  · exact Finsupp.not_mem_support_iff.mp hg
end
end Ginzburg333.Bar
