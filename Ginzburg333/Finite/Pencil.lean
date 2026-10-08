import Ginzburg333.Finite.Rank

/-!
# Singular members of a pencil

This is a linear-algebraic reformulation of the determinant-root argument in
Section 3 of the source note. Over an algebraically closed field, if μ(b) is
invertible, an eigenvector of μ(b)⁻¹ μ(a) gives a noninjective μ(a - t • b).
No determinant polynomial has to be constructed in Lean.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333
open Module
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- A two-dimensional family of endomorphisms has a noninjective member
represented by a nonzero vector of the parameter plane. -/
theorem exists_noninjective_in_plane
    (μ : Vec k →ₗ[k] Vec k →ₗ[k] Vec k)
    (U : Submodule k (Vec k)) {a b : Vec k}
    (haU : a ∈ U) (hbU : b ∈ U) (hb : b ≠ 0)
    (hab : ∀ t : k, a ≠ t • b) :
    ∃ c : Vec k, c ∈ U ∧ c ≠ 0 ∧ ¬ Function.Injective (μ c) := by
  classical
  by_cases hB : Function.Injective (μ b)
  · let e : Vec k ≃ₗ[k] Vec k :=
      LinearEquiv.ofBijective (μ b) ⟨hB, LinearMap.surjective_of_injective hB⟩
    let f : Module.End k (Vec k) := e.symm.toLinearMap.comp (μ a)
    obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue f
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (f.eigenspace t)).mp ht
    have hfx : f x = t • x := Module.End.mem_eigenspace_iff.mp hx
    have hAx : μ a x = t • μ b x := by
      have hh := congrArg (fun y : Vec k => e y) hfx
      change e (e.symm (μ a x)) = e (t • x) at hh
      rw [e.apply_symm_apply, e.map_smul] at hh
      exact hh
    refine ⟨a - t • b, U.sub_mem haU (U.smul_mem t hbU),
      sub_ne_zero.mpr (hab t), ?_⟩
    intro hinj
    have hzero : μ (a - t • b) x = 0 := by
      simp [hAx]
    apply hx0
    apply hinj
    simpa using hzero
  · exact ⟨b, hbU, hb, hB⟩

namespace CyclicData

/-- Lemma B: every plane contains a nonzero rank-two contraction. -/
theorem plane_contains_rank_two (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (U : Submodule k (Vec k)) (hU : finrank k U = 2) :
    ∃ a : Vec k, a ∈ U ∧ a ≠ 0 ∧
      finrank k (LinearMap.range (D.mul i a)) = 2 := by
  classical
  let bU : Basis (Fin 2) k U := (Module.finBasis k U).reindex (finCongr hU)
  let a : Vec k := (bU 0 : U)
  let b : Vec k := (bU 1 : U)
  have hb : b ≠ 0 := by
    intro h
    apply bU.ne_zero 1
    apply Subtype.ext
    exact h
  have hab : ∀ t : k, a ≠ t • b := by
    intro t h
    have h' : bU 0 = t • bU 1 := by
      apply Subtype.ext
      exact h
    have hh := congrArg (fun v : U => bU.repr v 0) h'
    simpa using hh
  obtain ⟨c, hcU, hc, hci⟩ := exists_noninjective_in_plane (D.mul i) U
    (bU 0).property (bU 1).property hb hab
  exact ⟨c, hcU, hc, D.rank_two_of_not_injective hD i hc hci⟩

end CyclicData
end Ginzburg333
