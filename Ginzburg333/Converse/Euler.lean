import Ginzburg333.Converse.LowDegree

namespace Ginzburg333.Ginzburg
open Ginzburg333.Homology
variable {k : Type*} [Field k]
noncomputable section

abbrev negativeTerm (n s : ℕ) := bigradedComponent (k := k) n (-(s : ℤ))

def negativeDifferential (w : Tensor k) (n s : ℕ) :
    negativeTerm (k := k) n (s + 1) →ₗ[k] negativeTerm (k := k) n s :=
  componentDifferential w n (-(s + 1 : ℕ) : ℤ) (-(s : ℤ)) (by omega)

theorem negativeDifferential_exact (w : Tensor k) (hw : GinzburgRegular w) (n s : ℕ) :
    ExactAt (negativeDifferential w n (s + 1)) (negativeDifferential w n s) := by
  intro x
  constructor
  · intro hx
    have hxc := (mem_bigradedComponent n (-(s + 1 : ℕ) : ℤ) x.val).mp x.property
    obtain ⟨y, hyq, hdy⟩ := hw (-(s + 1 : ℕ) : ℤ) (by omega) x.val hxc.2
      (congrArg Subtype.val hx)
    refine ⟨⟨internalProjection n y, ?_⟩, ?_⟩
    · apply (mem_bigradedComponent _ _ _).mpr
      refine ⟨internalProjection_internal n y, ?_⟩
      have he : (-(s + 1 : ℕ) : ℤ) - 1 = (-(s + 1 + 1 : ℕ) : ℤ) := by omega
      rw [he] at hyq
      exact internalProjection_cohomological n _ y hyq
    · apply Subtype.ext
      change differential w (internalProjection n y) = x.val
      rw [← internalProjection_differential, hdy, internalProjection_eq_self n _ hxc.1]
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact differential_square w y.val

theorem negativeTerm_eq_zero (n s : ℕ) (hs : 0 < s) (hns : n ≤ s)
    (x : negativeTerm (k := k) n s) : x = 0 := by
  apply Subtype.ext
  ext p
  by_cases hp : p ∈ x.val.support
  · obtain ⟨hi, hc⟩ := x.property hp
    rw [cohomologicalDegree_eq_length_sub_weight, hi] at hc
    have hl : p.val.2.length = 0 := by omega
    have he := List.length_eq_zero_iff.mp hl
    simp [internalDegree, he] at hi
    omega
  · exact Finsupp.not_mem_support_iff.mp hp

/-- The actual internal-degree-zero-cohomology quotient. -/
abbrev internalJacobi (w : Tensor k) (n : ℕ) :=
  negativeTerm (k := k) n 0 ⧸ LinearMap.range (negativeDifferential w n 0)

def negativeDimension (n s : ℕ) : ℕ := Module.finrank k (negativeTerm (k := k) n s)
def boundaryDimension (w : Tensor k) (n s : ℕ) : ℕ :=
  Module.finrank k (LinearMap.range (negativeDifferential w n s))

theorem negativeDimension_eq_boundaries (w : Tensor k) (hw : GinzburgRegular w) (n s : ℕ) :
    negativeDimension (k := k) n (s + 1) =
      boundaryDimension w n s + boundaryDimension w n (s + 1) := by
  have he := (exactAt_iff_range_eq_ker _ _).mp (negativeDifferential_exact w hw n s)
  have hd := LinearMap.finrank_range_add_finrank_ker (negativeDifferential w n s)
  rw [← he] at hd
  exact hd.symm

theorem boundaryDimension_terminal (w : Tensor k) (n : ℕ) : boundaryDimension w n n = 0 := by
  have hz : negativeDifferential w n n = 0 := by
    ext x
    rw [negativeTerm_eq_zero n (n + 1) (by omega) (by omega) x, map_zero]
    rfl
  simp [boundaryDimension, hz]

theorem jacobiDimension_add_boundary (w : Tensor k) (n : ℕ) :
    Module.finrank k (internalJacobi w n) + boundaryDimension w n 0 = negativeDimension (k := k) n 0 :=
  Submodule.finrank_quotient_add_finrank _

/-- Euler identity derived from actual Ginzburg exactness, without a resolution certificate. -/
theorem internalJacobi_finrank_euler (w : Tensor k) (hw : GinzburgRegular w) (n : ℕ) :
    (Module.finrank k (internalJacobi w n) : ℤ) =
      ∑ s ∈ Finset.range (n + 1), (-1 : ℤ) ^ s * (negativeDimension (k := k) n s : ℤ) := by
  have he (L : ℕ) :
      (∑ s ∈ Finset.range (L + 1), (-1 : ℤ) ^ s * (negativeDimension (k := k) n s : ℤ)) =
        (Module.finrank k (internalJacobi w n) : ℤ) +
          (-1 : ℤ) ^ L * (boundaryDimension w n L : ℤ) := by
    induction L with
    | zero =>
        have hd := jacobiDimension_add_boundary w n
        simpa using congrArg (fun a : ℕ => (a : ℤ)) hd.symm
    | succ L ih =>
        rw [Finset.sum_range_succ, ih, negativeDimension_eq_boundaries w hw n L, Nat.cast_add, pow_succ]
        ring
  rw [he n, boundaryDimension_terminal, Nat.cast_zero, mul_zero, add_zero]
end
end Ginzburg333.Ginzburg
