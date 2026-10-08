import Ginzburg333.Ginzburg.Homogeneous
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Prod

/-! Finiteness of each internal-degree path space. No infinite dual is taken. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]

theorem generator_card : Fintype.card Generator = 21 := by decide

theorem word_length_le_weight (gs : List Generator) : gs.length ≤ wordWeight gs := by
  have h := word_degree gs
  change (wordWeight gs : ℤ) = (gs.length : ℤ) + (wordNegative gs : ℤ) at h
  omega

instance finite_internal_basis (n : ℕ) : Finite {p : BasisPath // internalDegree p = n} := by
  classical
  letI : Fintype {gs : List Generator // gs.length ≤ n} :=
    (List.finite_length_le Generator n).fintype
  let f : {p : BasisPath // internalDegree p = n} →
      Vertex × {gs : List Generator // gs.length ≤ n} := fun p =>
    (p.val.val.1, ⟨p.val.val.2, by
      have h := word_length_le_weight p.val.val.2
      have hp : wordWeight p.val.val.2 = n := p.property
      omega⟩)
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun t : Vertex × {gs : List Generator // gs.length ≤ n} => t.1) h)
    (congrArg (fun t : Vertex × {gs : List Generator // gs.length ≤ n} => t.2.val) h)

noncomputable def internalComponent (n : ℕ) : Submodule k (PathSpace k) :=
  Finsupp.supported k k {p | internalDegree p = n}

noncomputable instance finiteDimensional_internalComponent (n : ℕ) :
    FiniteDimensional k (internalComponent (k := k) n) := by
  classical
  let e : internalComponent (k := k) n ≃ₗ[k] ({p : BasisPath // internalDegree p = n} →₀ k) :=
    Finsupp.supportedEquivFinsupp {p : BasisPath | internalDegree p = n}
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem cohomologicalDegree_nonpositive (p : BasisPath) : cohomologicalDegree p ≤ 0 := by
  unfold cohomologicalDegree
  omega

theorem homogeneous_positive_eq_zero (q : ℤ) (hq : 0 < q) (x : PathSpace k)
    (hx : Homogeneous q x) : x = 0 := by
  classical
  ext p
  by_cases hp : p ∈ x.support
  · have h := hx p hp
    have hle := cohomologicalDegree_nonpositive p
    omega
  · exact Finsupp.not_mem_support_iff.mp hp

end Ginzburg333.Ginzburg
