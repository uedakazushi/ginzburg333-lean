import Ginzburg333.Finite.Rank

/-!
# The annihilator calculation as equality of kernels and images

A row e_i E has graded pieces k, k³, k³, k. `leftOne D i a` is
left multiplication by the degree-one vector a on the adjacent row.
The theorem `annihilator_eq_adjacent_image` compares all four degrees, not
merely the degree-one kernel.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333
open Module
variable {k : Type*} [Field k]

abbrev Row (k : Type*) := k × Vec k × Vec k × k

@[simp] theorem finrank_row : finrank k (Row k) = 8 := by
  simp [Row, Vec]

namespace CyclicData

/-- Multiplication by a degree-one element, as a linear map between rows. -/
def leftOne (D : CyclicData k) (i : Vertex) (a : Vec k) : Row k →ₗ[k] Row k where
  toFun r := (0, r.1 • a, D.mul i a r.2.1, dot a r.2.2.1)
  map_add' := by
    rintro ⟨s, b, v, t⟩ ⟨s', b', v', t'⟩
    simp [add_smul, dot_add_right]
  map_smul' := by
    intro t r
    rcases r with ⟨s, b, v, u⟩
    simp [smul_smul, dot_smul_right]

@[simp] theorem leftOne_apply (D : CyclicData k) (i : Vertex)
    (a : Vec k) (s : k) (b v : Vec k) (t : k) :
    D.leftOne i a (s, b, v, t) = (0, s • a, D.mul i a b, dot a v) := rfl

/-- Two adjacent degree-one multiplication maps compose to zero
when their tensor contraction vanishes. -/
theorem leftOne_comp_zero (D : CyclicData k) (i : Vertex)
    {a b : Vec k} (hab : D.mul i a b = 0) :
    (D.leftOne i a).comp (D.leftOne (next i) b) = 0 := by
  apply LinearMap.ext
  intro r
  rcases r with ⟨s, c, v, t⟩
  have hz : dot a (D.mul (next i) b c) = 0 := by
    rw [← D.cyclic, hab, dot_zero_left]
  simp [leftOne, hab, hz]

/-- Lemma C in a concrete eight-dimensional form. It is independent of
any implementation of right ideals or of a bar resolution. -/
theorem annihilator_eq_adjacent_image (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) {a b : Vec k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hr : finrank k (LinearMap.range (D.mul i a)) = 2)
    (hab : D.mul i a b = 0) :
    LinearMap.ker (D.leftOne i a) =
      LinearMap.range (D.leftOne (next i) b) := by
  apply le_antisymm
  · intro r hrker
    rcases r with ⟨s, y, z, t⟩
    have hzero : D.leftOne i a (s, y, z, t) = 0 := hrker
    have hs : s • a = 0 := congrArg (fun r : Row k => r.2.1) hzero
    have hy : D.mul i a y = 0 := congrArg (fun r : Row k => r.2.2.1) hzero
    have hz : dot a z = 0 := congrArg (fun r : Row k => r.2.2.2) hzero
    have hs0 : s = 0 := (smul_eq_zero.mp hs).resolve_right ha
    have hyspan : y ∈ Submodule.span k {b} := by
      rw [← D.kernel_eq_span i hr hb hab]
      exact hy
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hyspan
    have hzrange : z ∈ LinearMap.range (D.mul (next i) b) := by
      rw [D.adjacent_range_eq_dot_ker hD i ha hb hab]
      exact hz
    obtain ⟨c, hc⟩ := hzrange
    obtain ⟨v, hv⟩ := dotMap_surjective hb t
    refine ⟨(u, c, v, 0), ?_⟩
    change (0, u • b, D.mul (next i) b c, dot b v) = (s, y, z, t)
    change dot b v = t at hv
    rw [hs0, hu, hc, hv]
  · rintro r ⟨s, rfl⟩
    change D.leftOne i a (D.leftOne (next i) b s) = 0
    have hh := congrArg (fun f : Row k →ₗ[k] Row k => f s)
      (D.leftOne_comp_zero i hab)
    exact hh

end CyclicData
end Ginzburg333
