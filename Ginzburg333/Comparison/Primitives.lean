import Ginzburg333.Comparison.FiniteChain
import Ginzburg333.Comparison.PathVertices
import Ginzburg333.Comparison.DualExact

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem rowPath_primitive [IsAlgClosed k] (w : Tensor k) (hD : (ofTensor w).Regular)
    (i : Vertex) (r n : ℕ) (hne : n ≠ r + 1)
    (x : rowPathComponent (k := k) i (r + 1) n) (hdx : differential w x.val = 0) :
    ∃ y : rowPathComponent (k := k) i r n, differential w y.val = x.val := by
  let e := finiteDualReversal (ofTensor w) hD i (r + 1) n
  let f := e.symm x
  have hf : (internallyNormalizedDifferential (ofTensor w) i ⊤ (r + 1) n).dualMap f = 0 := by
    apply (finiteDualReversal (ofTensor w) hD i (r + 1 + 1) n).injective
    apply Subtype.ext
    rw [map_zero]
    rw [finiteDualReversal_differential]
    have he : finiteDualReversal (ofTensor w) hD i (r + 1) n f = x := e.apply_symm_apply x
    rw [he, hdx]
    rfl
  obtain ⟨g, hg⟩ := (simple_dual_bar_off_diagonal (ofTensor w) hD i r n hne f).mp hf
  refine ⟨finiteDualReversal (ofTensor w) hD i r n g, ?_⟩
  rw [← finiteDualReversal_differential, hg]
  exact congrArg Subtype.val (e.apply_symm_apply x)

/-- Actual internally homogeneous primitives from tensor regularity. -/
theorem ginzburg_internal_primitives [IsAlgClosed k] (w : Tensor k) (hD : (ofTensor w).Regular)
    (n : ℕ) (q : ℤ) (hq : q < 0) (x : PathSpace k)
    (hxn : InternallyHomogeneous n x) (hxq : Homogeneous q x) (hdx : differential w x = 0) :
    ∃ y : PathSpace k, InternallyHomogeneous n y ∧ Homogeneous (q - 1) y ∧ differential w y = x := by
  classical
  by_cases hz : x = 0
  · subst x
    refine ⟨0, ?_, ?_, map_zero _⟩
    all_goals intro p hp; simp at hp
  · have hex : ∃ p, x p ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      ext p
      exact h p
    obtain ⟨p, hp⟩ := hex
    have hps := Finsupp.mem_support_iff.mpr hp
    have hn := hxn p hps
    have hq0 := hxq p hps
    cases hs : p.val.2 with
    | nil =>
        simp [cohomologicalDegree, hs] at hq0
        omega
    | cons g gs =>
        have heq : q = ((gs.length + 1 : ℕ) : ℤ) - (n : ℤ) := by
          rw [cohomologicalDegree_eq_length_sub_weight, hs, List.length_cons, hn] at hq0
          exact hq0.symm
        have hne : n ≠ gs.length + 1 := by omega
        have hxbi : x ∈ bigradedComponent (k := k) n (((gs.length + 1 : ℕ) : ℤ) - (n : ℤ)) := by
          apply (mem_bigradedComponent _ _ _).mpr
          exact ⟨hxn, heq ▸ hxq⟩
        have hxi (i : Vertex) : differential w (vertexProjection i x) = 0 := by
          rw [← vertexProjection_differential, hdx, map_zero]
        have hprim (i : Vertex) : ∃ y : rowPathComponent (k := k) i gs.length n,
            differential w y.val = vertexProjection i x :=
          rowPath_primitive w hD i gs.length n hne
            ⟨vertexProjection i x, vertexProjection_row_mem i (gs.length + 1) n x hxbi⟩ (hxi i)
        choose y hy using hprim
        have hdeg : q - 1 = (gs.length : ℤ) - (n : ℤ) := by omega
        have hys : (∑ i, (y i).val) ∈ bigradedComponent (k := k) n (q - 1) := by
          rw [hdeg]
          apply Submodule.sum_mem
          intro i hi
          exact rowPathComponent_bigraded i gs.length n (y i)
        obtain ⟨hyN, hyQ⟩ := (mem_bigradedComponent _ _ _).mp hys
        refine ⟨∑ i, (y i).val, hyN, hyQ, ?_⟩
        rw [map_sum]
        simp only [hy]
        exact sum_vertexProjection x
end
end Ginzburg333.Comparison

namespace Ginzburg333
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
/-- Avatar-free negative acyclicity of the original finite-support Ginzburg complex. -/
theorem tensorRegular_ginzburgRegular (w : Tensor k) (hw : TensorRegular w) :
    Ginzburg.GinzburgRegular w := by
  apply Ginzburg.ginzburgRegular_of_internal_primitives
  change (ofTensor w).Regular at hw
  exact Comparison.ginzburg_internal_primitives w hw
end Ginzburg333
