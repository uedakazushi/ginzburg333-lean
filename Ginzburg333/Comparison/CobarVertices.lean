import Ginzburg333.Comparison.Transpose

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem cobarBasis_startsAt (D : CyclicData k) (gs : List Generator) (i : Vertex) (hi : startsAt i gs) :
    cobarBasis D gs ∈ Finsupp.supported k k {cs | startsAt i cs} := by
  classical
  induction gs generalizing i with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      obtain ⟨hgi, hgs⟩ := (startsAt_cons i g gs).mp hi
      apply Submodule.sub_mem
      · rw [splitBasis]
        simp only [map_sum, map_smul, appendWords_single, List.cons_append, List.nil_append]
        apply Submodule.sum_mem
        intro h hh
        apply Submodule.sum_mem
        intro t ht
        by_cases hm : positiveMultiplication D h t g = 0
        · simp [hm]
        · apply Submodule.smul_mem
          apply Finsupp.single_mem_supported k 1
          obtain ⟨hht, hgh, hgt, hw⟩ := positiveMultiplication_support D h t g hm
          apply (startsAt_cons i h (t :: gs)).mpr
          refine ⟨hgh.symm.trans hgi, ?_⟩
          apply (startsAt_cons h.target t gs).mpr
          refine ⟨hht.symm, ?_⟩
          simpa only [← hgt] using hgs
      · apply Finsupp.supported_comap_lmapDomain k k
        intro cs hcs
        apply (startsAt_cons i g cs).mpr
        exact ⟨hgi, ih g.target hgs hcs⟩

theorem cobarBasis_scalar_mem (D : CyclicData k) (i : Vertex) (r n : ℕ) (gs : SimpleRowBasis i r n) :
    cobarBasis D gs.val ∈ scalarSimpleTerm (k := k) i (r + 1) n := by
  intro cs hcs
  refine ⟨cobarBasis_startsAt D gs.val i gs.property.1 hcs, ?_, ?_⟩
  · simpa only [gs.property.2.1] using cobarBasis_length D gs.val hcs
  · simpa only [gs.property.2.2] using cobarBasis_internal D gs.val hcs
end
end Ginzburg333.Comparison
