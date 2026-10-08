import Ginzburg333.Comparison.Reversal

/-! Finite word vectors for the transpose of the inner bar multiplication. -/
namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

def splitBasis (D : CyclicData k) (g : Generator) : WordSpace k :=
  ∑ h, ∑ t, positiveMultiplication D h t g • Finsupp.single [h, t] 1

theorem splitBasis_coefficient (D : CyclicData k) (g h t : Generator) :
    splitBasis D g [h, t] = positiveMultiplication D h t g := by
  classical
  simp [splitBasis, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, ite_and]

def cobarBasis (D : CyclicData k) : List Generator → WordSpace k
  | [] => 0
  | g :: gs => appendWords gs (splitBasis D g) - prependWords [g] (cobarBasis D gs)

def cobarDifferential (D : CyclicData k) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (cobarBasis D)

theorem splitBasis_internal (D : CyclicData k) (g : Generator) :
    splitBasis D g ∈ Finsupp.supported k k {gs | wordWeight gs = g.weight} := by
  classical
  apply Submodule.sum_mem
  intro h hh
  apply Submodule.sum_mem
  intro t ht
  by_cases hm : positiveMultiplication D h t g = 0
  · simp [hm]
  · apply Submodule.smul_mem
    apply Finsupp.single_mem_supported k 1
    have hw := (positiveMultiplication_support D h t g hm).2.2.2
    simpa using hw.symm

theorem splitBasis_length (D : CyclicData k) (g : Generator) :
    splitBasis D g ∈ Finsupp.supported k k {gs | gs.length = 2} := by
  classical
  apply Submodule.sum_mem
  intro h hh
  apply Submodule.sum_mem
  intro t ht
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported k 1 rfl

theorem cobarBasis_internal (D : CyclicData k) (gs : List Generator) :
    cobarBasis D gs ∈ Finsupp.supported k k {cs | wordWeight cs = wordWeight gs} := by
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      apply Submodule.sub_mem
      · apply Finsupp.supported_comap_lmapDomain k k
        intro cs hcs
        have h := splitBasis_internal D g hcs
        simpa [wordWeight_append, wordWeight_cons] using congrArg (· + wordWeight gs) h
      · apply Finsupp.supported_comap_lmapDomain k k
        intro cs hcs
        have h := ih hcs
        simpa [wordWeight_append, wordWeight_cons] using congrArg (g.weight + ·) h

theorem cobarBasis_length (D : CyclicData k) (gs : List Generator) :
    cobarBasis D gs ∈ Finsupp.supported k k {cs | cs.length = gs.length + 1} := by
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      apply Submodule.sub_mem
      · apply Finsupp.supported_comap_lmapDomain k k
        intro cs hcs
        have h := splitBasis_length D g hcs
        simp only [Set.mem_setOf_eq, Set.mem_preimage, List.length_append, List.length_cons,
          List.length_nil] at h ⊢
        omega
      · apply Finsupp.supported_comap_lmapDomain k k
        intro cs hcs
        have h := ih hcs
        simp only [Set.mem_setOf_eq, Set.mem_preimage, List.length_append, List.length_cons,
          List.length_singleton, List.length_nil] at h ⊢
        omega
end
end Ginzburg333.Comparison
