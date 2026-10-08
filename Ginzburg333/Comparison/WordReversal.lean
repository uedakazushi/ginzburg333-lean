import Ginzburg333.Comparison.Cobar
import Ginzburg333.Comparison.Generators
import Mathlib.Algebra.Ring.Commute

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

def signedWordReversal : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (fun gs => wordSign (k := k) gs • Finsupp.single gs.reverse (1 : k))

@[simp] theorem signedWordReversal_single (gs : List Generator) (a : k) :
    signedWordReversal (Finsupp.single gs a) = wordSign (k := k) gs • Finsupp.single gs.reverse a := by
  simp [signedWordReversal, Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem wordSign_cons (g : Generator) (gs : List Generator) :
    wordSign (k := k) (g :: gs) =
      (-1 : k) ^ (wordWeight gs + gs.length + Signs.three g.weight) * wordSign gs := by
  simp only [wordSign, List.map_cons, Signs.sigma, wordWeight, List.length_map]
  rw [pow_add, pow_add, pow_add]
  ring

theorem signedWordReversal_prepend (g : Generator) (r n : ℕ) (x : WordSpace k)
    (hx : x ∈ Finsupp.supported k k {gs | gs.length = r ∧ wordWeight gs = n}) :
    signedWordReversal (prependWords [g] x) =
      (-1 : k) ^ (n + r + Signs.three g.weight) • appendWords [g] (signedWordReversal x) := by
  classical
  conv_lhs => rw [← x.sum_single]
  conv_rhs => rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro gs hgs
  obtain ⟨hl, hw⟩ := hx hgs
  simp [wordSign_cons, hl, hw, smul_smul, List.reverse_cons, mul_assoc]

def pairVector (f : Generator → Generator → k) : WordSpace k :=
  ∑ h, ∑ t, f h t • Finsupp.single [h, t] 1

theorem pairVector_apply (f : Generator → Generator → k) (gs : List Generator) :
    pairVector f gs = match gs with | [h, t] => f h t | _ => 0 := by
  classical
  cases gs with
  | nil => simp [pairVector, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  | cons h gs =>
      cases gs with
      | nil => simp [pairVector, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
      | cons t gs =>
          cases gs <;> simp [pairVector, Finset.sum_apply, Finsupp.smul_apply,
            smul_eq_mul, Finsupp.single_apply, ite_and]

theorem pairVector_reconstruct (x : WordSpace k)
    (hx : x ∈ Finsupp.supported k k {gs | gs.length = 2}) :
    pairVector (fun h t => x [h, t]) = x := by
  have hz (gs : List Generator) (hl : gs.length ≠ 2) : x gs = 0 := by
    by_contra hn
    exact hl (hx (Finsupp.mem_support_iff.mpr hn))
  ext gs
  rw [pairVector_apply]
  cases gs with
  | nil => exact (hz [] (by simp)).symm
  | cons h gs =>
      cases gs with
      | nil => exact (hz [h] (by simp)).symm
      | cons t gs =>
          cases gs with
          | nil => rfl
          | cons u gs => exact (hz (h :: t :: u :: gs) (by simp)).symm

theorem generator_vector_length (w : Tensor k) (g : Generator) :
    wordVectorDifferential w [g] ∈ Finsupp.supported k k {gs | gs.length = 2} := by
  cases g with
  | forward i a => rw [forward_generator_vector]; exact Submodule.zero_mem _
  | reverse i a =>
      rw [reverse_generator_vector]
      apply Submodule.sum_mem
      intro b hb
      apply Submodule.sum_mem
      intro c hc
      apply Submodule.smul_mem
      exact Finsupp.single_mem_supported k 1 rfl
  | loop i =>
      rw [loop_generator_vector]
      apply Submodule.sub_mem
      all_goals
        apply Submodule.sum_mem
        intro a ha
        exact Finsupp.single_mem_supported k 1 rfl

theorem generator_vector_expansion (w : Tensor k) (g : Generator) :
    wordVectorDifferential w [g] =
      ∑ h, ∑ t, ((-1 : k) ^ (h.weight + 1) * positiveMultiplication (ofTensor w) h t g) •
        Finsupp.single [t, h] 1 := by
  classical
  rw [← pairVector_reconstruct (wordVectorDifferential w [g]) (generator_vector_length w g)]
  simp only [pairVector, generator_structure_coefficient]
  rw [Finset.sum_comm]

theorem multiplication_cut (D : CyclicData k) (g h t : Generator)
    (hm : positiveMultiplication D h t g ≠ 0) :
    ∃ c : Signs.Cut, h.weight = c.left ∧ t.weight = c.right ∧ g.weight = c.left + c.right := by
  have hw := (positiveMultiplication_support D h t g hm).2.2.2
  cases g <;> cases h <;> cases t
  all_goals simp only [Generator.weight] at hw ⊢
  all_goals first
    | omega
    | exact ⟨.oneOne, rfl, rfl, rfl⟩
    | exact ⟨.oneTwo, rfl, rfl, rfl⟩
    | exact ⟨.twoOne, rfl, rfl, rfl⟩

theorem neg_pow_eq_of_mod_two {a b : ℕ} (h : a % 2 = b % 2) : (-1 : k) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, h]

theorem wordSign_split (D : CyclicData k) (g h t : Generator) (gs : List Generator)
    (hm : positiveMultiplication D h t g ≠ 0) :
    wordSign (k := k) (h :: t :: gs) =
      wordSign (g :: gs) * (-1 : k) ^ wordNegative gs * (-1 : k) ^ (h.weight + 1) := by
  obtain ⟨c, hh, ht, hg⟩ := multiplication_cut D g h t hm
  have hn : (gs.map Generator.weight).sum = gs.length + wordNegative gs := by
    exact_mod_cast word_degree gs
  have hb := Signs.split_balance [] (gs.map Generator.weight) c
  unfold wordSign
  rw [← pow_add, ← pow_add]
  apply neg_pow_eq_of_mod_two
  simp only [List.map_cons, hh, ht, hg]
  cases c <;>
    norm_num [Signs.Cut.left, Signs.Cut.right, Signs.sigma, Signs.three] at hb ⊢ <;> omega

@[simp] theorem wordNegative_reverse (gs : List Generator) : wordNegative gs.reverse = wordNegative gs := by
  simp [wordNegative, List.map_reverse, List.sum_reverse]

theorem signedWordReversal_split_suffix (w : Tensor k) (g : Generator) (gs : List Generator) :
    signedWordReversal (appendWords gs (splitBasis (ofTensor w) g)) =
      (wordSign (k := k) (g :: gs) * (-1 : k) ^ wordNegative gs) •
        prependWords gs.reverse (wordVectorDifferential w [g]) := by
  classical
  rw [splitBasis, generator_vector_expansion]
  simp only [map_sum, map_smul, Finset.smul_sum, appendWords_single, prependWords_single,
    signedWordReversal_single, List.cons_append, List.nil_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, smul_smul]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hm : positiveMultiplication (ofTensor w) h t g = 0
  · simp [hm]
  · rw [wordSign_split (ofTensor w) g h t gs hm]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    · simp [List.append_assoc]
    · ring

theorem signedWordReversal_cobar (w : Tensor k) (gs : List Generator) :
    signedWordReversal (cobarBasis (ofTensor w) gs) =
      wordSign (k := k) gs • wordVectorDifferential w gs.reverse := by
  induction gs with
  | nil => simp [cobarBasis]
  | cons g gs ih =>
      have hx : cobarBasis (ofTensor w) gs ∈
          Finsupp.supported k k {cs | cs.length = gs.length + 1 ∧ wordWeight cs = wordWeight gs} :=
        fun cs hc => ⟨cobarBasis_length (ofTensor w) gs hc, cobarBasis_internal (ofTensor w) gs hc⟩
      rw [cobarBasis, map_sub, signedWordReversal_split_suffix,
        signedWordReversal_prepend g (gs.length + 1) (wordWeight gs) _ hx,
        ih, List.reverse_cons, wordVectorDifferential_append]
      rw [show wordWeight gs + (gs.length + 1) + Signs.three g.weight =
        (wordWeight gs + gs.length + Signs.three g.weight) + 1 by omega, pow_succ]
      simp only [map_smul, wordNegative_reverse, wordSign_cons, smul_add, smul_smul,
        mul_neg, mul_one, neg_mul, neg_smul, sub_neg_eq_add, mul_assoc]
      abel
theorem signedWordReversal_differential (w : Tensor k) (x : WordSpace k) :
    signedWordReversal (cobarDifferential (ofTensor w) x) =
      freeDifferential w (signedWordReversal x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp [cobarDifferential, signedWordReversal_cobar, smul_smul, mul_comm]

end
end Ginzburg333.Comparison
