import Ginzburg333.Bar.Ambient

namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
def mergeHead (D : CyclicData k) (g : Generator) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (fun
    | [] => 0
    | h :: cs => ∑ t, positiveMultiplication D g h t • Finsupp.single (t :: cs) 1)
theorem mergeHead_prepend (D : CyclicData k) (g h : Generator) (x : WordSpace k) :
    mergeHead D g (prependWords [h] x) =
      ∑ t, positiveMultiplication D g h t • prependWords [t] x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add, Finset.sum_add_distrib]
  | single cs a =>
      simp [mergeHead, List.singleton_append, Finset.smul_sum, smul_smul, mul_comm]
theorem weighted_double_sum (a : Generator → k) (b : Generator → Generator → k)
    (v : Generator → WordSpace k) :
    (∑ t, a t • ∑ u, b t u • v u) = ∑ u, (∑ t, a t * b t u) • v u := by
  classical
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_smul]
theorem mergeHead_mergeHead (D : CyclicData k) (g h : Generator) (x : WordSpace k) :
    mergeHead D g (mergeHead D h x) =
      ∑ t, positiveMultiplication D g h t • mergeHead D t x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add, Finset.sum_add_distrib]
  | single cs a =>
      cases cs with
      | nil => simp [mergeHead]
      | cons l cs =>
          simp only [mergeHead, Finsupp.linearCombination_single, map_smul, map_sum, smul_smul, smul_zero]
          rw [weighted_double_sum, weighted_double_sum]
          simp only [mul_one, Finset.smul_sum, smul_smul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          calc
            (∑ t, a * (positiveMultiplication D h l t * positiveMultiplication D g t u)) =
                a * ∑ t, positiveMultiplication D h l t * positiveMultiplication D g t u := by
              rw [Finset.mul_sum]
            _ = a * ∑ t, positiveMultiplication D g h t * positiveMultiplication D t l u := by
              rw [positiveMultiplication_assoc]
            _ = ∑ t, positiveMultiplication D g h t * a * positiveMultiplication D t l u := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t ht
              ring
theorem innerDifferential_prepend (D : CyclicData k) (g : Generator) (x : WordSpace k) :
    innerDifferential D (prependWords [g] x) =
      mergeHead D g x - prependWords [g] (innerDifferential D x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single cs a =>
      cases cs <;> simp [innerDifferential, innerBasisDifferential, mergeHead,
        smul_sub, Finset.smul_sum, List.singleton_append]
theorem innerDifferential_mergeHead (D : CyclicData k) (g : Generator) (x : WordSpace k) :
    innerDifferential D (mergeHead D g x) = mergeHead D g (innerDifferential D x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single as a =>
      cases as with
      | nil => simp [mergeHead, innerDifferential, innerBasisDifferential]
      | cons h cs =>
          have heq : (Finsupp.single (h :: cs) a : WordSpace k) = prependWords [h] (Finsupp.single cs a) := by simp
          rw [heq, mergeHead_prepend, map_sum]
          simp only [map_smul, innerDifferential_prepend]
          rw [map_sub, mergeHead_mergeHead, mergeHead_prepend]
          simp [smul_sub, Finset.sum_sub_distrib]
theorem innerDifferential_square_word (D : CyclicData k) (gs : List Generator) :
    innerDifferential D (innerDifferential D (Finsupp.single gs 1)) = 0 := by
  induction gs with
  | nil => simp [innerDifferential, innerBasisDifferential]
  | cons g gs ih =>
      have heq : (Finsupp.single (g :: gs) 1 : WordSpace k) = prependWords [g] (Finsupp.single gs 1) := by simp
      rw [heq, innerDifferential_prepend, map_sub, innerDifferential_mergeHead,
        innerDifferential_prepend, ih, map_zero]
      abel
theorem innerDifferential_square (D : CyclicData k) (x : WordSpace k) :
    innerDifferential D (innerDifferential D x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a =>
      have heq : (Finsupp.single gs a : WordSpace k) = a • Finsupp.single gs 1 := by
        simp [Finsupp.smul_single, smul_eq_mul]
      rw [heq, map_smul, map_smul, innerDifferential_square_word, smul_zero]
end
end Ginzburg333.Bar
