import Ginzburg333.Bar.InnerSquare

/-! Square-zero of the bar differential with its actual coefficient action. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
noncomputable section
def liftWordOperator (f : WordSpace k →ₗ[k] WordSpace k) : Ambient M →ₗ[k] Ambient M :=
  Finsupp.lsum k (fun gs => tensorWords (f (Finsupp.single gs 1)))
theorem liftWordOperator_tensorWords (f : WordSpace k →ₗ[k] WordSpace k) (x : WordSpace k) (m : M) :
    liftWordOperator f (tensorWords x m) = tensorWords (f x) m := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a =>
      simp only [tensorWords_single, map_smul, liftWordOperator, Finsupp.lsum_single]
      have heq : (Finsupp.single gs a : WordSpace k) = a • Finsupp.single gs 1 := by
        simp [Finsupp.smul_single, smul_eq_mul]
      rw [heq, map_smul, map_smul]
      rfl
theorem tensorWords_prepend (gs : List Generator) (x : WordSpace k) (m : M) :
    tensorWords (prependWords gs x) m = prependChain (k := k) gs (tensorWords x m) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs a => simp [prependChain, Finsupp.lmapDomain_apply]
def innerChainDifferential (D : CyclicData k) : Ambient M →ₗ[k] Ambient M :=
  liftWordOperator (innerDifferential D)
def mergeHeadChain (D : CyclicData k) (g : Generator) : Ambient M →ₗ[k] Ambient M :=
  liftWordOperator (mergeHead D g)
def firstAction {D : CyclicData k} (A : RightAction D M) : Ambient M →ₗ[k] Ambient M :=
  Finsupp.lsum k (fun
    | [] => 0
    | g :: cs => (Finsupp.lsingle cs).comp (A.action (positiveBasis g)))
@[simp] theorem firstAction_nil {D : CyclicData k} (A : RightAction D M) (m : M) :
    firstAction A (Finsupp.single [] m) = 0 := by simp [firstAction, Finsupp.lsum_single]
@[simp] theorem firstAction_cons {D : CyclicData k} (A : RightAction D M) (g : Generator)
    (cs : List Generator) (m : M) :
    firstAction A (Finsupp.single (g :: cs) m) = Finsupp.single cs (A.action (positiveBasis g) m) := by
  simp [firstAction, Finsupp.lsum_single]
@[simp] theorem prependChain_single (gs cs : List Generator) (m : M) :
    prependChain (k := k) gs (Finsupp.single cs m) = Finsupp.single (gs ++ cs) m := by
  simp [prependChain, Finsupp.lmapDomain_apply]
theorem firstAction_prepend {D : CyclicData k} (A : RightAction D M) (g : Generator) (x : Ambient M) :
    firstAction A (prependChain (k := k) [g] x) = coefficientMap (A.action (positiveBasis g)) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs m => simp
theorem innerChainDifferential_tensorWords (D : CyclicData k) (x : WordSpace k) (m : M) :
    innerChainDifferential D (tensorWords x m) = tensorWords (innerDifferential D x) m :=
  liftWordOperator_tensorWords _ _ _
theorem mergeHeadChain_tensorWords (D : CyclicData k) (g : Generator) (x : WordSpace k) (m : M) :
    mergeHeadChain D g (tensorWords x m) = tensorWords (mergeHead D g x) m :=
  liftWordOperator_tensorWords _ _ _
theorem innerChainDifferential_prepend (D : CyclicData k) (g : Generator) (x : Ambient M) :
    innerChainDifferential D (prependChain (k := k) [g] x) =
      mergeHeadChain D g x - prependChain (k := k) [g] (innerChainDifferential D x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single cs m =>
      have heq : Finsupp.single cs m = tensorWords (k := k) (Finsupp.single cs 1) m := by simp
      rw [heq, ← tensorWords_prepend, innerChainDifferential_tensorWords,
        innerDifferential_prepend, map_sub, LinearMap.sub_apply, tensorWords_prepend,
        ← mergeHeadChain_tensorWords, ← innerChainDifferential_tensorWords]
theorem innerChainDifferential_coefficientMap (D : CyclicData k) (f : M →ₗ[k] N) (x : Ambient M) :
    innerChainDifferential D (coefficientMap f x) = coefficientMap f (innerChainDifferential D x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs m =>
      have heq : Finsupp.single cs m = tensorWords (k := k) (Finsupp.single cs 1) m := by simp
      rw [heq, coefficientMap_tensorWords, innerChainDifferential_tensorWords,
        innerChainDifferential_tensorWords, coefficientMap_tensorWords]
theorem innerChainDifferential_square (D : CyclicData k) (x : Ambient M) :
    innerChainDifferential D (innerChainDifferential D x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs m =>
      have heq : Finsupp.single cs m = tensorWords (k := k) (Finsupp.single cs 1) m := by simp
      rw [heq, innerChainDifferential_tensorWords, innerChainDifferential_tensorWords,
        innerDifferential_square, map_zero, LinearMap.zero_apply]
theorem action_positiveMultiplication {D : CyclicData k} (A : RightAction D M)
    (g h : Generator) (m : M) :
    (∑ t, positiveMultiplication D g h t • A.action (positiveBasis t) m) =
      A.action (D.multiply (positiveBasis g) (positiveBasis h)) m := by
  classical
  calc
    (∑ t, positiveMultiplication D g h t • A.action (positiveBasis t) m) =
        ∑ t, A.action.flip m (positiveMultiplication D g h t • positiveBasis t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (A.action.flip m).map_smul _ _ |>.symm
    _ = A.action.flip m (∑ t, positiveMultiplication D g h t • positiveBasis t) :=
      (map_sum (A.action.flip m).toAddMonoidHom _ Finset.univ).symm
    _ = _ := by rw [sum_positiveMultiplication]; rfl
theorem firstAction_mergeHeadChain {D : CyclicData k} (A : RightAction D M)
    (g : Generator) (x : Ambient M) :
    firstAction A (mergeHeadChain D g x) =
      firstAction A (coefficientMap (A.action (positiveBasis g)) x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs m =>
      cases cs with
      | nil => simp [mergeHeadChain, liftWordOperator, Finsupp.lsum_single, mergeHead]
      | cons h cs =>
          simp only [mergeHeadChain, liftWordOperator, Finsupp.lsum_single,
            mergeHead, Finsupp.linearCombination_single, one_smul, map_sum, map_smul,
            firstAction_cons, coefficientMap_single]
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensorWords_single,
            one_smul, map_sum, map_smul, firstAction_cons]
          calc
            (∑ t, positiveMultiplication D g h t • Finsupp.single cs (A.action (positiveBasis t) m)) =
                Finsupp.single cs (∑ t, positiveMultiplication D g h t • A.action (positiveBasis t) m) := by
              change _ = (Finsupp.lsingle cs : M →ₗ[k] Ambient M) _
              rw [map_sum]
              simp only [map_smul, Finsupp.lsingle_apply]
            _ = _ := by rw [action_positiveMultiplication, A.assoc]
theorem firstAction_square_identity {D : CyclicData k} (A : RightAction D M) (x : Ambient M) :
    firstAction A (firstAction A x) = firstAction A (innerChainDifferential D x) +
      innerChainDifferential D (firstAction A x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single cs m =>
      cases cs with
      | nil => simp [innerChainDifferential, liftWordOperator, Finsupp.lsum_single,
          innerDifferential, innerBasisDifferential]
      | cons g cs =>
          have heq : Finsupp.single (g :: cs) m = prependChain (k := k) [g] (Finsupp.single cs m) := by simp
          rw [heq, firstAction_prepend, innerChainDifferential_prepend, map_sub,
            firstAction_mergeHeadChain, firstAction_prepend, innerChainDifferential_coefficientMap]
          abel
theorem ambientDifferential_eq {D : CyclicData k} (A : RightAction D M) (x : Ambient M) :
    ambientDifferential A x = innerChainDifferential D x - firstAction A x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single cs m =>
      cases cs <;>
        simp [onWord, innerChainDifferential, liftWordOperator, Finsupp.lsum_single,
          innerDifferential, innerBasisDifferential, firstAction] <;> abel
theorem ambientDifferential_square {D : CyclicData k} (A : RightAction D M) (x : Ambient M) :
    ambientDifferential A (ambientDifferential A x) = 0 := by
  rw [ambientDifferential_eq A x, map_sub, ambientDifferential_eq, ambientDifferential_eq,
    innerChainDifferential_square, firstAction_square_identity]
  abel
end
end Ginzburg333.Bar
