import Ginzburg333.Ginzburg.Words

/-! The Leibniz differential on finite word vectors, before path restriction. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

abbrev WordSpace (k : Type*) [Zero k] := List Generator →₀ k
def wordTerm (t : k × List Generator) : WordSpace k := Finsupp.single t.2 t.1
def wordVectorDifferential (w : Tensor k) (gs : List Generator) : WordSpace k :=
  ((wordDifferential w gs).map wordTerm).sum
def freeDifferential (w : Tensor k) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (wordVectorDifferential w)
def prependWords (as : List Generator) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.lmapDomain k k (fun bs => as ++ bs)
def appendWords (bs : List Generator) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.lmapDomain k k (fun as => as ++ bs)
def concatenate (x y : WordSpace k) : WordSpace k :=
  Finsupp.linearCombination k (fun as => prependWords as y) x
def parity : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (fun as => (-1 : k) ^ wordNegative as • Finsupp.single as 1)

@[simp] theorem freeDifferential_single (w : Tensor k) (gs : List Generator) (a : k) :
    freeDifferential w (Finsupp.single gs a) = a • wordVectorDifferential w gs := by
  simp [freeDifferential]
@[simp] theorem prependWords_single (as bs : List Generator) (a : k) :
    prependWords as (Finsupp.single bs a) = Finsupp.single (as ++ bs) a := by
  simp [prependWords, Finsupp.lmapDomain_apply]
@[simp] theorem appendWords_single (as bs : List Generator) (a : k) :
    appendWords bs (Finsupp.single as a) = Finsupp.single (as ++ bs) a := by
  simp [appendWords, Finsupp.lmapDomain_apply]
@[simp] theorem concatenate_single_left (as : List Generator) (a : k) (y : WordSpace k) :
    concatenate (Finsupp.single as a) y = a • prependWords as y := by simp [concatenate]
theorem concatenate_add_left (x z y : WordSpace k) :
    concatenate (x + z) y = concatenate x y + concatenate z y :=
  (Finsupp.linearCombination k (fun as => prependWords as y)).map_add x z
theorem concatenate_smul_left (a : k) (x y : WordSpace k) :
    concatenate (a • x) y = a • concatenate x y :=
  (Finsupp.linearCombination k (fun as => prependWords as y)).map_smul a x
theorem concatenate_neg_left (x y : WordSpace k) :
    concatenate (-x) y = -concatenate x y :=
  (Finsupp.linearCombination k (fun as => prependWords as y)).map_neg x
@[simp] theorem concatenate_zero_left (y : WordSpace k) : concatenate 0 y = 0 := by
  simp [concatenate]
theorem concatenate_add_right (x y z : WordSpace k) :
    concatenate x (y + z) = concatenate x y + concatenate x z := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp only [concatenate_add_left, hx, hz]; abel
  | single as a => simp [smul_add]
theorem concatenate_smul_right (a : k) (x y : WordSpace k) :
    concatenate x (a • y) = a • concatenate x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp only [concatenate_add_left, hx, hz, smul_add]
  | single as b => simp [smul_smul, mul_comm]
@[simp] theorem concatenate_zero_right (x : WordSpace k) : concatenate x 0 = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [concatenate_add_left, hx, hz]
  | single as a => simp
@[simp] theorem concatenate_single_right (x : WordSpace k) (bs : List Generator) (a : k) :
    concatenate x (Finsupp.single bs a) = a • appendWords bs x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [concatenate_add_left, hx, hz, smul_add]
  | single as b => simp [Finsupp.smul_single, smul_eq_mul, mul_comm]
@[simp] theorem parity_single (gs : List Generator) (a : k) :
    parity (Finsupp.single gs a) = (-1 : k) ^ wordNegative gs • Finsupp.single gs a := by
  simp [parity, smul_smul, Finsupp.smul_single, smul_eq_mul, mul_comm]
@[simp] theorem wordVectorDifferential_nil (w : Tensor k) : wordVectorDifferential w [] = 0 := by
  simp [wordVectorDifferential, wordDifferential]
theorem wordVectorDifferential_cons (w : Tensor k) (g : Generator) (gs : List Generator) :
    wordVectorDifferential w (g :: gs) =
      appendWords gs (wordVectorDifferential w [g]) +
      (-1 : k) ^ g.negativeDegree • prependWords [g] (wordVectorDifferential w gs) := by
  classical
  unfold wordVectorDifferential
  simp only [wordDifferential, List.map_append, List.sum_append]
  congr 1
  · simp [map_list_sum, List.map_map, Function.comp_def, wordTerm, appendWords_single]
  · simp only [map_list_sum, List.map_map, Function.comp_def]
    rw [List.smul_sum]
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    simp [wordTerm, prependWords_single, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem prependWords_prependWords (as bs : List Generator) (x : WordSpace k) :
    prependWords as (prependWords bs x) = prependWords (as ++ bs) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs a => simp [List.append_assoc]
@[simp] theorem appendWords_appendWords (as bs : List Generator) (x : WordSpace k) :
    appendWords bs (appendWords as x) = appendWords (as ++ bs) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs a => simp [List.append_assoc]
@[simp] theorem prependWords_appendWords (as bs : List Generator) (x : WordSpace k) :
    prependWords as (appendWords bs x) = appendWords bs (prependWords as x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs a => simp [List.append_assoc]
@[simp] theorem prependWords_nil (x : WordSpace k) : prependWords [] x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs a => simp

theorem wordVectorDifferential_append (w : Tensor k) (as bs : List Generator) :
    wordVectorDifferential w (as ++ bs) =
      appendWords bs (wordVectorDifferential w as) +
      (-1 : k) ^ wordNegative as • prependWords as (wordVectorDifferential w bs) := by
  induction as with
  | nil => simp
  | cons g as ih =>
      simp only [List.cons_append]
      rw [wordVectorDifferential_cons w g (as ++ bs), ih, wordVectorDifferential_cons w g as]
      simp only [map_add, map_smul, smul_add, smul_smul, wordNegative_cons, pow_add,
        appendWords_appendWords, prependWords_appendWords, prependWords_prependWords,
        List.singleton_append, add_assoc]

theorem freeDifferential_leibniz (w : Tensor k) (x y : WordSpace k) :
    freeDifferential w (concatenate x y) =
      concatenate (freeDifferential w x) y + concatenate (parity x) (freeDifferential w y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz =>
      simp only [concatenate_add_left, map_add, hx, hz]; abel
  | single as a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y z hy hz =>
          simp only [concatenate_add_right, map_add, hy, hz]; abel
      | single bs b =>
          simp [wordVectorDifferential_append, concatenate_smul_left,
            concatenate_smul_right, smul_smul, smul_add, mul_comm, mul_left_comm, mul_assoc]

theorem negate_list_sum (xs : List (WordSpace k)) : -xs.sum = (xs.map (- ·)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [neg_add, ih, add_comm]
theorem parity_wordVectorDifferential (w : Tensor k) (gs : List Generator) :
    parity (wordVectorDifferential w gs) =
      -((-1 : k) ^ wordNegative gs • wordVectorDifferential w gs) := by
  classical
  unfold wordVectorDifferential
  rw [map_list_sum, List.smul_sum, negate_list_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn := (wordDifferential_degrees w gs hp).2
  have hsign : (-1 : k) ^ wordNegative p.2 = -((-1 : k) ^ wordNegative gs) := by
    rw [← hn, pow_succ]
    ring
  simp only [wordTerm, parity_single]
  rw [hsign]
  simp [Finsupp.smul_single, smul_eq_mul, mul_comm]
theorem freeDifferential_parity (w : Tensor k) (x : WordSpace k) :
    freeDifferential w (parity x) = -parity (freeDifferential w x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | single gs a =>
      rw [parity_single, map_smul, freeDifferential_single, map_smul,
        parity_wordVectorDifferential]
      simp only [smul_neg, neg_neg]
      exact smul_comm _ _ _
theorem parity_square (x : WordSpace k) : parity (parity x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a =>
      rw [parity_single, map_smul, parity_single, smul_smul]
      have h : (-1 : k) ^ wordNegative gs * (-1 : k) ^ wordNegative gs = 1 := by
        rw [← mul_pow]; simp
      rw [h, one_smul]

set_option maxRecDepth 4096 in
theorem generator_wordDifferential_square (w : Tensor k) (g : Generator) :
    freeDifferential w (wordVectorDifferential w [g]) = 0 := by
  classical
  cases g with
  | forward i a => simp [wordVectorDifferential, wordDifferential, generatorDifferential]
  | reverse i a =>
      simp [wordVectorDifferential, wordDifferential, generatorDifferential,
        coordinates, wordTerm, map_list_sum]
  | loop i =>
      fin_cases i <;>
        simp [wordVectorDifferential, wordDifferential, generatorDifferential,
          coordinates, wordTerm, map_list_sum, Generator.negativeDegree, coeff, next] <;> abel
theorem wordVectorDifferential_square (w : Tensor k) (gs : List Generator) :
    freeDifferential w (wordVectorDifferential w gs) = 0 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      have hgen : freeDifferential w (freeDifferential w (Finsupp.single [g] 1)) = 0 := by
        simpa using generator_wordDifferential_square w g
      have htail : freeDifferential w (freeDifferential w (Finsupp.single gs 1)) = 0 := by
        simpa using ih
      have hcons : (Finsupp.single (g :: gs) 1 : WordSpace k) =
          concatenate (Finsupp.single [g] 1) (Finsupp.single gs 1) := by simp
      suffices h : freeDifferential w (freeDifferential w (Finsupp.single (g :: gs) 1)) = 0 by
        simpa using h
      rw [hcons, freeDifferential_leibniz, map_add,
        freeDifferential_leibniz, freeDifferential_leibniz]
      simp only [hgen, htail, concatenate_zero_left, concatenate_zero_right,
        zero_add, add_zero, freeDifferential_parity, concatenate_neg_left, add_neg_cancel]
theorem freeDifferential_square (w : Tensor k) (x : WordSpace k) :
    freeDifferential w (freeDifferential w x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp [wordVectorDifferential_square]

end
end Ginzburg333.Ginzburg
