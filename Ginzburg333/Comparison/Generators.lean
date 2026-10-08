import Ginzburg333.Bar.SimpleCoordinates
import Ginzburg333.Signs

/-! Actual generator coefficients in the bar/Ginzburg comparison. -/
namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem reverse_generator_vector (w : Tensor k) (i : Vertex) (a : Fin 3) :
    wordVectorDifferential w [.reverse i a] =
      ∑ b : Fin 3, ∑ c : Fin 3, coeff w i a b c •
        Finsupp.single [.forward (next (next i)) c, .forward (next i) b] 1 := by
  simp [wordVectorDifferential, wordDifferential, generatorDifferential, coordinates,
    wordTerm, Fin.sum_univ_succ, Finsupp.smul_single, smul_eq_mul]
  abel

theorem loop_generator_vector (w : Tensor k) (i : Vertex) :
    wordVectorDifferential w [.loop i] =
      (∑ a : Fin 3, Finsupp.single [.reverse i a, .forward i a] 1) -
        ∑ a : Fin 3, Finsupp.single [.forward (next (next i)) a, .reverse (next (next i)) a] 1 := by
  simp [wordVectorDifferential, wordDifferential, generatorDifferential, coordinates,
    wordTerm, Fin.sum_univ_succ, Finsupp.single_neg]
  abel

theorem forward_generator_vector (w : Tensor k) (i : Vertex) (a : Fin 3) :
    wordVectorDifferential w [.forward i a] = 0 := by
  simp [wordVectorDifferential, wordDifferential, generatorDifferential]

set_option maxHeartbeats 12000000 in
/-- Factor reversal and the (-1)^(left weight+1) sign, for the original tensor. -/
theorem generator_structure_coefficient (w : Tensor k) (g h t : Generator) :
    wordVectorDifferential w [g] [h, t] =
      (-1 : k) ^ (t.weight + 1) * positiveMultiplication (ofTensor w) t h g := by
  classical
  cases g <;> cases h <;> cases t
  case forward.forward.forward i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.forward.reverse i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.forward.loop i a j b l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.reverse.forward i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.reverse.reverse i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.reverse.loop i a j b l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.loop.forward i a j l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.loop.reverse i a j l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case forward.loop.loop i a j l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.forward.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.forward.reverse i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.forward.loop i a j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.reverse.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.reverse.reverse i a j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.reverse.loop i a j b l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.loop.forward i a j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.loop.reverse i a j l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case reverse.loop.loop i a j l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.forward.forward i j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.forward.reverse i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.forward.loop i j b l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.reverse.forward i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.reverse.reverse i j b l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.reverse.loop i j b l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.loop.forward i j l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.loop.reverse i j l c =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
  case loop.loop.loop i j l =>
      (simp only [reverse_generator_vector, loop_generator_vector, forward_generator_vector]
       simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, positiveMultiplication, positiveCoordinate,
        positiveBasis, embedRow, CyclicData.multiply, ofTensor, contraction, contract,
        Generator.weight, next, Finsupp.single_apply, ite_and, apply_ite, unitVec, dot] <;> simp_all [coeff] <;> norm_num)
end
end Ginzburg333.Comparison
