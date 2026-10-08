import Ginzburg333.Bar.Positive

namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 3000000 in
theorem positiveMultiplication_support (D : CyclicData k) (g h t : Generator)
    (hm : positiveMultiplication D g h t ≠ 0) :
    g.target = h.source ∧ t.source = g.source ∧ t.target = h.target ∧
      t.weight = g.weight + h.weight := by
  classical
  cases g <;> cases h <;> cases t
  case forward.forward.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.forward.reverse i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.forward.loop i a j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.reverse.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.reverse.reverse i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.reverse.loop i a j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.loop.forward i a j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.loop.reverse i a j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case forward.loop.loop i a j l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.forward.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.forward.reverse i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.forward.loop i a j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.reverse.forward i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.reverse.reverse i a j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.reverse.loop i a j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.loop.forward i a j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.loop.reverse i a j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case reverse.loop.loop i a j l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.forward.forward i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.forward.reverse i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.forward.loop i j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.reverse.forward i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.reverse.reverse i j b l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.reverse.loop i j b l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.loop.forward i j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.loop.reverse i j l c =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
  case loop.loop.loop i j l =>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [positiveMultiplication, positiveCoordinate, positiveBasis, embedRow,
        CyclicData.multiply, Generator.source, Generator.target, Generator.weight, next, apply_ite]
end
end Ginzburg333.Bar
