import Ginzburg333.Converse.JacobiMap
import Ginzburg333.Converse.LoopLifts

namespace Ginzburg333.Converse
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
set_option maxHeartbeats 4000000

/-- Genuine free words survive in the image of the actual internal Jacobi quotient. -/
theorem freeCorner_exponential_lower_bound (w : Tensor k) (i : Vertex) (a : Vec k)
    (ha : a ≠ 0) (d : FreeCornerData w i a) (m : ℕ) :
    2 ^ m ≤ Module.finrank k (internalJacobi w (3 * m)) := by
  classical
  obtain ⟨L⟩ := loopLiftData_exists w i a ha d
  let x (s : Fin m → Fin 2) : WordSpace k := liftFreeWord L (List.ofFn s)
  have hx (s : Fin m → Fin 2) : x s ∈ closedWords (next i) (3 * m) := by
    simpa only [x, List.length_ofFn] using liftFreeWord_closed L (List.ofFn s)
  let b (s : Fin m → Fin 2) : internalJacobi w (3 * m) :=
    (LinearMap.range (negativeDifferential w (3 * m) 0)).mkQ
      ⟨wordToPaths (next i) (x s), wordToPaths_bigraded (next i) (3 * m) (x s) (hx s)⟩
  let f := jacobiEvaluation w i a d (3 * m)
  have hf (s : Fin m → Fin 2) : f (b s) = MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn s)) 1 := by
    rw [jacobiEvaluation_wordToPaths w i a d (next i) (3 * m) (x s) (hx s)]
    exact liftFreeWord_entry00 L (List.ofFn s)
  have hinj : Function.Injective (fun s : Fin m → Fin 2 => FreeMonoid.ofList (List.ofFn s)) := by
    intro s t h
    exact List.ofFn_injective (FreeMonoid.ofList.injective h)
  have ht : LinearIndependent k (fun s : Fin m → Fin 2 =>
      MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn s)) (1 : k)) :=
    (Finsupp.linearIndependent_single_one k (FreeMonoid (Fin 2))).comp _ hinj
  have hb : LinearIndependent k b := by
    apply LinearIndependent.of_comp f
    simpa only [Function.comp_def, hf] using ht
  have hd := hb.fintype_card_le_finrank
  simpa only [Fintype.card_fun, Fintype.card_fin] using hd
end
end Ginzburg333.Converse
