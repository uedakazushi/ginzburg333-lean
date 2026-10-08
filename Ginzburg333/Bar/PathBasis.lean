import Ginzburg333.Bar.Simple
import Ginzburg333.Ginzburg.Complex

/-! Vertex conventions under factor reversal in the bar/path comparison. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]

/-- The empty word retains its row vertex. -/
def startsAt (i : Vertex) (gs : List Generator) : Prop :=
  composable gs ∧ match gs with
    | [] => True
    | g :: _ => g.source = i

theorem startsAt_cons (i : Vertex) (g : Generator) (gs : List Generator) :
    startsAt i (g :: gs) ↔ g.source = i ∧ startsAt g.target gs := by
  cases gs <;> simp [startsAt, composable, eq_comm, and_comm, and_left_comm]

theorem endpoint_reverse_cons (i : Vertex) (g : Generator) (gs : List Generator) :
    endpoint? i (g :: gs).reverse = if g.source = i then endpoint? g.target gs.reverse else none := by
  rw [List.reverse_cons, endpoint_append]
  by_cases hi : g.source = i <;> simp [endpoint?, hi]

theorem reverse_valid_iff (i : Vertex) (gs : List Generator) :
    ValidPath (i, gs.reverse) ↔ startsAt i gs := by
  induction gs generalizing i with
  | nil => simp [ValidPath, endpoint?, startsAt, composable]
  | cons g gs ih =>
      rw [startsAt_cons]
      unfold ValidPath
      rw [endpoint_reverse_cons]
      by_cases hi : g.source = i
      · simpa only [if_pos hi, hi, true_and] using ih g.target
      · simp [hi]

@[simp] theorem wordWeight_reverse (gs : List Generator) : wordWeight gs.reverse = wordWeight gs := by
  simp [wordWeight, List.map_reverse, List.sum_reverse]

abbrev SimpleBarBasis (r n : ℕ) :=
  {p : Vertex × List Generator // startsAt p.1 p.2 ∧ p.2.length = r ∧ wordWeight p.2 = n}

abbrev GinzburgLengthBasis (r n : ℕ) :=
  {p : BasisPath // p.val.2.length = r ∧ internalDegree p = n}

/-- Reversal preserves actual vertices and gives exactly the valid path basis. -/
def reversedBasisEquiv (r n : ℕ) : SimpleBarBasis r n ≃ GinzburgLengthBasis r n where
  toFun p := ⟨⟨(p.val.1, p.val.2.reverse), (reverse_valid_iff _ _).mpr p.property.1⟩,
    by
      constructor
      · simpa using p.property.2.1
      · change wordWeight p.val.2.reverse = n
        rw [wordWeight_reverse]
        exact p.property.2.2⟩
  invFun p := ⟨(p.val.val.1, p.val.val.2.reverse),
    ⟨by
      apply (reverse_valid_iff _ _).mp
      simpa using p.val.property,
      by simpa [internalDegree] using p.property⟩⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp

theorem reversedBasis_cohomological (r n : ℕ) (p : SimpleBarBasis r n) :
    cohomologicalDegree ((reversedBasisEquiv r n p).val) = (r : ℤ) - (n : ℤ) := by
  rw [cohomologicalDegree_eq_length_sub_weight]
  rw [((reversedBasisEquiv r n p).property).1, ((reversedBasisEquiv r n p).property).2]
end Ginzburg333.Bar
