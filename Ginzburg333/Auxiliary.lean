import Ginzburg333.Finite.Corner

/-!
# The 24-dimensional auxiliary multiplication

The multiplication below is the multiplication table of Section 2 of the
source note, not the quadratic dual of a Jacobi algebra by definition.
It is given on a k-module with three eight-dimensional rows.

The ring/algebra typeclass adapter and the graded right-module interfaces
remain to be installed. Associativity and the unit laws are written directly
for the explicit multiplication, so their statement does not depend on that
adapter.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333
open Module
variable {k : Type*} [Field k]

abbrev Auxiliary (k : Type*) := Vertex → Row k

@[simp] theorem finrank_auxiliary : finrank k (Auxiliary k) = 24 := by
  simp [Auxiliary, Module.finrank_pi_fintype, Vertex, finrank_row]

namespace CyclicData

/-- Multiplication table in the corner convention e_i E_d e_(i+d). -/
def multiply (D : CyclicData k) (a b : Auxiliary k) : Auxiliary k := fun i =>
  ((a i).1 * (b i).1,
   (a i).1 • (b i).2.1 + (b (next i)).1 • (a i).2.1,
   (a i).1 • (b i).2.2.1 + D.mul i (a i).2.1 (b (next i)).2.1 +
     (b (next (next i))).1 • (a i).2.2.1,
   (a i).1 * (b i).2.2.2 + dot (a i).2.1 (b (next i)).2.2.1 +
     dot (a i).2.2.1 (b (next (next i))).2.1 +
     (a i).2.2.2 * (b i).1)

def identityRow : Row k := (1, 0, 0, 0)

def identityAuxiliary : Auxiliary k := fun _ => identityRow

/-- The only nontrivial positive-degree associativity identity is `D.cyclic`. -/
theorem multiply_assoc (D : CyclicData k) (a b c : Auxiliary k) :
    D.multiply (D.multiply a b) c = D.multiply a (D.multiply b c) := by
  funext i
  apply Prod.ext
  · simp [multiply, mul_assoc]
  · apply Prod.ext
    · funext j
      simp [multiply, smul_add, add_smul, smul_smul] <;> ring
    · apply Prod.ext
      · funext j
        simp [multiply, next_three, map_add, map_smul,
          smul_add, add_smul, smul_smul] <;> ring
      · simp [multiply, next_three, map_add, map_smul,
          dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
          D.cyclic] <;> ring

@[simp] theorem identity_multiply (D : CyclicData k) (a : Auxiliary k) :
    D.multiply identityAuxiliary a = a := by
  funext i
  simp [multiply, identityAuxiliary, identityRow]

@[simp] theorem multiply_identity (D : CyclicData k) (a : Auxiliary k) :
    D.multiply a identityAuxiliary = a := by
  funext i
  simp [multiply, identityAuxiliary, identityRow]

theorem multiply_add_left (D : CyclicData k) (a b c : Auxiliary k) :
    D.multiply (a + b) c = D.multiply a c + D.multiply b c := by
  ext i j <;>
    simp [multiply, add_smul, smul_add, add_mul, mul_add,
      map_add, dot_add_left, dot_add_right] <;> ring

theorem multiply_add_right (D : CyclicData k) (a b c : Auxiliary k) :
    D.multiply a (b + c) = D.multiply a b + D.multiply a c := by
  ext i j <;>
    simp [multiply, add_smul, smul_add, add_mul, mul_add,
      map_add, dot_add_left, dot_add_right] <;> ring

theorem multiply_smul_left (D : CyclicData k) (t : k) (a b : Auxiliary k) :
    D.multiply (t • a) b = t • D.multiply a b := by
  ext i j <;>
    simp [multiply, smul_smul, smul_add, map_smul,
      dot_smul_left, dot_smul_right, smul_eq_mul] <;> ring <;> simp

theorem multiply_smul_right (D : CyclicData k) (t : k) (a b : Auxiliary k) :
    D.multiply a (t • b) = t • D.multiply a b := by
  ext i j <;>
    simp [multiply, smul_smul, smul_add, map_smul,
      dot_smul_left, dot_smul_right, smul_eq_mul] <;> ring <;> simp

/-- A degree-one element supported at the labelled corner i. -/
def degreeOneElement (i : Vertex) (a : Vec k) : Auxiliary k :=
  fun j => if j = i then (0, a, 0, 0) else 0

/-- Connection between the global multiplication table and the local
annihilator/colon calculations. -/
theorem degreeOne_multiply_at (D : CyclicData k)
    (i : Vertex) (a : Vec k) (b : Auxiliary k) :
    D.multiply (degreeOneElement i a) b i = D.leftOne i a (b (next i)) := by
  simp [multiply, degreeOneElement, leftOne]

end CyclicData
end Ginzburg333
