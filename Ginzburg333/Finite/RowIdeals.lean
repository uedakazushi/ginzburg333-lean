import Ginzburg333.Auxiliary
import Ginzburg333.Finite.Colon
import Ginzburg333.Homology.Quotient

/-! Right actions and the actual generated row subspaces used in the filtration. -/
namespace Ginzburg333
open Module
variable {k : Type*} [Field k]

def embedRow (i : Vertex) (r : Row k) : Auxiliary k :=
  fun j => if j = i then r else 0

namespace CyclicData

def leftOneBilinear (D : CyclicData k) (i : Vertex) :
    Vec k →ₗ[k] Row k →ₗ[k] Row k where
  toFun := D.leftOne i
  map_add' := by
    intro a b
    apply LinearMap.ext
    rintro ⟨s, c, v, t⟩
    simp [leftOne, smul_add, dot_add_left]
  map_smul' := by
    intro t a
    apply LinearMap.ext
    rintro ⟨s, c, v, u⟩
    simp [leftOne, smul_smul, dot_smul_left, smul_eq_mul, mul_comm]

@[simp] theorem leftOne_zero (D : CyclicData k) (i : Vertex) :
    D.leftOne i 0 = 0 := (D.leftOneBilinear i).map_zero

theorem leftOne_add (D : CyclicData k) (i : Vertex) (a b : Vec k) :
    D.leftOne i (a + b) = D.leftOne i a + D.leftOne i b :=
  (D.leftOneBilinear i).map_add a b

theorem leftOne_smul (D : CyclicData k) (i : Vertex) (t : k) (a : Vec k) :
    D.leftOne i (t • a) = t • D.leftOne i a :=
  (D.leftOneBilinear i).map_smul t a

@[simp] theorem rowGenerated_bot (D : CyclicData k) (i : Vertex) :
    D.rowGenerated i ⊥ = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    intro a
    have ha : (a : Vec k) = 0 := a.property
    simp [ha]
  · exact bot_le

theorem rowGenerated_mono (D : CyclicData k) (i : Vertex)
    {U V : Submodule k (Vec k)} (h : U ≤ V) :
    D.rowGenerated i U ≤ D.rowGenerated i V := by
  apply iSup_le
  intro a
  rintro r ⟨s, rfl⟩
  exact D.leftOne_mem_rowGenerated i V (h a.property) s

theorem rowGenerated_span (D : CyclicData k) (i : Vertex) (a : Vec k) :
    D.rowGenerated i (Submodule.span k {a}) = LinearMap.range (D.leftOne i a) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp x.property
    rintro r ⟨s, rfl⟩
    rw [← ht, D.leftOne_smul]
    exact (LinearMap.range (D.leftOne i a)).smul_mem t ⟨s, rfl⟩
  · rintro r ⟨s, rfl⟩
    exact D.leftOne_mem_rowGenerated i _ (Submodule.subset_span (by simp)) s

theorem rowGenerated_sup (D : CyclicData k) (i : Vertex)
    (U V : Submodule k (Vec k)) :
    D.rowGenerated i (U ⊔ V) = D.rowGenerated i U ⊔ D.rowGenerated i V := by
  apply le_antisymm
  · apply iSup_le
    intro a
    rintro r ⟨s, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp a.property
    rw [← huv, D.leftOne_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (D.leftOne_mem_rowGenerated i U hu s)
      (D.leftOne_mem_rowGenerated i V hv s)
  · exact sup_le (D.rowGenerated_mono i le_sup_left) (D.rowGenerated_mono i le_sup_right)

def rowAction (D : CyclicData k) (i : Vertex) (r : Row k) (b : Auxiliary k) : Row k :=
  D.multiply (embedRow i r) b i

@[simp] theorem rowAction_formula (D : CyclicData k) (i : Vertex)
    (r : Row k) (b : Auxiliary k) :
    D.rowAction i r b =
    (r.1 * (b i).1,
     r.1 • (b i).2.1 + (b (next i)).1 • r.2.1,
     r.1 • (b i).2.2.1 + D.mul i r.2.1 (b (next i)).2.1 +
       (b (next (next i))).1 • r.2.2.1,
     r.1 * (b i).2.2.2 + dot r.2.1 (b (next i)).2.2.1 +
       dot r.2.2.1 (b (next (next i))).2.1 + r.2.2.2 * (b i).1) := by
  simp [rowAction, multiply, embedRow]

theorem multiply_embedRow (D : CyclicData k) (i : Vertex)
    (r : Row k) (b : Auxiliary k) :
    D.multiply (embedRow i r) b = embedRow i (D.rowAction i r b) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [embedRow, rowAction]
  · simp [multiply, embedRow, h]

theorem rowAction_assoc (D : CyclicData k) (i : Vertex) (r : Row k)
    (b c : Auxiliary k) :
    D.rowAction i (D.rowAction i r b) c = D.rowAction i r (D.multiply b c) := by
  have h := congrArg (fun x : Auxiliary k => x i) (D.multiply_assoc (embedRow i r) b c)
  rw [D.multiply_embedRow] at h
  exact h

@[simp] theorem rowAction_identity (D : CyclicData k) (i : Vertex) (r : Row k) :
    D.rowAction i r identityAuxiliary = r := by
  simp [rowAction, embedRow]

def rowActionLinear (D : CyclicData k) (i : Vertex) (b : Auxiliary k) :
    Row k →ₗ[k] Row k where
  toFun r := D.rowAction i r b
  map_add' := by
    intro r s
    have h : embedRow i (r + s) = embedRow i r + embedRow i s := by
      funext j
      by_cases hj : j = i <;> simp [embedRow, hj]
    simp only [rowAction, h, D.multiply_add_left, Pi.add_apply]
  map_smul' := by
    intro t r
    have h : embedRow i (t • r) = t • embedRow i r := by
      funext j
      by_cases hj : j = i <;> simp [embedRow, hj]
    simp only [rowAction, h, D.multiply_smul_left, Pi.smul_apply, RingHom.id_apply]

theorem leftOne_rowAction (D : CyclicData k) (i : Vertex)
    (a : Vec k) (r : Row k) (b : Auxiliary k) :
    D.rowAction i (D.leftOne i a r) b = D.leftOne i a (D.rowAction (next i) r b) := by
  rcases r with ⟨s, c, v, t⟩
  ext j <;>
    simp [rowAction_formula, leftOne, next_three, map_add, map_smul,
      dot_add_right, dot_smul_left, dot_smul_right, D.cyclic,
      smul_smul, smul_add, smul_eq_mul] <;> ring <;> simp

/-- The computed generated row subspace really is stable under right multiplication. -/
theorem rowGenerated_right_stable (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (b : Auxiliary k) :
    D.rowGenerated i U ≤ (D.rowGenerated i U).comap (D.rowActionLinear i b) := by
  apply iSup_le
  intro a
  rintro r ⟨s, rfl⟩
  change D.rowAction i (D.leftOne i (a : Vec k) s) b ∈ D.rowGenerated i U
  rw [D.leftOne_rowAction]
  exact D.leftOne_mem_rowGenerated i U a.property _

end CyclicData
end Ginzburg333
