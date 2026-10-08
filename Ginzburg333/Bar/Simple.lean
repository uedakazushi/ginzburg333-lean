import Ginzburg333.Bar.Filtration

/-! Identify the actual full row quotient with its vertex simple module. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

def rowScalar : Row k →ₗ[k] k := LinearMap.fst k k (Vec k × Vec k × k)

def simpleCoefficient (D : CyclicData k) (hD : D.Regular) (i : Vertex) :
    D.QuotientRow i ⊤ →ₗ[k] k :=
  (D.rowGenerated i ⊤).liftQ rowScalar (by
    intro r hr
    rw [D.rowGenerated_eq_planeRows hD i ⊤ (by simp)] at hr
    exact hr.1)

@[simp] theorem simpleCoefficient_mkQ (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r : Row k) :
    simpleCoefficient D hD i ((D.rowGenerated i ⊤).mkQ r) = r.1 := rfl

def simpleUnit (D : CyclicData k) (i : Vertex) : D.QuotientRow i ⊤ :=
  (D.rowGenerated i ⊤).mkQ CyclicData.identityRow

theorem simpleRow_expand (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (x : D.QuotientRow i ⊤) : x = simpleCoefficient D hD i x • simpleUnit D i := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i ⊤).mkQ_surjective x
  rw [simpleCoefficient_mkQ]
  change (D.rowGenerated i ⊤).mkQ r = r.1 • (D.rowGenerated i ⊤).mkQ CyclicData.identityRow
  rw [← map_smul]
  apply (Submodule.Quotient.eq _).mpr
  rw [D.rowGenerated_eq_planeRows hD i ⊤ (by simp)]
  simp [planeRows, Submodule.mem_prod, CyclicData.identityRow]

@[simp] theorem simpleCoefficient_unit (D : CyclicData k) (hD : D.Regular) (i : Vertex) :
    simpleCoefficient D hD i (simpleUnit D i) = 1 := rfl

def simpleRowEquiv (D : CyclicData k) (hD : D.Regular) (i : Vertex) : D.QuotientRow i ⊤ ≃ₗ[k] k where
  toLinearMap := simpleCoefficient D hD i
  invFun a := a • simpleUnit D i
  left_inv := fun x => (simpleRow_expand D hD i x).symm
  right_inv := by intro a; simp

theorem simpleRow_action (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (a : Auxiliary k) (x : D.QuotientRow i ⊤) :
    D.quotientAction i ⊤ a x = (a i).1 • x := by
  apply (simpleRowEquiv D hD i).injective
  obtain ⟨r, rfl⟩ := (D.rowGenerated i ⊤).mkQ_surjective x
  change simpleCoefficient D hD i (D.quotientAction i ⊤ a ((D.rowGenerated i ⊤).mkQ r)) =
    simpleCoefficient D hD i ((a i).1 • (D.rowGenerated i ⊤).mkQ r)
  rw [CyclicData.quotientAction_mkQ, simpleCoefficient_mkQ, map_smul, simpleCoefficient_mkQ]
  simp only [D.rowAction_formula, smul_eq_mul]
  exact mul_comm _ _

@[simp] theorem simpleRow_positive_action (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (g : Generator) (x : D.QuotientRow i ⊤) : D.quotientAction i ⊤ (positiveBasis g) x = 0 := by
  rw [simpleRow_action D hD]
  have h := congrFun (augmentation_positiveBasis (k := k) g) i
  change (positiveBasis (k := k) g i).1 = 0 at h
  rw [h, zero_smul]

theorem simpleRow_corner (D : CyclicData k) (hD : D.Regular) (i j : Vertex)
    (x : D.QuotientRow i ⊤) : D.quotientAction i ⊤ (vertexIdempotent j) x = if i = j then x else 0 := by
  rw [simpleRow_action D hD]
  by_cases h : i = j <;> simp [vertexIdempotent, embedRow, CyclicData.identityRow, h]

theorem simpleRow_degree (D : CyclicData k) (hD : D.Regular) (i : Vertex)
    (d : Fin 4) (x : D.QuotientRow i ⊤) : D.quotientProjection i ⊤ d x = if d = 0 then x else 0 := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i ⊤).mkQ_surjective x
  rw [CyclicData.quotientProjection_mkQ]
  fin_cases d
  · rw [simpleRow_expand D hD i ((D.rowGenerated i ⊤).mkQ r)]
    change (D.rowGenerated i ⊤).mkQ (degreeProjection 0 r) =
      simpleCoefficient D hD i ((D.rowGenerated i ⊤).mkQ r) • (D.rowGenerated i ⊤).mkQ CyclicData.identityRow
    rw [simpleCoefficient_mkQ, ← map_smul]
    congr 1
    simp [degreeProjection, CyclicData.identityRow]
  all_goals
    simp only [Fin.isValue, reduceCtorEq, if_false]
    apply (Submodule.Quotient.eq _).mpr
    rw [D.rowGenerated_eq_planeRows hD i ⊤ (by simp)]
    simp [degreeProjection, planeRows, Submodule.mem_prod]

/-- The coefficient action in the full quotient is exactly e_i S. -/
theorem simple_normalized_bar_off_diagonal [IsAlgClosed k] (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (r n : ℕ) (hne : n ≠ r) : BarExact D i ⊤ r n :=
  normalized_bar_off_diagonal D hD i ⊤ (Or.inr (Or.inr (Or.inr rfl))) r n hne
end
end Ginzburg333.Bar
