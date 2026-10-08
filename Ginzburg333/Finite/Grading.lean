import Ginzburg333.Finite.Filtration

/-! Four-degree row decomposition and homogeneous maps in the filtration sequence. -/
namespace Ginzburg333
variable {k : Type*} [Field k]

def degreeProjection (d : Fin 4) : Row k →ₗ[k] Row k where
  toFun r := match d.val with
    | 0 => (r.1, 0, 0, 0)
    | 1 => (0, r.2.1, 0, 0)
    | 2 => (0, 0, r.2.2.1, 0)
    | _ => (0, 0, 0, r.2.2.2)
  map_add' := by intro r s; fin_cases d <;> simp
  map_smul' := by intro t r; fin_cases d <;> simp

def previousDegree : Fin 4 → Fin 4 := ![0, 0, 1, 2]

theorem sum_degreeProjection (r : Row k) : ∑ d : Fin 4, degreeProjection d r = r := by
  rcases r with ⟨s, a, v, t⟩
  simp [degreeProjection, Fin.sum_univ_succ]

theorem degreeProjection_comp (d e : Fin 4) (r : Row k) :
    degreeProjection d (degreeProjection e r) = if d = e then degreeProjection d r else 0 := by
  fin_cases d <;> fin_cases e <;> simp [degreeProjection]

def augmentation : Auxiliary k →ₗ[k] (Vertex → k) where
  toFun b := fun i => (b i).1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

namespace CyclicData

@[simp] theorem augmentation_multiply (D : CyclicData k) (a b : Auxiliary k) :
    augmentation (D.multiply a b) = augmentation a * augmentation b := rfl

@[simp] theorem augmentation_identity :
    augmentation (identityAuxiliary : Auxiliary k) = 1 := rfl

theorem degreeProjection_leftOne (D : CyclicData k) (i : Vertex) (a : Vec k)
    (r : Row k) (d : Fin 4) :
    degreeProjection d (D.leftOne i a r) =
      if d = 0 then 0 else D.leftOne i a (degreeProjection (previousDegree d) r) := by
  fin_cases d <;> simp [degreeProjection, previousDegree, leftOne]

/-- The generated ideal is homogeneous, degree by degree. -/
theorem rowGenerated_degree_stable (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (d : Fin 4) :
    D.rowGenerated i U ≤ (D.rowGenerated i U).comap (degreeProjection d) := by
  apply iSup_le
  intro a
  rintro r ⟨s, rfl⟩
  change degreeProjection d (D.leftOne i (a : Vec k) s) ∈ D.rowGenerated i U
  rw [D.degreeProjection_leftOne]
  split_ifs
  · exact Submodule.zero_mem _
  · exact D.leftOne_mem_rowGenerated i U a.property _

def quotientProjection (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (d : Fin 4) : D.QuotientRow i U →ₗ[k] D.QuotientRow i U :=
  (D.rowGenerated i U).mapQ (D.rowGenerated i U) (degreeProjection d)
    (D.rowGenerated_degree_stable i U d)

@[simp] theorem quotientProjection_mkQ (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (d : Fin 4) (r : Row k) :
    D.quotientProjection i U d ((D.rowGenerated i U).mkQ r) =
      (D.rowGenerated i U).mkQ (degreeProjection d r) := rfl

theorem quotientProjection_sum (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (x : D.QuotientRow i U) :
    ∑ d : Fin 4, D.quotientProjection i U d x = x := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simpa only [map_sum, quotientProjection_mkQ] using
    congrArg (D.rowGenerated i U).mkQ (sum_degreeProjection r)

theorem quotientProjection_comp (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (d e : Fin 4) (x : D.QuotientRow i U) :
    D.quotientProjection i U d (D.quotientProjection i U e x) =
      if d = e then D.quotientProjection i U d x else 0 := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simp only [quotientProjection_mkQ, degreeProjection_comp]
  split_ifs <;> simp

def quotientAction (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (b : Auxiliary k) : D.QuotientRow i U →ₗ[k] D.QuotientRow i U :=
  (D.rowGenerated i U).mapQ (D.rowGenerated i U) (D.rowActionLinear i b)
    (D.rowGenerated_right_stable i U b)

@[simp] theorem quotientAction_mkQ (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (b : Auxiliary k) (r : Row k) :
    D.quotientAction i U b ((D.rowGenerated i U).mkQ r) =
      (D.rowGenerated i U).mkQ (D.rowAction i r b) := rfl

theorem quotientAction_assoc (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (b c : Auxiliary k) (x : D.QuotientRow i U) :
    D.quotientAction i U c (D.quotientAction i U b x) =
      D.quotientAction i U (D.multiply b c) x := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simp only [quotientAction_mkQ, D.rowAction_assoc]

@[simp] theorem quotientAction_identity (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (x : D.QuotientRow i U) :
    D.quotientAction i U identityAuxiliary x = x := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simp only [quotientAction_mkQ, D.rowAction_identity]

theorem quotientAction_add (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (b c : Auxiliary k) (x : D.QuotientRow i U) :
    D.quotientAction i U (b + c) x = D.quotientAction i U b x + D.quotientAction i U c x := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simp only [quotientAction_mkQ, rowAction, D.multiply_add_right, Pi.add_apply, map_add]

theorem quotientAction_smul (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (t : k) (b : Auxiliary k) (x : D.QuotientRow i U) :
    D.quotientAction i U (t • b) x = t • D.quotientAction i U b x := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective x
  simp only [quotientAction_mkQ, rowAction, D.multiply_smul_right, Pi.smul_apply, map_smul]

namespace FiltrationStep
variable {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}

/-- In internal degrees the inclusion has degree +1. -/
theorem inclusion_degree (s : D.FiltrationStep i U) (d : Fin 4)
    (x : D.QuotientRow (next i) s.colon) :
    D.quotientProjection i s.smaller d (s.inclusion x) =
      if d = 0 then 0 else s.inclusion (D.quotientProjection (next i) s.colon (previousDegree d) x) := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated (next i) s.colon).mkQ_surjective x
  simp only [inclusion_mkQ, quotientProjection_mkQ, D.degreeProjection_leftOne]
  split_ifs <;> simp

theorem projection_degree (s : D.FiltrationStep i U) (d : Fin 4)
    (x : D.QuotientRow i s.smaller) :
    D.quotientProjection i U d (s.projection x) =
      s.projection (D.quotientProjection i s.smaller d x) := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i s.smaller).mkQ_surjective x
  simp only [projection_mkQ, quotientProjection_mkQ]

theorem inclusion_action (s : D.FiltrationStep i U) (b : Auxiliary k)
    (x : D.QuotientRow (next i) s.colon) :
    D.quotientAction i s.smaller b (s.inclusion x) =
      s.inclusion (D.quotientAction (next i) s.colon b x) := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated (next i) s.colon).mkQ_surjective x
  simp only [inclusion_mkQ, quotientAction_mkQ, D.leftOne_rowAction]

theorem projection_action (s : D.FiltrationStep i U) (b : Auxiliary k)
    (x : D.QuotientRow i s.smaller) :
    D.quotientAction i U b (s.projection x) = s.projection (D.quotientAction i s.smaller b x) := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i s.smaller).mkQ_surjective x
  simp only [projection_mkQ, quotientAction_mkQ]

end FiltrationStep
end CyclicData
end Ginzburg333
