import Ginzburg333.Bar.InternalExact
import Ginzburg333.Bar.InternalDifferential

/-! The free row action and the vertex-balanced normalized contracting operator. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

def rowRightAction (D : CyclicData k) (i : Vertex) : RightAction D (Row k) where
  action :=
    { toFun := D.rowActionLinear i
      map_add' := by
        intro a b; apply LinearMap.ext; intro r
        simp [CyclicData.rowActionLinear, CyclicData.rowAction, D.multiply_add_right]
      map_smul' := by
        intro a b; apply LinearMap.ext; intro r
        simp [CyclicData.rowActionLinear, CyclicData.rowAction, D.multiply_smul_right] }
  assoc := fun a b r => D.rowAction_assoc i r a b
  identity := D.rowAction_identity i

def rowCoordinates (i : Vertex) : Row k →ₗ[k] (Generator → k) where
  toFun r := positiveCoordinates (embedRow i r)
  map_add' := by
    intro r s
    have he : embedRow i (r + s) = embedRow i r + embedRow i s := by
      funext j; by_cases h : j = i <;> simp [embedRow, h]
    rw [he, map_add]
  map_smul' := by
    intro a r
    have he : embedRow i (a • r) = a • embedRow i r := by
      funext j; by_cases h : j = i <;> simp [embedRow, h]
    rw [he, map_smul]
    rfl

theorem rowCoordinates_source (i : Vertex) (r : Row k) (g : Generator)
    (hg : rowCoordinates i r g ≠ 0) : g.source = i := by
  cases g <;> simp_all [rowCoordinates, positiveCoordinates, positiveCoordinate,
    embedRow, Generator.source, apply_ite]
  all_goals split_ifs at hg <;> simp_all

set_option maxHeartbeats 1000000 in
theorem rowCoordinates_corner (D : CyclicData k) (i j : Vertex) (r : Row k) (g : Generator) :
    rowCoordinates i (D.rowAction i r (vertexIdempotent j)) g =
      if g.target = j then rowCoordinates i r g else 0 := by
  classical
  cases g with
  | forward l a => fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [rowCoordinates, positiveCoordinates, positiveCoordinate, CyclicData.rowAction_formula,
      vertexIdempotent, embedRow, CyclicData.identityRow, Generator.target, next, apply_ite]
  | reverse l a => fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [rowCoordinates, positiveCoordinates, positiveCoordinate, CyclicData.rowAction_formula,
      vertexIdempotent, embedRow, CyclicData.identityRow, Generator.target, next, apply_ite]
  | loop l => fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [rowCoordinates, positiveCoordinates, positiveCoordinate, CyclicData.rowAction_formula,
      vertexIdempotent, embedRow, CyclicData.identityRow, Generator.target, next, apply_ite]

def rowContractionOnWord (i : Vertex) (gs : List Generator) : Row k →ₗ[k] Ambient (Row k) where
  toFun r := -∑ g : Generator, rowCoordinates i r g • Finsupp.single (g :: gs) CyclicData.identityRow
  map_add' := by
    intro r s
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]
  map_smul' := by
    intro a r
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_neg, RingHom.id_apply]

def rowContraction (i : Vertex) : Ambient (Row k) →ₗ[k] Ambient (Row k) :=
  Finsupp.lsum k (rowContractionOnWord i)

@[simp] theorem rowContraction_single (i : Vertex) (gs : List Generator) (r : Row k) :
    rowContraction (k := k) i (Finsupp.single gs r) =
      -∑ g : Generator, rowCoordinates i r g • Finsupp.single (g :: gs) CyclicData.identityRow := by
  simp [rowContraction, Finsupp.lsum_single, rowContractionOnWord]

theorem identityRow_corner (D : CyclicData k) (i : Vertex) :
    cornerProjection (rowRightAction D i) i CyclicData.identityRow = CyclicData.identityRow := by
  simp [cornerProjection, rowRightAction, CyclicData.rowActionLinear,
    CyclicData.rowAction_formula, vertexIdempotent, embedRow, CyclicData.identityRow]

/-- The inserted positive factor meets both vertex conditions. -/
theorem rowContraction_single_balanced (D : CyclicData k) (i : Vertex)
    (gs : List Generator) (r : Row k) (hc : composable gs)
    (hr : initialProjection (rowRightAction D i) gs r = r) :
    rowContraction (k := k) i (Finsupp.single gs r) ∈ balancedAmbient (rowRightAction D i) := by
  classical
  rw [rowContraction_single]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro g hg
  by_cases hcoord : rowCoordinates i r g = 0
  · simp [hcoord]
  · have hsource := rowCoordinates_source i r g hcoord
    apply Submodule.smul_mem
    apply balanced_single
    · cases gs with
      | nil => trivial
      | cons h gs =>
          refine ⟨?_, hc⟩
          have he : D.rowAction i r (vertexIdempotent h.source) = r := hr
          have ht := rowCoordinates_corner D i h.source r g
          rw [he] at ht
          by_contra hn
          rw [if_neg hn] at ht
          exact hcoord ht
    · change cornerProjection (rowRightAction D i) g.source CyclicData.identityRow = _
      rw [hsource]
      exact identityRow_corner D i

theorem rowContraction_balanced (D : CyclicData k) (i : Vertex) (x : Ambient (Row k))
    (hx : x ∈ balancedAmbient (rowRightAction D i)) :
    rowContraction (k := k) i x ∈ balancedAmbient (rowRightAction D i) := by
  rw [← (mem_balancedAmbient_iff _ _).mp hx]
  suffices h : ∀ y : Ambient (Row k), rowContraction (k := k) i (normalization (rowRightAction D i) y) ∈
      balancedAmbient (rowRightAction D i) from h x
  intro y
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | single gs r =>
      rw [normalization_single]
      by_cases hc : composable gs
      · rw [if_pos hc]
        exact rowContraction_single_balanced D i gs _ hc (initialProjection_idempotent _ _ _)
      · simp [hc]

theorem rowContraction_length (i : Vertex) (r : ℕ) (x : Ambient (Row k))
    (hx : x ∈ lengthComponent (k := k) r) : rowContraction (k := k) i x ∈ lengthComponent (k := k) (r + 1) := by
  classical
  change x.support.sum (fun gs => rowContractionOnWord (k := k) i gs (x gs)) ∈ _
  apply Submodule.sum_mem
  intro gs hgs
  change -(∑ g, rowCoordinates i (x gs) g • Finsupp.single (g :: gs) CyclicData.identityRow) ∈ _
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported k _
  simpa only [Set.mem_setOf_eq, List.length_cons] using congrArg (· + 1) (hx hgs)

def normalizedRowContraction (D : CyclicData k) (i : Vertex) (r : ℕ) :
    normalizedTerm (rowRightAction D i) r →ₗ[k] normalizedTerm (rowRightAction D i) (r + 1) where
  toFun x := ⟨rowContraction (k := k) i x.val, rowContraction_balanced D i _ x.property.1,
    rowContraction_length i r _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

end
end Ginzburg333.Bar
