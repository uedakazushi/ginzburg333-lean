import Ginzburg333.Bar.Free
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

@[simp] theorem rowRightAction_apply (D : CyclicData k) (i : Vertex) (a : Auxiliary k) (r : Row k) :
    (rowRightAction D i).action a r = D.rowAction i r a := rfl

theorem positiveBasis_embed_source (g : Generator) :
    embedRow g.source (positiveBasis (k := k) g g.source) = positiveBasis g := by
  cases g <;> simp [positiveBasis, Generator.source, embedRow]

theorem rowCoordinates_basis (i : Vertex) (t g : Generator) (ht : t.source = i) :
    rowCoordinates (k := k) i (positiveBasis t i) g = if g = t then 1 else 0 := by
  subst i
  simp [rowCoordinates, positiveCoordinates, positiveBasis_embed_source, positiveCoordinate_basis]

theorem rowContraction_basis (i : Vertex) (t : Generator) (ht : t.source = i)
    (gs : List Generator) :
    rowContraction (k := k) i (Finsupp.single gs (positiveBasis t i)) =
      -Finsupp.single (t :: gs) CyclicData.identityRow := by
  classical
  simp [rowContraction_single, rowCoordinates_basis i t _ ht]

theorem rowContraction_tensor_basis (i : Vertex) (t : Generator) (ht : t.source = i)
    (x : WordSpace k) :
    rowContraction (k := k) i (tensorWords x (positiveBasis t i)) =
      -prependChain (k := k) [t] (tensorWords x CyclicData.identityRow) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
      abel
  | single gs a =>
      simp only [tensorWords_single, map_smul, rowContraction_basis i t ht,
        prependChain_single, smul_neg, List.singleton_append]

theorem rowCoordinates_action_basis (D : CyclicData k) (i : Vertex) (t g u : Generator)
    (ht : t.source = i) :
    rowCoordinates i (D.rowAction i (positiveBasis t i) (positiveBasis g)) u =
      positiveMultiplication D t g u := by
  have he : embedRow i (positiveBasis (k := k) t i) = positiveBasis t := by
    rw [← ht]; exact positiveBasis_embed_source t
  change positiveCoordinate (embedRow i (D.rowAction i (positiveBasis t i) (positiveBasis g))) u = _
  rw [← D.multiply_embedRow, he]
  rfl

theorem rowAction_identity_positive (D : CyclicData k) (i : Vertex) (t : Generator) :
    D.rowAction i CyclicData.identityRow (positiveBasis t) = positiveBasis t i := by
  simp [CyclicData.rowAction_formula, CyclicData.identityRow]

theorem rowContraction_homotopy_basis (D : CyclicData k) (i : Vertex)
    (t : Generator) (ht : t.source = i) (gs : List Generator) :
    ambientDifferential (rowRightAction D i)
        (rowContraction (k := k) i (Finsupp.single gs (positiveBasis t i))) +
      rowContraction (k := k) i (ambientDifferential (rowRightAction D i) (Finsupp.single gs (positiveBasis t i))) =
      Finsupp.single gs (positiveBasis t i) := by
  classical
  rw [rowContraction_basis i t ht, map_neg, ambientDifferential_single, ambientDifferential_single]
  cases gs with
  | nil =>
      simp only [onWord, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        Finsupp.lsingle_apply, rowRightAction_apply, rowAction_identity_positive,
        innerBasisDifferential, map_zero, LinearMap.zero_apply, add_zero, neg_neg]
  | cons g gs =>
      simp only [onWord, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        Finsupp.lsingle_apply, map_add, map_neg, rowContraction_tensor_basis i t ht]
      simp only [rowRightAction_apply, rowAction_identity_positive,
        rowContraction_single, rowCoordinates_action_basis D i t g _ ht,
        innerBasisDifferential, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply,
        map_smul, LinearMap.smul_apply, tensorWords_single,
        one_smul, tensorWords_prepend]
      abel


@[simp] theorem rowCoordinates_identity (i : Vertex) (g : Generator) :
    rowCoordinates (k := k) i CyclicData.identityRow g = 0 := by
  cases g <;> simp [rowCoordinates, positiveCoordinates, positiveCoordinate, embedRow,
    CyclicData.identityRow, apply_ite]

theorem row_decomposition (i : Vertex) (r : Row k) :
    r.1 • CyclicData.identityRow +
      ∑ g : Generator, rowCoordinates i r g • positiveBasis g i = r := by
  classical
  let a : Auxiliary k := fun j => (0, (embedRow i r j).2)
  have ha : augmentation a = 0 := rfl
  have hc : positiveCoordinate a = positiveCoordinate (embedRow i r) := by
    funext g; cases g <;> rfl
  have he := congrArg (fun b : Auxiliary k => b i) (sum_positive_basis a ha)
  simp only [Finset.sum_apply, Pi.smul_apply, hc] at he
  change (∑ g, rowCoordinates i r g • positiveBasis g i) = (0, (embedRow i r i).2) at he
  rw [he]
  simp [embedRow, CyclicData.identityRow]

@[simp] theorem rowContraction_identity (i : Vertex) (gs : List Generator) :
    rowContraction (k := k) i (Finsupp.single gs CyclicData.identityRow) = 0 := by
  simp [rowContraction_single]

theorem rowContraction_tensor_identity (i : Vertex) (x : WordSpace k) :
    rowContraction (k := k) i (tensorWords x CyclicData.identityRow) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp

theorem positiveBasis_at_of_source_ne (g : Generator) (i : Vertex) (hi : g.source ≠ i) :
    positiveBasis (k := k) g i = 0 := by
  cases g <;> simp_all [positiveBasis, Generator.source, embedRow, eq_comm]

theorem rowContraction_homotopy_identity (D : CyclicData k) (i : Vertex)
    (g : Generator) (gs : List Generator) (hi : g.source = i) :
    ambientDifferential (rowRightAction D i)
        (rowContraction (k := k) i (Finsupp.single (g :: gs) CyclicData.identityRow)) +
      rowContraction (k := k) i (ambientDifferential (rowRightAction D i)
        (Finsupp.single (g :: gs) CyclicData.identityRow)) =
      Finsupp.single (g :: gs) CyclicData.identityRow := by
  simp only [rowContraction_identity, map_zero, zero_add, ambientDifferential_single,
    onWord, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, map_add, map_neg, rowContraction_tensor_identity]
  change -rowContraction (k := k) i (Finsupp.single gs (D.rowAction i CyclicData.identityRow (positiveBasis g))) + 0 = _
  rw [rowAction_identity_positive, rowContraction_basis i g hi, neg_neg, add_zero]

def rowHomotopyOperator (D : CyclicData k) (i : Vertex) : Ambient (Row k) →ₗ[k] Ambient (Row k) :=
  (ambientDifferential (rowRightAction D i)).comp (rowContraction (k := k) i) +
    (rowContraction (k := k) i).comp (ambientDifferential (rowRightAction D i))

theorem rowContraction_homotopy_single (D : CyclicData k) (i : Vertex)
    (g : Generator) (gs : List Generator) (m : Row k)
    (hm : initialProjection (rowRightAction D i) (g :: gs) m = m) :
    rowHomotopyOperator D i (Finsupp.single (g :: gs) m) = Finsupp.single (g :: gs) m := by
  classical
  let f : Row k →ₗ[k] Ambient (Row k) := (rowHomotopyOperator D i).comp (Finsupp.lsingle (g :: gs))
  let j : Row k →ₗ[k] Ambient (Row k) := Finsupp.lsingle (g :: gs)
  have hz : f (m.1 • CyclicData.identityRow) = j (m.1 • CyclicData.identityRow) := by
    by_cases hi : g.source = i
    · change rowHomotopyOperator D i _ = _
      simp only [Finsupp.smul_single, map_smul]
      exact congrArg (m.1 • ·) (rowContraction_homotopy_identity D i g gs hi)
    · have he : D.rowAction i m (vertexIdempotent g.source) = m := hm
      have h0 := congrArg (fun r : Row k => r.1) he
      have hmi : m.1 = 0 := by
        simpa [CyclicData.rowAction_formula, vertexIdempotent, embedRow, CyclicData.identityRow,
          Ne.symm hi] using h0.symm
      simp [hmi]
  have ht : ∀ t : Generator, rowCoordinates i m t • f (positiveBasis t i) =
      rowCoordinates i m t • j (positiveBasis t i) := by
    intro t
    by_cases hc : rowCoordinates i m t = 0
    · simp [hc]
    · apply congrArg (rowCoordinates i m t • ·)
      exact rowContraction_homotopy_basis D i t (rowCoordinates_source i m t hc) (g :: gs)
  change f m = j m
  conv_lhs => rw [← row_decomposition i m]
  rw [map_add, map_sum, hz]
  simp only [map_smul, ht]
  simp only [← map_smul]
  rw [← map_sum, ← map_add, row_decomposition]

end
end Ginzburg333.Bar
