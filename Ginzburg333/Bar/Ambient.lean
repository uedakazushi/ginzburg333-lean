import Ginzburg333.Bar.Positive
import Ginzburg333.Ginzburg.FreeWords

/-! Finite bar word vectors for an actual right action of the auxiliary algebra. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
noncomputable section
structure RightAction (D : CyclicData k) (M : Type*) [AddCommGroup M] [Module k M] where
  action : Auxiliary k →ₗ[k] M →ₗ[k] M
  assoc : ∀ a b m, action b (action a m) = action (D.multiply a b) m
  identity : ∀ m, action CyclicData.identityAuxiliary m = m
def quotientRightAction (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) :
    RightAction D (D.QuotientRow i U) where
  action :=
    { toFun := D.quotientAction i U
      map_add' := by
        intro a b; apply LinearMap.ext; intro x; exact D.quotientAction_add i U a b x
      map_smul' := by
        intro a b; apply LinearMap.ext; intro x; exact D.quotientAction_smul i U a b x }
  assoc := D.quotientAction_assoc i U
  identity := D.quotientAction_identity i U
abbrev Ambient (M : Type*) [Zero M] := List Generator →₀ M
def prependChain (gs : List Generator) : Ambient M →ₗ[k] Ambient M :=
  Finsupp.lmapDomain M k (fun as => gs ++ as)
def coefficientMap (f : M →ₗ[k] N) : Ambient M →ₗ[k] Ambient N := Finsupp.mapRange.linearMap f
@[simp] theorem coefficientMap_single (f : M →ₗ[k] N) (gs : List Generator) (m : M) :
    coefficientMap f (Finsupp.single gs m) = Finsupp.single gs (f m) := by
  simp [coefficientMap]
def tensorWords : WordSpace k →ₗ[k] M →ₗ[k] Ambient M :=
  Finsupp.linearCombination k (fun gs => Finsupp.lsingle gs)
@[simp] theorem tensorWords_single (gs : List Generator) (a : k) (m : M) :
    tensorWords (Finsupp.single gs a) m = a • Finsupp.single gs m := by
  simp [tensorWords]
theorem coefficientMap_tensorWords (f : M →ₗ[k] N) (x : WordSpace k) (m : M) :
    coefficientMap f (tensorWords x m) = tensorWords x (f m) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp
def innerBasisDifferential (D : CyclicData k) : List Generator → WordSpace k
  | [] => 0
  | [_] => 0
  | g :: h :: gs => (∑ t, positiveMultiplication D g h t • Finsupp.single (t :: gs) 1) -
      prependWords [g] (innerBasisDifferential D (h :: gs))
def innerDifferential (D : CyclicData k) : WordSpace k →ₗ[k] WordSpace k :=
  Finsupp.linearCombination k (innerBasisDifferential D)
def onWord {D : CyclicData k} (A : RightAction D M) : List Generator → M →ₗ[k] Ambient M
  | [] => 0
  | g :: gs => -(Finsupp.lsingle gs).comp (A.action (positiveBasis g)) +
      tensorWords (innerBasisDifferential D (g :: gs))
def ambientDifferential {D : CyclicData k} (A : RightAction D M) : Ambient M →ₗ[k] Ambient M :=
  Finsupp.lsum k (onWord A)
@[simp] theorem ambientDifferential_single {D : CyclicData k} (A : RightAction D M)
    (gs : List Generator) (m : M) :
    ambientDifferential A (Finsupp.single gs m) = onWord A gs m := by
  simp only [ambientDifferential, Finsupp.lsum_single]
theorem ambientDifferential_natural {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (x : Ambient M) :
    coefficientMap f (ambientDifferential A x) = ambientDifferential B (coefficientMap f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs m => cases gs <;> simp [onWord, coefficientMap_tensorWords, hf]
theorem filtration_inclusion_natural {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}
    (s : D.FiltrationStep i U) (x : Ambient (D.QuotientRow (next i) s.colon)) :
    coefficientMap s.inclusion (ambientDifferential (quotientRightAction D (next i) s.colon) x) =
      ambientDifferential (quotientRightAction D i s.smaller) (coefficientMap s.inclusion x) := by
  apply ambientDifferential_natural
  intro a m
  exact (s.inclusion_action a m).symm
theorem filtration_projection_natural {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}
    (s : D.FiltrationStep i U) (x : Ambient (D.QuotientRow i s.smaller)) :
    coefficientMap s.projection (ambientDifferential (quotientRightAction D i s.smaller) x) =
      ambientDifferential (quotientRightAction D i U) (coefficientMap s.projection x) := by
  apply ambientDifferential_natural
  intro a m
  exact (s.projection_action a m).symm
end
end Ginzburg333.Bar
