import Ginzburg333.Ginzburg.FreeWords
import Ginzburg333.Ginzburg.Homogeneous

/-! Transfer square-zero through the injective map forgetting path validity. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
abbrev LocatedWordSpace (k : Type*) [Zero k] := (Vertex × List Generator) →₀ k
def locateWords (start : Vertex) : WordSpace k →ₗ[k] LocatedWordSpace k :=
  Finsupp.lmapDomain k k (fun gs => (start, gs))
def locatedDifferential (w : Tensor k) : LocatedWordSpace k →ₗ[k] LocatedWordSpace k :=
  Finsupp.linearCombination k (fun p => locateWords p.1 (wordVectorDifferential w p.2))
@[simp] theorem locateWords_single (start : Vertex) (gs : List Generator) (a : k) :
    locateWords start (Finsupp.single gs a) = Finsupp.single (start, gs) a := by
  simp [locateWords, Finsupp.lmapDomain_apply]
@[simp] theorem locatedDifferential_single (w : Tensor k) (p : Vertex × List Generator) (a : k) :
    locatedDifferential w (Finsupp.single p a) = a • locateWords p.1 (wordVectorDifferential w p.2) := by
  simp [locatedDifferential]
theorem locatedDifferential_locateWords (w : Tensor k) (start : Vertex) (x : WordSpace k) :
    locatedDifferential w (locateWords start x) = locateWords start (freeDifferential w x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp
theorem locatedDifferential_square (w : Tensor k) (x : LocatedWordSpace k) :
    locatedDifferential w (locatedDifferential w x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a => simp [locatedDifferential_locateWords, wordVectorDifferential_square]
def forgetPathValidity : PathSpace k →ₗ[k] LocatedWordSpace k :=
  Finsupp.lmapDomain k k Subtype.val
theorem forgetPathValidity_injective : Function.Injective (forgetPathValidity (k := k)) := by
  exact Finsupp.mapDomain_injective Subtype.val_injective
@[simp] theorem forgetPathValidity_single (p : BasisPath) (a : k) :
    forgetPathValidity (Finsupp.single p a) = Finsupp.single p.val a := by
  simp [forgetPathValidity, Finsupp.lmapDomain_apply]
theorem forgetPathValidity_pathTerm (start : Vertex) (t : k × List Generator)
    (ht : ValidPath (start, t.2)) :
    forgetPathValidity (pathTerm start t) = Finsupp.single (start, t.2) t.1 := by
  simp [pathTerm, ht]
theorem forgetPathValidity_basisDifferential (w : Tensor k) (p : BasisPath) :
    forgetPathValidity (basisDifferential w p) = locateWords p.val.1 (wordVectorDifferential w p.val.2) := by
  classical
  unfold basisDifferential wordVectorDifferential
  rw [map_list_sum, map_list_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [forgetPathValidity_pathTerm _ _ (differential_term_valid w p ht)]
  simp [wordTerm]
theorem forgetPathValidity_differential (w : Tensor k) (x : PathSpace k) :
    forgetPathValidity (differential w x) = locatedDifferential w (forgetPathValidity x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a => simp [differential, forgetPathValidity_basisDifferential, locatedDifferential]
theorem differential_square (w : Tensor k) (x : PathSpace k) :
    differential w (differential w x) = 0 := by
  apply forgetPathValidity_injective
  rw [forgetPathValidity_differential, forgetPathValidity_differential,
    locatedDifferential_square, map_zero]
end
end Ginzburg333.Ginzburg
