import Ginzburg333.Comparison.CobarVertices
import Ginzburg333.Bar.SimpleDifferential

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem simpleBarLinearBasis_repr (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (x : internallyNormalizedTerm D i ⊤ r n) :
    (simpleBarLinearBasis D hD i r n).repr x =
      Finsupp.supportedEquivFinsupp (R := k) (M := k) {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}
        (simpleBarCoordinatesEquiv D hD i r n x) := by
  classical
  rw [simpleBarLinearBasis]
  rfl

theorem simpleBarLinearBasis_scalar (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (gs : SimpleRowBasis i r n) :
    (simpleBarCoordinatesEquiv D hD i r n (simpleBarLinearBasis D hD i r n gs)).val =
      Finsupp.single gs.val 1 := by
  classical
  have h := (simpleBarLinearBasis D hD i r n).repr_self gs
  rw [simpleBarLinearBasis_repr] at h
  let e := Finsupp.supportedEquivFinsupp (R := k) (M := k)
    {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}
  have hh := congrArg e.symm h
  dsimp only [e] at hh
  simp only [LinearEquiv.symm_apply_apply] at hh
  have hv := congrArg (fun z : scalarSimpleTerm (k := k) i r n => z.val) hh
  dsimp only at hv
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single] at hv
  exact hv

def dualWordCoordinates (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    Module.Dual k (internallyNormalizedTerm D i ⊤ r n) →ₗ[k] WordSpace k :=
  (scalarSimpleTerm (k := k) i r n).subtype.comp
    ((Finsupp.supportedEquivFinsupp (R := k) (M := k) {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm.toLinearMap.comp
      (simpleBarDualCoordinates D hD i r n).toLinearMap)

theorem dualWordCoordinates_apply (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (f : Module.Dual k (internallyNormalizedTerm D i ⊤ r n)) (gs : SimpleRowBasis i r n) :
    dualWordCoordinates D hD i r n f gs.val = f (simpleBarLinearBasis D hD i r n gs) := by
  classical
  change ((Finsupp.supportedEquivFinsupp (R := k) (M := k) {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm
    (simpleBarDualCoordinates D hD i r n f)).val gs.val = _
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe]
  rw [Finsupp.extendDomain_toFun]
  split_ifs with hh
  · have he : (⟨gs.val, hh⟩ : SimpleRowBasis i r n) = gs := Subtype.ext rfl
    rw [he]
    exact simpleBarDualCoordinates_apply D hD i r n f gs
  · exact (hh gs.property).elim

theorem dualWordCoordinates_mem (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (f : Module.Dual k (internallyNormalizedTerm D i ⊤ r n)) :
    dualWordCoordinates D hD i r n f ∈ scalarSimpleTerm (k := k) i r n :=
  ((Finsupp.supportedEquivFinsupp (R := k) (M := k) {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm
    (simpleBarDualCoordinates D hD i r n f)).property
theorem basisDualCoordinates_dualBasis {ι M : Type*} [AddCommGroup M] [Module k M] [Finite ι] [DecidableEq ι]
    (b : Basis ι k M) (j : ι) :
    basisDualCoordinates b (Basis.dualBasis (R := k) (M := M) b j) = Finsupp.single j 1 := by
  classical
  ext l
  rw [basisDualCoordinates_apply, Basis.dualBasis_apply, Basis.repr_self]
  simp only [Finsupp.single_apply, eq_comm]

theorem dualWordCoordinates_dualBasis (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (gs : SimpleRowBasis i r n) :
    dualWordCoordinates D hD i r n
      (Basis.dualBasis (R := k) (M := internallyNormalizedTerm D i ⊤ r n)
        (simpleBarLinearBasis D hD i r n) gs) = Finsupp.single gs.val 1 := by
  classical
  change ((Finsupp.supportedEquivFinsupp (R := k) (M := k)
    {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm
      (simpleBarDualCoordinates D hD i r n
        (Basis.dualBasis (R := k) (M := internallyNormalizedTerm D i ⊤ r n)
          (simpleBarLinearBasis D hD i r n) gs))).val = _
  simp only [simpleBarDualCoordinates, basisDualCoordinates_dualBasis,
    Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single]

theorem dualWordCoordinates_differential (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (f : Module.Dual k (internallyNormalizedTerm D i ⊤ r n)) :
    dualWordCoordinates D hD i (r + 1) n ((internallyNormalizedDifferential D i ⊤ r n).dualMap f) =
      cobarDifferential D (dualWordCoordinates D hD i r n f) := by
  classical
  have heq : (dualWordCoordinates D hD i (r + 1) n).comp
      (internallyNormalizedDifferential D i ⊤ r n).dualMap =
      (cobarDifferential D).comp (dualWordCoordinates D hD i r n) := by
    apply (Basis.dualBasis (R := k) (M := internallyNormalizedTerm D i ⊤ r n)
      (simpleBarLinearBasis D hD i r n)).ext
    intro a
    ext hs
    simp only [LinearMap.comp_apply]
    by_cases hhs : startsAt i hs ∧ hs.length = r + 1 ∧ wordWeight hs = n
    · rw [dualWordCoordinates_apply D hD i (r + 1) n _ ⟨hs, hhs⟩]
      change (Basis.dualBasis (R := k) (M := internallyNormalizedTerm D i ⊤ r n)
        (simpleBarLinearBasis D hD i r n) a)
        (internallyNormalizedDifferential D i ⊤ r n (simpleBarLinearBasis D hD i (r + 1) n ⟨hs, hhs⟩)) = _
      rw [Basis.dualBasis_apply, simpleBarLinearBasis_repr]
      change (simpleScalarMap D hD i r n
        (internallyNormalizedDifferential D i ⊤ r n (simpleBarLinearBasis D hD i (r + 1) n ⟨hs, hhs⟩))).val a.val = _
      rw [simpleScalarMap_differential]
      change (innerDifferential D
        (simpleBarCoordinatesEquiv D hD i (r + 1) n (simpleBarLinearBasis D hD i (r + 1) n ⟨hs, hhs⟩)).val) a.val = _
      rw [simpleBarLinearBasis_scalar, dualWordCoordinates_dualBasis]
      simp [innerDifferential, cobarDifferential, cobarBasis_transpose]
    · have hL : dualWordCoordinates D hD i (r + 1) n
          ((internallyNormalizedDifferential D i ⊤ r n).dualMap
            (Basis.dualBasis (R := k) (M := internallyNormalizedTerm D i ⊤ r n)
              (simpleBarLinearBasis D hD i r n) a)) hs = 0 := by
        by_contra hn
        exact hhs (dualWordCoordinates_mem D hD i (r + 1) n _ (Finsupp.mem_support_iff.mpr hn))
      have hR : cobarBasis D a.val hs = 0 := by
        by_contra hn
        exact hhs (cobarBasis_scalar_mem D i r n a (Finsupp.mem_support_iff.mpr hn))
      rw [hL, dualWordCoordinates_dualBasis]
      simp [cobarDifferential, hR]
  exact LinearMap.congr_fun heq f


def scalarWordCoordinates (i : Vertex) (r n : ℕ) : (SimpleRowBasis i r n →₀ k) →ₗ[k] WordSpace k :=
  (scalarSimpleTerm (k := k) i r n).subtype.comp
    (Finsupp.supportedEquivFinsupp (R := k) (M := k)
      {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm.toLinearMap

def reversedCoordinates (i : Vertex) (r n : ℕ) : (SimpleRowBasis i r n →₀ k) →ₗ[k] PathSpace k :=
  (rowPathComponent (k := k) i r n).subtype.comp
    ((Finsupp.supportedEquivFinsupp (R := k) (M := k)
      {p : BasisPath | p.val.1 = i ∧ p.val.2.length = r ∧ internalDegree p = n}).symm.toLinearMap.comp
      ((Finsupp.domLCongr (R := k) (M := k) (rowReversedBasisEquiv i r n)).toLinearMap.comp (signCoordinates i r n)))

theorem reversedCoordinates_forget (i : Vertex) (r n : ℕ) (x : SimpleRowBasis i r n →₀ k) :
    forgetPathValidity (reversedCoordinates i r n x) =
      locateWords i (signedWordReversal (scalarWordCoordinates i r n x)) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a =>
      change forgetPathValidity
        ((Finsupp.supportedEquivFinsupp (R := k) (M := k)
          {p : BasisPath | p.val.1 = i ∧ p.val.2.length = r ∧ internalDegree p = n}).symm
            (Finsupp.domLCongr (R := k) (M := k) (rowReversedBasisEquiv i r n)
              (signCoordinates i r n (Finsupp.single gs a)))).val =
        locateWords i (signedWordReversal
          ((Finsupp.supportedEquivFinsupp (R := k) (M := k)
            {gs | startsAt i gs ∧ gs.length = r ∧ wordWeight gs = n}).symm (Finsupp.single gs a)).val)
      rw [signCoordinates_single]
      simp only [map_smul, Finsupp.domLCongr_single,
        Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single,
        Submodule.coe_smul, forgetPathValidity_single, signedWordReversal_single, locateWords_single, rowReversedBasisEquiv]
      rfl

theorem finiteDualReversal_forget (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ)
    (f : Module.Dual k (internallyNormalizedTerm D i ⊤ r n)) :
    forgetPathValidity (finiteDualReversal D hD i r n f).val =
      locateWords i (signedWordReversal (dualWordCoordinates D hD i r n f)) := by
  change forgetPathValidity (reversedCoordinates i r n (simpleBarDualCoordinates D hD i r n f)) =
    locateWords i (signedWordReversal (scalarWordCoordinates i r n (simpleBarDualCoordinates D hD i r n f)))
  exact reversedCoordinates_forget i r n _

/-- The actual finite-degree bar dual and actual Ginzburg path differential commute. -/
theorem finiteDualReversal_differential (w : Tensor k) (hD : (ofTensor w).Regular)
    (i : Vertex) (r n : ℕ) (f : Module.Dual k (internallyNormalizedTerm (ofTensor w) i ⊤ r n)) :
    (finiteDualReversal (ofTensor w) hD i (r + 1) n
      ((internallyNormalizedDifferential (ofTensor w) i ⊤ r n).dualMap f)).val =
      differential w (finiteDualReversal (ofTensor w) hD i r n f).val := by
  apply forgetPathValidity_injective
  rw [finiteDualReversal_forget, forgetPathValidity_differential,
    finiteDualReversal_forget, locatedDifferential_locateWords,
    dualWordCoordinates_differential, signedWordReversal_differential]
end
end Ginzburg333.Comparison
