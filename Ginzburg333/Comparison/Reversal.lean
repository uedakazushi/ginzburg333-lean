import Ginzburg333.Comparison.FiniteDual
import Ginzburg333.Signs

/-! Signed factor reversal on actual finite internal-degree dual terms. -/
namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

abbrev RowPathBasis (i : Vertex) (r n : ℕ) :=
  {p : BasisPath // p.val.1 = i ∧ p.val.2.length = r ∧ internalDegree p = n}

def rowReversedBasisEquiv (i : Vertex) (r n : ℕ) : SimpleRowBasis i r n ≃ RowPathBasis i r n where
  toFun gs := ⟨⟨(i, gs.val.reverse), (reverse_valid_iff i gs.val).mpr gs.property.1⟩,
    ⟨rfl, by simpa using gs.property.2.1, by simpa [internalDegree] using gs.property.2.2⟩⟩
  invFun p := ⟨p.val.val.2.reverse, by
    refine ⟨?_, by simpa using p.property.2.1, ?_⟩
    · apply (reverse_valid_iff i _).mp
      have hi : (i, p.val.val.2) = p.val.val := Prod.ext p.property.1.symm rfl
      simpa only [List.reverse_reverse, hi] using p.val.property
    · simpa [internalDegree] using p.property.2.2⟩
  left_inv := by intro gs; apply Subtype.ext; simp
  right_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.1.symm
    · simp

def rowPathComponent (i : Vertex) (r n : ℕ) : Submodule k (PathSpace k) :=
  Finsupp.supported k k {p | p.val.1 = i ∧ p.val.2.length = r ∧ internalDegree p = n}

def wordSign (gs : List Generator) : k := (-1 : k) ^ Signs.sigma (gs.map Generator.weight)

theorem wordSign_square (gs : List Generator) : wordSign (k := k) gs * wordSign gs = 1 := by
  rw [wordSign, ← mul_pow]
  simp

def signCoordinates (i : Vertex) (r n : ℕ) :
    (SimpleRowBasis i r n →₀ k) →ₗ[k] (SimpleRowBasis i r n →₀ k) :=
  Finsupp.linearCombination k (fun gs => wordSign (k := k) gs.val • Finsupp.single gs (1 : k))

@[simp] theorem signCoordinates_single (i : Vertex) (r n : ℕ) (gs : SimpleRowBasis i r n) (a : k) :
    signCoordinates i r n (Finsupp.single gs a) = wordSign (k := k) gs.val • Finsupp.single gs a := by
  simp [signCoordinates, smul_smul, Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem signCoordinates_square (i : Vertex) (r n : ℕ) (x : SimpleRowBasis i r n →₀ k) :
    signCoordinates i r n (signCoordinates i r n x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp [smul_smul, ← mul_assoc, wordSign_square]

def signCoordinatesEquiv (i : Vertex) (r n : ℕ) :
    (SimpleRowBasis i r n →₀ k) ≃ₗ[k] (SimpleRowBasis i r n →₀ k) where
  toLinearMap := signCoordinates i r n
  invFun := signCoordinates i r n
  left_inv := signCoordinates_square i r n
  right_inv := signCoordinates_square i r n

/-- A vector-space equivalence. Compatibility with the differentials is a separate obligation. -/
def finiteDualReversal (D : CyclicData k) (hD : D.Regular) (i : Vertex) (r n : ℕ) :
    Module.Dual k (internallyNormalizedTerm D i ⊤ r n) ≃ₗ[k] rowPathComponent (k := k) i r n :=
  (simpleBarDualCoordinates D hD i r n).trans
    ((signCoordinatesEquiv i r n).trans
      ((Finsupp.domLCongr (rowReversedBasisEquiv i r n)).trans
        (Finsupp.supportedEquivFinsupp {p : BasisPath | p.val.1 = i ∧ p.val.2.length = r ∧ internalDegree p = n}).symm))

theorem rowPathComponent_bigraded (i : Vertex) (r n : ℕ) (x : rowPathComponent (k := k) i r n) :
    x.val ∈ bigradedComponent (k := k) n ((r : ℤ) - (n : ℤ)) := by
  intro p hp
  obtain ⟨hi, hl, hw⟩ := x.property hp
  refine ⟨hw, ?_⟩
  rw [cohomologicalDegree_eq_length_sub_weight, hl, hw]
end
end Ginzburg333.Comparison
