import Ginzburg333.Comparison.WordReversal

namespace Ginzburg333.Comparison
open Ginzburg333.Ginzburg Ginzburg333.Bar
variable {k : Type*} [Field k]
noncomputable section

theorem prependWords_nil_apply (g : Generator) (x : WordSpace k) : prependWords [g] x [] = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single gs a => simp [Finsupp.single_apply]

theorem prependWords_cons_apply (g h : Generator) (gs : List Generator) (x : WordSpace k) :
    prependWords [g] x (h :: gs) = if g = h then x gs else 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, Finsupp.add_apply, hx, hy]
      by_cases he : g = h <;> simp [he]
  | single cs a => by_cases he : g = h <;> simp [Finsupp.single_apply, he, eq_comm]

theorem append_pairVector_apply (f : Generator → Generator → k) (gs hs : List Generator)
    (h t : Generator) :
    appendWords gs (pairVector f) (h :: t :: hs) = if gs = hs then f h t else 0 := by
  classical
  by_cases he : gs = hs <;>
    simp [pairVector, map_sum, map_smul, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.single_apply, ite_and, he, eq_comm]

theorem headVector_apply (f : Generator → k) (gs hs : List Generator) (g : Generator) :
    (∑ t, f t • Finsupp.single (t :: gs) (1 : k)) (g :: hs) =
      if gs = hs then f g else 0 := by
  classical
  by_cases he : gs = hs <;>
    simp [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, ite_and, he, eq_comm]

theorem cobarBasis_nil_apply (D : CyclicData k) (gs : List Generator) : cobarBasis D gs [] = 0 := by
  by_contra hn
  have h := cobarBasis_length D gs (Finsupp.mem_support_iff.mpr hn)
  simp at h

theorem cobarBasis_one_apply (D : CyclicData k) (gs : List Generator) (g : Generator) :
    cobarBasis D gs [g] = 0 := by
  cases gs with
  | nil => rfl
  | cons h gs =>
      by_contra hn
      have h := cobarBasis_length D (h :: gs) (Finsupp.mem_support_iff.mpr hn)
      simp at h

/-- The actual coefficient matrix transpose, for words of every length. -/
theorem cobarBasis_transpose (D : CyclicData k) (gs hs : List Generator) :
    cobarBasis D gs hs = innerBasisDifferential D hs gs := by
  classical
  induction hs generalizing gs with
  | nil => simp [cobarBasis_nil_apply, innerBasisDifferential]
  | cons h hs ih =>
      cases hs with
      | nil => simp [cobarBasis_one_apply, innerBasisDifferential]
      | cons t hs =>
          cases gs with
          | nil =>
              simp [cobarBasis, innerBasisDifferential, Finset.sum_apply,
                Finsupp.smul_apply, Finsupp.single_apply, prependWords_nil_apply]
          | cons g gs =>
              simp only [cobarBasis, innerBasisDifferential, Finsupp.sub_apply]
              rw [show splitBasis D g = pairVector (fun h t => positiveMultiplication D h t g) by rfl,
                append_pairVector_apply, prependWords_cons_apply, prependWords_cons_apply,
                headVector_apply, ih]
              simp only [eq_comm]
end
end Ginzburg333.Comparison
