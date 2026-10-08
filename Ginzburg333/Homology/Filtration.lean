import Ginzburg333.Homology.Exact

/-!
# The well-founded induction behind a Koszul filtration

The predicate P below will be exactness of a fixed internal-degree bar
complex. The theorem proves the induction, but does NOT assume or assert
that the required reductions have been constructed for that bar complex.
The still-missing instantiation is tracked in GAPS.md.
The free case is restricted to positive homological degree: its degree-zero
homology at internal degree zero must NOT be assumed to vanish.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333.Homology

/-- Double induction on homological degree and the number of linear generators.
The step can return to an arbitrary index c because its homological degree
has already decreased. No finite enumeration of the family is needed. -/
theorem filtration_induction
    {I : Type*} (size : I → ℕ) (P : I → ℕ → ℕ → Prop)
    (hzero : ∀ a n, 0 < n → P a 0 n)
    (hfree : ∀ a r n, size a = 0 → P a (r + 1) n)
    (hstep : ∀ a r n, size a ≠ 0 →
      ∃ b c, size b < size a ∧
        (P b (r + 1) (n + 1) → P c r n → P a (r + 1) (n + 1))) :
    ∀ r a n, r < n → P a r n := by
  intro r
  induction r with
  | zero =>
      intro a n hn
      exact hzero a n hn
  | succ r ihr =>
      have aux : ∀ d a, size a = d → ∀ n, r + 1 < n → P a (r + 1) n := by
        intro d
        induction d using Nat.strong_induction_on with
        | h d ihd =>
            intro a had n hn
            by_cases hd : size a = 0
            · exact hfree a r n hd
            · cases n with
              | zero => omega
              | succ n =>
                  obtain ⟨b, c, hsize, hred⟩ := hstep a r n hd
                  apply hred
                  · exact ihd (size b) (by omega) b rfl (n + 1) hn
                  · exact ihr c n (by omega)
      intro a n hn
      exact aux (size a) a rfl n hn

/-- Adding the automatic below-diagonal vanishing gives diagonal concentration. -/
theorem diagonal_of_filtration
    {I : Type*} (size : I → ℕ) (P : I → ℕ → ℕ → Prop)
    (hzero : ∀ a n, 0 < n → P a 0 n)
    (hfree : ∀ a r n, size a = 0 → P a (r + 1) n)
    (hstep : ∀ a r n, size a ≠ 0 →
      ∃ b c, size b < size a ∧
        (P b (r + 1) (n + 1) → P c r n → P a (r + 1) (n + 1)))
    (hbelow : ∀ a r n, n < r → P a r n) :
    ∀ a r n, n ≠ r → P a r n := by
  intro a r n hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hbelow a r n hlt
  · exact filtration_induction size P hzero hfree hstep r a n hgt

/-- Arithmetic at the last step of the Ginzburg/bar comparison.
The relation q = r - n is an integer relation, not truncated subtraction. -/
theorem negative_degree_is_off_diagonal {r n : ℕ} {q : ℤ}
    (hq : q < 0) (hdegree : q = (r : ℤ) - (n : ℤ)) : r < n := by
  omega

end Ginzburg333.Homology
