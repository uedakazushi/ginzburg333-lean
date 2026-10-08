import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum

/-!
# All-length sign identity for the bar/Ginzburg comparison

The recursive definition of sigma is exactly
  Σ_j (j-1) d_j + choose(length,2) + #{j : d_j=3}.
The comparison theorem is for arbitrary prefix and suffix lists; it is not
an enumeration up to a fixed internal degree.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333.Signs

def three (d : ℕ) : ℕ := if d = 3 then 1 else 0

def weighted : List ℕ → ℕ
  | [] => 0
  | _ :: ds => weighted ds + ds.sum

def countThree : List ℕ → ℕ
  | [] => 0
  | d :: ds => countThree ds + three d

def sigma : List ℕ → ℕ
  | [] => 0
  | d :: ds => sigma ds + ds.sum + ds.length + three d

/-- Identification with the exponent in equation (6.4) of the source note. -/
theorem sigma_formula (ds : List ℕ) :
    sigma ds = weighted ds + ds.length.choose 2 + countThree ds := by
  induction ds with
  | nil => simp [sigma, weighted, countThree]
  | cons d ds ih =>
      simp only [sigma, weighted, countThree, List.length_cons, ih,
        Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
      omega

/-- The only nonzero splittings in the positive-degree multiplication table. -/
inductive Cut
  | oneOne
  | oneTwo
  | twoOne
  deriving DecidableEq

def Cut.left : Cut → ℕ
  | .oneOne => 1
  | .oneTwo => 1
  | .twoOne => 2

def Cut.right : Cut → ℕ
  | .oneOne => 1
  | .oneTwo => 2
  | .twoOne => 1

/-- An equality in ℕ, stronger than the parity relation needed below. -/
theorem split_balance (pre post : List ℕ) (c : Cut) :
    sigma (pre ++ [c.left, c.right] ++ post) + three (c.left + c.right) =
    sigma (pre ++ [c.left + c.right] ++ post) + c.right + post.sum +
      (pre.length + 1 + post.length) := by
  induction pre with
  | nil =>
      cases c <;>
        simp [Cut.left, Cut.right, sigma, three] <;> omega
  | cons d pre ih =>
      simp only [List.cons_append, sigma, List.sum_append, List.length_append,
        List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at *
      omega

/-- Exponent from the graded Leibniz rule after reversing the factors. -/
def ginExponent (pre post : List ℕ) (c : Cut) : ℤ :=
  (sigma (pre ++ [c.left + c.right] ++ post) : ℤ) +
    (post.length : ℤ) - (post.sum : ℤ) + (c.left : ℤ) + 1

/-- Exponent from the bar sign and the sign of the split word. -/
def barExponent (pre post : List ℕ) (c : Cut) : ℤ :=
  (sigma (pre ++ [c.left, c.right] ++ post) : ℤ) + (pre.length : ℤ)

/-- The sign comparison for words of every length. -/
theorem comparison_parity (pre post : List ℕ) (c : Cut) :
    ginExponent pre post c % 2 = barExponent pre post c % 2 := by
  have hb := split_balance pre post c
  have hbi :
      (sigma (pre ++ [c.left, c.right] ++ post) : ℤ) +
        (three (c.left + c.right) : ℤ) =
      (sigma (pre ++ [c.left + c.right] ++ post) : ℤ) +
        (c.right : ℤ) + (post.sum : ℤ) +
        ((pre.length : ℤ) + 1 + (post.length : ℤ)) := by
    exact_mod_cast hb
  unfold ginExponent barExponent
  cases c <;>
    norm_num [Cut.left, Cut.right, three] at hbi ⊢ <;> omega

theorem split_preserves_internal_degree (pre post : List ℕ) (c : Cut) :
    (pre ++ [c.left, c.right] ++ post).sum =
      (pre ++ [c.left + c.right] ++ post).sum := by
  simp only [List.sum_append, List.sum_cons, List.sum_nil]
  omega

theorem split_increases_length (pre post : List ℕ) (c : Cut) :
    (pre ++ [c.left, c.right] ++ post).length =
      (pre ++ [c.left + c.right] ++ post).length + 1 := by
  simp <;> omega

theorem length_le_sum (ds : List ℕ) (h : ∀ d ∈ ds, 1 ≤ d) :
    ds.length ≤ ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd := h d (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [List.length_cons, List.sum_cons]
      omega

end Ginzburg333.Signs
