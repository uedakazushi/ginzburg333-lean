import Ginzburg333.Bar.Zero
import Ginzburg333.Homology.Filtration

/-! Filtration induction applied to the actual internally graded normalized bar. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

def chainDifferential (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (r n : ℕ) : internallyNormalizedTerm D i U r n →ₗ[k] internallyNormalizedTerm D i U (r - 1) n :=
  match r with
  | 0 => 0
  | r + 1 => internallyNormalizedDifferential D i U r n

@[simp] theorem chainDifferential_succ (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) :
    chainDifferential D i U (r + 1) n = internallyNormalizedDifferential D i U r n := rfl

@[simp] theorem chainDifferential_zero (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) : chainDifferential D i U 0 n = 0 := rfl

def BarExact (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) (r n : ℕ) : Prop :=
  Homology.ExactAt (k := k)
    (A := internallyNormalizedTerm D i U (r + 1) n)
    (B := internallyNormalizedTerm D i U r n)
    (C := internallyNormalizedTerm D i U (r - 1) n)
    (internallyNormalizedDifferential D i U r n) (chainDifferential D i U r n)

theorem chainDifferential_square (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) (x : internallyNormalizedTerm D i U (r + 1) n) :
    chainDifferential D i U r n (internallyNormalizedDifferential D i U r n x) = 0 := by
  cases r with
  | zero => rfl
  | succ r => exact internallyNormalizedDifferential_square D i U r n x

theorem barExact_zero (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (n : ℕ) (hn : 0 < n) : BarExact D i U 0 n := by
  intro x
  constructor
  · intro hx; exact internallyNormalized_zero_surjective D i U n hn x
  · intro hx; rfl

theorem barExact_free (D : CyclicData k) (i : Vertex) (r n : ℕ) : BarExact D i ⊥ (r + 1) n :=
  internally_normalized_free_exact D i r n

theorem barExact_below (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (r n : ℕ) (hn : n < r) : BarExact D i U r n := by
  have hz : ∀ x : internallyNormalizedTerm D i U r n, x = 0 := by
    intro x
    apply Subtype.ext
    exact (internallyNormalizedTerm_eq_bot D i U r n hn ▸ x.property : x.val ∈ (⊥ : Submodule k _))
  intro x
  rw [hz x, map_zero]
  constructor
  · intro hx; exact ⟨0, map_zero _⟩
  · intro hx; rfl

theorem internalInclusion_chainDifferential {D : CyclicData k} {i : Vertex}
    {U : Submodule k (Vec k)} (s : D.FiltrationStep i U) (r n : ℕ)
    (x : internallyNormalizedTerm D (next i) s.colon r n) :
    internalInclusion s (r - 1) n (chainDifferential D (next i) s.colon r n x) =
      chainDifferential D i s.smaller r (n + 1) (internalInclusion s r n x) := by
  cases r with
  | zero => simp
  | succ r => exact internalInclusion_differential s r n x

set_option maxHeartbeats 2000000 in
theorem barExact_filtration_step {D : CyclicData k} {i : Vertex} {U : Submodule k (Vec k)}
    (s : D.FiltrationStep i U) (r n : ℕ)
    (hB : BarExact D i s.smaller (r + 1) (n + 1))
    (hA : BarExact D (next i) s.colon r n) : BarExact D i U (r + 1) (n + 1) := by
  exact Homology.quotient_exact_of_exact (k := k)
    (A₀ := internallyNormalizedTerm D (next i) s.colon (r - 1) n)
    (A₁ := internallyNormalizedTerm D (next i) s.colon r n)
    (A₂ := internallyNormalizedTerm D (next i) s.colon (r + 1) n)
    (B₀ := internallyNormalizedTerm D i s.smaller (r - 1) (n + 1))
    (B₁ := internallyNormalizedTerm D i s.smaller r (n + 1))
    (B₂ := internallyNormalizedTerm D i s.smaller (r + 1) (n + 1))
    (B₃ := internallyNormalizedTerm D i s.smaller (r + 1 + 1) (n + 1))
    (C₁ := internallyNormalizedTerm D i U r (n + 1))
    (C₂ := internallyNormalizedTerm D i U (r + 1) (n + 1))
    (C₃ := internallyNormalizedTerm D i U (r + 1 + 1) (n + 1))
    (chainDifferential D (next i) s.colon r n) (internallyNormalizedDifferential D (next i) s.colon r n)
    (chainDifferential D i s.smaller r (n + 1))
    (internallyNormalizedDifferential D i s.smaller r (n + 1))
    (internallyNormalizedDifferential D i s.smaller (r + 1) (n + 1))
    (internallyNormalizedDifferential D i U r (n + 1))
    (internallyNormalizedDifferential D i U (r + 1) (n + 1))
    (internalInclusion s (r - 1) n) (internalInclusion s r n) (internalInclusion s (r + 1) n)
    (internalQuotient s r (n + 1)) (internalQuotient s (r + 1) (n + 1))
    (internalQuotient s (r + 1 + 1) (n + 1))
    hA hB (chainDifferential_square D i s.smaller r (n + 1))
    (internallyNormalizedDifferential_square D i U r (n + 1))
    (internalInclusion_injective s (r - 1) n) (internalQuotient_surjective s (r + 1) (n + 1))
    (internalInclusion_exact s r n)
    (fun x => (internalInclusion_exact s (r + 1) n (internalInclusion s (r + 1) n x)).mpr ⟨x, rfl⟩)
    (internalInclusion_chainDifferential s r n)
    (fun x => (internalInclusion_differential s r n x).symm)
    (internalQuotient_differential s r (n + 1)) (internalQuotient_differential s (r + 1) (n + 1))

/-- Actual off-diagonal exactness, with no acyclicity or comparison assumptions. -/
theorem normalized_bar_off_diagonal [IsAlgClosed k] (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (U : Submodule k (Vec k)) (hU : D.Allowed i U)
    (r n : ℕ) (hne : n ≠ r) : BarExact D i U r n := by
  let I := {a : Vertex × Submodule k (Vec k) // D.Allowed a.1 a.2}
  let size : I → ℕ := fun a => Module.finrank k a.val.2
  let P : I → ℕ → ℕ → Prop := fun a => BarExact D a.val.1 a.val.2
  have hzero : ∀ a n, 0 < n → P a 0 n := fun a n hn => barExact_zero D _ _ n hn
  have hfree : ∀ a r n, size a = 0 → P a (r + 1) n := by
    intro a r n ha
    have he : a.val.2 = ⊥ := Submodule.finrank_eq_zero.mp ha
    change BarExact D a.val.1 a.val.2 (r + 1) n
    rw [he]
    exact barExact_free D _ r n
  have hstep : ∀ a r n, size a ≠ 0 → ∃ b c : I, size b < size a ∧
      (P b (r + 1) (n + 1) → P c r n → P a (r + 1) (n + 1)) := by
    intro a r n ha
    have hbot : a.val.2 ≠ ⊥ := by intro h; exact ha (by simp [size, h])
    obtain ⟨s⟩ := D.exists_filtrationStep hD a.val.1 a.val.2 a.property hbot
    refine ⟨⟨(a.val.1, s.smaller), s.smaller_allowed⟩,
      ⟨(next a.val.1, s.colon), s.colon_allowed⟩, ?_, ?_⟩
    · change Module.finrank k s.smaller < Module.finrank k a.val.2
      have h := s.size_drop
      omega
    · exact barExact_filtration_step s r n
  have hbelow : ∀ a r n, n < r → P a r n := fun a r n hn => barExact_below D _ _ r n hn
  exact Homology.diagonal_of_filtration size P hzero hfree hstep hbelow
    (⟨(i, U), hU⟩ : I) r n hne
end
end Ginzburg333.Bar
