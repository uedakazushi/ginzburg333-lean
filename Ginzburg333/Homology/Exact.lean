import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exactness by cycles and boundaries

This file isolates the elementary diagram chase needed by the double induction.
It is not an assumed long exact sequence and does not yet instantiate the bar
complex. It works for actual linear maps with explicitly stated hypotheses.

Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333.Homology

section Exact
variable {k A B C : Type*} [Field k]
  [AddCommGroup A] [Module k A]
  [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

/-- Cycles are exactly boundaries. This is equivalent to range f = ker g. -/
def ExactAt (f : A →ₗ[k] B) (g : B →ₗ[k] C) : Prop :=
  ∀ b, g b = 0 ↔ ∃ a, f a = b

theorem exactAt_iff_range_eq_ker (f : A →ₗ[k] B) (g : B →ₗ[k] C) :
    ExactAt f g ↔ LinearMap.range f = LinearMap.ker g := by
  constructor
  · intro h
    ext b
    exact (h b).symm
  · intro h b
    change b ∈ LinearMap.ker g ↔ b ∈ LinearMap.range f
    rw [h]

theorem trivial_middle_of_exact (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : ExactAt f g) [Subsingleton A] [Subsingleton C] :
    ∀ b : B, b = 0 := by
  intro b
  obtain ⟨a, ha⟩ := (h b).mp (Subsingleton.elim _ _)
  rw [← ha, Subsingleton.elim a 0, map_zero]

end Exact

section QuotientChase
variable {k A₀ A₁ A₂ B₀ B₁ B₂ B₃ C₁ C₂ C₃ : Type*} [Field k]
  [AddCommGroup A₀] [Module k A₀]
  [AddCommGroup A₁] [Module k A₁]
  [AddCommGroup A₂] [Module k A₂]
  [AddCommGroup B₀] [Module k B₀]
  [AddCommGroup B₁] [Module k B₁]
  [AddCommGroup B₂] [Module k B₂]
  [AddCommGroup B₃] [Module k B₃]
  [AddCommGroup C₁] [Module k C₁]
  [AddCommGroup C₂] [Module k C₂]
  [AddCommGroup C₃] [Module k C₃]

/-- The fragment of the long exact sequence needed for a quotient:
if H_r(B)=0 and H_(r-1)(A)=0 then H_r(C)=0.

The subscripts 0,1,2,3 stand for consecutive chain degrees. In the intended
application, B₂ is B_r, A₁ is A_(r-1), and C₂ is C_r. -/
theorem quotient_exact_of_exact
    (dA₁ : A₁ →ₗ[k] A₀) (dA₂ : A₂ →ₗ[k] A₁)
    (dB₁ : B₁ →ₗ[k] B₀) (dB₂ : B₂ →ₗ[k] B₁) (dB₃ : B₃ →ₗ[k] B₂)
    (dC₂ : C₂ →ₗ[k] C₁) (dC₃ : C₃ →ₗ[k] C₂)
    (f₀ : A₀ →ₗ[k] B₀) (f₁ : A₁ →ₗ[k] B₁) (f₂ : A₂ →ₗ[k] B₂)
    (q₁ : B₁ →ₗ[k] C₁) (q₂ : B₂ →ₗ[k] C₂) (q₃ : B₃ →ₗ[k] C₃)
    (hA : ExactAt dA₂ dA₁) (hB : ExactAt dB₃ dB₂)
    (hBsq : ∀ b, dB₁ (dB₂ b) = 0)
    (hCsq : ∀ c, dC₂ (dC₃ c) = 0)
    (hf₀ : Function.Injective f₀)
    (hq₂ : Function.Surjective q₂)
    (hrow₁ : ExactAt f₁ q₁)
    (hqf₂ : ∀ a, q₂ (f₂ a) = 0)
    (hfd₁ : ∀ a, f₀ (dA₁ a) = dB₁ (f₁ a))
    (hfd₂ : ∀ a, dB₂ (f₂ a) = f₁ (dA₂ a))
    (hqd₂ : ∀ b, q₁ (dB₂ b) = dC₂ (q₂ b))
    (hqd₃ : ∀ b, q₂ (dB₃ b) = dC₃ (q₃ b)) :
    ExactAt dC₃ dC₂ := by
  intro c
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := hq₂ c
    have hqb : q₁ (dB₂ b) = 0 := by rw [hqd₂, hb, hc]
    obtain ⟨a, ha⟩ := (hrow₁ (dB₂ b)).mp hqb
    have hda : dA₁ a = 0 := by
      apply hf₀
      rw [map_zero, hfd₁, ha, hBsq]
    obtain ⟨a', ha'⟩ := (hA a).mp hda
    have hcycle : dB₂ (b - f₂ a') = 0 := by
      rw [map_sub, hfd₂, ha', ha, sub_self]
    obtain ⟨b', hb'⟩ := (hB (b - f₂ a')).mp hcycle
    refine ⟨q₃ b', ?_⟩
    rw [← hqd₃, hb', map_sub, hqf₂, sub_zero, hb]
  · rintro ⟨c', rfl⟩
    exact hCsq c'

end QuotientChase
end Ginzburg333.Homology
