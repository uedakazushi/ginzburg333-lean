import Ginzburg333.Homology.Exact
import Mathlib.LinearAlgebra.Finsupp.Defs

namespace Ginzburg333.Homology
variable {k I A B C : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]
noncomputable section
theorem finsupp_map_injective (f : A →ₗ[k] B) (hf : Function.Injective f) :
    Function.Injective (Finsupp.mapRange.linearMap f : (I →₀ A) →ₗ[k] (I →₀ B)) :=
  Finsupp.mapRange_injective f f.map_zero hf
theorem finsupp_map_surjective (f : A →ₗ[k] B) (hf : Function.Surjective f) :
    Function.Surjective (Finsupp.mapRange.linearMap f : (I →₀ A) →ₗ[k] (I →₀ B)) :=
  Finsupp.mapRange_surjective f f.map_zero hf
theorem exactAt_finsupp (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : ExactAt f g) :
    ExactAt (Finsupp.mapRange.linearMap f : (I →₀ A) →ₗ[k] (I →₀ B))
      (Finsupp.mapRange.linearMap g) := by
  classical
  intro x
  constructor
  · intro hx
    have hx' : ∀ i, g (x i) = 0 := fun i => congrArg (fun x : I →₀ C => x i) hx
    choose a ha using fun i => (h (x i)).mp (hx' i)
    refine ⟨∑ i ∈ x.support, Finsupp.single i (a i), ?_⟩
    rw [map_sum]
    simpa [Finsupp.mapRange.linearMap, ha, Finsupp.sum] using x.sum_single
  · rintro ⟨y, rfl⟩
    ext i
    exact (h (f (y i))).mpr ⟨y i, rfl⟩
theorem short_exact_finsupp (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : Function.Injective f ∧ ExactAt f g ∧ Function.Surjective g) :
    Function.Injective (Finsupp.mapRange.linearMap f : (I →₀ A) →ₗ[k] (I →₀ B)) ∧
      ExactAt (Finsupp.mapRange.linearMap f : (I →₀ A) →ₗ[k] (I →₀ B))
        (Finsupp.mapRange.linearMap g) ∧
      Function.Surjective (Finsupp.mapRange.linearMap g : (I →₀ B) →ₗ[k] (I →₀ C)) :=
  ⟨finsupp_map_injective f h.1, exactAt_finsupp f g h.2.1, finsupp_map_surjective g h.2.2⟩
end
end Ginzburg333.Homology
