import Ginzburg333.Ginzburg.SquareZero
import Ginzburg333.Ginzburg.FiniteDegree
import Ginzburg333.Homology.Exact

/-! Actual finite-dimensional bigraded components and finite-support assembly. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section
def bigradedComponent (n : ℕ) (q : ℤ) : Submodule k (PathSpace k) :=
  Finsupp.supported k k {p | internalDegree p = n ∧ cohomologicalDegree p = q}
theorem mem_bigradedComponent (n : ℕ) (q : ℤ) (x : PathSpace k) :
    x ∈ bigradedComponent (k := k) n q ↔ InternallyHomogeneous n x ∧ Homogeneous q x := by
  constructor
  · intro h; exact ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩
  · rintro ⟨hi, hc⟩ p hp; exact ⟨hi p hp, hc p hp⟩
instance finiteDimensional_bigradedComponent (n : ℕ) (q : ℤ) :
    FiniteDimensional k (bigradedComponent (k := k) n q) := by
  let f : bigradedComponent (k := k) n q →ₗ[k] internalComponent (k := k) n :=
    Submodule.inclusion (by intro x hx; exact fun p hp => (hx hp).1)
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective _)
def componentDifferential (w : Tensor k) (n : ℕ) (q r : ℤ) (h : q + 1 = r) :
    bigradedComponent (k := k) n q →ₗ[k] bigradedComponent (k := k) n r where
  toFun x := ⟨differential w x.val, by
    obtain ⟨hi, hc⟩ := (mem_bigradedComponent n q x.val).mp x.property
    apply (mem_bigradedComponent n r _).mpr
    exact ⟨differential_internal w n x.val hi, h ▸ differential_cohomological w q x.val hc⟩⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _
@[simp] theorem componentDifferential_val (w : Tensor k) (n : ℕ) (q r : ℤ) (h : q + 1 = r)
    (x : bigradedComponent (k := k) n q) :
    (componentDifferential w n q r h x).val = differential w x.val := rfl
theorem componentDifferential_square (w : Tensor k) (n : ℕ) (q r s : ℤ)
    (h : q + 1 = r) (h' : r + 1 = s) (x : bigradedComponent (k := k) n q) :
    componentDifferential w n r s h' (componentDifferential w n q r h x) = 0 := by
  apply Subtype.ext
  exact differential_square w x.val
def internalProjection (n : ℕ) : PathSpace k →ₗ[k] PathSpace k where
  toFun := Finsupp.filter (fun p => internalDegree p = n)
  map_add' := by intro x y; exact Finsupp.filter_add
  map_smul' := by
    intro a x
    ext p
    by_cases hp : internalDegree p = n <;> simp [Finsupp.filter_apply, hp]
@[simp] theorem internalProjection_apply (n : ℕ) (x : PathSpace k) (p : BasisPath) :
    internalProjection n x p = if internalDegree p = n then x p else 0 := rfl
theorem internalProjection_internal (n : ℕ) (x : PathSpace k) :
    InternallyHomogeneous n (internalProjection n x) := by
  intro p hp
  change p ∈ x.support.filter (fun p => internalDegree p = n) at hp
  exact (Finset.mem_filter.mp hp).2
theorem internalProjection_eq_self (n : ℕ) (x : PathSpace k) (hx : InternallyHomogeneous n x) :
    internalProjection n x = x := by
  apply (Finsupp.filter_eq_self_iff (fun p => internalDegree p = n) x).mpr
  intro p hp
  exact hx p (Finsupp.mem_support_iff.mpr hp)
theorem internalProjection_eq_zero (n m : ℕ) (hnm : n ≠ m) (x : PathSpace k)
    (hx : InternallyHomogeneous m x) : internalProjection n x = 0 := by
  classical
  ext p
  by_cases hp : p ∈ x.support
  · have hm := hx p hp
    simp [internalProjection_apply, hm, Ne.symm hnm]
  · simp [internalProjection_apply, Finsupp.not_mem_support_iff.mp hp]
theorem internalProjection_cohomological (n : ℕ) (q : ℤ) (x : PathSpace k) (hx : Homogeneous q x) :
    Homogeneous q (internalProjection n x) := by
  intro p hp
  apply hx p
  change p ∈ x.support.filter (fun p => internalDegree p = n) at hp
  exact (Finset.mem_filter.mp hp).1
theorem internalProjection_differential (w : Tensor k) (n : ℕ) (x : PathSpace k) :
    internalProjection n (differential w x) = differential w (internalProjection n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a =>
      by_cases hp : internalDegree p = n
      · have hf : internalProjection n (Finsupp.single p a) = Finsupp.single p a := by
          exact Finsupp.filter_single_of_pos (fun p => internalDegree p = n) hp
        rw [hf]
        apply internalProjection_eq_self
        apply differential_internal
        intro t ht
        have he := (Finsupp.mem_support_single _ _ _).mp ht
        simpa [he.1] using hp
      · have hf : internalProjection n (Finsupp.single p a) = 0 := by
          exact Finsupp.filter_single_of_neg (fun p => internalDegree p = n) hp
        rw [hf, map_zero, differential, Finsupp.linearCombination_single, map_smul]
        rw [internalProjection_eq_zero n (internalDegree p) (Ne.symm hp) _ (basisDifferential_internal w p), smul_zero]
theorem sum_internalProjection (x : PathSpace k) :
    (∑ n ∈ x.support.image internalDegree, internalProjection n x) = x := by
  classical
  ext p
  by_cases hp : p ∈ x.support
  · have hn : internalDegree p ∈ x.support.image internalDegree := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simp [internalProjection_apply, hn]
  · simp [internalProjection_apply, Finsupp.not_mem_support_iff.mp hp]
theorem ginzburgRegular_of_internal_primitives (w : Tensor k)
    (h : ∀ (n : ℕ) (q : ℤ), q < 0 → ∀ x : PathSpace k,
      InternallyHomogeneous n x → Homogeneous q x → differential w x = 0 →
        ∃ y : PathSpace k, InternallyHomogeneous n y ∧ Homogeneous (q - 1) y ∧ differential w y = x) :
    GinzburgRegular w := by
  classical
  intro q hq x hx hdx
  have hp (n : ℕ) : ∃ y : PathSpace k,
      InternallyHomogeneous n y ∧ Homogeneous (q - 1) y ∧
        differential w y = internalProjection n x := by
    apply h n q hq _ (internalProjection_internal n x) (internalProjection_cohomological n q x hx)
    rw [← internalProjection_differential, hdx, map_zero]
  choose y hy using hp
  refine ⟨∑ n ∈ x.support.image internalDegree, y n, ?_, ?_⟩
  · change (∑ n ∈ x.support.image internalDegree, y n) ∈ Finsupp.supported k k {p | cohomologicalDegree p = q - 1}
    apply Submodule.sum_mem
    intro n hn
    exact (hy n).2.1
  · rw [map_sum]
    simp only [(hy _).2.2]
    exact sum_internalProjection x
end
end Ginzburg333.Ginzburg
