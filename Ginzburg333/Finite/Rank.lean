import Ginzburg333.Finite.Coordinates

/-!
# The rank lemmas used in the Koszul filtration

The claims below concern the actual coordinate contraction maps; no geometric
avatar, Koszulness or cohomological vanishing is an input.
Status: compiled and kernel-checked with Lean 4.19.0.
-/

namespace Ginzburg333
open Module
variable {k : Type*} [Field k]

namespace CyclicData

/-- Linear span of all products with first factor in `U`. -/
def productSpan (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k)) :
    Submodule k (Vec k) :=
  ⨆ a : U, LinearMap.range (D.mul i (a : Vec k))

theorem mul_mem_productSpan (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) {a : Vec k} (ha : a ∈ U) (b : Vec k) :
    D.mul i a b ∈ D.productSpan i U := by
  exact (le_iSup (fun x : U => LinearMap.range (D.mul i (x : Vec k)))
    ⟨a, ha⟩) ⟨b, rfl⟩

/-- Lemma A of the direct proof. -/
theorem productSpan_eq_top_of_two_le (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (U : Submodule k (Vec k)) (hU : 2 ≤ finrank k U) :
    D.productSpan i U = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨f, hf, hPf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hproper) (by infer_instance)
  let z : Vec k := vectorOfFunctional f
  have hz : z ≠ 0 := vectorOfFunctional_ne_zero hf
  have hvanish (a : Vec k) (ha : a ∈ U) (b : Vec k) :
      dot z (D.mul i a b) = 0 := by
    rw [dot_vectorOfFunctional]
    have hm : f (D.mul i a b) ∈ (D.productSpan i U).map f :=
      ⟨D.mul i a b, D.mul_mem_productSpan i U ha b, rfl⟩
    simpa [hPf] using hm
  have hker : U ≤ LinearMap.ker (D.mul (next (next i)) z) := by
    intro a ha
    change D.mul (next (next i)) z a = 0
    apply eq_zero_of_dot_right
    intro b
    rw [D.cyclic, next_three]
    exact hvanish a ha b
  have hk : 2 ≤ finrank k (LinearMap.ker (D.mul (next (next i)) z)) := by
    exact hU.trans (Submodule.finrank_mono hker)
  have hr := hD (next (next i)) z hz
  have hd := LinearMap.finrank_range_add_finrank_ker (D.mul (next (next i)) z)
  rw [finrank_vec] at hd
  omega

/-- The plane version used in the source note. -/
theorem productSpan_eq_top (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) (U : Submodule k (Vec k)) (hU : finrank k U = 2) :
    D.productSpan i U = ⊤ :=
  D.productSpan_eq_top_of_two_le hD i U (by omega)

/-- The inclusion which drives the adjacent-rank and annihilator computations. -/
theorem adjacent_range_le_dot_ker (D : CyclicData k)
    (i : Vertex) (a b : Vec k) (hab : D.mul i a b = 0) :
    LinearMap.range (D.mul (next i) b) ≤ LinearMap.ker (dotMap a) := by
  rintro x ⟨c, rfl⟩
  change dot a (D.mul (next i) b c) = 0
  rw [← D.cyclic, hab, dot_zero_left]

/-- The adjacent nonzero kernel vector also has contraction rank two. -/
theorem adjacent_rank_two (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) {a b : Vec k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : D.mul i a b = 0) :
    finrank k (LinearMap.range (D.mul (next i) b)) = 2 := by
  have hle := Submodule.finrank_mono (D.adjacent_range_le_dot_ker i a b hab)
  rw [finrank_dot_ker ha] at hle
  exact Nat.le_antisymm hle (hD (next i) b hb)

/-- The degree-two piece of the right annihilator is the adjacent image. -/
theorem adjacent_range_eq_dot_ker (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) {a b : Vec k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : D.mul i a b = 0) :
    LinearMap.range (D.mul (next i) b) = LinearMap.ker (dotMap a) := by
  apply Submodule.eq_of_le_of_finrank_eq (D.adjacent_range_le_dot_ker i a b hab)
  rw [D.adjacent_rank_two hD i ha hb hab, finrank_dot_ker ha]

theorem finrank_kernel_of_rank_two (D : CyclicData k) (i : Vertex) (a : Vec k)
    (hr : finrank k (LinearMap.range (D.mul i a)) = 2) :
    finrank k (LinearMap.ker (D.mul i a)) = 1 := by
  have hd := LinearMap.finrank_range_add_finrank_ker (D.mul i a)
  rw [hr, finrank_vec] at hd
  omega

/-- A useful form of the one-dimensional-kernel statement, avoiding a basis choice. -/
theorem kernel_eq_span (D : CyclicData k) (i : Vertex) {a b : Vec k}
    (hr : finrank k (LinearMap.range (D.mul i a)) = 2)
    (hb : b ≠ 0) (hab : D.mul i a b = 0) :
    LinearMap.ker (D.mul i a) = Submodule.span k {b} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hab
  · rw [finrank_span_singleton hb, D.finrank_kernel_of_rank_two i a hr]

/-- Noninjectivity and the lower rank bound force rank exactly two. -/
theorem rank_two_of_not_injective (D : CyclicData k) (hD : D.Regular)
    (i : Vertex) {a : Vec k} (ha : a ≠ 0)
    (hinj : ¬ Function.Injective (D.mul i a)) :
    finrank k (LinearMap.range (D.mul i a)) = 2 := by
  have hk : LinearMap.ker (D.mul i a) ≠ ⊥ := by
    intro hbot
    exact hinj (LinearMap.ker_eq_bot.mp hbot)
  have hkpos : 0 < finrank k (LinearMap.ker (D.mul i a)) := by
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).mp hk
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    intro hzero
    exact hb0 (congrArg Subtype.val hzero)
  have hr := hD i a ha
  have hd := LinearMap.finrank_range_add_finrank_ker (D.mul i a)
  rw [finrank_vec] at hd
  omega

end CyclicData
end Ginzburg333
