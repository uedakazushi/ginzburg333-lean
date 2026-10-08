import Ginzburg333.Bar.Homological

/-! A finite-support realization of tensoring over the vertex algebra. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
noncomputable section
def vertexIdempotent (j : Vertex) : Auxiliary k := embedRow j CyclicData.identityRow
theorem multiply_vertexIdempotent (D : CyclicData k) (i j : Vertex) :
    D.multiply (vertexIdempotent i) (vertexIdempotent j) =
      if i = j then vertexIdempotent i else 0 := by
  classical
  funext l
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp [vertexIdempotent, embedRow, CyclicData.identityRow, CyclicData.multiply, next]
theorem sum_vertexIdempotent : (∑ i, vertexIdempotent (k := k) i) = CyclicData.identityAuxiliary := by
  funext l
  fin_cases l <;>
    simp [vertexIdempotent, embedRow, CyclicData.identityRow, CyclicData.identityAuxiliary,
      Fin.sum_univ_succ]
theorem positiveBasis_right_corner (D : CyclicData k) (g : Generator) :
    D.multiply (positiveBasis g) (vertexIdempotent g.target) = positiveBasis g := by
  classical
  funext j
  cases g with
  | forward i a => fin_cases i <;> fin_cases j <;>
      simp [positiveBasis, vertexIdempotent, embedRow, CyclicData.identityRow,
        CyclicData.multiply, Generator.target, next]
  | reverse i a => fin_cases i <;> fin_cases j <;>
      simp [positiveBasis, vertexIdempotent, embedRow, CyclicData.identityRow,
        CyclicData.multiply, Generator.target, next]
  | loop i => fin_cases i <;> fin_cases j <;>
      simp [positiveBasis, vertexIdempotent, embedRow, CyclicData.identityRow,
        CyclicData.multiply, Generator.target, next]
def cornerProjection {D : CyclicData k} (A : RightAction D M) (j : Vertex) : M →ₗ[k] M :=
  A.action (vertexIdempotent j)
theorem cornerProjection_idempotent {D : CyclicData k} (A : RightAction D M) (j : Vertex) (m : M) :
    cornerProjection A j (cornerProjection A j m) = cornerProjection A j m := by
  unfold cornerProjection
  rw [A.assoc, multiply_vertexIdempotent]
  simp
def composable : List Generator → Prop
  | [] => True
  | [_] => True
  | g :: h :: cs => g.target = h.source ∧ composable (h :: cs)
instance composable_decidable (gs : List Generator) : Decidable (composable gs) := by
  induction gs with
  | nil => exact inferInstanceAs (Decidable True)
  | cons g gs ih =>
      cases gs with
      | nil => exact inferInstanceAs (Decidable True)
      | cons h cs =>
          letI := ih
          exact inferInstanceAs (Decidable (g.target = h.source ∧ composable (h :: cs)))
def initialProjection {D : CyclicData k} (A : RightAction D M) : List Generator → M →ₗ[k] M
  | [] => LinearMap.id
  | g :: _ => cornerProjection A g.source
theorem initialProjection_idempotent {D : CyclicData k} (A : RightAction D M)
    (gs : List Generator) (m : M) :
    initialProjection A gs (initialProjection A gs m) = initialProjection A gs m := by
  cases gs
  · rfl
  · exact cornerProjection_idempotent _ _ _
def normalization {D : CyclicData k} (A : RightAction D M) : Ambient M →ₗ[k] Ambient M :=
  Finsupp.lsum k (fun gs => if composable gs then
    (Finsupp.lsingle gs).comp (initialProjection A gs) else 0)
theorem normalization_single {D : CyclicData k} (A : RightAction D M) (gs : List Generator) (m : M) :
    normalization A (Finsupp.single gs m) =
      if composable gs then Finsupp.single gs (initialProjection A gs m) else 0 := by
  simp only [normalization, Finsupp.lsum_single]
  split_ifs <;> rfl
theorem normalization_apply {D : CyclicData k} (A : RightAction D M) (x : Ambient M) (gs : List Generator) :
    normalization A x gs = if composable gs then initialProjection A gs (x gs) else 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => by_cases hc : composable gs <;> simp [hx, hy, hc]
  | single cs m =>
      rw [normalization_single]
      by_cases hc : composable cs
      all_goals
        by_cases h : gs = cs
        · subst gs; simp [Finsupp.single_apply, hc]
        · simp [Finsupp.single_apply, h, Ne.symm h, hc]
theorem normalization_idempotent {D : CyclicData k} (A : RightAction D M) (x : Ambient M) :
    normalization A (normalization A x) = normalization A x := by
  ext gs
  rw [normalization_apply, normalization_apply]
  split_ifs
  · exact initialProjection_idempotent _ _ _
  · rfl
def balancedAmbient {D : CyclicData k} (A : RightAction D M) : Submodule k (Ambient M) :=
  LinearMap.range (normalization A)
theorem mem_balancedAmbient_iff {D : CyclicData k} (A : RightAction D M) (x : Ambient M) :
    x ∈ balancedAmbient A ↔ normalization A x = x := by
  constructor
  · rintro ⟨y, rfl⟩; exact normalization_idempotent A y
  · intro hx; exact ⟨x, hx⟩
def normalizedTerm {D : CyclicData k} (A : RightAction D M) (r : ℕ) : Submodule k (Ambient M) :=
  balancedAmbient A ⊓ lengthComponent r
theorem normalization_homological {D : CyclicData k} (A : RightAction D M) (r : ℕ)
    (x : Ambient M) (hx : x ∈ lengthComponent (k := k) r) :
    normalization A x ∈ lengthComponent (k := k) r := by
  intro gs hgs
  apply hx
  change gs ∈ (normalization A x).support at hgs
  change gs ∈ x.support
  rw [Finsupp.mem_support_iff] at hgs ⊢
  intro heq
  apply hgs
  rw [normalization_apply, heq, map_zero]
  split_ifs <;> rfl
theorem normalization_mem_normalizedTerm {D : CyclicData k} (A : RightAction D M)
    (r : ℕ) (x : Ambient M) (hx : x ∈ lengthComponent (k := k) r) :
    normalization A x ∈ normalizedTerm A r :=
  ⟨⟨x, rfl⟩, normalization_homological A r x hx⟩
theorem normalization_natural {D : CyclicData k} (A : RightAction D M) (B : RightAction D N)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (A.action a m) = B.action a (f m)) (x : Ambient M) :
    coefficientMap f (normalization A x) = normalization B (coefficientMap f x) := by
  ext gs
  change f (normalization A x gs) = normalization B (coefficientMap f x) gs
  rw [normalization_apply, normalization_apply]
  by_cases hc : composable gs
  · simp only [if_pos hc]
    cases gs with
    | nil => rfl
    | cons g gs => exact hf (vertexIdempotent g.source) (x (g :: gs))
  · simp [hc]
end
end Ginzburg333.Bar
