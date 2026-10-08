import Ginzburg333.Bar.NormalizedExact

/-! Internal grading of the actual normalized quotient-row bar complex. -/
namespace Ginzburg333.Bar
open Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

/-- Coefficient degree plus the sum of the positive-factor weights. -/
def internalComponent (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (n : ℕ) : Submodule k (Ambient (D.QuotientRow i U)) where
  carrier := {x | ∀ gs d, d.val + wordWeight gs ≠ n → D.quotientProjection i U d (x gs) = 0}
  zero_mem' := by intro gs d hn; exact map_zero (D.quotientProjection i U d)
  add_mem' := by intro x y hx hy gs d hn; simp [hx gs d hn, hy gs d hn]
  smul_mem' := by intro a x hx gs d hn; simp [hx gs d hn]

def coefficientProjection (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (n : ℕ) (gs : List Generator) : D.QuotientRow i U →ₗ[k] D.QuotientRow i U :=
  ∑ d : Fin 4, if d.val + wordWeight gs = n then D.quotientProjection i U d else 0

def internalProjection (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (n : ℕ) : Ambient (D.QuotientRow i U) →ₗ[k] Ambient (D.QuotientRow i U) :=
  Finsupp.lsum k (fun gs => (Finsupp.lsingle gs).comp (coefficientProjection D i U n gs))

@[simp] theorem internalProjection_single (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (gs : List Generator) (m : D.QuotientRow i U) :
    internalProjection D i U n (Finsupp.single gs m) =
      Finsupp.single gs (coefficientProjection D i U n gs m) := by
  simp [internalProjection]

theorem internalProjection_apply (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U)) (gs : List Generator) :
    internalProjection D i U n x gs = coefficientProjection D i U n gs (x gs) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single cs m =>
      by_cases h : cs = gs
      · subst cs; simp
      · simp [Finsupp.single_apply, h, Ne.symm h]

theorem quotientProjection_coefficientProjection (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (gs : List Generator) (e : Fin 4) (m : D.QuotientRow i U) :
    D.quotientProjection i U e (coefficientProjection D i U n gs m) =
      if e.val + wordWeight gs = n then D.quotientProjection i U e m else 0 := by
  classical
  simp only [coefficientProjection, LinearMap.sum_apply, map_sum]
  have h : ∀ d : Fin 4, D.quotientProjection i U e
      ((if d.val + wordWeight gs = n then D.quotientProjection i U d else 0) m) =
      if d = e then (if e.val + wordWeight gs = n then D.quotientProjection i U e m else 0) else 0 := by
    intro d
    by_cases hd : d = e
    · subst d; by_cases hn : e.val + wordWeight gs = n <;> simp [hn, D.quotientProjection_comp]
    · by_cases hn : d.val + wordWeight gs = n
      · simp [hn, D.quotientProjection_comp, hd, Ne.symm hd]
      · simp [hn, hd]
  simp only [h]
  simp

theorem internalProjection_mem (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U)) :
    internalProjection D i U n x ∈ internalComponent D i U n := by
  intro gs d hn
  rw [internalProjection_apply, quotientProjection_coefficientProjection, if_neg hn]

theorem internalProjection_eq_self (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ internalComponent D i U n) : internalProjection D i U n x = x := by
  classical
  ext gs
  rw [internalProjection_apply]
  conv_rhs => rw [← D.quotientProjection_sum i U (x gs)]
  simp only [coefficientProjection, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : d.val + wordWeight gs = n
  · simp [hn]
  · simp [hn, hx gs d hn]

theorem internalProjection_idempotent (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U)) :
    internalProjection D i U n (internalProjection D i U n x) = internalProjection D i U n x :=
  internalProjection_eq_self D i U n _ (internalProjection_mem D i U n x)

theorem internal_single (D : CyclicData k) (i : Vertex) (U : Submodule k (Vec k))
    (n : ℕ) (gs : List Generator) (m : D.QuotientRow i U)
    (hm : ∀ d : Fin 4, d.val + wordWeight gs ≠ n → D.quotientProjection i U d m = 0) :
    Finsupp.single gs m ∈ internalComponent D i U n := by
  intro cs d hn
  by_cases hc : cs = gs
  · subst cs; simpa using hm d hn
  · simp [Finsupp.single_apply, hc, Ne.symm hc]

theorem internal_single_projected (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (gs : List Generator) (e : Fin 4) (m : D.QuotientRow i U) :
    Finsupp.single gs (D.quotientProjection i U e m) ∈ internalComponent D i U (e.val + wordWeight gs) := by
  apply internal_single
  intro d hn
  have hd : d ≠ e := by intro h; subst d; exact hn rfl
  simp [D.quotientProjection_comp, hd]

set_option maxHeartbeats 2000000 in
/-- The original coefficient action adds the weight of a positive basis element. -/
theorem rowAction_positive_degree (D : CyclicData k) (i : Vertex) (g : Generator)
    (d e : Fin 4) (r : Row k) :
    degreeProjection d (D.rowAction i (degreeProjection e r) (positiveBasis g)) =
      if d.val = e.val + g.weight then D.rowAction i (degreeProjection e r) (positiveBasis g) else 0 := by
  classical
  cases g <;> fin_cases d <;> fin_cases e <;>
    simp [degreeProjection, CyclicData.rowAction_formula, positiveBasis, embedRow,
      Generator.weight, apply_ite]
  all_goals split_ifs <;> simp_all

theorem quotientAction_positive_degree (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (g : Generator) (d e : Fin 4) (m : D.QuotientRow i U) :
    D.quotientProjection i U d (D.quotientAction i U (positiveBasis g) (D.quotientProjection i U e m)) =
      if d.val = e.val + g.weight then D.quotientAction i U (positiveBasis g) (D.quotientProjection i U e m) else 0 := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective m
  simp only [CyclicData.quotientProjection_mkQ, CyclicData.quotientAction_mkQ, rowAction_positive_degree]
  split_ifs <;> simp

/-- Degree projections also commute with the vertex projections used in normalization. -/
theorem quotientProjection_corner (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (d : Fin 4) (j : Vertex) (m : D.QuotientRow i U) :
    D.quotientProjection i U d (D.quotientAction i U (vertexIdempotent j) m) =
      D.quotientAction i U (vertexIdempotent j) (D.quotientProjection i U d m) := by
  obtain ⟨r, rfl⟩ := (D.rowGenerated i U).mkQ_surjective m
  simp only [CyclicData.quotientProjection_mkQ, CyclicData.quotientAction_mkQ]
  congr 1
  fin_cases d <;>
    simp [degreeProjection, CyclicData.rowAction_formula, vertexIdempotent, embedRow,
      CyclicData.identityRow, apply_ite]
  all_goals split_ifs <;> simp_all


theorem innerBasisDifferential_internal (D : CyclicData k) (gs : List Generator) :
    innerBasisDifferential D gs ∈ Finsupp.supported k k {cs | wordWeight cs = wordWeight gs} := by
  classical
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
      cases gs with
      | nil => exact Submodule.zero_mem _
      | cons h cs =>
          apply Submodule.sub_mem
          · apply Submodule.sum_mem
            intro t ht
            by_cases hm : positiveMultiplication D g h t = 0
            · simp [hm]
            · apply Submodule.smul_mem
              apply Finsupp.single_mem_supported k 1
              have hw := (positiveMultiplication_support D g h t hm).2.2.2
              simp only [Set.mem_setOf_eq, wordWeight_cons]
              omega
          · apply Finsupp.supported_comap_lmapDomain k k
            intro as has
            have hi := ih has
            simpa only [Set.mem_preimage, Set.mem_setOf_eq, wordWeight_append,
              wordWeight_cons, wordWeight_nil, add_zero] using congrArg (g.weight + ·) hi

theorem tensorWords_internal_projected (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (e : Fin 4) (m : D.QuotientRow i U)
    (v : ℕ) (x : WordSpace k) (hx : x ∈ Finsupp.supported k k {gs | wordWeight gs = v}) :
    tensorWords x (D.quotientProjection i U e m) ∈ internalComponent D i U (e.val + v) := by
  classical
  change (x.support.sum (fun gs => x gs • (Finsupp.lsingle gs : D.QuotientRow i U →ₗ[k] _))) _ ∈ _
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro gs hgs
  apply Submodule.smul_mem
  have h := internal_single_projected D i U gs e m
  rw [hx hgs] at h
  exact h

theorem onWord_internal_projected (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (gs : List Generator) (e : Fin 4) (m : D.QuotientRow i U) :
    onWord (quotientRightAction D i U) gs (D.quotientProjection i U e m) ∈
      internalComponent D i U (e.val + wordWeight gs) := by
  cases gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs =>
      apply Submodule.add_mem
      · apply Submodule.neg_mem
        apply internal_single
        intro d hn
        change D.quotientProjection i U d
          (D.quotientAction i U (positiveBasis g) (D.quotientProjection i U e m)) = 0
        rw [quotientAction_positive_degree]
        apply if_neg
        intro hd
        apply hn
        simp only [wordWeight_cons]
        omega
      · exact tensorWords_internal_projected D i U e m _ _ (innerBasisDifferential_internal D _)

theorem ambientDifferential_internal (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ internalComponent D i U n) :
    ambientDifferential (quotientRightAction D i U) x ∈ internalComponent D i U n := by
  classical
  change x.support.sum (fun gs => onWord (quotientRightAction D i U) gs (x gs)) ∈ _
  apply Submodule.sum_mem
  intro gs hgs
  rw [← D.quotientProjection_sum i U (x gs), map_sum]
  apply Submodule.sum_mem
  intro e he
  by_cases hn : e.val + wordWeight gs = n
  · rw [← hn]
    exact onWord_internal_projected D i U gs e (x gs)
  · rw [hx gs e hn, map_zero]
    exact Submodule.zero_mem _

theorem internalProjection_normalization (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U)) :
    internalProjection D i U n (normalization (quotientRightAction D i U) x) =
      normalization (quotientRightAction D i U) (internalProjection D i U n x) := by
  classical
  ext gs
  rw [internalProjection_apply, normalization_apply, normalization_apply, internalProjection_apply]
  by_cases hc : composable gs
  · simp only [if_pos hc]
    cases gs with
    | nil => rfl
    | cons g gs =>
        change coefficientProjection D i U n (g :: gs) (D.quotientAction i U (vertexIdempotent g.source) _) =
          D.quotientAction i U (vertexIdempotent g.source) (coefficientProjection D i U n (g :: gs) _)
        simp only [coefficientProjection, LinearMap.sum_apply, map_sum]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hn : d.val + wordWeight (g :: gs) = n
        · simpa only [if_pos hn] using quotientProjection_corner D i U d g.source _
        · simp only [if_neg hn, LinearMap.zero_apply, map_zero]
  · simp [hc]

theorem internalProjection_balanced (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ balancedAmbient (quotientRightAction D i U)) :
    internalProjection D i U n x ∈ balancedAmbient (quotientRightAction D i U) := by
  apply (mem_balancedAmbient_iff _ _).mpr
  rw [← internalProjection_normalization, (mem_balancedAmbient_iff _ _).mp hx]

theorem internalProjection_length (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (n r : ℕ) (x : Ambient (D.QuotientRow i U))
    (hx : x ∈ lengthComponent (k := k) r) :
    internalProjection D i U n x ∈ lengthComponent (k := k) r := by
  intro gs hgs
  apply hx
  apply Finsupp.mem_support_iff.mpr
  intro heq
  have hn := Finsupp.mem_support_iff.mp hgs
  apply hn
  rw [internalProjection_apply, heq, map_zero]

/-- B_(r,n), with the original vertex balancing conditions retained. -/
def internallyNormalizedTerm (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) : Submodule k (Ambient (D.QuotientRow i U)) :=
  normalizedTerm (quotientRightAction D i U) r ⊓ internalComponent D i U n

def internallyNormalizedDifferential (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) :
    internallyNormalizedTerm D i U (r + 1) n →ₗ[k] internallyNormalizedTerm D i U r n where
  toFun x := ⟨ambientDifferential (quotientRightAction D i U) x.val,
    ⟨ambientDifferential_balanced _ _ x.property.1.1,
      ambientDifferential_homological _ r _ x.property.1.2⟩,
    ambientDifferential_internal D i U n _ x.property.2⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _

theorem internallyNormalizedDifferential_square (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) (x : internallyNormalizedTerm D i U (r + 1 + 1) n) :
    internallyNormalizedDifferential D i U r n (internallyNormalizedDifferential D i U (r + 1) n x) = 0 := by
  apply Subtype.ext
  exact ambientDifferential_square _ x.val

instance finiteDimensional_internallyNormalizedTerm (D : CyclicData k) (i : Vertex)
    (U : Submodule k (Vec k)) (r n : ℕ) : FiniteDimensional k (internallyNormalizedTerm D i U r n) := by
  let f : internallyNormalizedTerm D i U r n →ₗ[k]
      lengthComponent (k := k) (M := D.QuotientRow i U) r :=
    Submodule.inclusion (fun _ hx => hx.1.2)
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective _)

end
end Ginzburg333.Bar
