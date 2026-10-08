import Ginzburg333.Converse.Paths

namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]
noncomputable section

instance (n : ℕ) : Fintype (WeightLetters n) := Fintype.ofFinite _
instance (n s : ℕ) : Fintype (BigradedLetters n s) := Fintype.ofFinite _

theorem letterWeight_zero (ls : List PathLetter) (h : letterWeight ls = 0) : ls = [] := by
  apply List.length_eq_zero_iff.mp
  have hl := letter_length_le_weight ls
  omega

def zeroLettersEquiv : Unit ≃ WeightLetters 0 where
  toFun _ := ⟨[], rfl⟩
  invFun _ := ()
  left_inv := by intro u; cases u; rfl
  right_inv := by intro ls; apply Subtype.ext; exact (letterWeight_zero ls.val ls.property).symm

theorem letterWeight_one (ls : List PathLetter) (h : letterWeight ls = 1) :
    ∃ a, ls = [.forward a] := by
  cases ls with
  | nil => simp [letterWeight] at h
  | cons l ls =>
      cases l with
      | forward a =>
          have ht : letterWeight ls = 0 := by simpa [letterWeight, PathLetter.weight] using h
          exact ⟨a, by rw [letterWeight_zero ls ht]⟩
      | reverse a => simp [letterWeight, PathLetter.weight] at h; omega
      | loop => simp [letterWeight, PathLetter.weight] at h; omega

def oneLettersEquiv : Fin 3 ≃ WeightLetters 1 :=
  Equiv.ofBijective (fun a => ⟨[.forward a], rfl⟩) ⟨
    by intro a b h; simpa using congrArg Subtype.val h,
    by intro ls; obtain ⟨a, ha⟩ := letterWeight_one ls.val ls.property; exact ⟨a, Subtype.ext ha.symm⟩⟩

def twoLetters : ((Fin 3 × Fin 3) ⊕ Fin 3) → WeightLetters 2
  | .inl ab => ⟨[.forward ab.1, .forward ab.2], rfl⟩
  | .inr a => ⟨[.reverse a], rfl⟩

def twoLettersEquiv : ((Fin 3 × Fin 3) ⊕ Fin 3) ≃ WeightLetters 2 :=
  Equiv.ofBijective twoLetters ⟨by
    intro x y h
    cases x <;> cases y <;> simpa [twoLetters, Prod.ext_iff] using h,
    by
      rintro ⟨ls, hl⟩
      cases ls with
      | nil => simp [letterWeight] at hl
      | cons l ls =>
          cases l with
          | forward a =>
              have ht : letterWeight ls = 1 := by
                simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight] at hl ⊢
                omega
              obtain ⟨b, rfl⟩ := letterWeight_one ls ht
              exact ⟨Sum.inl (a, b), rfl⟩
          | reverse a =>
              have ht : letterWeight ls = 0 := by
                simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight] at hl ⊢
                omega
              have he := letterWeight_zero ls ht
              subst ls
              exact ⟨Sum.inr a, rfl⟩
          | loop => simp [letterWeight, PathLetter.weight] at hl; omega⟩

def stepLetters (n : ℕ) :
    ((Fin 3 × WeightLetters (n + 2)) ⊕ ((Fin 3 × WeightLetters (n + 1)) ⊕ WeightLetters n)) →
      WeightLetters (n + 3)
  | .inl al => ⟨.forward al.1 :: al.2.val, by
      simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight]
      have ht := al.2.property; unfold letterWeight at ht; omega⟩
  | .inr (.inl al) => ⟨.reverse al.1 :: al.2.val, by
      simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight]
      have ht := al.2.property; unfold letterWeight at ht; omega⟩
  | .inr (.inr ls) => ⟨.loop :: ls.val, by
      simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight]
      have ht := ls.property; unfold letterWeight at ht; omega⟩

def stepLettersEquiv (n : ℕ) :
    ((Fin 3 × WeightLetters (n + 2)) ⊕ ((Fin 3 × WeightLetters (n + 1)) ⊕ WeightLetters n)) ≃
      WeightLetters (n + 3) := Equiv.ofBijective (stepLetters n) ⟨by
    intro x y h
    rcases x with ⟨a, x⟩ | (⟨a, x⟩ | x)
    all_goals rcases y with ⟨b, y⟩ | (⟨b, y⟩ | y)
    all_goals simpa [stepLetters, Prod.ext_iff, Subtype.ext_iff] using h,
    by
      rintro ⟨ls, hl⟩
      cases ls with
      | nil => simp [letterWeight] at hl
      | cons l ls =>
          cases l with
          | forward a =>
              have ht : letterWeight ls = n + 2 := by
                simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight] at hl ⊢
                omega
              exact ⟨Sum.inl (a, ⟨ls, ht⟩), rfl⟩
          | reverse a =>
              have ht : letterWeight ls = n + 1 := by
                simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight] at hl ⊢
                omega
              exact ⟨Sum.inr (Sum.inl (a, ⟨ls, ht⟩)), rfl⟩
          | loop =>
              have ht : letterWeight ls = n := by
                simp only [letterWeight, List.map_cons, List.sum_cons, PathLetter.weight] at hl ⊢
                omega
              exact ⟨Sum.inr (Sum.inr ⟨ls, ht⟩), rfl⟩⟩

def signedLetterEuler (n : ℕ) : ℤ := ∑ ls : WeightLetters n, (-1 : ℤ) ^ letterNegative ls.val

theorem signedLetterEuler_zero : signedLetterEuler 0 = 1 := by
  rw [signedLetterEuler, ← zeroLettersEquiv.sum_comp]
  simp [zeroLettersEquiv, letterNegative]

theorem signedLetterEuler_one : signedLetterEuler 1 = 3 := by
  rw [signedLetterEuler, ← oneLettersEquiv.sum_comp]
  simp [oneLettersEquiv, letterNegative, PathLetter.negative]

theorem signedLetterEuler_two : signedLetterEuler 2 = 6 := by
  rw [signedLetterEuler, ← twoLettersEquiv.sum_comp]
  simp [twoLettersEquiv, twoLetters, letterNegative, PathLetter.negative]

theorem signedLetterEuler_step (n : ℕ) :
    signedLetterEuler (n + 3) = 3 * signedLetterEuler (n + 2) - 3 * signedLetterEuler (n + 1) + signedLetterEuler n := by
  rw [signedLetterEuler, ← (stepLettersEquiv n).sum_comp]
  simp [stepLettersEquiv, stepLetters, letterNegative, PathLetter.negative, pow_add,
    Fintype.sum_prod_type, signedLetterEuler]
  ring

theorem signedLetterEuler_quadratic (n : ℕ) :
    2 * signedLetterEuler n = ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  have hall (n : ℕ) :
      (2 * signedLetterEuler n = ((n : ℤ) + 1) * ((n : ℤ) + 2)) ∧
      (2 * signedLetterEuler (n + 1) = ((n : ℤ) + 2) * ((n : ℤ) + 3)) ∧
      (2 * signedLetterEuler (n + 2) = ((n : ℤ) + 3) * ((n : ℤ) + 4)) := by
    induction n with
    | zero => norm_num [signedLetterEuler_zero, signedLetterEuler_one, signedLetterEuler_two]
    | succ n ih =>
        refine ⟨?_, ?_, ?_⟩
        · simpa [Nat.cast_add, Nat.cast_one] using ih.2.1
        · simpa [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using ih.2.2
        · have he := signedLetterEuler_step n
          have h1 := ih.1
          have h2 := ih.2.1
          have h3 := ih.2.2
          have hn : n + 1 + 2 = n + 3 := by omega
          rw [hn, he]
          push_cast
          nlinarith
  exact (hall n).1

def sigmaBigradedLettersEquiv (n : ℕ) :
    (Σ s : Fin (n + 1), BigradedLetters n s.val) ≃ WeightLetters n :=
  Equiv.ofBijective (fun t => ⟨t.2.val, t.2.property.1⟩) ⟨by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have he : x.val = y.val := congrArg Subtype.val h
    have hab : a = b := by
      apply Fin.ext
      rw [← x.property.2, ← y.property.2, he]
    subst b
    have hxy : x = y := Subtype.ext he
    subst y
    rfl,
    by
      intro ls
      have hneg : letterNegative ls.val < n + 1 := by
        have hb := letter_negative_le_weight ls.val
        rw [ls.property] at hb
        omega
      exact ⟨⟨⟨letterNegative ls.val, hneg⟩, ⟨ls.val, ls.property, rfl⟩⟩, rfl⟩⟩

theorem signedLetterEuler_sum_counts (n : ℕ) :
    (∑ s ∈ Finset.range (n + 1), (-1 : ℤ) ^ s * (letterCount n s : ℤ)) = signedLetterEuler n := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold signedLetterEuler
  rw [← (sigmaBigradedLettersEquiv n).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  change (-1 : ℤ) ^ s.val * (letterCount n s.val : ℤ) =
    ∑ ls : BigradedLetters n s.val, (-1 : ℤ) ^ letterNegative ls.val
  simp_rw [show ∀ ls : BigradedLetters n s.val, letterNegative ls.val = s.val from fun ls => ls.property.2]
  simp [letterCount, Nat.card_eq_fintype_card, mul_comm]

/-- The polynomial growth forced by actual negative acyclicity. -/
theorem internalJacobi_quadratic_growth (w : Tensor k) (hw : GinzburgRegular w) (n : ℕ) :
    2 * (Module.finrank k (internalJacobi w n) : ℤ) = 3 * ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  rw [internalJacobi_finrank_euler w hw n]
  simp_rw [negativeDimension_letterCount, Nat.cast_mul, Nat.cast_ofNat]
  have he : (∑ s ∈ Finset.range (n + 1), (-1 : ℤ) ^ s * (3 * (letterCount n s : ℤ))) =
      3 * signedLetterEuler n := by
    rw [← signedLetterEuler_sum_counts]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [he]
  have hpoly := signedLetterEuler_quadratic n
  nlinarith

theorem internalJacobi_finrank_36 (w : Tensor k) (hw : GinzburgRegular w) :
    Module.finrank k (internalJacobi w 36) = 2109 := by
  have h := internalJacobi_quadratic_growth w hw 36
  norm_num at h
  omega
end
end Ginzburg333.Ginzburg
