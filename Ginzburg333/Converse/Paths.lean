import Ginzburg333.Converse.Euler

namespace Ginzburg333.Ginzburg
open Ginzburg333.Bar
variable {k : Type*} [Field k]

/-- Labels retain arrow type and coordinate; the current vertex determines the generator. -/
inductive PathLetter
  | forward (a : Fin 3)
  | reverse (a : Fin 3)
  | loop
  deriving DecidableEq, Fintype

namespace PathLetter
def weight : PathLetter → ℕ
  | .forward _ => 1
  | .reverse _ => 2
  | .loop => 3
def negative : PathLetter → ℕ
  | .forward _ => 0
  | .reverse _ => 1
  | .loop => 2
def atVertex (i : Vertex) : PathLetter → Generator
  | .forward a => .forward i a
  | .reverse a => .reverse (next (next i)) a
  | .loop => .loop i
@[simp] theorem atVertex_source (i : Vertex) (l : PathLetter) : (l.atVertex i).source = i := by
  cases l <;> simp [atVertex, Generator.source]
@[simp] theorem atVertex_weight (i : Vertex) (l : PathLetter) : (l.atVertex i).weight = l.weight := by
  cases l <;> rfl
@[simp] theorem atVertex_negative (i : Vertex) (l : PathLetter) : (l.atVertex i).negativeDegree = l.negative := by
  cases l <;> rfl
end PathLetter

def generatorLetter : Generator → PathLetter
  | .forward _ a => .forward a
  | .reverse _ a => .reverse a
  | .loop _ => .loop

@[simp] theorem generatorLetter_atVertex (i : Vertex) (l : PathLetter) : generatorLetter (l.atVertex i) = l := by
  cases l <;> rfl
@[simp] theorem atVertex_generatorLetter (g : Generator) : (generatorLetter g).atVertex g.source = g := by
  cases g <;> simp [generatorLetter, PathLetter.atVertex, Generator.source]

def letterWord (i : Vertex) : List PathLetter → List Generator
  | [] => []
  | l :: ls => l.atVertex i :: letterWord (l.atVertex i).target ls

theorem letterWord_startsAt (i : Vertex) (ls : List PathLetter) : startsAt i (letterWord i ls) := by
  induction ls generalizing i with
  | nil => simp [letterWord, startsAt, composable]
  | cons l ls ih => rw [letterWord, startsAt_cons]; exact ⟨PathLetter.atVertex_source i l, ih _⟩

theorem letterWord_decode (i : Vertex) (ls : List PathLetter) : (letterWord i ls).map generatorLetter = ls := by
  induction ls generalizing i with
  | nil => rfl
  | cons l ls ih => simp [letterWord, ih]

theorem decode_letterWord (i : Vertex) (gs : List Generator) (h : startsAt i gs) :
    letterWord i (gs.map generatorLetter) = gs := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih =>
      obtain ⟨hi, hs⟩ := startsAt_cons i g gs |>.mp h
      rw [List.map_cons, letterWord, ← hi, atVertex_generatorLetter, ih _ hs]

def letterPath (i : Vertex) (ls : List PathLetter) : BasisPath :=
  ⟨(i, (letterWord i ls).reverse), (reverse_valid_iff i _).mpr (letterWord_startsAt i ls)⟩

def pathLettersEquiv : BasisPath ≃ Vertex × List PathLetter where
  toFun p := (p.val.1, p.val.2.reverse.map generatorLetter)
  invFun p := letterPath p.1 p.2
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    ·
      change (letterWord p.val.1 (p.val.2.reverse.map generatorLetter)).reverse = p.val.2
      rw [decode_letterWord]
      · simp
      · apply (reverse_valid_iff _ _).mp
        simpa using p.property
  right_inv := by
    intro p
    apply Prod.ext
    · rfl
    ·
      simp [letterPath, letterWord_decode]

def letterWeight (ls : List PathLetter) : ℕ := (ls.map PathLetter.weight).sum
def letterNegative (ls : List PathLetter) : ℕ := (ls.map PathLetter.negative).sum

theorem letterWord_weight (i : Vertex) (ls : List PathLetter) : wordWeight (letterWord i ls) = letterWeight ls := by
  induction ls generalizing i with
  | nil => rfl
  | cons l ls ih => simp [letterWord, wordWeight_cons, ih, letterWeight]

theorem letterWord_negative (i : Vertex) (ls : List PathLetter) : wordNegative (letterWord i ls) = letterNegative ls := by
  induction ls generalizing i with
  | nil => rfl
  | cons l ls ih => simp [letterWord, wordNegative_cons, ih, letterNegative]

theorem letterPath_internal (i : Vertex) (ls : List PathLetter) : internalDegree (letterPath i ls) = letterWeight ls := by
  change wordWeight (letterWord i ls).reverse = _
  rw [wordWeight_reverse, letterWord_weight]

theorem letterPath_cohomological (i : Vertex) (ls : List PathLetter) :
    cohomologicalDegree (letterPath i ls) = -(letterNegative ls : ℤ) := by
  change -(wordNegative (letterWord i ls).reverse : ℤ) = _
  have hr : wordNegative (letterWord i ls).reverse = wordNegative (letterWord i ls) := by
    simp only [wordNegative, List.map_reverse, List.sum_reverse]
  rw [hr, letterWord_negative]

theorem letter_length_le_weight (ls : List PathLetter) : ls.length ≤ letterWeight ls := by
  induction ls with
  | nil => simp [letterWeight]
  | cons l ls ih =>
      have hp : 0 < l.weight := by cases l <;> simp [PathLetter.weight, PathLetter.negative]
      simp only [List.length_cons, letterWeight, List.map_cons, List.sum_cons] at *
      omega

theorem letter_negative_le_weight (ls : List PathLetter) : letterNegative ls ≤ letterWeight ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      have hp : l.negative ≤ l.weight := by cases l <;> simp [PathLetter.weight, PathLetter.negative]
      simp only [letterWeight, letterNegative, List.map_cons, List.sum_cons] at *
      omega

abbrev WeightLetters (n : ℕ) := {ls : List PathLetter // letterWeight ls = n}
abbrev BigradedLetters (n s : ℕ) := {ls : List PathLetter // letterWeight ls = n ∧ letterNegative ls = s}

instance finite_WeightLetters (n : ℕ) : Finite (WeightLetters n) := by
  classical
  letI : Fintype {ls : List PathLetter // ls.length ≤ n} := (List.finite_length_le PathLetter n).fintype
  let f : WeightLetters n → {ls : List PathLetter // ls.length ≤ n} := fun ls =>
    ⟨ls.val, by have h := letter_length_le_weight ls.val; rw [ls.property] at h; exact h⟩
  exact Finite.of_injective f (by intro a b h; exact Subtype.ext (congrArg (fun t : {ls : List PathLetter // ls.length ≤ n} => t.val) h))

instance finite_BigradedLetters (n s : ℕ) : Finite (BigradedLetters n s) :=
  Finite.of_injective (fun ls : BigradedLetters n s => (⟨ls.val, ls.property.1⟩ : WeightLetters n))
    (by intro a b h; exact Subtype.ext (congrArg (fun t : WeightLetters n => t.val) h))

noncomputable def bigradedLettersEquiv (n s : ℕ) :
    {p : BasisPath // internalDegree p = n ∧ cohomologicalDegree p = -(s : ℤ)} ≃
      Vertex × BigradedLetters n s where
  toFun p := (pathLettersEquiv p.val |>.1,
    ⟨pathLettersEquiv p.val |>.2, by
      have he := pathLettersEquiv.symm_apply_apply p.val
      have hi := letterPath_internal (pathLettersEquiv p.val).1 (pathLettersEquiv p.val).2
      have hc := letterPath_cohomological (pathLettersEquiv p.val).1 (pathLettersEquiv p.val).2
      change internalDegree (pathLettersEquiv.symm (pathLettersEquiv p.val)) = _ at hi
      change cohomologicalDegree (pathLettersEquiv.symm (pathLettersEquiv p.val)) = _ at hc
      rw [he] at hi hc
      refine ⟨hi.symm.trans p.property.1, ?_⟩
      have hn := p.property.2
      rw [hc] at hn
      omega⟩)
  invFun p := ⟨letterPath p.1 p.2.val, by
    rw [letterPath_internal, letterPath_cohomological, p.2.property.1, p.2.property.2]
    exact ⟨rfl, rfl⟩⟩
  left_inv := by intro p; apply Subtype.ext; exact pathLettersEquiv.symm_apply_apply p.val
  right_inv := by
    intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact congrArg Prod.snd (pathLettersEquiv.apply_symm_apply (p.1, p.2.val))

noncomputable def letterCount (n s : ℕ) : ℕ := Nat.card (BigradedLetters n s)

theorem negativeDimension_letterCount (n s : ℕ) : negativeDimension (k := k) n s = 3 * letterCount n s := by
  classical
  let S := {p : BasisPath | internalDegree p = n ∧ cohomologicalDegree p = -(s : ℤ)}
  let e := Finsupp.supportedEquivFinsupp (R := k) (M := k) S
  have hdim : negativeDimension (k := k) n s = Nat.card S := by
    change Module.finrank k (Finsupp.supported k k S) = Nat.card S
    rw [e.finrank_eq]
    letI : Finite S := Finite.of_injective (bigradedLettersEquiv n s) (bigradedLettersEquiv n s).injective
    letI : Fintype S := Fintype.ofFinite S
    rw [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]
  rw [hdim]
  change Nat.card {p : BasisPath // internalDegree p = n ∧ cohomologicalDegree p = -(s : ℤ)} = _
  rw [Nat.card_congr (bigradedLettersEquiv n s), Nat.card_prod]
  simp [Vertex, letterCount, Nat.card_eq_fintype_card]
end Ginzburg333.Ginzburg
