import Ginzburg333.Ginzburg

/-! Endpoint and degree verification for the actual Leibniz differential. -/
namespace Ginzburg333.Ginzburg
variable {k : Type*} [Field k]

def wordWeight (gs : List Generator) : ℕ := (gs.map Generator.weight).sum
def wordNegative (gs : List Generator) : ℕ := (gs.map Generator.negativeDegree).sum

@[simp] theorem wordWeight_nil : wordWeight [] = 0 := rfl
@[simp] theorem wordNegative_nil : wordNegative [] = 0 := rfl
@[simp] theorem wordWeight_cons (g : Generator) (gs : List Generator) :
    wordWeight (g :: gs) = g.weight + wordWeight gs := rfl
@[simp] theorem wordNegative_cons (g : Generator) (gs : List Generator) :
    wordNegative (g :: gs) = g.negativeDegree + wordNegative gs := rfl
@[simp] theorem wordWeight_append (as bs : List Generator) :
    wordWeight (as ++ bs) = wordWeight as + wordWeight bs := by
  simp [wordWeight]
@[simp] theorem wordNegative_append (as bs : List Generator) :
    wordNegative (as ++ bs) = wordNegative as + wordNegative bs := by
  simp [wordNegative]

theorem endpoint_append (start : Vertex) (as bs : List Generator) :
    endpoint? start (as ++ bs) = (endpoint? start bs).bind (fun v => endpoint? v as) := by
  induction as generalizing start with
  | nil => simp [endpoint?]
  | cons g as ih =>
      cases h : endpoint? start bs <;> simp [endpoint?, ih, h]

theorem generatorDifferential_terms (w : Tensor k) (g : Generator)
    {t : k × List Generator} (ht : t ∈ generatorDifferential w g) :
    wordWeight t.2 = g.weight ∧ wordNegative t.2 + 1 = g.negativeDegree ∧
      endpoint? g.source t.2 = some g.target := by
  cases g with
  | forward i a => simp [generatorDifferential] at ht
  | reverse i a =>
      simp only [generatorDifferential, List.mem_flatMap, List.mem_map] at ht
      obtain ⟨b, _, c, _, rfl⟩ := ht
      simp [wordWeight, wordNegative, endpoint?, Generator.source, Generator.target,
        Generator.weight, Generator.negativeDegree, next_three]
  | loop i =>
      simp only [generatorDifferential, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;>
        simp [wordWeight, wordNegative, endpoint?, Generator.source, Generator.target,
          Generator.weight, Generator.negativeDegree, next_three]

theorem wordDifferential_degrees (w : Tensor k) (gs : List Generator)
    {t : k × List Generator} (ht : t ∈ wordDifferential w gs) :
    wordWeight t.2 = wordWeight gs ∧ wordNegative t.2 + 1 = wordNegative gs := by
  induction gs generalizing t with
  | nil => simp [wordDifferential] at ht
  | cons g gs ih =>
      simp only [wordDifferential, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨hw, hn, _⟩ := generatorDifferential_terms w g hp
        simp only [wordWeight_append, wordNegative_append, wordWeight_cons, wordNegative_cons]
        constructor <;> omega
      · obtain ⟨hw, hn⟩ := ih hp
        simp only [wordWeight_cons, wordNegative_cons]
        constructor <;> omega

theorem wordDifferential_endpoints (w : Tensor k) (gs : List Generator)
    (start finish : Vertex) (hpath : endpoint? start gs = some finish)
    {t : k × List Generator} (ht : t ∈ wordDifferential w gs) :
    endpoint? start t.2 = some finish := by
  induction gs generalizing finish t with
  | nil => simp [wordDifferential] at ht
  | cons g gs ih =>
      cases hv : endpoint? start gs with
      | none => simp [endpoint?, hv] at hpath
      | some v =>
          by_cases hgv : g.source = v
          · have hgf : g.target = finish := by
              simpa [endpoint?, hv, hgv] using hpath
            simp only [wordDifferential, List.mem_append, List.mem_map] at ht
            rcases ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
            · have hend := (generatorDifferential_terms w g hp).2.2
              rw [endpoint_append, hv]
              simpa [hgv, hgf] using hend
            · have hend := ih v hv hp
              simp [endpoint?, hend, hgv, hgf]
          · simp [endpoint?, hv, hgv] at hpath

/-- The validity branch in pathTerm is always taken for an actual differential term. -/
theorem differential_term_valid (w : Tensor k) (p : BasisPath)
    {t : k × List Generator} (ht : t ∈ wordDifferential w p.val.2) :
    ValidPath (p.val.1, t.2) := by
  have hp := p.property
  unfold ValidPath at hp ⊢
  cases h : endpoint? p.val.1 p.val.2 with
  | none => simp [h] at hp
  | some v =>
      rw [wordDifferential_endpoints w p.val.2 p.val.1 v h ht]
      rfl

end Ginzburg333.Ginzburg
