import Ginzburg333.Homology.Exact

/-!
# The short exact sequence associated to a colon

These are actual maps on quotients of vector spaces. The source of the first
map is the quotient by the preimage of P; the last quotient is by P + im f.
No homology or exactness assumption is used.
-/

namespace Ginzburg333.Homology
variable {k A B : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

def colonInclusion (P : Submodule k B) (f : A →ₗ[k] B) :
    (A ⧸ P.comap f) →ₗ[k] (B ⧸ P) :=
  (P.comap f).mapQ P f le_rfl

def stepProjection (P : Submodule k B) (f : A →ₗ[k] B) :
    (B ⧸ P) →ₗ[k] (B ⧸ (P ⊔ LinearMap.range f)) :=
  P.mapQ (P ⊔ LinearMap.range f) LinearMap.id (by simpa using le_sup_left)

@[simp] theorem colonInclusion_mkQ (P : Submodule k B) (f : A →ₗ[k] B) (a : A) :
    colonInclusion P f ((P.comap f).mkQ a) = P.mkQ (f a) := rfl

@[simp] theorem stepProjection_mkQ (P : Submodule k B) (f : A →ₗ[k] B) (b : B) :
    stepProjection P f (P.mkQ b) = (P ⊔ LinearMap.range f).mkQ b := rfl

theorem colonInclusion_injective (P : Submodule k B) (f : A →ₗ[k] B) :
    Function.Injective (colonInclusion P f) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := (P.comap f).mkQ_surjective x
    have hfa : P.mkQ (f a) = 0 := hx
    have ha : a ∈ P.comap f := by
      change f a ∈ P
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hfa
    change (P.comap f).mkQ a = 0
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using ha
  · exact bot_le

theorem stepProjection_surjective (P : Submodule k B) (f : A →ₗ[k] B) :
    Function.Surjective (stepProjection P f) := by
  intro x
  obtain ⟨b, rfl⟩ := (P ⊔ LinearMap.range f).mkQ_surjective x
  exact ⟨P.mkQ b, rfl⟩

theorem colon_quotient_exact (P : Submodule k B) (f : A →ₗ[k] B) :
    ExactAt (colonInclusion P f) (stepProjection P f) := by
  intro x
  obtain ⟨b, rfl⟩ := P.mkQ_surjective x
  constructor
  · intro hb
    change (P ⊔ LinearMap.range f).mkQ b = 0 at hb
    have hbmem : b ∈ P ⊔ LinearMap.range f := by
      simpa only [stepProjection_mkQ, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] using hb
    obtain ⟨p, hp, v, hv, hsum⟩ := Submodule.mem_sup.mp hbmem
    obtain ⟨a, rfl⟩ := hv
    refine ⟨(P.comap f).mkQ a, ?_⟩
    rw [colonInclusion_mkQ, ← hsum, map_add]
    have hpzero : P.mkQ p = 0 := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hp
    rw [hpzero, zero_add]
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := (P.comap f).mkQ_surjective y
    rw [← hy, colonInclusion_mkQ, stepProjection_mkQ]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (show LinearMap.range f ≤ P ⊔ LinearMap.range f from le_sup_right) ⟨a, rfl⟩

theorem quotient_maps_short_exact
    (P Q : Submodule k B) (T : Submodule k A) (f : A →ₗ[k] B)
    (hf : T ≤ P.comap f) (hPQ : P ≤ Q)
    (hcolon : P.comap f = T) (hsup : Q = P ⊔ LinearMap.range f) :
    Function.Injective (T.mapQ P f hf) ∧
    ExactAt (T.mapQ P f hf) (P.mapQ Q LinearMap.id (by simpa using hPQ)) ∧
    Function.Surjective (P.mapQ Q LinearMap.id (by simpa using hPQ)) := by
  subst T
  subst Q
  exact ⟨colonInclusion_injective P f, colon_quotient_exact P f,
    stepProjection_surjective P f⟩

end Ginzburg333.Homology
