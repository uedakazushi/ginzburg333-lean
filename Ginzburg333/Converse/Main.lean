import Ginzburg333.Converse.Growth
import Ginzburg333.Converse.Counting
import Ginzburg333.Comparison.Bases

namespace Ginzburg333
variable {k : Type*} [Field k]

/-- Negative acyclicity of the actual Ginzburg complex forces all three rank bounds. -/
theorem ginzburgRegular_tensorRegular (w : Tensor k) (hw : Ginzburg.GinzburgRegular w) :
    TensorRegular w := by
  change ∀ (i : Vertex) (a : Vec k), a ≠ 0 →
    2 ≤ Module.finrank k (LinearMap.range ((ofTensor w).mul i a))
  intro i a ha
  by_contra hbad
  obtain ⟨h⟩ := Converse.rankOneSlice_of_not_regular w hw i a ha hbad
  obtain ⟨d⟩ := Converse.freeCornerData_exists w i a ha h
  have hlow := Converse.freeCorner_exponential_lower_bound w i a ha d 12
  have hupp := Ginzburg.internalJacobi_finrank_36 w hw
  norm_num at hlow
  rw [hupp] at hlow
  norm_num at hlow

/-- The two original regularity predicates are equivalent, without avatars. -/
theorem ginzburgRegular_iff_tensorRegular [IsAlgClosed k] [CharZero k] (w : Tensor k) :
    Ginzburg.GinzburgRegular w ↔ TensorRegular w :=
  ⟨ginzburgRegular_tensorRegular w, tensorRegular_ginzburgRegular w⟩

end Ginzburg333

namespace Ginzburg333.Comparison
variable {k : Type*} [Field k]
variable {X Y Z : Type*} [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]

theorem ginzburgRegular_tensorRegular_in_bases
    (bx : Basis (Fin 3) k X) (by_ : Basis (Fin 3) k Y) (bz : Basis (Fin 3) k Z)
    (w : TensorProduct k (TensorProduct k X Y) Z)
    (hw : Ginzburg.GinzburgRegular (tensorCoordinatesEquiv bx by_ bz w)) :
    TensorRegular (tensorCoordinatesEquiv bx by_ bz w) :=
  Ginzburg333.ginzburgRegular_tensorRegular _ hw

theorem ginzburgRegular_iff_tensorRegular_in_bases [IsAlgClosed k] [CharZero k]
    (bx : Basis (Fin 3) k X) (by_ : Basis (Fin 3) k Y) (bz : Basis (Fin 3) k Z)
    (w : TensorProduct k (TensorProduct k X Y) Z) :
    Ginzburg.GinzburgRegular (tensorCoordinatesEquiv bx by_ bz w) ↔
      TensorRegular (tensorCoordinatesEquiv bx by_ bz w) :=
  Ginzburg333.ginzburgRegular_iff_tensorRegular _

variable [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]

theorem ginzburgRegular_tensorRegular_chosen_bases
    (hx : Module.finrank k X = 3) (hy : Module.finrank k Y = 3) (hz : Module.finrank k Z = 3)
    (w : TensorProduct k (TensorProduct k X Y) Z)
    (hw : Ginzburg.GinzburgRegular (chosenTensorCoordinates hx hy hz w)) :
    TensorRegular (chosenTensorCoordinates hx hy hz w) :=
  Ginzburg333.ginzburgRegular_tensorRegular _ hw

theorem ginzburgRegular_iff_tensorRegular_chosen_bases [IsAlgClosed k] [CharZero k]
    (hx : Module.finrank k X = 3) (hy : Module.finrank k Y = 3) (hz : Module.finrank k Z = 3)
    (w : TensorProduct k (TensorProduct k X Y) Z) :
    Ginzburg.GinzburgRegular (chosenTensorCoordinates hx hy hz w) ↔
      TensorRegular (chosenTensorCoordinates hx hy hz w) :=
  Ginzburg333.ginzburgRegular_iff_tensorRegular _
end Ginzburg333.Comparison
