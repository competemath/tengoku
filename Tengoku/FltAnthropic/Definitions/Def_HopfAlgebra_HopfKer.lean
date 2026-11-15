import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]

noncomputable def coaction (π : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)).comp (Bialgebra.comulAlgHom R A)

/--
@isnad1 id=eq.0h5v.s11.9b1ec127b348 from=translated src=- shape=61f9c7d9 vocab=2cba3430
-/
theorem coaction_apply (π : A →ₐc[R] B) (a : A) :
    coaction π a = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) (Coalgebra.comul (R := R) a) := rfl

noncomputable def hopfKer (π : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (coaction π) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)

/--
@isnad1 id=iff.0h5v.s9.02b285fbf633 from=translated src=- shape=4174f222 vocab=320e4224
-/
theorem mem_hopfKer_iff (π : A →ₐc[R] B) (a : A) : a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 := Iff.rfl

/--
@isnad1 id=eq.1h5v.s9.101fb20ca193 from=translated src=- shape=70b18ca1 vocab=320e4224
-/
theorem coaction_eq_of_mem (π : A →ₐc[R] B) {a : A} (h : a ∈ hopfKer π) : coaction π a = a ⊗ₜ[R] 1 := h

noncomputable def canAlgHom (π : A →ₐc[R] B) : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (coaction π)
    (fun _ _ => Commute.all _ _)

/--
@isnad1 id=eq.0h6v.s10.0e95f617e61a from=translated src=- shape=9d63413d vocab=d4c69692
-/
@[simp] theorem canAlgHom_tmul (π : A →ₐc[R] B) (a a' : A) :
    canAlgHom π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  Algebra.TensorProduct.lift_tmul _ _ _ a a'

noncomputable def canMap (π : A →ₐc[R] B) : A ⊗[R] A →ₗ[R] A ⊗[R] B := (canAlgHom π).toLinearMap

/--
@isnad1 id=eq.0h5v.s11.551c03a8ab2a from=translated src=- shape=ad450c9c vocab=148fffa0
-/
theorem canMap_apply (π : A →ₐc[R] B) (z : A ⊗[R] A) : canMap π z = canAlgHom π z := rfl

/--
@isnad1 id=eq.0h6v.s11.d7fc841508b7 from=translated src=- shape=59452cb2 vocab=02028c41
-/
@[simp] theorem canMap_tmul (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canAlgHom_tmul π a a'

/--
@isnad1 id=eq.1h7v.s11.92472a435fa0 from=translated src=- shape=1fb96aa3 vocab=322420cd
-/
theorem canMap_mul_tmul (π : A →ₐc[R] B) (a a' : A) {h : A} (hh : h ∈ hopfKer π) :
    canMap π ((a * h) ⊗ₜ[R] a') = canMap π (a ⊗ₜ[R] (h * a')) := by
  rw [canMap_tmul, canMap_tmul, map_mul, coaction_eq_of_mem π hh, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

/--
@isnad1 id=eq.0h5v.s10.1a228778bfa0 from=translated src=- shape=33098e00 vocab=375a7e56
-/
theorem canMap_tmul_one (π : A →ₐc[R] B) (a : A) : canMap π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canMap_tmul, map_one, mul_one]

/--
@isnad1 id=eq.0h5v.s10.9fbf2b609798 from=translated src=- shape=911e91bd vocab=98ab2c8b
-/
theorem canMap_one_tmul (π : A →ₐc[R] B) (a : A) : canMap π (1 ⊗ₜ[R] a) = coaction π a := by
  rw [canMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]

def balancingRelations (π : A →ₐc[R] B) : Set (A ⊗[R] A) :=
  {x | ∃ (a h a' : A), h ∈ hopfKer π ∧ x = (a * h) ⊗ₜ[R] a' - a ⊗ₜ[R] (h * a')}

/--
@isnad1 id=eq.1h5v.s11.a4034bfc8d5a from=translated src=- shape=a6e8f8bd vocab=984ac5bf
-/
theorem canMap_eq_zero_of_mem_span (π : A →ₐc[R] B) {z : A ⊗[R] A}
    (hz : z ∈ Submodule.span R (balancingRelations π)) : canMap π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, h, a', hh, rfl⟩ := hx
    rw [map_sub, canMap_mul_tmul π a a' hh, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

def IsHopfGalois (π : A →ₐc[R] B) : Prop :=
  Function.Surjective (canMap π) ∧ ∀ z, canMap π z = 0 → z ∈ Submodule.span R (balancingRelations π)

end HopfAlgebra
