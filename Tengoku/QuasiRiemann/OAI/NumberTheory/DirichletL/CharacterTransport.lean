import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.FiniteConductor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

namespace SevenEighths.CharacterTransport

open SevenEighths.FiniteFourier

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simpa using h.map e.symm.toMonoidHom

/--
@isnad1 id=eq.0h5v.s8.b39fc7e48404 from=translated src=- shape=8177ca7e vocab=44b82207
-/
@[simp] theorem pullback_apply (e : R ≃+* S) (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl

/--
@isnad1 id=eq.0h4v.s7.a9dbb326a3d7 from=translated src=- shape=8d3d30ca vocab=d19ada68
-/
@[simp] theorem pullback_symm (e : R ≃+* S) (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp

/--
@isnad1 id=eq.0h5v.s7.00be3de434fc from=translated src=- shape=101ab002 vocab=163f3ece
-/
@[simp] theorem pullback_mul (e : R ≃+* S) (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by
  apply MulChar.ext'
  intro x
  rfl

/--
@isnad1 id=isprimit.1h4v.s6.dd5e0383dd92 from=translated src=- shape=971082c3 vocab=f9eb6c59
-/
theorem primitive_pullback (e : R ≃+* S) (χ : MulChar S ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : IsPrimitiveOnIdeals (pullback e χ) := by
  intro I hI
  let J : Ideal S := I.comap e.symm.toRingHom
  have hJ : J ≠ ⊥ := by
    intro hJ
    apply hI
    apply le_antisymm _ bot_le
    intro x hx
    have he : e x ∈ J := by
      change e.symm (e x) ∈ I
      simpa using hx
    rw [hJ] at he
    have hx0 : x = 0 := e.injective (by simpa using he)
    exact hx0
  obtain ⟨u, hu, hχu⟩ := hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · change e.symm (u : S) - 1 ∈ I
    change e.symm ((u : S) - 1) ∈ I at hu
    simpa only [map_sub, map_one] using hu
  · simpa [v, pullback] using hχu

/--
@isnad1 id=iff.0h4v.s6.d38f964996f3 from=translated src=- shape=9a1813bb vocab=f9eb6c59
-/
theorem primitive_pullback_iff (e : R ≃+* S) (χ : MulChar S ℂ) :
    IsPrimitiveOnIdeals (pullback e χ) ↔ IsPrimitiveOnIdeals χ := by
  constructor
  · intro h
    simpa using primitive_pullback e.symm (pullback e χ) h
  · exact primitive_pullback e χ

end

end SevenEighths.CharacterTransport

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
