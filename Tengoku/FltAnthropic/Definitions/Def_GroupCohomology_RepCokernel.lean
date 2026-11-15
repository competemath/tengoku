import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepCokernel

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)

noncomputable def π : Y ⟶ obj f := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

/--
@isnad1 id=iff.0h6v.s10.8f4bf33f4f0b from=translated src=- shape=a8bd6375 vocab=e722a5e1
-/
theorem π_hom_apply_eq_zero_iff (y : Y) : (π f).hom y = 0 ↔ y ∈ LinearMap.range f.hom.toLinearMap :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def seq : ShortComplex (Rep.{u} k G) where
  X₁ := X
  X₂ := Y
  X₃ := obj f
  f := f
  g := π f
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩))

end GroupCohomology.RepCokernel
