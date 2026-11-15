import Tengoku.Seed.AlgebraicGeometry.Morphisms.Proper
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

noncomputable abbrev finFibrePow : Scheme.{u} :=
  widePullback (Spec (CommRingCat.of k)) (fun _ : Fin r => C) (fun _ => c)

namespace finFibrePow

noncomputable abbrev proj (l : Fin r) : finFibrePow c r ⟶ C :=
  WidePullback.π (fun _ : Fin r => c) l

noncomputable abbrev toBase : finFibrePow c r ⟶ Spec (CommRingCat.of k) :=
  WidePullback.base (fun _ : Fin r => c)

/--
@isnad1 id=eq.0h5v.s6.f6d5d6b1ab1a from=translated src=- shape=73c70ab5 vocab=6266dffe
-/
@[reassoc]
theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _

noncomputable def permHom (σ : Equiv.Perm (Fin r)) : finFibrePow c r ⟶ finFibrePow c r :=
  WidePullback.lift (toBase c r) (fun j => proj c r (σ⁻¹ j)) (fun _ => WidePullback.π_arrow _ _)

/--
@isnad1 id=eq.0h6v.s6.ede0751974e3 from=translated src=- shape=6f55b4e5 vocab=2afae03e
-/
@[reassoc]
theorem permHom_proj (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    permHom c r σ ≫ proj c r j = proj c r (σ⁻¹ j) :=
  WidePullback.lift_π _ _ _ _ _

/--
@isnad1 id=eq.0h5v.s6.07d52d4ff2ce from=translated src=- shape=b8def020 vocab=1387b6a0
-/
@[reassoc]
theorem permHom_toBase (σ : Equiv.Perm (Fin r)) : permHom c r σ ≫ toBase c r = toBase c r :=
  WidePullback.lift_base _ _ _ _

/--
@isnad1 id=eq.0h4v.s6.1921552ea552 from=translated src=- shape=462dfe6d vocab=574506bb
-/
theorem permHom_one : permHom c r 1 = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.id_comp, inv_one, Equiv.Perm.one_apply]
  · rw [permHom_toBase, Category.id_comp]

/--
@isnad1 id=eq.0h6v.s6.9644b01d8d0d from=translated src=- shape=5706f49c vocab=4df96903
-/
theorem permHom_mul (σ τ : Equiv.Perm (Fin r)) :
    permHom c r (σ * τ) = permHom c r τ ≫ permHom c r σ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.assoc, permHom_proj, permHom_proj, mul_inv_rev,
      Equiv.Perm.mul_apply]
  · rw [permHom_toBase, Category.assoc, permHom_toBase, permHom_toBase]

noncomputable def permAut (σ : Equiv.Perm (Fin r)) : Aut (finFibrePow c r) where
  hom := permHom c r σ
  inv := permHom c r σ⁻¹
  hom_inv_id := by rw [← permHom_mul, inv_mul_cancel, permHom_one]
  inv_hom_id := by rw [← permHom_mul, mul_inv_cancel, permHom_one]

noncomputable def permAct : Equiv.Perm (Fin r) →* Aut (finFibrePow c r) :=
  MonoidHom.mk' (permAut c r) (fun σ τ => by
    ext : 1
    change permHom c r (σ * τ) = (permAut c r τ).hom ≫ (permAut c r σ).hom
    exact permHom_mul c r σ τ)

/--
@isnad1 id=eq.0h5v.s8.4ed5209772af from=translated src=- shape=bec7e284 vocab=8bf80883
-/
theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).hom = permHom c r σ := rfl

/--
@isnad1 id=eq.0h5v.s8.63d3646350d5 from=translated src=- shape=a0b9defd vocab=2fcc3acd
-/
theorem permAct_inv (σ : Equiv.Perm (Fin r)) : (permAct c r σ).inv = permHom c r σ⁻¹ := rfl

/--
@isnad1 id=eq.0h6v.s8.aa69d7cf1af4 from=translated src=- shape=3859b893 vocab=a70406b6
-/
@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h5v.s8.1287c80ae043 from=translated src=- shape=9399c1a2 vocab=4823d08c
-/
@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow

/--
@isnad1 id=le.1h5v.s9.36617ac82d11 from=translated src=- shape=790bb958 vocab=73119a4e
-/
theorem le_preimage_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ X) (q : X ⟶ Y) (h : g ≫ q = q)
    (V : Y.Opens) : q ⁻¹ᵁ V ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, h]

end AlgebraicGeometry

namespace AlgebraicCurve

open AlgebraicGeometry

structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where

  Csym : Scheme.{u}

  csym : Csym ⟶ Spec (CommRingCat.of k)

  π : finFibrePow c r ⟶ Csym

  π_comp_csym : π ≫ csym = finFibrePow.toBase c r

  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom ≫ π = π

  isFinite_π : IsFinite π

  surjective_π : Surjective π

  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔ ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.base x = x'

  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)

  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}

  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U

  integral : IsIntegral Csym

  proper : IsProper csym

  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve
