import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2M
namespace FlatIffTorsionFree

section Ring

variable {R A : Type*} [CommRing R] [CommRing A]

/--
@isnad1 id=flat.1h3v.s7.b702687b88b2 from=translated src=- shape=14c40af2 vocab=8ea41254
-/
theorem ringHom_flat_of_torsionFree [IsDedekindDomain R] (r : R →+* A)
    (htf : ∀ (c : R) (s : A), c ≠ 0 → r c * s = 0 → s = 0) : r.Flat := by
  letI : Algebra R A := r.toAlgebra
  haveI : Module.IsTorsionFree R A := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c s hcs
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (htf c s hc (by simp [Algebra.smul_def] at hcs; exact hcs))
  show Module.Flat R A
  infer_instance

/--
@isnad1 id=eq.3h5v.s7.05a36a9a407d from=translated src=- shape=35333295 vocab=84f29684
-/
theorem torsionFree_of_ringHom_flat [IsDomain R] (r : R →+* A) (hr : r.Flat)
    (c : R) (s : A) (hc : c ≠ 0) (hcs : r c * s = 0) : s = 0 := by
  letI : Algebra R A := r.toAlgebra
  haveI : Module.Flat R A := hr
  haveI : Module.IsTorsionFree R A := inferInstance
  have hreg : IsSMulRegular A c := (IsRegular.of_ne_zero hc).isSMulRegular
  have h0 : c • s = c • (0 : A) := by
    rw [smul_zero, Algebra.smul_def]
    exact hcs
  exact hreg h0

end Ring

section Scheme

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/--
@isnad1 id=iff.0h4v.s11.36ad2cbca783 from=translated src=- shape=497907ed vocab=6ba794fe
-/
theorem flat_appLE_iff (U : X.affineOpens) :
    RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom ↔
      RingHom.Flat ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (U : X.Opens) le_top).hom := by
  rw [CommRingCat.hom_comp]
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).symm

/--
@isnad1 id=iff.0h3v.s12.1e825b59066f from=translated src=- shape=19ce697b vocab=7bc37530
-/
theorem flat_iff [IsDedekindDomain R] :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 := by
  constructor
  · intro hf U c s hc hcs
    have h1 : RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) f hf ⟨⊤, isAffineOpen_top _⟩ U le_top
    rw [flat_appLE_iff] at h1
    exact torsionFree_of_ringHom_flat _ h1 c s hc hcs
  · intro htf
    refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : X.affineOpens ↦ U)
      (iSup_affineOpens_eq_top X) (fun U ↦ ?_)
    rw [flat_appLE_iff]
    exact ringHom_flat_of_torsionFree _ (fun c s hc hcs ↦ htf U c s hc hcs)

end Scheme

end P2M.FlatIffTorsionFree

/--
@isnad1 id=iff.0h3v.s12.b6b5a2d385e0 from=translated src=- shape=3251ff75 vocab=7bc37530
-/
theorem solution
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 :=
  P2M.FlatIffTorsionFree.flat_iff f
