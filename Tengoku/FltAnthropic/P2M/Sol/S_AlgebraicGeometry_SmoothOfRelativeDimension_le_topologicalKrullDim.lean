import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace P2mSmoothDimGe

/--
@isnad1 id=eq.0h3v.s6.23d888cdd3fc from=translated src=- shape=81b6d922 vocab=b413bf3b
-/
theorem height_eq_of_isMaximal_mvPolynomial (L : Type u) [Field L] (n : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin n) L)) [h𝔭 : 𝔭.IsMaximal] : 𝔭.height = n := by
  have hform := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType L 𝔭
  have hquot : ringKrullDim (MvPolynomial (Fin n) L ⧸ 𝔭) = 0 :=
    ringKrullDim_eq_zero_of_isField (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭 |>.mp h𝔭)
  have hP : ringKrullDim (MvPolynomial (Fin n) L) = n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  rw [hquot, hP, add_zero] at hform
  exact_mod_cast hform

/--
@isnad1 id=le.2h4v.s6.65cfdcbd69bb from=translated src=- shape=5eddd7af vocab=e1c61cf0
-/
theorem le_ringKrullDim_of_isStandardSmoothOfRelativeDimension {L R : Type u} [CommRing L] (hL : IsField L)
    [CommRing R] [Nontrivial R] (φ : L →+* R) (n : ℕ) (hφ : φ.IsStandardSmoothOfRelativeDimension n) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R := by
  letI : Field L := hL.toField
  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial

  algebraize [g]

  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let 𝔭 : Ideal (MvPolynomial (Fin n) L) := 𝔪.comap g

  haveI : 𝔭.IsMaximal := by
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : Algebra.FiniteType (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      Algebra.FiniteType.trans (S := R) inferInstance inferInstance
    haveI : Module.Finite (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      finite_of_finite_type_of_isJacobsonRing (MvPolynomial (Fin n) L) (R ⧸ 𝔪)
    haveI : Algebra.IsIntegral (MvPolynomial (Fin n) L) (R ⧸ 𝔪) := inferInstance
    have hbot : (⊥ : Ideal (R ⧸ 𝔪)).IsMaximal := Ideal.bot_isMaximal
    have hcomap : ((⊥ : Ideal (R ⧸ 𝔪)).comap (algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ⊥
    have heq : (⊥ : Ideal (R ⧸ 𝔪)).comap (algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪)) = 𝔭 := by
      rw [show algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪) = (Ideal.Quotient.mk 𝔪).comp g from rfl,
        ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [heq] at hcomap

  have hht : 𝔭.height = n := height_eq_of_isMaximal_mvPolynomial L n 𝔭

  have hle : (n : ℕ∞) ≤ Order.height (⟨𝔭, inferInstance⟩ : PrimeSpectrum (MvPolynomial (Fin n) L)) := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hht]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle

  haveI : 𝔪.LiesOver l.last.asIdeal := ⟨by rw [hlast]; rfl⟩
  obtain ⟨l', hl'len, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔪
  calc (n : WithBot ℕ∞) = (l'.length : WithBot ℕ∞) := by rw [hl'len, hlen]
    _ ≤ ringKrullDim R := Order.LTSeries.length_le_krullDim l'

/--
@isnad1 id=le.0h4v.s6.05937a72f71e from=translated src=- shape=a12f8abb vocab=bc734d07
-/
theorem le_topologicalKrullDim {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x

  have hU' : U = ⊤ := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    have hx : f.base x ∈ U := e hxV
    rwa [Subsingleton.elim y (f.base x)]
  subst hU'
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

  have hne : Nonempty (PrimeSpectrum Γ(X, V)) := ⟨(hV.isoSpec.hom.base ⟨x, hxV⟩ : PrimeSpectrum Γ(X, V))⟩
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne

  have hring : (n : WithBot ℕ∞) ≤ ringKrullDim Γ(X, V) :=
    le_ringKrullDim_of_isStandardSmoothOfRelativeDimension hK _ n hf
  have hSpec : (n : WithBot ℕ∞) ≤ topologicalKrullDim (Spec Γ(X, V)) := by
    change (n : WithBot ℕ∞) ≤ topologicalKrullDim (PrimeSpectrum Γ(X, V))
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph] at hSpec
  exact hSpec.trans (topologicalKrullDim_subspace_le X (V : Set X))

end P2mSmoothDimGe

/--
@isnad1 id=le.0h4v.s6.05937a72f71e from=translated src=- shape=a12f8abb vocab=bc734d07
-/
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X :=
  P2mSmoothDimGe.le_topologicalKrullDim f n
