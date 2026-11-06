import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_BaseChangeGalois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

abbrev algebraAlong (φ : F →ₐ[K] F') : Algebra F F' := φ.toRingHom.toAlgebra

/--
@isnad1 id=isscalar.0h4v.s7.e228c3270179 from=translated src=- shape=326cc340 vocab=6d179758
-/
theorem isScalarTower_along (φ : F →ₐ[K] F') :
    letI := algebraAlong φ; IsScalarTower K F F' :=
  letI := algebraAlong φ
  IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm

/--
@isnad1 id=isintegr.1h4v.s7.ac5a9c5ff7f4 from=translated src=- shape=89b8970a vocab=b75377eb
-/
theorem isIntegral_along (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    letI := algebraAlong φ; Algebra.IsIntegral F F' :=
  letI := algebraAlong φ
  ⟨hφ⟩

variable (K) in

def FundamentalIdentityAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] : Prop :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  FundamentalIdentity K F F'

variable (K) in

def FiniteAlong (φ : F →ₐ[K] F') : Prop :=
  letI := algebraAlong φ
  Module.Finite F F'

variable (K) in

def NormFormulaAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) : Prop :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  Divisor.PushforwardNormFormula K F F'

variable (K) in

def finrankAlong (φ : F →ₐ[K] F') : ℕ :=
  letI := algebraAlong φ
  Module.finrank F F'

end AlongHom

namespace Divisor

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

section Pullback

variable [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pullbackAlong : Divisor K F →+ Divisor K F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Divisor.pullback F'

/--
@isnad1 id=isprinci.2h5v.s8.9965398240be from=translated src=- shape=97740af0 vocab=32c65492
-/
theorem isPrincipal_pullbackAlong {D : Divisor K F} (hD : D.IsPrincipal) :
    (pullbackAlong φ hφ D).IsPrincipal := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.isPrincipal_pullback hD

/--
@isnad1 id=eq.2h5v.s8.1bfbb78c756b from=translated src=- shape=6296193c vocab=d5a9051b
-/
theorem degree_pullbackAlong (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F) :
    degree (pullbackAlong φ hφ D) = (finrankAlong K φ : ℤ) * degree D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FundamentalIdentity K F F' := hFI
  exact Divisor.degree_pullback D

/--
@isnad1 id=mem.3h5v.s8.57adb2666940 from=translated src=- shape=b3a519e1 vocab=c9f98a7c
-/
theorem pullbackAlong_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    pullbackAlong φ hφ D ∈ degZero (K := K) (F := F') := by
  rw [mem_degZero, degree_pullbackAlong φ hφ hFI, mem_degZero.mp hD, mul_zero]

end Pullback

section Pushforward

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pushforwardAlong : Divisor K F' →+ Divisor K F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Divisor.pushforward F

/--
@isnad1 id=eq.1h5v.s8.fe7f2ad7ad60 from=translated src=- shape=bedeb1f5 vocab=001a3c94
-/
@[simp]
theorem degree_pushforwardAlong (D : Divisor K F') :
    degree (pushforwardAlong φ hφ D) = degree D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.degree_pushforward D

/--
@isnad1 id=mem.2h5v.s8.01ac74498812 from=translated src=- shape=dfde750b vocab=546c571d
-/
theorem pushforwardAlong_mem_degZero {D : Divisor K F'}
    (hD : D ∈ degZero (K := K) (F := F')) :
    pushforwardAlong φ hφ D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_pushforwardAlong]

/--
@isnad1 id=isprinci.4h5v.s8.ca3fe063655f from=translated src=- shape=75f8a9f0 vocab=903c00c7
-/
theorem isPrincipal_pushforwardAlong (hfin : FiniteAlong K φ)
    (hN : NormFormulaAlong K φ hfin) {D : Divisor K F'} (hD : D.IsPrincipal) :
    (pushforwardAlong φ hφ D).IsPrincipal := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  exact Divisor.isPrincipal_pushforward_of_normFormula hN hD

end Pushforward

end AlongHom

section Correspondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

def correspondence : Divisor K F →+ Divisor K F :=
  (pushforwardAlong ψ hψ).comp (pullbackAlong φ hφ)

/--
@isnad1 id=mem.4h6v.s8.a961cd853a93 from=translated src=- shape=c5a80764 vocab=4a1841c7
-/
theorem correspondence_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ degZero (K := K) (F := F) :=
  pushforwardAlong_mem_degZero ψ hψ (pullbackAlong_mem_degZero φ hφ hFI hD)

/--
@isnad1 id=mem.5h6v.s8.00601fdb1906 from=translated src=- shape=1da66468 vocab=4cafa0ca
-/
theorem correspondence_mem_principal (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ principal (K := K) (F := F) :=
  isPrincipal_pushforwardAlong ψ hψ hfin hN (isPrincipal_pullbackAlong φ hφ hD)

end Correspondence

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)
variable (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)

def degZeroCorrespondence :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.correspondence φ ψ hφ hψ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.correspondence_mem_degZero φ ψ hφ hψ hFI D.2)

def correspondence : Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (degZeroCorrespondence φ ψ hφ hψ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.correspondence_mem_principal φ ψ hφ hψ hfin hN hD)

end Pic0

end AlgebraicCurve

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def Place.restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    Place K F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  w.restrict F

def Place.ramificationIndexAlong (φ : F →ₐ[K] F') (w : Place K F') : ℕ :=
  letI := algebraAlong φ
  w.ramificationIndex F

end AlongPlaces

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K Z]

namespace Place

section Fiber

variable [HasPrincipalDivisors K Z]

end Fiber

end Place

end AlgebraicCurve

namespace AlgebraicCurve

section AlongTransport

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

end AlongTransport

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

section Intertwines

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

end Intertwines

end SemilinearAut

end AlgebraicCurve
