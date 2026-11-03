/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Module.GradedModule.Localization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transporting graded-module localizations along equal denominators

The equivalences in this file change only the name of an equal power
submonoid.  They are generic graded-module localization operations; Čech
complexes consume them when comparing product and monomial denominators.
-/

noncomputable section

namespace GradedModule.DegreeZeroLocalization

variable {ι A M σA σM : Type*}
variable [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable {𝒜 : ι → σA} {𝓜 : ι → σM}
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-- Transport a degree-zero localization along an equality of denominators.
The element never moves; only the name of its type does.-/
noncomputable def powersCongr {f g : A} (h : f = g) :
    DegreeZeroLocalization 𝒜 𝓜 (.powers f) ≃+ DegreeZeroLocalization 𝒜 𝓜 (.powers g) := by
  subst h
  exact AddEquiv.refl _

/--
@isnad1 id=eq.4h12v.s13.235af7802d2f from=translated src=- shape=a16942f8 vocab=92c5e832
-/
theorem powersCongr_awayMk {f g : A} (h : f = g) {e : ι} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 e)
    (n : ℕ) (m : M) (hm : m ∈ 𝓜 (n • e)) :
    powersCongr (𝒜 := 𝒜) (𝓜 := 𝓜) h (awayMk hf n m hm) = awayMk hg n m hm := by
  subst h
  rfl

/--
@isnad1 id=eq.2h11v.s14.09d5fe2c9735 from=translated src=- shape=f9feb03e vocab=25d72c33
-/
theorem powersCongr_trans {f g l : A} (h₁ : f = g) (h₂ : g = l)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    powersCongr h₂ (powersCongr h₁ z) = powersCongr (h₁.trans h₂) z := by
  subst h₁
  subst h₂
  rfl

/--
@isnad1 id=eq.1h10v.s14.3d14a5fc41ec from=translated src=- shape=9fbb4809 vocab=ac0933ab
-/
theorem powersCongr_symm_apply_apply {f g : A} (h : f = g)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    (powersCongr (𝒜 := 𝒜) (𝓜 := 𝓜) h).symm (powersCongr h z) = z := by
  subst h
  rfl

/-- Absorb an inverse transport into a forward one.
@isnad1 id=eq.3h11v.s14.609f2baab667 from=translated src=- shape=68393427 vocab=ac0933ab
-/
theorem powersCongr_symm_trans {f g l : A} (h₀ : f = g) (e₁ : f = l) (h₁ : g = l)
    (u : DegreeZeroLocalization 𝒜 𝓜 (.powers g)) :
    powersCongr (𝒜 := 𝒜) (𝓜 := 𝓜) e₁ ((powersCongr h₀).symm u) = powersCongr h₁ u := by
  subst h₀
  subst e₁
  rfl

/-- Transport a face map along equalities of both denominators and of the
multiplier.
@isnad1 id=eq.9h15v.s15.b08f35d9fade from=translated src=- shape=cfc99c1c vocab=e002505e
-/
theorem powersCongr_faceMap {g₁ g₁' g₂ g₂' w w' : A} {e : ι}
    (e₁ : g₁ = g₁') (e₂ : g₂ = g₂') (e₃ : w = w')
    (hw : w ∈ 𝒜 e) (hw' : w' ∈ 𝒜 e)
    (hgw : g₁ * w ∈ Submonoid.powers g₂) (hgw' : g₁' * w' ∈ Submonoid.powers g₂')
    (hg : g₁ * w = g₂) (hg' : g₁' * w' = g₂')
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers g₁)) :
    powersCongr (𝒜 := 𝒜) (𝓜 := 𝓜) e₂ (faceMap (𝓜 := 𝓜) hw hgw hg z) =
      faceMap (𝓜 := 𝓜) hw' hgw' hg' (powersCongr e₁ z) := by
  subst e₁
  subst e₂
  subst e₃
  rfl

end GradedModule.DegreeZeroLocalization
