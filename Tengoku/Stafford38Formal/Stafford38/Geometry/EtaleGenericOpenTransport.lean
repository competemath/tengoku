module
public import Tengoku.Seed.RingTheory.Etale.Basic
public import Tengoku.Seed.RingTheory.Localization.Away.Basic
public import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization
public import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Stafford38.Geometry.EtaleGenericOpenTransport
universe u v

/-- The map from the finite integral chart algebra into the generic chart,
transported through the actual `Q_f ≃ B_f` equivalence.-/
def genericPointMap
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (f : Q) (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) : B →+* Localization.Away f :=
  (e.symm.toAlgHom.toRingHom).comp
    (algebraMap B (Localization.Away (algebraMap Q B f)))

/-- Denominators corresponding to elements of `B` outside the selected prime.-/
def genericOpenDenominators
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) : Submonoid (Localization.Away f) :=
  M.primeCompl.map (genericPointMap f e)

/-- The common generic open: the actual finite-birational open `B_f`, further
localized at the elements that are units at `B_M`, represented on `Q_f`.-/
abbrev genericOpenRing
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) : Type u :=
  Localization (genericOpenDenominators M f e)

/--
@isnad1 id=formally.0h5v.s9.5688943aae4b from=translated src=- shape=5a8dd7a6 vocab=c62df7fe
-/
theorem formallyEtale_genericOpenRing
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    Algebra.FormallyEtale Q (genericOpenRing M f e) := by
  letI : Algebra.FormallyEtale Q (Localization.Away f) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  letI : Algebra.FormallyEtale (Localization.Away f) (genericOpenRing M f e) :=
    Algebra.FormallyEtale.of_isLocalization (genericOpenDenominators M f e)
  exact Algebra.FormallyEtale.comp Q (Localization.Away f) (genericOpenRing M f e)

/-- The selected local ring maps to the common generic open. This map inverts
every element outside `M` by construction; it does not require `f ∉ M`.-/
def localPointToGenericOpen
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    Localization.AtPrime M →+* genericOpenRing M f e := by
  let φ : B →+* genericOpenRing M f e :=
    (algebraMap (Localization.Away f) (genericOpenRing M f e)).comp
      (genericPointMap f e)
  have hunit : ∀ s : M.primeCompl, IsUnit (φ s.1) := by
    intro s
    have hden : genericPointMap f e s.1 ∈ genericOpenDenominators M f e :=
      ⟨s.1, s.2, rfl⟩
    simpa [φ] using
      (IsLocalization.map_units (genericOpenRing M f e)
        ⟨genericPointMap f e s.1, hden⟩)
  exact IsLocalization.lift hunit

/-- The same generic arc induces the direct map from the selected local ring.-/
def localPointToField
    {B : Type v} [CommRing B] {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (ρ : B →+* L)
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) :
    Localization.AtPrime M →+* L :=
  IsLocalization.lift (M := M.primeCompl) (g := ρ) (fun s => hunitM s.1 s.2)

/--
@isnad1 id=eq.1h5v.s9.dc2b3542708c from=translated src=- shape=f9a0d175 vocab=27f841e3
-/
@[simp] theorem localPointToField_apply
    {B : Type v} [CommRing B] {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (ρ : B →+* L)
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) (b : B) :
    localPointToField M ρ hunitM (algebraMap B (Localization.AtPrime M) b) = ρ b := by
  simp [localPointToField, IsLocalization.lift_eq]

/-- A generic field-valued point of the integral chart algebra extends across
this same common open. The only additional requirement is that the generic
finite-birational denominator remain nonzero; it may vanish at the closed
point `M`.-/
def genericArcToGenericOpen
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (ρ : B →+* L)
    (hf : IsUnit (ρ (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) :
    genericOpenRing M f e →+* L := by
  let ρBf : Localization.Away (algebraMap Q B f) →+* L :=
    IsLocalization.lift (M := Submonoid.powers (algebraMap Q B f)) (g := ρ) (by
      intro s
      rcases (Submonoid.mem_powers_iff _ _).mp s.2 with ⟨n, hn⟩
      rw [← hn]
      simpa only [map_pow] using hf.pow n)
  let ρQf : Localization.Away f →+* L := ρBf.comp e.toAlgHom.toRingHom
  have hunit : ∀ s : genericOpenDenominators M f e, IsUnit (ρQf s.1) := by
    intro s
    obtain ⟨b, hbM, hsb⟩ := s.2
    have hpoint : ρQf s.1 = ρ b := by
      rw [← hsb]
      simp [ρQf, ρBf, genericPointMap, IsLocalization.lift_eq]
    rw [hpoint]
    exact hunitM b (by simpa using hbM)
  exact IsLocalization.lift hunit

/--
@isnad1 id=eq.0h6v.s10.bf25dbb6808b from=translated src=- shape=5b034a11 vocab=a8dafad1
-/
@[simp] theorem localPointToGenericOpen_apply
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) (b : B) :
    localPointToGenericOpen M f e (algebraMap B (Localization.AtPrime M) b) =
      (algebraMap (Localization.Away f) (genericOpenRing M f e))
      (genericPointMap f e b) := by
  simp [localPointToGenericOpen, IsLocalization.lift_eq]

/--
@isnad1 id=eq.2h8v.s10.28a1a15972d9 from=translated src=- shape=62eff346 vocab=1db10ae1
-/
@[simp] theorem genericArcToGenericOpen_apply
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (ρ : B →+* L)
    (hf : IsUnit (ρ (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) (b : B) :
    genericArcToGenericOpen M f e ρ hf hunitM
      ((algebraMap (Localization.Away f) (genericOpenRing M f e))
        (genericPointMap f e b)) = ρ b := by
  simp [genericArcToGenericOpen, genericPointMap, IsLocalization.lift_eq]

/-- The generic-open map and the point-local map induce the same arc on the
selected local ring. This does not require `f ∉ M`.
@isnad1 id=eq.2h7v.s9.3a5f35ed80d8 from=translated src=- shape=013c0f2a vocab=dce66be6
-/
theorem genericArcToGenericOpen_comp_localPointToGenericOpen
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (ρ : B →+* L)
    (hf : IsUnit (ρ (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) :
    (genericArcToGenericOpen M f e ρ hf hunitM).comp
      (localPointToGenericOpen M f e) = localPointToField M ρ hunitM := by
  apply IsLocalization.ringHom_ext M.primeCompl
  ext b
  simp [genericArcToGenericOpen_apply, localPointToGenericOpen_apply,
    localPointToField_apply]

/--
@isnad1 id=eq.2h8v.s10.8498946bdfe5 from=translated src=- shape=c8b1dbb4 vocab=debb9937
-/
@[simp] theorem genericArcToGenericOpen_base
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    {L : Type*} [Field L]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    (ρ : B →+* L)
    (hf : IsUnit (ρ (algebraMap Q B f)))
    (hunitM : ∀ b, b ∉ M → IsUnit (ρ b)) (q : Q) :
    genericArcToGenericOpen M f e ρ hf hunitM
      ((algebraMap (Localization.Away f) (genericOpenRing M f e))
        (algebraMap Q (Localization.Away f) q)) = ρ (algebraMap Q B q) := by
  have hpoint : genericPointMap f e (algebraMap Q B q) =
      algebraMap Q (Localization.Away f) q := by
    change e.symm (algebraMap B (Localization.Away (algebraMap Q B f))
      (algebraMap Q B q)) = algebraMap Q (Localization.Away f) q
    rw [← IsScalarTower.algebraMap_apply Q B (Localization.Away (algebraMap Q B f))]
    exact e.symm.commutes q
  rw [← hpoint]
  exact genericArcToGenericOpen_apply M f e ρ hf hunitM (algebraMap Q B q)

end Stafford38.Geometry.EtaleGenericOpenTransport
