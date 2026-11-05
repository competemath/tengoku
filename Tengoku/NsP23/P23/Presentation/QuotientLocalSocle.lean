import Tengoku.NsP23.P23.Presentation.FinitePolynomialQuotient
import Tengoku.NsP23.P23.Artin.LocalSocle
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Locality, socle, and type of the final polynomial quotient

The definitions in this file live on the quotient itself.  The frozen
algebra equivalence to the direct finite model is used only to prove exact
transport theorems.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie P23.Artin

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

private abbrev Q (k : Type*) [Field k] (S : Finset (Normal a b c)) :=
  FinitePolynomialQuotient k S

private abbrev A (k : Type*) [Field k] (S : Finset (Normal a b c)) :=
  MonomialArtin k S

/-- The final polynomial quotient is local, transported across the frozen
final-presentation algebra equivalence.
@isnad1 id=islocalr.3h5v.s6.860b553d0db0 from=translated src=- shape=ee94638b vocab=6260c981
-/
theorem quotientIsLocalRing (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    IsLocalRing (Q k S) := by
  letI := directIsLocalRing (k := k) S hS hdom hlive
  exact RingEquiv.isLocalRing
    (finitePolynomialQuotientEquiv (k := k) S hS hdom).symm.toRingEquiv

/-- The transported augmentation ideal on the final quotient.-/
def quotientAugmentationIdeal (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c) :
    Ideal (Q k S) :=
  (augmentationIdeal (k := k) S hS hdom).comap
    (finitePolynomialQuotientEquiv (k := k) S hS hdom).toRingHom

/--
@isnad1 id=iff.2h6v.s9.669b9cf61267 from=translated src=- shape=710358d5 vocab=fcab9aa2
-/
theorem mem_quotientAugmentationIdeal_iff
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (q : Q k S) :
    q ∈ quotientAugmentationIdeal (k := k) S hS hdom ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        augmentationIdeal (k := k) S hS hdom :=
  Iff.rfl

/-- Mathlib's intrinsic maximal ideal on the quotient is exactly the
transported augmentation ideal.
@isnad1 id=eq.3h5v.s7.26efb8ae5f1f from=translated src=- shape=f9dc9b2f vocab=02122b8b
-/
theorem quotientMaximalIdeal_eq_augmentationIdeal
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    letI := quotientIsLocalRing (k := k) S hS hdom hlive
    IsLocalRing.maximalIdeal (Q k S) =
      quotientAugmentationIdeal (k := k) S hS hdom := by
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  have hmax : (quotientAugmentationIdeal (k := k) S hS hdom).IsMaximal :=
    (augmentationIdeal_isMaximal (k := k) S hS hdom).comap_bijective
      (finitePolynomialQuotientEquiv (k := k) S hS hdom).toRingHom
      (finitePolynomialQuotientEquiv (k := k) S hS hdom).bijective
  exact (IsLocalRing.eq_maximalIdeal hmax).symm

/-- Exact maximal-ideal membership transport.
@isnad1 id=iff.3h6v.s9.b13d44132295 from=translated src=- shape=21250928 vocab=c78d3819
-/
theorem quotientMaximalIdeal_mem_iff
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (q : Q k S) :
    letI := quotientIsLocalRing (k := k) S hS hdom hlive
    q ∈ IsLocalRing.maximalIdeal (Q k S) ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        augmentationIdeal (k := k) S hS hdom := by
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  rw [quotientMaximalIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive]
  rfl

/-- Intrinsic quotient socle: the annihilator of the quotient's own maximal
ideal.  It is not defined as a preimage of the direct socle.-/
def QuotientSocle (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    Submodule k (Q k S) := by
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  exact {
    carrier := {q | ∀ r ∈ IsLocalRing.maximalIdeal (Q k S), r * q = 0}
    zero_mem' := by simp
    add_mem' := by
      intro q q' hq hq' r hr
      simp [mul_add, hq r hr, hq' r hr]
    smul_mem' := by
      intro t q hq r hr
      rw [mul_smul_comm, hq r hr, smul_zero]
  }

/-- Intrinsic quotient socle membership is exactly direct-socle membership
under the frozen algebra equivalence.
@isnad1 id=iff.3h6v.s10.a7744ea52afe from=translated src=- shape=15024bbb vocab=717d7e1e
-/
theorem mem_quotientSocle_iff_equiv_mem_directSocle
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (q : Q k S) :
    q ∈ QuotientSocle (k := k) S hS hdom hlive ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        DirectSocle (k := k) S hS hdom := by
  let E := finitePolynomialQuotientEquiv (k := k) S hS hdom
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  constructor
  · intro hq r hr
    let q' : Q k S := E.symm r
    have hq'max : q' ∈ IsLocalRing.maximalIdeal (Q k S) :=
      (quotientMaximalIdeal_mem_iff (k := k) S hS hdom hlive q').2 (by
        simpa [q', E] using hr)
    have hz := hq q' hq'max
    have := congrArg E hz
    simpa [q', E] using this
  · intro hq r hr
    have hEr : E r ∈ augmentationIdeal (k := k) S hS hdom :=
      (quotientMaximalIdeal_mem_iff (k := k) S hS hdom hlive r).1 hr
    have hz := hq (E r) hEr
    apply E.injective
    simpa [E] using hz

/-- Exact linear equivalence of intrinsic quotient and direct socles.-/
noncomputable def quotientSocleEquivDirectSocle
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    QuotientSocle (k := k) S hS hdom hlive ≃ₗ[k]
      DirectSocle (k := k) S hS hdom where
  toFun q := ⟨finitePolynomialQuotientEquiv (k := k) S hS hdom q.1,
    (mem_quotientSocle_iff_equiv_mem_directSocle
      (k := k) S hS hdom hlive q.1).1 q.2⟩
  invFun v := ⟨(finitePolynomialQuotientEquiv (k := k) S hS hdom).symm v.1,
    (mem_quotientSocle_iff_equiv_mem_directSocle
      (k := k) S hS hdom hlive _).2 (by simpa using v.2)⟩
  left_inv q := by ext; simp
  right_inv v := by ext; simp
  map_add' q q' := by ext; simp
  map_smul' t q := by ext; simp

/-- The intrinsic quotient socle has dimension equal to the selected-root
cardinality.
@isnad1 id=eq.4h5v.s10.ac29d836fd8c from=translated src=- shape=bf66d9b7 vocab=dd055ffc
-/
theorem quotientSocle_finrank_eq_card
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    Module.finrank k (QuotientSocle (k := k) S hS hdom hlive) = S.card := by
  rw [(quotientSocleEquivDirectSocle (k := k) S hS hdom hlive).finrank_eq]
  exact directSocle_finrank_eq_card (k := k) S hS hdom hlive hanti

/-- Algebraic type of the final polynomial quotient.-/
def quotientType (k : Type*) [Field k] (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) : ℕ :=
  Module.finrank k (QuotientSocle (k := k) S hS hdom hlive)

/--
@isnad1 id=eq.4h5v.s6.110b8c6cb26c from=translated src=- shape=6f9dded6 vocab=d1c527d7
-/
theorem quotientType_eq_rootCard
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    quotientType k S hS hdom hlive = S.card :=
  quotientSocle_finrank_eq_card (k := k) S hS hdom hlive hanti

/--
@isnad1 id=iff.4h5v.s6.a3be9724a4a8 from=translated src=- shape=0c17cfbf vocab=d1c527d7
-/
theorem quotientType_eq_three_iff
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    quotientType k S hS hdom hlive = 3 ↔ S.card = 3 := by
  rw [quotientType_eq_rootCard (k := k) S hS hdom hlive hanti]

end

end P23.Presentation
