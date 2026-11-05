import Tengoku.NsP23.P23.Presentation.QuotientDualTrace
import Tengoku.NsP23.P23.Presentation.KernelMinimality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical final-quotient H-L5

This module only assembles frozen quotient transport, direct-model H-L5, and
kernel-minimality APIs.  It does not concern arbitrary external quotients.
-/

namespace P23.Presentation

open P23.OneTie P23.Artin

noncomputable section

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- Intrinsic quotient type three forces exactly three selected roots.
@isnad1 id=eq.5h5v.s6.3b602eba2147 from=translated src=- shape=360f8ab3 vocab=d1c527d7
-/
theorem rootCard_eq_three_of_quotientType_eq_three
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S)
    (htype : quotientType k S hS hdom hlive = 3) :
    S.card = 3 :=
  (quotientType_eq_three_iff (k := k) S hS hdom hlive hanti).1 htype

/-- Intrinsic quotient nearly-Gorensteinness transports to the frozen direct
model predicate.
@isnad1 id=directne.4h5v.s6.adc9079b2ebd from=translated src=- shape=e1e8e1a3 vocab=3fdd9bb4
-/
theorem directNearlyGorenstein_of_quotientNearlyGorenstein
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hng : QuotientNearlyGorenstein k S hS hdom hlive) :
    DirectNearlyGorenstein k S hS hdom :=
  (quotientNearlyGorenstein_iff_directNearlyGorenstein
    (k := k) S hS hdom hlive).1 hng

/-- Mixed H-L5 in exact-border form for the canonical final polynomial
quotient.
@isnad1 id=ne.7h5v.s8.2f695aed013a from=translated src=- shape=8c5b4335 vocab=67e048df
-/
theorem mixed_quotient_HL5_border_ne_four
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 := by
  have hcard : S.card = 3 :=
    rootCard_eq_three_of_quotientType_eq_three
      (k := k) S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive hanti htype
  have hdirect : DirectNearlyGorenstein k S
      (nonempty_of_isLiveTie S hlive) ⟨ha, Or.inl ⟨hb, hc⟩⟩ :=
    directNearlyGorenstein_of_quotientNearlyGorenstein
      (k := k) S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive hng
  exact mixed_directModel_HL5_of_nearlyGorenstein
    (k := k) S ha hb hc hcard hlive hanti hdirect

/-- Pure H-L5 in exact-border form for the canonical final polynomial
quotient.
@isnad1 id=ne.6h4v.s8.22602b666503 from=translated src=- shape=567c54f7 vocab=1269496c
-/
theorem pure_quotient_HL5_border_ne_four
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive) :
    (borderFinset S).card ≠ 4 := by
  have hcard : S.card = 3 :=
    rootCard_eq_three_of_quotientType_eq_three
      (k := k) S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive hanti htype
  have hdirect : DirectNearlyGorenstein k S
      (nonempty_of_isLiveTie S hlive) ⟨ha, Or.inr ⟨hb, rfl⟩⟩ :=
    directNearlyGorenstein_of_quotientNearlyGorenstein
      (k := k) S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive hng
  exact pure_directModel_HL5_of_nearlyGorenstein
    (k := k) S ha hb hcard hlive hanti hdirect

/-- Mixed H-L5 in polynomial-kernel minimal-generator form.
@isnad1 id=ne.7h5v.s9.fcd24a6bbe47 from=translated src=- shape=73909b44 vocab=28975e52
-/
theorem mixed_quotient_HL5_kernel_mu_ne_five
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive) :
    idealGeneratorMu (k := k)
      (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5 := by
  intro hmu
  apply mixed_quotient_HL5_border_ne_four
    (k := k) S ha hb hc hlive hanti htype hng
  exact (kernel_mu_eq_five_iff_border_card_eq_four
    (k := k) S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive).1 hmu

/-- Pure H-L5 in polynomial-kernel minimal-generator form.
@isnad1 id=ne.6h4v.s9.81842f0005de from=translated src=- shape=c72ab4e5 vocab=8f3ad35b
-/
theorem pure_quotient_HL5_kernel_mu_ne_five
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    (htype : quotientType k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3)
    (hng : QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive) :
    idealGeneratorMu (k := k)
      (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5 := by
  intro hmu
  apply pure_quotient_HL5_border_ne_four
    (k := k) S ha hb hlive hanti htype hng
  exact (kernel_mu_eq_five_iff_border_card_eq_four
    (k := k) S (nonempty_of_isLiveTie S hlive)
      ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive).1 hmu

/-- Scope-explicit H-L5 package for the canonical final polynomial quotient.
It does not quantify over arbitrary external quotient rings.-/
structure CanonicalFiniteQuotientHL5 (k : Type*) [Field k] : Prop where
  mixedBorder : ∀ (a b c : ℕ) [NeZero a] (S : Finset (Normal a b c)),
    ∀ (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hlive : IsLiveTie S),
      IsRootAntichain S →
      quotientType k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3 →
      QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive →
      (borderFinset S).card ≠ 4
  mixedKernelMu : ∀ (a b c : ℕ) [NeZero a] (S : Finset (Normal a b c)),
    ∀ (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hlive : IsLiveTie S),
      IsRootAntichain S →
      quotientType k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive = 3 →
      QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inl ⟨hb, hc⟩⟩ hlive →
      idealGeneratorMu (k := k)
        (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5
  pureBorder : ∀ (a b : ℕ) [NeZero a] (S : Finset (Normal a b 0)),
    ∀ (ha : 2 ≤ a) (hb : 2 ≤ b) (hlive : IsLiveTie S),
      IsRootAntichain S →
      quotientType k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3 →
      QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive →
      (borderFinset S).card ≠ 4
  pureKernelMu : ∀ (a b : ℕ) [NeZero a] (S : Finset (Normal a b 0)),
    ∀ (ha : 2 ≤ a) (hb : 2 ≤ b) (hlive : IsLiveTie S),
      IsRootAntichain S →
      quotientType k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive = 3 →
      QuotientNearlyGorenstein k S (nonempty_of_isLiveTie S hlive)
        ⟨ha, Or.inr ⟨hb, rfl⟩⟩ hlive →
      idealGeneratorMu (k := k)
        (RingHom.ker (polyToDirectAlg (k := k) S).toRingHom) ≠ 5

/-- The canonical final quotient satisfies the mixed and pure H-L5
conclusions in both border and kernel-mu forms.
@isnad1 id=canonica.0h1v.s3.7e27ece37268 from=translated src=- shape=c6850a32 vocab=c0420f76
-/
theorem canonicalFiniteQuotient_HL5 : CanonicalFiniteQuotientHL5 k where
  mixedBorder := by
    intro a b c _ S ha hb hc hlive hanti htype hng
    exact mixed_quotient_HL5_border_ne_four
      (k := k) S ha hb hc hlive hanti htype hng
  mixedKernelMu := by
    intro a b c _ S ha hb hc hlive hanti htype hng
    exact mixed_quotient_HL5_kernel_mu_ne_five
      (k := k) S ha hb hc hlive hanti htype hng
  pureBorder := by
    intro a b _ S ha hb hlive hanti htype hng
    exact pure_quotient_HL5_border_ne_four
      (k := k) S ha hb hlive hanti htype hng
  pureKernelMu := by
    intro a b _ S ha hb hlive hanti htype hng
    exact pure_quotient_HL5_kernel_mu_ne_five
      (k := k) S ha hb hlive hanti htype hng

end

end P23.Presentation
