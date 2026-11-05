import Tengoku.NsP23.P23.Presentation.HL5Quotient
import Tengoku.NsP23.P23.OneTie.CoverBorderBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Local one-tie dominance only. No numerical-semigroup realization or AS. -/
namespace P23.Presentation
noncomputable section
open P23.OneTie P23.Artin Classical
variable {k : Type*} [Field k] {a b c : ℕ} [NeZero a]

/--
@isnad1 id=hasdirec.6h5v.s6.5d6d02f5191e from=translated src=- shape=e2ad136a vocab=b21dc0c4
-/
theorem canonical_ng_hasDirectionalCentres
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : 2≤S.card)
    (hn : QuotientNearlyGorenstein k S hS hd hl) : HasDirectionalCentres S := by
  exact hasDirectionalCentres_of_variablesInTrace (k:=k) S hS hc ha hd hl
    ((directNearlyGorenstein_iff_variablesInTrace S hS hd hl).mp
      (directNearlyGorenstein_of_quotientNearlyGorenstein S hS hd hl hn))

/--
@isnad1 id=le.3h5v.s6.a0eadb9e989f from=translated src=- shape=6869469d vocab=5323ab20
-/
theorem oneTie_nondominant_kernel_mu_le_type_plus_three
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (h : CoverHypotheses S) :
    idealGeneratorMu (finitePresentationIdeal (k:=k) S) ≤ S.card+3 := by
  have hm := polyToDirectAlg_kernel_mu_eq_one_add_borderCard (k:=k) S hS hd h.live_tie
  rw [polyToDirectAlg_ker (k:=k) S hS hd] at hm
  have hb := oneTie_nondominant_border_card_le_type_plus_two S h
  omega

/--
@isnad1 id=ex.7h5v.s7.b665a5206f71 from=translated src=- shape=a40e6f8d vocab=6016cc9d
-/
theorem oneTie_ng_kernel_mu_ge_type_plus_four_has_dominant
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : S.card=2 ∨ S.card=3)
    (hn : QuotientNearlyGorenstein k S hS hd hl)
    (hm : S.card+4 ≤ idealGeneratorMu (finitePresentationIdeal (k:=k) S)) :
    ∃ s∈S, IsDominantRoot S s := by
  by_contra hh
  have hno : ∀ s∈S, ¬IsDominantRoot S s := by simpa using hh
  have hlo : 2≤S.card := by omega
  have hhi : S.card≤3 := by omega
  have hc := canonical_ng_hasDirectionalCentres S hS hd hl ha hlo hn
  have hb := oneTie_nondominant_kernel_mu_le_type_plus_three (k:=k) S hS hd
    ⟨hd.1,hd.2,hl,hlo,hhi,ha,hc,hno⟩
  omega

end
end P23.Presentation
