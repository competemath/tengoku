import Tengoku.NsP23.P23.Semigroup.NormalizedMonomialIdeal
import Tengoku.NsP23.P23.Semigroup.ChosenBaseTrace
import Tengoku.NsP23.P23.Presentation.QuotientDualTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Intrinsic type and ordinary-trace transport along the actual normalization
equivalence. No H-L5 theorem is invoked in this module. -/
namespace P23.Semigroup
noncomputable section
open P23.OneTie P23.Artin P23.Presentation
set_option maxHeartbeats 800000
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable {a b c : ℕ} [NeZero a]
variable (S : Finset (Normal a b c)) (hS : S.Nonempty)
variable (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
variable (E : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] FinitePolynomialQuotient ℚ S)

/--
@isnad1 id=iff.3h8v.s10.ac8b1cba827f from=translated src=- shape=a6c337dc vocab=b4e64c94
-/
theorem chosenCanonical_maximal_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    letI := chosenBaseIsLocalRing (k := ℚ) D i
    letI := quotientIsLocalRing (k := ℚ) S hS hd hl
    x ∈ IsLocalRing.maximalIdeal (ChosenBaseQuotient (k := ℚ) D i) ↔
      E x ∈ IsLocalRing.maximalIdeal (FinitePolynomialQuotient ℚ S) := by
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := quotientIsLocalRing (k := ℚ) S hS hd hl
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_iff_not.mpr (MulEquiv.isUnit_map (f := E.toRingEquiv.toMulEquiv)).symm

/--
@isnad1 id=iff.3h8v.s11.66cc638cbb3b from=translated src=- shape=6ba2b850 vocab=f44340d8
-/
theorem chosenCanonical_socle_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    x ∈ ChosenBaseSocle (k := ℚ) D i ↔ E x ∈ QuotientSocle (k := ℚ) S hS hd hl := by
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := quotientIsLocalRing (k := ℚ) S hS hd hl
  constructor
  · intro hx r hr
    have hr' := (chosenCanonical_maximal_mem_iff S hS hd hl E (E.symm r)).mpr
      (by simpa using hr)
    have hz := congrArg E (hx (E.symm r) hr')
    simpa using hz
  · intro hx r hr
    apply E.injective
    simpa using hx (E r) ((chosenCanonical_maximal_mem_iff S hS hd hl E r).mp hr)

def chosenCanonicalSocleEquiv
    (E : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] FinitePolynomialQuotient ℚ S) :
    ChosenBaseSocle (k := ℚ) D i ≃ₗ[ℚ]
    QuotientSocle (k := ℚ) S hS hd hl where
  toFun x := ⟨E x.1, (chosenCanonical_socle_mem_iff S hS hd hl E x.1).mp x.2⟩
  invFun y := ⟨E.symm y.1, (chosenCanonical_socle_mem_iff S hS hd hl E _).mpr (by simpa using y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

include E in
/--
@isnad1 id=eq.3h7v.s8.e79632a737e8 from=translated src=- shape=438a5822 vocab=273d2440
-/
theorem chosenCanonical_type_eq : quotientType ℚ S hS hd hl = chosenBaseType (k := ℚ) D i :=
  (chosenCanonicalSocleEquiv S hS hd hl E).finrank_eq.symm

/-- Genuine precomposition of the intrinsic k-linear duals.-/
def chosenCanonicalOmegaEquiv : ChosenBaseOmega ℚ D i ≃ₗ[ℚ] QuotientOmega ℚ S where
  toFun φ := φ.comp E.symm.toLinearMap
  invFun ψ := ψ.comp E.toLinearMap
  left_inv φ := by apply LinearMap.ext; intro x; exact congrArg φ (E.symm_apply_apply x)
  right_inv ψ := by apply LinearMap.ext; intro x; exact congrArg ψ (E.apply_symm_apply x)
  map_add' φ ψ := by apply LinearMap.ext; intro x; rfl
  map_smul' r φ := by apply LinearMap.ext; intro x; rfl

/--
@isnad1 id=eq.0h9v.s13.a3e563cd57fc from=translated src=- shape=afba086c vocab=41728575
-/
theorem chosenCanonicalOmegaEquiv_smul (x : ChosenBaseQuotient (k := ℚ) D i)
    (φ : ChosenBaseOmega ℚ D i) :
    chosenCanonicalOmegaEquiv S E (x • φ) = E x • chosenCanonicalOmegaEquiv S E φ := by
  apply LinearMap.ext
  intro r
  change φ (x * E.symm r) = φ (E.symm (E x * r))
  congr 1
  simp

/--
@isnad1 id=eq.0h9v.s13.4a1bc295cadd from=translated src=- shape=75d8776b vocab=b73d34ef
-/
theorem chosenCanonicalOmegaEquiv_symm_smul (x : FinitePolynomialQuotient ℚ S)
    (ψ : QuotientOmega ℚ S) :
    (chosenCanonicalOmegaEquiv S E).symm (x • ψ) =
      E.symm x • (chosenCanonicalOmegaEquiv S E).symm ψ := by
  apply (chosenCanonicalOmegaEquiv S E).injective
  rw [chosenCanonicalOmegaEquiv_smul]
  simp

def pushChosenCanonicalHom
    (F : ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i) :
    QuotientOmega ℚ S →ₗ[FinitePolynomialQuotient ℚ S] FinitePolynomialQuotient ℚ S where
  toFun ψ := E (F ((chosenCanonicalOmegaEquiv S E).symm ψ))
  map_add' x y := by simp
  map_smul' x ψ := by
    rw [chosenCanonicalOmegaEquiv_symm_smul, F.map_smul]
    simp [smul_eq_mul]

def pullChosenCanonicalHom
    (F : QuotientOmega ℚ S →ₗ[FinitePolynomialQuotient ℚ S] FinitePolynomialQuotient ℚ S) :
    ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i where
  toFun φ := E.symm (F (chosenCanonicalOmegaEquiv S E φ))
  map_add' x y := by simp
  map_smul' x φ := by
    rw [chosenCanonicalOmegaEquiv_smul, F.map_smul]
    simp [smul_eq_mul]

/--
@isnad1 id=iff.0h8v.s11.bd24e7425eb8 from=translated src=- shape=8d4a4661 vocab=a6839888
-/
theorem chosenCanonical_trace_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    x ∈ ChosenBaseTraceSubmodule (k := ℚ) D i ↔ E x ∈ QuotientTraceSubmodule ℚ S := by
  constructor
  · intro hx
    refine Submodule.iSup_induction
      (fun F : ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i => F.range)
      (motive := fun x => E x ∈ QuotientTraceSubmodule ℚ S) hx ?_ (by simp) ?_
    · intro F x hx
      obtain ⟨φ,rfl⟩ := hx
      exact quotientTrace_range_le S (pushChosenCanonicalHom S E F)
        ⟨chosenCanonicalOmegaEquiv S E φ, by simp [pushChosenCanonicalHom]⟩
    · intro x y hx hy; simpa using (QuotientTraceSubmodule ℚ S).add_mem hx hy
  · intro hx
    have hback : E.symm (E x) ∈ ChosenBaseTraceSubmodule (k := ℚ) D i := by
      refine Submodule.iSup_induction
        (fun F : QuotientOmega ℚ S →ₗ[FinitePolynomialQuotient ℚ S] FinitePolynomialQuotient ℚ S => F.range)
        (motive := fun x => E.symm x ∈ ChosenBaseTraceSubmodule (k := ℚ) D i) hx ?_ (by simp) ?_
      · intro F x hx
        obtain ⟨ψ,rfl⟩ := hx
        exact chosenBaseTrace_range_le D i (pullChosenCanonicalHom S E F)
          ⟨(chosenCanonicalOmegaEquiv S E).symm ψ, by simp [pullChosenCanonicalHom]⟩
      · intro x y hx hy; simpa using (ChosenBaseTraceSubmodule (k := ℚ) D i).add_mem hx hy
    simpa using hback

include E in
/--
@isnad1 id=iff.3h7v.s8.edba13dfbbfe from=translated src=- shape=b5178bb7 vocab=d9a472ab
-/
theorem chosenCanonical_ng_iff : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔
    QuotientNearlyGorenstein ℚ S hS hd hl := by
  unfold ChosenBaseNearlyGorenstein QuotientNearlyGorenstein
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := quotientIsLocalRing (k := ℚ) S hS hd hl
  constructor
  · intro h x hx
    have hm := (chosenCanonical_maximal_mem_iff S hS hd hl E (E.symm x)).mpr (by simpa using hx)
    have ht := (chosenCanonical_trace_mem_iff S E (E.symm x)).mp (h hm)
    simpa using ht
  · intro h x hx
    exact (chosenCanonical_trace_mem_iff S E x).mpr
      (h ((chosenCanonical_maximal_mem_iff S hS hd hl E x).mp hx))

/--
@isnad1 id=eq.1h2v.s5.8081f2fc2381 from=translated src=- shape=0f369139 vocab=fa86f4af
-/
theorem idealGeneratorMu_eq_minimal_card (I : Ideal (ThreePoly ℚ)) (n : ℕ)
    (hmin : HasMinimalGeneratorCard I n) : idealGeneratorMu I = n := by
  classical
  obtain ⟨G,hG,hc⟩ := hmin.1
  have hex : ∃ m : ℕ, ∃ H : Finset (ThreePoly ℚ), Ideal.span (↑H : Set (ThreePoly ℚ)) = I ∧ H.card = m :=
    ⟨n,G,hG,hc⟩
  rw [idealGeneratorMu, dite_eq_left hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex ⟨G,hG,hc⟩
  · obtain ⟨H,hH,hcH⟩ := Nat.find_spec hex
    rw [← hcH]
    exact hmin.2 H hH

namespace BudgetOneNormalizedPresentation
variable (B : BudgetOneNormalizedPresentation D i)
/--
@isnad1 id=eq.0h3v.s6.eed28ae9044e from=translated src=- shape=d89d5614 vocab=386c5f1b
-/
theorem canonicalOneTieType_eq_chosenBaseType :
    quotientType ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live =
      chosenBaseType (k := ℚ) D i :=
  chosenCanonical_type_eq _ _ _ _ B.chosenBaseEquivCanonicalOneTie

/--
@isnad1 id=iff.0h3v.s5.098b155694d1 from=translated src=- shape=94d1e42d vocab=2c330ddf
-/
theorem canonicalOneTie_ng_iff : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔
    QuotientNearlyGorenstein ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live :=
  chosenCanonical_ng_iff _ _ _ _ B.chosenBaseEquivCanonicalOneTie

/--
@isnad1 id=eq.0h3v.s5.3a07dc9ffcea from=translated src=- shape=4d1e496c vocab=76734e35
-/
theorem canonicalKernelMu_eq_rho :
    idealGeneratorMu (finitePresentationIdeal (k := ℚ) B.roots) = D.semigroupRho := by
  apply idealGeneratorMu_eq_minimal_card
  rw [← B.canonical_ideal]
  exact renamedChosenBaseIdeal_minimalGeneratorCard B.coordinates
end BudgetOneNormalizedPresentation

/-- Stable budget-one normalization boundary. Intrinsic transports are the
proved methods of this data, not definitions of type or trace.-/
abbrev BudgetOneOneTieNormalization := BudgetOneNormalizedPresentation

/--
@isnad1 id=nonempty.1h2v.s4.a4025940eacb from=translated src=- shape=97de8cf9 vocab=e0d91b93
-/
theorem budgetOneOneTieNormalization (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) : Nonempty (BudgetOneOneTieNormalization D i) :=
  budgetOneNormalizedPresentation D i hB

/-- Exact future input package. All dependent indices come from the same
normalization; no obstruction or rho exclusion is a field.-/
structure ChosenBaseCanonicalOneTieBridge (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  normalization : BudgetOneOneTieNormalization D i
  liveDomain : IsLiveParameterDomain normalization.coordinates.a normalization.coordinates.b normalization.coordinates.c
  liveTie : IsLiveTie normalization.roots
  rootAntichain : IsRootAntichain normalization.roots
  rootNonempty : normalization.roots.Nonempty
  chosenBaseEquivCanonicalOneTie : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ]
    FinitePolynomialQuotient ℚ normalization.roots
  canonicalTypeThree : quotientType ℚ normalization.roots rootNonempty liveDomain liveTie = 3
  canonicalNearlyGorenstein : QuotientNearlyGorenstein ℚ normalization.roots rootNonempty liveDomain liveTie
  canonicalKernelMuEqRho : idealGeneratorMu (finitePresentationIdeal (k := ℚ) normalization.roots) = D.semigroupRho
  borderCardEqRhoSubOne : (borderFinset normalization.roots).card = D.semigroupRho - 1

/--
@isnad1 id=nonempty.3h2v.s5.f779bfcad618 from=translated src=- shape=cdc56e98 vocab=962cb2ce
-/
theorem chosenBaseCanonicalOneTieBridge (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) (ht : D.semigroupType = 3)
    (hng : SemigroupNearlyGorenstein D) : Nonempty (ChosenBaseCanonicalOneTieBridge D i) := by
  obtain ⟨B⟩ := budgetOneOneTieNormalization D i hB
  exact ⟨⟨B,B.coordinates.liveDomain,B.roots_live,B.roots_antichain,B.roots_nonempty,
    B.chosenBaseEquivCanonicalOneTie,
    B.canonicalOneTieType_eq_chosenBaseType.trans ((chosenBaseType_eq_semigroupType D i).trans ht),
    B.canonicalOneTie_ng_iff.mp (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hng),
    B.canonicalKernelMu_eq_rho,B.border_card⟩⟩
end
end P23.Semigroup
