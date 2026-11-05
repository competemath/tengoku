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

theorem chosenCanonical_maximal_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    letI := chosenBaseIsLocalRing (k := ℚ) D i
    letI := quotientIsLocalRing (k := ℚ) S hS hd hl
    x ∈ IsLocalRing.maximalIdeal (ChosenBaseQuotient (k := ℚ) D i) ↔
      E x ∈ IsLocalRing.maximalIdeal (FinitePolynomialQuotient ℚ S) := by
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := quotientIsLocalRing (k := ℚ) S hS hd hl
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_iff_not.mpr (MulEquiv.isUnit_map (f := E.toRingEquiv.toMulEquiv)).symm

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

theorem chosenCanonicalOmegaEquiv_smul (x : ChosenBaseQuotient (k := ℚ) D i)
    (φ : ChosenBaseOmega ℚ D i) :
    chosenCanonicalOmegaEquiv S E (x • φ) = E x • chosenCanonicalOmegaEquiv S E φ := by
  apply LinearMap.ext
  intro r
  change φ (x * E.symm r) = φ (E.symm (E x * r))
  congr 1
  simp

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
theorem canonicalOneTieType_eq_chosenBaseType :
    quotientType ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live =
      chosenBaseType (k := ℚ) D i :=
  chosenCanonical_type_eq _ _ _ _ B.chosenBaseEquivCanonicalOneTie

theorem canonicalOneTie_ng_iff : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔
    QuotientNearlyGorenstein ℚ B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live :=
  chosenCanonical_ng_iff _ _ _ _ B.chosenBaseEquivCanonicalOneTie

theorem canonicalKernelMu_eq_rho :
    idealGeneratorMu (finitePresentationIdeal (k := ℚ) B.roots) = D.semigroupRho := by
  apply idealGeneratorMu_eq_minimal_card
  rw [← B.canonical_ideal]
  exact renamedChosenBaseIdeal_minimalGeneratorCard B.coordinates
end BudgetOneNormalizedPresentation

/-- Stable budget-one normalization boundary. Intrinsic transports are the
proved methods of this data, not definitions of type or trace.-/
abbrev BudgetOneOneTieNormalization := BudgetOneNormalizedPresentation

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
