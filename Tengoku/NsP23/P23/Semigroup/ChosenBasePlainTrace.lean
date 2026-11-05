import Tengoku.NsP23.P23.Semigroup.ChosenBasePlainQuotient
import Tengoku.NsP23.P23.Semigroup.ChosenBaseTrace
import Tengoku.NsP23.P23.Monomial.PlainSocle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Intrinsic socle, dual, ordinary trace and NG transport along the genuine
chosen-base to plain polynomial quotient equivalence. No H-L5 is used. -/
namespace P23.Semigroup
noncomputable section
open P23.Monomial
set_option maxHeartbeats 800000
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (R : Finset PlainExp) (hR : R.Nonempty)
variable (E : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ R)

theorem chosenPlain_maximal_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    letI := chosenBaseIsLocalRing (k := ℚ) D i
    letI := plainIsLocalRing (k := ℚ) R hR
    x ∈ IsLocalRing.maximalIdeal (ChosenBaseQuotient (k := ℚ) D i) ↔
      E x ∈ IsLocalRing.maximalIdeal (PlainMonomialArtin ℚ R) := by
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := plainIsLocalRing (k := ℚ) R hR
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_iff_not.mpr (MulEquiv.isUnit_map (f := E.toRingEquiv.toMulEquiv)).symm

theorem chosenPlain_socle_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    x ∈ ChosenBaseSocle (k := ℚ) D i ↔ E x ∈ PlainDirectSocle (k := ℚ) R hR := by
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := plainIsLocalRing (k := ℚ) R hR
  have hmax : IsLocalRing.maximalIdeal (PlainMonomialArtin ℚ R) = plainAugmentationIdeal R hR :=
    plainMaximalIdeal_eq_augmentationIdeal R hR _ (IsLocalRing.maximalIdeal.isMaximal _)
  constructor
  · intro hx r hr
    have hr' := (chosenPlain_maximal_mem_iff R hR E (E.symm r)).mpr
      (by simpa [hmax] using hr)
    have hz := congrArg E (hx (E.symm r) hr')
    simpa using hz
  · intro hx r hr
    apply E.injective
    simpa using hx (E r) (by simpa [hmax] using (chosenPlain_maximal_mem_iff R hR E r).mp hr)

def chosenPlainSocleEquiv
    (E : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ R) :
    ChosenBaseSocle (k := ℚ) D i ≃ₗ[ℚ]
    PlainDirectSocle (k := ℚ) R hR where
  toFun x := ⟨E x.1, (chosenPlain_socle_mem_iff R hR E x.1).mp x.2⟩
  invFun y := ⟨E.symm y.1, (chosenPlain_socle_mem_iff R hR E _).mpr (by simpa using y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

include E in
theorem chosenPlain_type_eq : plainDirectType ℚ R hR = chosenBaseType (k := ℚ) D i :=
  (chosenPlainSocleEquiv R hR E).finrank_eq.symm

/-- Genuine precomposition of the intrinsic k-linear duals.-/
def chosenPlainOmegaEquiv : ChosenBaseOmega ℚ D i ≃ₗ[ℚ] PlainOmega ℚ R where
  toFun φ := φ.comp E.symm.toLinearMap
  invFun ψ := ψ.comp E.toLinearMap
  left_inv φ := by apply LinearMap.ext; intro x; exact congrArg φ (E.symm_apply_apply x)
  right_inv ψ := by apply LinearMap.ext; intro x; exact congrArg ψ (E.apply_symm_apply x)
  map_add' φ ψ := by apply LinearMap.ext; intro x; rfl
  map_smul' r φ := by apply LinearMap.ext; intro x; rfl

theorem chosenPlainOmegaEquiv_smul (x : ChosenBaseQuotient (k := ℚ) D i)
    (φ : ChosenBaseOmega ℚ D i) :
    chosenPlainOmegaEquiv R E (x • φ) = E x • chosenPlainOmegaEquiv R E φ := by
  apply LinearMap.ext
  intro r
  change φ (x * E.symm r) = φ (E.symm (E x * r))
  congr 1
  simp

theorem chosenPlainOmegaEquiv_symm_smul (x : PlainMonomialArtin ℚ R)
    (ψ : PlainOmega ℚ R) :
    (chosenPlainOmegaEquiv R E).symm (x • ψ) =
      E.symm x • (chosenPlainOmegaEquiv R E).symm ψ := by
  apply (chosenPlainOmegaEquiv R E).injective
  rw [chosenPlainOmegaEquiv_smul]
  simp

def pushChosenPlainHom
    (F : ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i) :
    PlainOmega ℚ R →ₗ[PlainMonomialArtin ℚ R] PlainMonomialArtin ℚ R where
  toFun ψ := E (F ((chosenPlainOmegaEquiv R E).symm ψ))
  map_add' x y := by simp
  map_smul' x ψ := by
    rw [chosenPlainOmegaEquiv_symm_smul, F.map_smul]
    simp [smul_eq_mul]

def pullChosenPlainHom
    (F : PlainOmega ℚ R →ₗ[PlainMonomialArtin ℚ R] PlainMonomialArtin ℚ R) :
    ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i where
  toFun φ := E.symm (F (chosenPlainOmegaEquiv R E φ))
  map_add' x y := by simp
  map_smul' x φ := by
    rw [chosenPlainOmegaEquiv_smul, F.map_smul]
    simp [smul_eq_mul]

theorem chosenPlain_trace_mem_iff (x : ChosenBaseQuotient (k := ℚ) D i) :
    x ∈ ChosenBaseTraceSubmodule (k := ℚ) D i ↔ E x ∈ PlainTraceSubmodule ℚ R := by
  constructor
  · intro hx
    refine Submodule.iSup_induction
      (fun F : ChosenBaseOmega ℚ D i →ₗ[ChosenBaseQuotient (k := ℚ) D i] ChosenBaseQuotient (k := ℚ) D i => F.range)
      (motive := fun x => E x ∈ PlainTraceSubmodule ℚ R) hx ?_ (by simp) ?_
    · intro F x hx
      obtain ⟨φ,rfl⟩ := hx
      exact plainTrace_range_le R (pushChosenPlainHom R E F)
        ⟨chosenPlainOmegaEquiv R E φ, by simp [pushChosenPlainHom]⟩
    · intro x y hx hy; simpa using (PlainTraceSubmodule ℚ R).add_mem hx hy
  · intro hx
    have hback : E.symm (E x) ∈ ChosenBaseTraceSubmodule (k := ℚ) D i := by
      refine Submodule.iSup_induction
        (fun F : PlainOmega ℚ R →ₗ[PlainMonomialArtin ℚ R] PlainMonomialArtin ℚ R => F.range)
        (motive := fun x => E.symm x ∈ ChosenBaseTraceSubmodule (k := ℚ) D i) hx ?_ (by simp) ?_
      · intro F x hx
        obtain ⟨ψ,rfl⟩ := hx
        exact chosenBaseTrace_range_le D i (pullChosenPlainHom R E F)
          ⟨(chosenPlainOmegaEquiv R E).symm ψ, by simp [pullChosenPlainHom]⟩
      · intro x y hx hy; simpa using (ChosenBaseTraceSubmodule (k := ℚ) D i).add_mem hx hy
    simpa using hback

include E in
theorem chosenPlain_ng_iff : ChosenBaseNearlyGorenstein (k := ℚ) D i ↔
    PlainDirectNearlyGorenstein ℚ R hR := by
  unfold ChosenBaseNearlyGorenstein PlainDirectNearlyGorenstein
  letI := chosenBaseIsLocalRing (k := ℚ) D i
  letI := plainIsLocalRing (k := ℚ) R hR
  have hmax : IsLocalRing.maximalIdeal (PlainMonomialArtin ℚ R) = plainAugmentationIdeal R hR :=
    plainMaximalIdeal_eq_augmentationIdeal R hR _ (IsLocalRing.maximalIdeal.isMaximal _)
  rw [← hmax]
  constructor
  · intro h x hx
    have hm := (chosenPlain_maximal_mem_iff R hR E (E.symm x)).mpr (by simpa using hx)
    have ht := (chosenPlain_trace_mem_iff R E (E.symm x)).mp (h hm)
    simpa using ht
  · intro h x hx
    exact (chosenPlain_trace_mem_iff R E x).mpr
      (h ((chosenPlain_maximal_mem_iff R hR E x).mp hx))

end
end P23.Semigroup
