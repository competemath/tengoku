import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @solution` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt

set_option autoImplicit false

theorem solution
    (m : ℕ)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
        cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓm) := by
  intro A hA τ hτ
  have hm0 : m ≠ 0 := fun h => hℓm (h ▸ dvd_zero ℓ)
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m

  have hfr : τ ζ = ζ ^ ℓ :=
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ m hA hτ
      (hℓ.coprime_iff_not_dvd.mpr hℓm).symm ζ hζ.pow_eq_one

  have hkey : ζ ^ ((cyc τ : ZMod m)).val = ζ ^ ℓ := (hcyc τ ζ hζ.pow_eq_one).symm.trans hfr
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, Nat.pos_of_ne_zero hm0, hζ.pow_eq_one⟩
  have hmod : ((cyc τ : ZMod m)).val ≡ ℓ [MOD m] := by
    have h := hfin.pow_eq_pow_iff_modEq.mp hkey
    rwa [← hζ.eq_orderOf] at h
  refine Units.ext ?_
  rw [ZMod.coe_unitOfCoprime]
  have hv : (((cyc τ : ZMod m)).val : ZMod m) = ((ℓ : ℕ) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rwa [ZMod.natCast_val, ZMod.cast_id] at hv

