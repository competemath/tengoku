import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow

set_option autoImplicit false

open scoped NNReal

open IsLocalRing in
/--
@isnad1 id=eq.0h2v.s6.bf6b80fcef01 from=translated src=- shape=5aa45293 vocab=c7142b22
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) = Nat.card (IsLocalRing.ResidueField R) ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ k : ℕ, IsLocalRing.maximalIdeal R ^ k = Ideal.span {π ^ k} := fun k => by rw [hmax, Ideal.span_singleton_pow]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_of_subsingleton (0 : R ⧸ (⊤ : Ideal R))
  | succ n ih =>

    set T : Submodule R R := IsLocalRing.maximalIdeal R ^ (n + 1) with hT
    set S : Submodule R R := IsLocalRing.maximalIdeal R ^ n with hS
    have hTS : T ≤ S := Ideal.pow_le_pow_right (Nat.le_succ n)
    have hmul := Submodule.card_quotient_mul_card_quotient S T hTS

    let f : R →ₗ[R] R ⧸ T := T.mkQ ∘ₗ LinearMap.lsmul R R (π ^ n)
    have hf : ∀ r, f r = T.mkQ (π ^ n * r) := fun r => rfl
    have hker : LinearMap.ker f = IsLocalRing.maximalIdeal R := by
      ext r
      rw [LinearMap.mem_ker, hf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT, hpow, hmax,
        Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hπ0)]
    have hrange : LinearMap.range f = Submodule.map T.mkQ S := by
      ext y
      constructor
      · rintro ⟨r, rfl⟩
        refine ⟨π ^ n * r, ?_, rfl⟩
        show π ^ n * r ∈ S
        rw [hS, hpow, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ S := hx
        rw [hS, hpow, Ideal.mem_span_singleton] at hx'
        obtain ⟨r, rfl⟩ := hx'
        exact ⟨r, rfl⟩
    let g : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] R ⧸ T := (IsLocalRing.maximalIdeal R).liftQ f hker.ge
    have hginj : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
    have hgrange : LinearMap.range g = Submodule.map T.mkQ S := by
      rw [Submodule.range_liftQ, hrange]
    have hcardS : Nat.card (Submodule.map T.mkQ S) = Nat.card (IsLocalRing.ResidueField R) := by
      rw [← hgrange]
      exact (Nat.card_congr (LinearEquiv.ofInjective g hginj).toEquiv).symm
    rw [← hmul, hcardS, ih, pow_succ, mul_comm]
