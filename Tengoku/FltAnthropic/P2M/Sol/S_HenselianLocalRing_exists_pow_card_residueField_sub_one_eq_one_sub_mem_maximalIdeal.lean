import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal

open IsLocalRing Polynomial

/--
@isnad1 id=isunit.0h1v.s5.9803fca5a843 from=translated src=- shape=ce9428e8 vocab=25cb136a
-/
theorem w2aux_unit
    {A : Type*} [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] :
    IsUnit ((Nat.card (IsLocalRing.ResidueField A) - 1 : ℕ) : A) := by
  have h1 : 1 < Nat.card (ResidueField A) := Finite.one_lt_card
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have h0 : (residue A) ((Nat.card (ResidueField A) - 1 : ℕ) : A) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_natCast] at h0
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  have hq0 : (Nat.card (ResidueField A) : ResidueField A) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  rw [Nat.cast_sub h1.le, hq0, Nat.cast_one, zero_sub, neg_eq_zero] at h0
  exact one_ne_zero h0

/--
@isnad1 id=mem.1h2v.s7.4f0bd88c7a27 from=translated src=- shape=cf120dea vocab=2fbf9d1b
-/
theorem w2aux_fermat
    {A : Type*} [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    {u : A} (hu : IsUnit u) :
    u ^ (Nat.card (IsLocalRing.ResidueField A) - 1) - 1 ∈ IsLocalRing.maximalIdeal A := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  have hū : residue A u ≠ 0 := IsUnit.ne_zero (hu.map (residue A))
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one (residue A u) hū

/--
@isnad1 id=ex.1h2v.s7.863685b64ffb from=translated src=- shape=0dc13783 vocab=55c6d427
-/
theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Finite (IsLocalRing.ResidueField A)] {u : A} (hu : IsUnit u) :
    ∃ ω : A, ω ^ (Nat.card (IsLocalRing.ResidueField A) - 1) = 1 ∧
      ω - u ∈ IsLocalRing.maximalIdeal A := by
  have hne : Nat.card (ResidueField A) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Finite.one_lt_card)
  set f : A[X] := X ^ (Nat.card (ResidueField A) - 1) - C 1 with hfdef
  have hfmonic : f.Monic := monic_X_pow_sub_C (1 : A) hne
  have hfeval : f.eval u ∈ maximalIdeal A := by
    simpa [hfdef] using w2aux_fermat hu
  have hfderiv : IsUnit (f.derivative.eval u) := by
    simp only [hfdef, derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_natCast, eval_pow, eval_X, map_natCast]
    exact (w2aux_unit).mul (hu.pow _)
  obtain ⟨ω, hroot, hmem⟩ := HenselianLocalRing.is_henselian f hfmonic u hfeval hfderiv
  refine ⟨ω, ?_, hmem⟩
  have h : ω ^ (Nat.card (ResidueField A) - 1) - 1 = 0 := by simpa [hfdef] using hroot
  linear_combination h
