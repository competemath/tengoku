import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularProlongation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace R4Sep1k

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/--
@isnad1 id=le.1h4v.s6.8b7be70d1b92 from=translated src=- shape=c89bac7e vocab=d89c618f
-/
theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

/--
@isnad1 id=iff.1h4v.s7.1dd615751220 from=translated src=- shape=8604ba8d vocab=38f1c540
-/
theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [Place.ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := WithZero.exp_log (v.adicValuation_ne_zero hf)
    rw [h, WithZero.exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, WithZero.log_one]

/--
@isnad1 id=iff.2h4v.s9.67016b32ea7b from=translated src=- shape=bd807425 vocab=395f7d1f
-/
theorem mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0) (hmem : x ∈ v.toValuationSubring) :
    (⟨x, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord x := by
  have hnonneg : 0 ≤ v.ord x := ord_nonneg_of_mem v hmem
  have hcoe : ((⟨x, hmem⟩ : v.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    hcoe, ← ord_eq_zero_iff_adicValuation_eq_one v hx]
  omega

end R4Sep1k

/--
@isnad1 id=ex.6h9v.s12.aefea30aba70 from=translated src=- shape=4cc06704 vocab=21222840
-/
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {FSS : Type} [Field FSS] [Algebra (ResidueField ↥A) FSS]
    (R : RegularProlongation A F FSS)
    (O : Subring F) [IsLocalRing ↥O] (hOR : ∀ f : F, f ∈ O → f ∈ R.integers)
    (Bx : Subring F) (hBO : Bx ≤ O)
    (hloc : ∀ f : F, f ∈ O ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (nd y : Place (ResidueField ↥A) FSS)

    (huniq : ∀ y' : Place (ResidueField ↥A) FSS,
      (∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring) →
      (∀ (b : F) (hb : b ∈ Bx), ¬ IsUnit (⟨b, hBO hb⟩ : ↥O) →
        ∃ hm : R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring, (⟨_, hm⟩ : ↥y'.toValuationSubring) ∈ maximalIdeal ↥y'.toValuationSubring) →
      y' = nd)
    (hy : ∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y.toValuationSubring)
    (hne : y ≠ nd) :
    ∃ (g : F) (hg : g ∈ Bx), ¬ IsUnit (⟨g, hBO hg⟩ : ↥O) ∧
      y.ord (R.residue ⟨g, hOR g (hBO hg)⟩) = 0 ∧ R.residue ⟨g, hOR g (hBO hg)⟩ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine huniq y hy ?_
  intro b hb hbu
  refine ⟨hy b hb, ?_⟩
  by_cases h0 : R.residue ⟨b, hOR b (hBO hb)⟩ = 0
  · have : (⟨R.residue ⟨b, hOR b (hBO hb)⟩, hy b hb⟩ : ↥y.toValuationSubring) = 0 :=
      Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  · rw [R4Sep1k.mem_maximalIdeal_iff_ord_pos y h0 (hy b hb)]
    have hnn := R4Sep1k.ord_nonneg_of_mem y (hy b hb)
    have hne0 : y.ord (R.residue ⟨b, hOR b (hBO hb)⟩) ≠ 0 := fun h => h0 (hcon b hb hbu h)
    omega
