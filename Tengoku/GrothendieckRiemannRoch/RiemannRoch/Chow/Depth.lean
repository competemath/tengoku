/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.ReesDepth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homological depth and regular sequences

For a finite module `M` and an ideal `I`, depth is the least degree in which
`Ext (R ⧸ I) M` is nonzero, with value `∞` if every degree vanishes.  Rees's theorem identifies
the inequality `n ≤ depth` with the existence of an `M`-regular sequence of length `n` in `I`.
-/

noncomputable section

universe v u

open CategoryTheory Abelian RingTheory.Sequence

variable {R : Type u} [CommRing R]

namespace ModuleCat

/-- The depth of `M` along `I`, defined as the first nonvanishing degree of
`Ext_R(R/I, M)`.  An empty infimum is `∞`.-/
def depth [Small.{v} R] (I : Ideal R) (M : ModuleCat.{v} R) : ℕ∞ :=
  ⨅ i : {i : ℕ // Nontrivial
      (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)}, (i.1 : ℕ∞)

/-- A natural number is at most the depth precisely when all lower `Ext` groups vanish.-/
theorem natCast_le_depth_iff [Small.{v} R] (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i) := by
  constructor
  · intro h i hi
    rw [depth] at h
    by_contra hsub
    letI : Nontrivial (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i) :=
      not_subsingleton_iff_nontrivial.mp hsub
    have hle : (n : ℕ∞) ≤ (i : ℕ∞) :=
      h.trans (iInf_le (fun j : {j : ℕ // Nontrivial
        (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M j)} ↦ (j.1 : ℕ∞)) ⟨i, inferInstance⟩)
    exact (not_le_of_gt hi) (by exact_mod_cast hle)
  · intro h
    rw [depth]
    refine le_iInf fun i ↦ ?_
    by_contra hle
    have hi : i.1 < n := by
      exact_mod_cast (lt_of_not_ge hle)
    exact not_subsingleton_iff_nontrivial.mpr i.2 (h i.1 hi)

/-- Quotienting by an `M`-regular element lowers depth by at most one.  This is the
vanishing consequence of the covariant long exact `Ext` sequence of
`0 → M → M → M/rM → 0`.-/
theorem natCast_le_depth_quotSMulTop_of_succ_le_depth [Small.{v} R]
    (I : Ideal R) (M : ModuleCat.{v} R) (r : R) (hr : IsSMulRegular M r) (n : ℕ)
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ depth I M) :
    (n : ℕ∞) ≤ depth I (ModuleCat.of R (QuotSMulTop r M)) := by
  rw [natCast_le_depth_iff] at h ⊢
  intro i hi
  have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    ((Ext.covariant_sequence_exact₃'
      (ModuleCat.of R (Shrink.{v} (R ⧸ I))) hr.smulShortComplex_shortExact)
      i (i + 1) rfl)
    (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

/-- The depth of a module over a local ring, taken along the maximal ideal.-/
def localDepth [Small.{v} R] [IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal R) M

end ModuleCat
