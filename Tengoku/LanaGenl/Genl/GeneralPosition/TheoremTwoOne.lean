/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaGenl.Genl.GeneralPosition.ProofPackage
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Theorem 2.1 of "Arithmetic elliptic curves in general position"

This file proves the two implications of Theorem 2.1 of [mochizuki2010] for an abstract
height formalism `T : Genl.HeightTheory` equipped with the arithmetic-geometric inputs
`A : T.ProofPackage`:

- `Genl.HeightTheory.statementII_implies_statementI`: the substantial implication
  (ii) ⇒ (i), following the proof printed on pp. 13–14 of [mochizuki2010];
- `Genl.HeightTheory.statementI_implies_statementII`: the immediate implication
  (i) ⇒ (ii);
- `Genl.HeightTheory.statementI_iff_statementII`: the equivalence.

The proof of (ii) ⇒ (i) proceeds in two steps, exactly as in loc. cit.:

1. `le_of_statementII_ptEQ` treats the case of a divisor free hyperbolic curve `X` on the
   locus `X(ℚ̄)^{=d}` of points of degree exactly `d`, by contradiction: if the desired
   inequality fails, the field `belyi` of the proof package produces a noncritical Belyi
   map `φ : X → ℙ` and a compactly bounded subset `K_V` to which statement (ii) applies;
   the displayed chain of BD-inequalities on p. 14 then bounds `ht_{ω_X}` on the failure
   locus `Ξ`, contradicting the unboundedness of the failure. The tolerance is
   `ε' = ε / (1 + q (1 + ε))`, which satisfies `1 + ε' = (1 + ε)(1 - ε' q)` — the
   requirement `1 + ε' ≤ (1 + ε)(1 - ε' · deg E / deg ω_X)` of loc. cit., with
   `deg E / deg ω_X` replaced by the number `q > deg E / deg ω_X` of the proof package.
2. `statementI_of_divisorFree` reduces the general case to the divisor free case: for a
   hyperbolic `(X, D)`, the field `covering` of the proof package produces a covering
   `Y → X` ramified exactly over `D` with large ramification index; the case `D = ∅`
   applied to `Y` with tolerance `ε' = √(1 + ε) - 1` combines with the comparisons along
   `Y → X` to give the desired inequality on `U_X(ℚ̄)^{≤d}`, since `(1 + ε')² = 1 + ε`.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/

local notation:50 f:51 " ≲[" s "] " g:51 => DiscrepancyLE f g s
local notation:50 f:51 " ≈[" s "] " g:51 => DiscrepancyEquiv f g s

universe u

namespace Genl

namespace HeightTheory

variable (T : HeightTheory.{u})

/-- The divisor free case of the implication (ii) ⇒ (i) of Theorem 2.1 of
[mochizuki2010], on the locus of points of degree exactly `d` (second half of the proof
of Theorem 2.1, pp. 13–14 of loc. cit.). -/
theorem le_of_statementII_ptEQ (A : T.ProofPackage) (hII : T.StatementII) {X : T.Curve}
    (hX : T.Hyperbolic X) (hD : T.DivisorFree X) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    T.htCan X ≲[T.ptEQ X d] (1 + ε) • T.logDiff X := by
  by_contra hfail
  have B := A.belyi X hX hD d ε hε hfail
  have hq : 0 < B.q := B.q_pos
  have hden : 0 < 1 + B.q * (1 + ε) := by nlinarith
  set ε' : ℝ := ε / (1 + B.q * (1 + ε)) with hε'def
  have hε' : 0 < ε' := div_pos hε hden
  have hkey : 1 + ε' = (1 + ε) * (1 - ε' * B.q) := by
    rw [hε'def]
    field_simp
    ring
  have h1q : 0 < 1 - ε' * B.q := by nlinarith
  -- apply statement (ii) to `K_V` and pull back along the Belyi map
  have h2 : (T.htCan T.tripod ∘ B.φ) ≲[B.Ξ]
      (1 + ε') • (T.logDiff T.tripod ∘ B.φ + T.logCond T.tripod ∘ B.φ) :=
    (hII B.d' ε' hε' B.K).comp B.φ B.mapsTo
  -- the displayed chain of BD-inequalities on p. 14 of [mochizuki2010]
  have chain : T.htCan X ≲[B.Ξ] (1 + ε') • T.logDiff X + (ε' * B.q) • T.htCan X := by
    have hε'1 : (0 : ℝ) ≤ 1 + ε' := by linarith
    have c1 : T.htCan X ≲[B.Ξ] (T.htCan T.tripod ∘ B.φ - B.htE) := B.htCan_equiv.le
    have c2 := h2.sub_right B.htE
    have c3 := (B.logDiff_comp_le.smul hε'1).sub_right B.htE
    have c4 := (((DiscrepancyLE.refl (T.logDiff X) B.Ξ).add B.logCondE_le).smul
      hε'1).sub_right B.htE
    have c5 : (1 + ε') • (T.logDiff X + B.htE) - B.htE
        = (1 + ε') • T.logDiff X + ε' • B.htE := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have c6 : ε' • B.htE ≲[B.Ξ] (ε' * B.q) • T.htCan X := by
      have h := B.htE_le.smul hε'.le
      rwa [smul_smul] at h
    have c8 := ((c1.trans c2).trans c3).trans c4
    rw [c5] at c8
    exact c8.trans ((DiscrepancyLE.refl ((1 + ε') • T.logDiff X) B.Ξ).add c6)
  -- derive a numerical contradiction with the unboundedness of the failure
  obtain ⟨C, hC⟩ := chain
  obtain ⟨x, hxΞ, hxlt⟩ := B.unbounded (C / (1 - ε' * B.q))
  have h5 := hC x hxΞ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h5
  have key2 : (1 + ε') * T.logDiff X x = (1 + ε) * (1 - ε' * B.q) * T.logDiff X x := by
    rw [hkey]
  have expand : (1 - ε' * B.q) * T.htCan X x
      = T.htCan X x - ε' * B.q * T.htCan X x := by
    ring
  have step1 : (1 - ε' * B.q) * T.htCan X x
      ≤ (1 + ε) * (1 - ε' * B.q) * T.logDiff X x + C := by
    linarith
  have step2 : (1 - ε' * B.q) * ((1 + ε) * T.logDiff X x + C / (1 - ε' * B.q))
      < (1 - ε' * B.q) * T.htCan X x :=
    mul_lt_mul_of_pos_left hxlt h1q
  have hne : (1 - ε' * B.q) ≠ 0 := h1q.ne'
  have step3 : (1 - ε' * B.q) * ((1 + ε) * T.logDiff X x + C / (1 - ε' * B.q))
      = (1 + ε) * (1 - ε' * B.q) * T.logDiff X x + C := by
    field_simp
  linarith

/-- The divisor free case of the implication (ii) ⇒ (i) of Theorem 2.1 of
[mochizuki2010], on the locus of points of degree at most `d`. -/
theorem le_of_statementII_divisorFree (A : T.ProofPackage) (hII : T.StatementII)
    {X : T.Curve} (hX : T.Hyperbolic X) (hD : T.DivisorFree X) (d : ℕ) {ε : ℝ}
    (hε : 0 < ε) : T.htCan X ≲[T.ptLE X d] (1 + ε) • T.logDiff X := by
  induction d with
  | zero =>
      rw [T.ptLE_zero]
      exact DiscrepancyLE.empty
  | succ n ih =>
      rw [T.ptLE_succ]
      exact ih.union (T.le_of_statementII_ptEQ A hII hX hD (n + 1) hε)

/-- The reduction of statement (i) of Theorem 2.1 of [mochizuki2010] to the divisor free
case, via coverings ramified exactly over `D` with large ramification index (first
paragraph of the proof of Theorem 2.1, p. 13 of loc. cit.). -/
theorem statementI_of_divisorFree (A : T.ProofPackage)
    (hfree : ∀ Y, T.Hyperbolic Y → T.DivisorFree Y → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
      T.htCan Y ≲[T.ptLE Y d] (1 + ε) • T.logDiff Y) :
    T.StatementI := by
  intro X hX d ε hε
  set ε' : ℝ := Real.sqrt (1 + ε) - 1 with hε'def
  have hsq : Real.sqrt (1 + ε) * Real.sqrt (1 + ε) = 1 + ε :=
    Real.mul_self_sqrt (by linarith)
  have hε' : 0 < ε' := by
    rw [hε'def, sub_pos]
    nlinarith [Real.sqrt_nonneg (1 + ε), hsq]
  have h1ε' : 1 + ε' = Real.sqrt (1 + ε) := by
    rw [hε'def]
    ring
  have hsmul : (1 + ε') * (1 + ε') = 1 + ε := by
    rw [h1ε']
    exact hsq
  have Cov := A.covering X hX d ε' hε'
  have hY := hfree Cov.Y Cov.hyperbolic Cov.divisorFree Cov.d' ε' hε'
  have step1 : (T.htCan X ∘ Cov.π) ≲[T.ptLE Cov.Y Cov.d']
      ((1 + ε') * (1 + ε')) • T.logDiff Cov.Y := by
    have h := Cov.htCan_le.trans (hY.smul (by linarith : (0 : ℝ) ≤ 1 + ε'))
    rwa [smul_smul] at h
  rw [hsmul] at step1
  have step2 : (T.htCan X ∘ Cov.π) ≲[T.ptLE Cov.Y Cov.d']
      ((1 + ε) • (T.logDiff X + T.logCond X)) ∘ Cov.π :=
    step1.trans (Cov.logDiff_le.smul (by linarith : (0 : ℝ) ≤ 1 + ε))
  exact DiscrepancyLE.of_comp_surjOn Cov.surjOn step2

/-- **Theorem 2.1 of [mochizuki2010], (ii) ⇒ (i)**: for a height formalism satisfying
the arithmetic-geometric inputs of `ProofPackage`, the ABC conjecture for `Σ`-supported
compactly bounded subsets of the tripod implies the Effective Mordell/ABC/Vojta
conjecture for arbitrary hyperbolic curves over number fields. -/
theorem statementII_implies_statementI (A : T.ProofPackage) (hII : T.StatementII) :
    T.StatementI :=
  T.statementI_of_divisorFree A fun _ hY hD d _ hε ↦
    T.le_of_statementII_divisorFree A hII hY hD d hε

/-- **Theorem 2.1 of [mochizuki2010], (i) ⇒ (ii)**: the Effective Mordell/ABC/Vojta
conjecture restricts to compactly bounded subsets of the tripod. This implication is
immediate from the definitions. -/
theorem statementI_implies_statementII (hI : T.StatementI) : T.StatementII := by
  intro d ε hε K
  exact (hI T.tripod T.hyperbolic_tripod d ε hε).mono Set.inter_subset_right

/-- **Theorem 2.1 of [mochizuki2010]**: statements (i) and (ii) are equivalent. -/
theorem statementI_iff_statementII (A : T.ProofPackage) :
    T.StatementI ↔ T.StatementII :=
  ⟨T.statementI_implies_statementII, T.statementII_implies_statementI A⟩

end HeightTheory

end Genl
