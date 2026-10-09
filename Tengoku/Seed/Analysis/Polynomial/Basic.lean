/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Polynomial.Roots
public import Tengoku.Seed.Analysis.Asymptotics.AsymptoticEquivalent
public import Tengoku.Seed.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rational functions.
The main result is `Polynomial.isEquivalent_atTop_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

public section


open Filter Finset Asymptotics

open Asymptotics Polynomial Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

/--
@isnad1 id=eventual.1h2v.s6.0024eeaa126e from=seed src=0 shape=21554829 vocab=80d375fc
-/
theorem eventually_atTop_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

/--
@isnad1 id=eventual.1h2v.s6.0024eeaa126e from=seed src=0 shape=21554829 vocab=80d375fc
-/
@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_not_isRoot

/--
@isnad1 id=eventual.1h2v.s6.d9a5878ecff3 from=seed src=0 shape=21554829 vocab=42792181
-/
theorem eventually_atBot_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atBot, ¬P.IsRoot x :=
  atBot_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

variable [OrderTopology 𝕜]

section PolynomialAtTop

/--
@isnad1 id=isequiva.0h2v.s7.3c4c49078eb1 from=seed src=0 shape=83688265 vocab=fa19e9b0
-/
theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

/--
@isnad1 id=tendsto.2h2v.s7.1eeca3964085 from=seed src=0 shape=cc81afb0 vocab=2b70d31d
-/
theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg

/--
@isnad1 id=iff.0h2v.s7.8dce3910bfe3 from=seed src=0 shape=4271fecd vocab=2b70d31d
-/
theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff, ← pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

/--
@isnad1 id=iff.0h2v.s7.71ee581509ee from=seed src=0 shape=206c8011 vocab=cda7a2ce
-/
theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

/--
@isnad1 id=tendsto.2h2v.s7.5c933955f82e from=seed src=0 shape=5d16f039 vocab=cda7a2ce
-/
theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

/--
@isnad1 id=tendsto.1h2v.s7.5769e8f9d502 from=seed src=0 shape=d27d5dbd vocab=4ca538d8
-/
theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

/--
@isnad1 id=iff.0h2v.s7.c609e45d2930 from=seed src=0 shape=1e63e34e vocab=276cde01
-/
theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

/--
@isnad1 id=iff.0h2v.s7.c609e45d2930 from=seed src=0 shape=1e63e34e vocab=276cde01
-/
@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := isBoundedUnder_abs_atTop_iff

/--
@isnad1 id=iff.0h2v.s7.c1e65ffa31e5 from=seed src=0 shape=63726516 vocab=4ca538d8
-/
theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

/--
@isnad1 id=iff.0h3v.s7.6ecc7b5df9d4 from=seed src=0 shape=ecbb78da vocab=5a768fde
-/
theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

end PolynomialAtTop

section PolynomialAtBot

/--
@isnad1 id=isequiva.0h2v.s7.b14ab7ca7599 from=seed src=0 shape=83688265 vocab=f7cf9374
-/
theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

/--
@isnad1 id=tendsto.1h2v.s7.7632f78625f0 from=seed src=0 shape=d27d5dbd vocab=daffb116
-/
theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

/--
@isnad1 id=iff.0h2v.s7.54fc14ae61cb from=seed src=0 shape=1e63e34e vocab=f34a4bcc
-/
theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

/--
@isnad1 id=iff.0h2v.s7.5ae41d883330 from=seed src=0 shape=42d8a68d vocab=daffb116
-/
theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

end PolynomialAtBot

section PolynomialDivAtTop

/--
@isnad1 id=isequiva.0h3v.s8.3f575248761f from=seed src=0 shape=9529ad85 vocab=bfe2cf88
-/
theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]

/--
@isnad1 id=tendsto.1h3v.s7.db6f54779cca from=seed src=0 shape=c72110e8 vocab=c6b702db
-/
theorem div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

/--
@isnad1 id=tendsto.1h3v.s7.db6f54779cca from=seed src=0 shape=c72110e8 vocab=c6b702db
-/
@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt

/--
@isnad1 id=iff.1h3v.s8.c364af6d7af4 from=seed src=0 shape=210ad5eb vocab=c6b702db
-/
theorem div_tendsto_atTop_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

/--
@isnad1 id=iff.1h3v.s8.c364af6d7af4 from=seed src=0 shape=210ad5eb vocab=c6b702db
-/
@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt

/--
@isnad1 id=tendsto.1h3v.s7.21102944f6c9 from=seed src=0 shape=7d853ca2 vocab=e53a2a85
-/
theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : ℤ) = Q.natDegree by simp [hdeg, natDegree]]
  simp

/--
@isnad1 id=tendsto.1h3v.s7.21102944f6c9 from=seed src=0 shape=7d853ca2 vocab=e53a2a85
-/
@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq

/--
@isnad1 id=tendsto.2h3v.s8.b25d44efef58 from=seed src=0 shape=6103c1ec vocab=569eb271
-/
theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia

/--
@isnad1 id=tendsto.3h3v.s8.6d3c617971c3 from=seed src=0 shape=8e39791f vocab=0501f06b
-/
theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos

/--
@isnad1 id=tendsto.2h3v.s8.abbad5781b0b from=seed src=0 shape=9a6939cd vocab=569cc7ee
-/
theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia

/--
@isnad1 id=tendsto.3h3v.s8.6bc909fa7917 from=seed src=0 shape=1db57b13 vocab=9b2a41aa
-/
theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg

/--
@isnad1 id=tendsto.2h3v.s7.cb3fb07c51be from=seed src=0 shape=b3c2e475 vocab=827669d0
-/
theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

/--
@isnad1 id=tendsto.2h3v.s7.cb3fb07c51be from=seed src=0 shape=b3c2e475 vocab=827669d0
-/
@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

end PolynomialDivAtTop

section PolynomialDivAtBot

/--
@isnad1 id=isequiva.0h3v.s8.756a723de787 from=seed src=0 shape=9529ad85 vocab=d1c31b24
-/
theorem isEquivalent_atBot_div :
    (fun x ↦ P.eval x / Q.eval x) ~[atBot] fun x ↦
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]

/--
@isnad1 id=tendsto.1h3v.s7.28a62ccb0ff7 from=seed src=0 shape=c72110e8 vocab=6bc0cf41
-/
theorem div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

/--
@isnad1 id=iff.1h3v.s8.06004aee38ba from=seed src=0 shape=210ad5eb vocab=6bc0cf41
-/
theorem div_tendsto_atBot_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert! h.comp tendsto_neg_atTop_atBot using 2
  simp

/--
@isnad1 id=tendsto.1h3v.s7.09095a696682 from=seed src=0 shape=7d853ca2 vocab=3df400d6
-/
theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]

/--
@isnad1 id=tendsto.2h3v.s7.e7dc9a2ce600 from=seed src=0 shape=b3c2e475 vocab=70c60c61
-/
theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

end PolynomialDivAtBot

/--
@isnad1 id=islittle.1h3v.s7.b22097758cf1 from=seed src=0 shape=94f7dc23 vocab=92b84306
-/
theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

/--
@isnad1 id=islittle.1h3v.s7.cb44ace2328b from=seed src=0 shape=94f7dc23 vocab=5c442553
-/
theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

/--
@isnad1 id=isbigo.1h3v.s7.7b2bdedba500 from=seed src=0 shape=94f7dc23 vocab=db0255af
-/
theorem isBigO_atTop_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)

/--
@isnad1 id=isbigo.1h3v.s7.bbaf97f31926 from=seed src=0 shape=94f7dc23 vocab=55c9736c
-/
theorem isBigO_atBot_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

/--
@isnad1 id=isbigo.1h3v.s7.7b2bdedba500 from=seed src=0 shape=94f7dc23 vocab=db0255af
-/
@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

section Cobounded

open Bornology

variable {R : Type*} [NormedRing R] [NormMulClass R] {P Q : R[X]}

/--
@isnad1 id=isequiva.0h2v.s6.b7b42295a64a from=seed src=0 shape=a9da5244 vocab=d6457c0b
-/
lemma isEquivalent_cobounded_leading_monomial :
    P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree) := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi ↦
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

/--
@isnad1 id=islittle.1h3v.s6.896af8215ad3 from=seed src=0 shape=f2b8a228 vocab=f4720c9c
-/
theorem isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) :
    P.eval =o[cobounded R] Q.eval := by
  by_cases hP : P = 0
  · simp [hP]
  · refine isEquivalent_cobounded_leading_monomial.trans_isLittleO <|
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

/--
@isnad1 id=isbigo.1h3v.s6.89a28c37a007 from=seed src=0 shape=f2b8a228 vocab=eef90239
-/
theorem isBigO_cobounded_of_degree_le (h : P.degree ≤ Q.degree) :
    P.eval =O[cobounded R] Q.eval := by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
  · refine isEquivalent_cobounded_leading_monomial.trans_isBigO <|
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

end Cobounded

/-- If `deg Q < deg P`, there are only finitely many integers `x` where `|P(x)| ≤ |Q(x)|`.
@isnad1 id=finite.1h2v.s5.28e3dd809cf4 from=seed src=0 shape=d006a345 vocab=625841bc
-/
lemma finite_abs_eval_le_of_degree_lt {P Q : ℤ[X]} (h : Q.degree < P.degree) :
    {x | |P.eval x| ≤ |Q.eval x|}.Finite := by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq, ← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

/-- If `Q(x) ∣ P(x)` at infinitely many integers `x` and `Q` is monic, `Q ∣ P`.
@isnad1 id=dvd.2h2v.s6.073acf198d0c from=seed src=0 shape=013151b2 vocab=f8873d82
-/
theorem dvd_of_infinite_eval_dvd_eval
    {P Q : ℤ[X]} (mQ : Q.Monic) (h : {a | Q.eval a ∣ P.eval a}.Infinite) : Q ∣ P := by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx ↦ ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR, eval_add, eval_mul, Int.dvd_add_self_mul, ← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

end Polynomial
