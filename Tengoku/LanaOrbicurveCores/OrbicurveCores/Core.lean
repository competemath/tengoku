/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Takeuchi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cores of Fuchsian groups, and [CanLift] Prop. 2.7 at the level of groups

For a Fuchsian group `Γ ⊆ SL(2, ℝ)` uniformising a hyperbolic curve `X = Γ \ ℍ`, the curve admits
a (hyperbolic) core iff `Γ` has finite index in its commensurator `Comm(Γ)`. The core is then
`[Comm(Γ) \ ℍ]` ([Corr] §3, [CanLift] Rem. 2.1.2). This file:

* defines `OrbicurveCores.AdmitsCore Γ :⇔ [Comm(Γ) : Γ] < ∞`;
* proves that **arithmetic groups admit no core** (`IsArithmeticSL.not_admitsCore`). If
  `Γ` is conjugate to a group commensurable with `SL(2, ℤ)`, then `Comm(Γ)` contains a conjugate of
  `diag(√2, 1/√2)`, and no positive power of it lies in `Γ` because its squared trace
  `2ⁿ + 2 + 2⁻ⁿ` is not an integer (`IsArithmeticSL.sq_tr_int`);
* states **Margulis' commensurator theorem** in the special case needed (`MargulisOneInfty`):
  a `(1;∞)`-group with infinite index in its commensurator is arithmetic. This is
  [Marg] Ch. IX Thm. (B) (with [Corr] Thm. 2.5) restricted to once-punctured torus groups. It is
  **not** proved here (see `Blueprint.md`, items M1–M2);
* assembles the group-theoretic form of [CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1
  (`canLift27_group`): assuming `MargulisOneInfty`, a `(1;∞)`-group without core has, up to Nielsen
  equivalence, one of Takeuchi's four trace triples.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- A subgroup `Γ` *admits a core* if it has finite index in its commensurator. For a Fuchsian
group `Γ ⊆ SL(2, ℝ)` this is equivalent to the existence of a hyperbolic core of `Γ \ ℍ`
([Corr] §3, [CanLift] Rem. 2.1.2); the core is `[Comm(Γ) \ ℍ]`. -/
def AdmitsCore {G : Type*} [Group G] (Γ : Subgroup G) : Prop :=
  Γ.relIndex (commensurator Γ) ≠ 0

/-- If `Γ` admits a core, then every element of the commensurator has a positive power in `Γ`. -/
lemma AdmitsCore.exists_pow_mem {G : Type*} [Group G] {Γ : Subgroup G} (h : AdmitsCore Γ)
    {σ : G} (hσ : σ ∈ commensurator Γ) : ∃ n : ℕ, 0 < n ∧ σ ^ n ∈ Γ := by
  obtain ⟨n, hn, -, hmem⟩ := exists_pow_mem_of_relIndex_ne_zero h hσ
  exact ⟨n, hn, hmem.1⟩

section conj

variable {G H : Type*} [Group G] [Group H]

/-- Conjugation commutes with taking images. -/
lemma map_conjAct_smul (f : G →* H) (x : G) (K : Subgroup G) :
    (ConjAct.toConjAct x • K).map f = ConjAct.toConjAct (f x) • K.map f := by
  ext y
  simp only [mem_map, mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x⁻¹ * z * x, hz, by simp [mul_assoc]⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨x * z * x⁻¹, by simpa [mul_assoc] using hz, ?_⟩
    rw [map_mul, map_mul, hzy, map_inv]
    group

end conj

/-- The rational matrix `diag(2, 1)`. -/
noncomputable def diagTwo : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 0; 0, 1] (by simp [det_fin_two])

/-- The squared trace `2ⁿ + 2 + 2⁻ⁿ` is not an integer for `n ≥ 1`. -/
lemma not_int_two_pow {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ((2 : ℝ) ^ n + 1) ^ 2 / 2 ^ n ≠ m := by
  intro h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hsplit : ((2 : ℝ) ^ n + 1) ^ 2 / 2 ^ n = 2 ^ n + 2 + 1 / 2 ^ n := by
    field_simp
    ring
  rw [hsplit] at h
  have hlt : (1 : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one h2]
    exact one_lt_pow₀ (by norm_num) hn.ne'
  have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
  -- `1 / 2ⁿ = m - 2ⁿ - 2` is an integer strictly between `0` and `1`
  have hk : (1 : ℝ) / 2 ^ n = ((m - 2 ^ n - 2 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk] at hlt hpos
  have h1 : (0 : ℤ) < m - 2 ^ n - 2 := by exact_mod_cast hpos
  have h2' : m - 2 ^ n - 2 < (1 : ℤ) := by exact_mod_cast hlt
  lia

/-- **Margulis' commensurator theorem for once-punctured torus groups** (statement only).
If `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2` and `tr A ≠ 0` (so `⟨A, B⟩` is a Fuchsian group of
signature `(1;∞)`: Fricke, see Goldman, *Geom. Topol.* 7 (2003)) and `⟨A, B⟩` has infinite index in
its commensurator, then `⟨A, B⟩` is arithmetic.

This is [Marg] Ch. IX Thm. (B) (see also [Zim] Thm. 6.2.5 and [Corr] Thm. 2.5), combined with
the fact that a non-cocompact arithmetic Fuchsian group is commensurable with a conjugate of
`SL(2, ℤ)`. It is **not proved** in this repository; it is the input M1+M2 of `Blueprint.md`. -/
def MargulisOneInfty : Prop :=
  ∀ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 →
    ¬ AdmitsCore (Subgroup.closure {A, B}) → IsArithmeticSL (Subgroup.closure {A, B})

end OrbicurveCores
