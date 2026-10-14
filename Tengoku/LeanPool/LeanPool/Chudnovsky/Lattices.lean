/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Tengoku.LeanPool.LeanPool.Chudnovsky.Quasiperiods

/-!
# Equivalent lattices and scaling laws

Statements from chapter 3 of Milla (arXiv:1809.00533v6, file `080_Lattices.tex`):

* `PeriodPair.smul` : the period pair `a•L` with periods `(a·ω₁, a·ω₂)` for `a ∈ ℂˣ`,
  generating the equivalent (rotated/scaled) lattice `a·L`;
* `PeriodPair.discr`, `PeriodPair.J` : the discriminant `Δ(L) = g₂³ - 27g₃²` and Klein's
  absolute invariant `J(L) = g₂³/(g₂³ - 27g₃²)` of a lattice (paper Def. `defijdelta`);
* the scaling laws `G_n(aL) = a⁻ⁿG_n(L)`, `g₂(aL) = a⁻⁴g₂(L)`, `g₃(aL) = a⁻⁶g₃(L)`,
  `Δ(aL) = a⁻¹²Δ(L)`, `J(aL) = J(L)` (paper `trafog23`), the function scaling laws
  `℘(az; aL) = a⁻²℘(z; L)`, `ζ(az; aL) = a⁻¹ζ(z; L)`, `σ(az; aL) = a·σ(z; L)`, and the
  quasiperiod scaling `η_k(aL) = a⁻¹η_k(L)` (paper `etatransf`).

All nontrivial proofs are `sorry`-ed for now; this file pins the statements.
-/

@[expose] public section

noncomputable section

namespace PeriodPair

/-- The period pair `a•L` with periods `(a·ω₁, a·ω₂)`, generating the equivalent lattice
`a·L` (paper ch. 3: "equivalent lattices"). -/
def smul (a : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := by
    have h := L.indep.map' (LinearMap.mulLeft ℝ (a : ℂ))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ a.ne_zero))
    have hcomp : ⇑(LinearMap.mulLeft ℝ (a : ℂ)) ∘ ![L.ω₁, L.ω₂] =
        ![(a : ℂ) * L.ω₁, (a : ℂ) * L.ω₂] := by
      funext i; fin_cases i <;> simp
    rwa [hcomp] at h

instance instSMulUnitsPeriodPair : SMul ℂˣ PeriodPair := ⟨smul⟩

variable (a : ℂˣ) (L : PeriodPair)

/--
@isnad1 id=eq.0h2v.s5.896642a5982f from=translated src=- shape=e420e314 vocab=4bff42ae
-/
@[simp] lemma smul_ω₁ : (a • L).ω₁ = a * L.ω₁ := rfl

/--
@isnad1 id=eq.0h2v.s5.3db0bbf835e9 from=translated src=- shape=e420e314 vocab=29754846
-/
@[simp] lemma smul_ω₂ : (a • L).ω₂ = a * L.ω₂ := rfl

/-- The lattice of `a•L` is the scaled lattice `a·L` (paper ch. 3).
@isnad1 id=iff.0h3v.s6.809c6891ef7b from=translated src=- shape=efac5075 vocab=47d29a45
-/
theorem mem_smul_lattice_iff (z : ℂ) :
    z ∈ (a • L).lattice ↔ ∃ w ∈ L.lattice, z = a * w := by
  rw [mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m * L.ω₁ + n * L.ω₂, mem_lattice.mpr ⟨m, n, rfl⟩, ?_⟩
    rw [← h, smul_ω₁, smul_ω₂]; ring
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, n, rfl⟩ := mem_lattice.mp hw
    exact ⟨m, n, by rw [smul_ω₁, smul_ω₂]; ring⟩

/-- Multiplication by `a` as an equivalence between the lattice of `L` and that of `a•L`. -/
def smulLatticeEquiv : L.lattice ≃ (a • L).lattice where
  toFun l := ⟨(a : ℂ) * l, (mem_smul_lattice_iff a L _).mpr ⟨(l : ℂ), l.2, rfl⟩⟩
  invFun z := ⟨(a : ℂ)⁻¹ * z, by
    obtain ⟨w, hw, hz⟩ := (mem_smul_lattice_iff a L _).mp z.2
    rw [hz, ← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]; exact hw⟩
  left_inv l := by
    apply Subtype.ext; simp only; rw [← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]
  right_inv z := by
    apply Subtype.ext; simp only; rw [← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]

/--
@isnad1 id=eq.0h3v.s9.7fd440c7907b from=translated src=- shape=ae62b51f vocab=e9816023
-/
@[simp] lemma smulLatticeEquiv_coe (l : L.lattice) :
    ((smulLatticeEquiv a L l : (a • L).lattice) : ℂ) = (a : ℂ) * (l : ℂ) := rfl

/-- Multiplication by `a` as an equivalence between the nonzero lattice points of `L` and
those of `a•L`. -/
def smulLatticeEquiv' :
    {l : L.lattice // l ≠ 0} ≃ {l : (a • L).lattice // l ≠ 0} :=
  (smulLatticeEquiv a L).subtypeEquiv fun l => by
    have ha : (a : ℂ) ≠ 0 := a.ne_zero
    simp only [ne_eq, ← Submodule.coe_eq_zero, smulLatticeEquiv_coe, mul_eq_zero, ha, false_or]

/--
@isnad1 id=eq.0h3v.s11.d868c5a7f2b3 from=translated src=- shape=7c608db0 vocab=bea79aab
-/
@[simp] lemma smulLatticeEquiv'_coe (l : {l : L.lattice // l ≠ 0}) :
    (((smulLatticeEquiv' a L l).1 : (a • L).lattice) : ℂ) = (a : ℂ) * ((l : L.lattice) : ℂ) :=
  rfl

/-! ### Termwise scaling identities (helpers) -/

private lemma pTerm_aux (c u v : ℂ) :
    1 / (c * u) ^ 2 - 1 / (c * v) ^ 2 = (c ^ 2)⁻¹ * (1 / u ^ 2 - 1 / v ^ 2) := by
  simp only [one_div, mul_pow, mul_inv, mul_sub]

private lemma derivTerm_aux (c u : ℂ) : 2 / (c * u) ^ 3 = (c ^ 3)⁻¹ * (2 / u ^ 3) := by
  rw [mul_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

private lemma zetaTerm_aux {c : ℂ} (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    weierstrassZetaTerm (c * z) (c * w) = c⁻¹ * weierstrassZetaTerm z w := by
  have hcw : c * w ≠ 0 := mul_ne_zero hc hw
  unfold weierstrassZetaTerm
  by_cases hzw : z = w
  · subst hzw
    simp only [sub_self, div_zero, zero_add]
    field_simp
  · have h1 : c * z - c * w ≠ 0 := by
      rw [← mul_sub]; exact mul_ne_zero hc (sub_ne_zero.mpr hzw)
    have h2 : z - w ≠ 0 := sub_ne_zero.mpr hzw
    field_simp

private lemma sigmaTerm_aux {c : ℂ} (hc : c ≠ 0) (z w : ℂ) :
    weierstrassSigmaTerm (c * z) (c * w) = weierstrassSigmaTerm z w := by
  unfold weierstrassSigmaTerm
  have e1 : (c * z) / (c * w) = z / w := mul_div_mul_left z w hc
  have e2 : (c * z) ^ 2 / (2 * (c * w) ^ 2) = z ^ 2 / (2 * w ^ 2) := by
    rw [show (c * z) ^ 2 = c ^ 2 * z ^ 2 from by ring,
        show 2 * (c * w) ^ 2 = c ^ 2 * (2 * w ^ 2) from by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)
  simp only [e1, e2]

/-! ## The discriminant and Klein's absolute invariant (paper Def. `defijdelta`) -/

/-- The discriminant of a lattice, `Δ(L) = g₂(L)³ - 27·g₃(L)²` (paper Def. `defijdelta`). -/
def discr : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- Klein's absolute invariant of a lattice,
`J(L) = g₂(L)³ / (g₂(L)³ - 27·g₃(L)²)` (paper Def. `defijdelta`). -/
def J : ℂ := L.g₂ ^ 3 / L.discr

/-! ## Scaling laws (paper `trafog23`, `etatransf`) -/

/-- Scaling law for the Eisenstein series: `G_n(aL) = a⁻ⁿ·G_n(L)` (paper `trafog23`).
@isnad1 id=eq.0h3v.s6.ff8e1c227374 from=translated src=- shape=259854b4 vocab=bf53432f
-/
theorem G_smul (n : ℕ) : (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n := by
  rw [G, G, ← (smulLatticeEquiv a L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [smulLatticeEquiv_coe, mul_pow, mul_inv]

/-- Scaling law `g₂(aL) = a⁻⁴·g₂(L)` (paper `trafog23`).
@isnad1 id=eq.0h2v.s6.c5db2416ecec from=translated src=- shape=18e08f3a vocab=07478389
-/
theorem g₂_smul : (a • L).g₂ = ((a : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [g₂, g₂, G_smul]; ring

/-- Scaling law `g₃(aL) = a⁻⁶·g₃(L)` (paper `trafog23`).
@isnad1 id=eq.0h2v.s6.8f4315f74360 from=translated src=- shape=18e08f3a vocab=9fbe6093
-/
theorem g₃_smul : (a • L).g₃ = ((a : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [g₃, g₃, G_smul]; ring

/-- Scaling law `Δ(aL) = a⁻¹²·Δ(L)` (paper `trafog23`).
@isnad1 id=eq.0h2v.s6.8b9cdc08dbb8 from=translated src=- shape=18e08f3a vocab=22fe89b8
-/
theorem discr_smul : (a • L).discr = ((a : ℂ) ^ 12)⁻¹ * L.discr := by
  rw [discr, discr, g₂_smul, g₃_smul]; ring

/-- Klein's absolute invariant is invariant under scaling: `J(aL) = J(L)`
(paper `trafog23`).
@isnad1 id=eq.0h2v.s4.690bf5efd73b from=translated src=- shape=c4095571 vocab=78d6966e
-/
theorem J_smul : (a • L).J = L.J := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have key : ((a : ℂ) ^ 4)⁻¹ ^ 3 = ((a : ℂ) ^ 12)⁻¹ := by rw [inv_pow, ← pow_mul]
  rw [J, J, g₂_smul, discr_smul, mul_pow, key,
      mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 12 ha))]

/-- Scaling law for the ℘-function: `℘(az; aL) = a⁻²·℘(z; L)`.
@isnad1 id=eq.0h3v.s6.760531775785 from=translated src=- shape=e2fb26ec vocab=430c665a
-/
theorem weierstrassP_smul (z : ℂ) :
    (a • L).weierstrassP ((a : ℂ) * z) = ((a : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  rw [weierstrassP, weierstrassP, ← (smulLatticeEquiv a L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [smulLatticeEquiv_coe, ← mul_sub]
  exact pTerm_aux _ _ _

/-- Scaling law for ℘′: `℘'(az; aL) = a⁻³·℘'(z; L)`.
@isnad1 id=eq.0h3v.s6.a63b0d602047 from=translated src=- shape=e2fb26ec vocab=6a1072ca
-/
theorem derivWeierstrassP_smul (z : ℂ) :
    (a • L).derivWeierstrassP ((a : ℂ) * z) = ((a : ℂ) ^ 3)⁻¹ * L.derivWeierstrassP z := by
  rw [derivWeierstrassP, derivWeierstrassP, mul_neg, neg_inj,
      ← (smulLatticeEquiv a L).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [smulLatticeEquiv_coe, ← mul_sub]
  exact derivTerm_aux _ _

/-- Scaling law for the ζ-function: `ζ(az; aL) = a⁻¹·ζ(z; L)` (paper `etatransf`).
@isnad1 id=eq.0h3v.s6.d49330a6eb72 from=translated src=- shape=5171c3eb vocab=7c030c33
-/
theorem weierstrassZeta_smul (z : ℂ) :
    (a • L).weierstrassZeta ((a : ℂ) * z) = (a : ℂ)⁻¹ * L.weierstrassZeta z := by
  rw [weierstrassZeta, weierstrassZeta, mul_add, ← (smulLatticeEquiv' a L).tsum_eq,
      ← tsum_mul_left]
  congr 1
  · simp only [one_div, mul_inv]
  · refine tsum_congr fun l => ?_
    rw [smulLatticeEquiv'_coe]
    exact zetaTerm_aux a.ne_zero (Submodule.coe_eq_zero.not.mpr l.2) z

/-- Scaling law for the σ-function: `σ(az; aL) = a·σ(z; L)`.
@isnad1 id=eq.0h3v.s5.bcb1d0c96305 from=translated src=- shape=1eebba11 vocab=27bdabc2
-/
theorem weierstrassSigma_smul (z : ℂ) :
    (a • L).weierstrassSigma ((a : ℂ) * z) = (a : ℂ) * L.weierstrassSigma z := by
  have hprod :
      ∏' l : {l : L.lattice // l ≠ 0},
          weierstrassSigmaTerm ((a : ℂ) * z) (((smulLatticeEquiv' a L l).1 : (a • L).lattice) : ℂ)
        = ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z ((l : L.lattice) : ℂ) := by
    refine tprod_congr fun l => ?_
    rw [smulLatticeEquiv'_coe]
    exact sigmaTerm_aux a.ne_zero z _
  rw [weierstrassSigma, weierstrassSigma, ← (smulLatticeEquiv' a L).tprod_eq, hprod]
  ring

/-- Scaling law for the first quasiperiod: `η₁(aL) = a⁻¹·η₁(L)` (paper `etatransf`).
@isnad1 id=eq.0h2v.s5.f5d43dcbe039 from=translated src=- shape=f6e8ba40 vocab=8cf03452
-/
theorem eta₁_smul : (a • L).eta₁ = (a : ℂ)⁻¹ * L.eta₁ := by
  rw [eta₁, eta₁, smul_ω₁, show (a : ℂ) * L.ω₁ / 2 = (a : ℂ) * (L.ω₁ / 2) from by ring,
      weierstrassZeta_smul]
  ring

/-- Scaling law for the second quasiperiod: `η₂(aL) = a⁻¹·η₂(L)` (paper `etatransf`).
@isnad1 id=eq.0h2v.s5.8237eb0c3f05 from=translated src=- shape=f6e8ba40 vocab=d907edda
-/
theorem eta₂_smul : (a • L).eta₂ = (a : ℂ)⁻¹ * L.eta₂ := by
  rw [eta₂, eta₂, smul_ω₂, show (a : ℂ) * L.ω₂ / 2 = (a : ℂ) * (L.ω₂ / 2) from by ring,
      weierstrassZeta_smul]
  ring

end PeriodPair
