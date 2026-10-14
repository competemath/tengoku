/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.M.Basic
public import Tengoku

/-!
# Planar configuration and block entries of `M`

The normalized configuration of `docs/sol.tex` §4 (`eq:coordinates`,
`eq:blocks`): `z₀ = (1,0)`, `zᵢ = √sᵢ (-1, tᵢ)`, `yⱼ = √ρⱼ (xⱼ, 1)`.

Indices are identified with `Option (Fin k) ⊕ Fin p` via `configIdxEquiv`:
`none` is `z₀`, `some i` is `zᵢ`, and `Sum.inr j` is `yⱼ`. The carrier is
`Fin (k + 1 + p)`, which supplies `LinearOrder` for `M`.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix Finset Function
open scoped Matrix

noncomputable section

variable {k p : ℕ}

/-- Index type identified with `Option (Fin k) ⊕ Fin p`: `0` is `z₀`,
`1..k` are the `zᵢ`, and `k+1..` are the `yⱼ`. -/
abbrev ConfigIdx (k p : ℕ) := Fin (k + 1 + p)

/-- `none = z₀`, `some i = zᵢ`, `inr j = yⱼ`. -/
def configIdxEquiv (k p : ℕ) : ConfigIdx k p ≃ Option (Fin k) ⊕ Fin p :=
  (finSumFinEquiv (m := k + 1) (n := p)).symm.trans
    (Equiv.sumCongr (finSuccEquiv k) (Equiv.refl _))

/-- The `z₀` index (`none`). -/
def idxZ0 : ConfigIdx k p := (configIdxEquiv k p).symm (Sum.inl none)

/-- The `zᵢ` index (`some i`). -/
def idxZ (i : Fin k) : ConfigIdx k p := (configIdxEquiv k p).symm (Sum.inl (some i))

/-- The `yⱼ` index. -/
def idxY (j : Fin p) : ConfigIdx k p := (configIdxEquiv k p).symm (Sum.inr j)

/--
@isnad1 id=eq.0h2v.s5.d454000bcfb3 from=translated src=- shape=70dc7345 vocab=d3b57da9
-/
lemma idxZ0_eq : (idxZ0 : ConfigIdx k p) = 0 := by
  simp only [idxZ0, configIdxEquiv, Equiv.symm_trans, Equiv.sumCongr_symm, Equiv.refl_symm,
    Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl,
    finSuccEquiv_symm_none, finSumFinEquiv_apply_left]
  ext
  simp

/--
@isnad1 id=eq.0h3v.s5.94f1a8fea5c0 from=translated src=- shape=41da7840 vocab=b1ed792d
-/
lemma idxZ_val (i : Fin k) : (idxZ (p := p) i).val = i.val + 1 := by
  simp [idxZ, configIdxEquiv]

/--
@isnad1 id=eq.0h3v.s5.e29429c3d0e7 from=translated src=- shape=57a7933f vocab=d4162c05
-/
lemma idxY_val (j : Fin p) : (idxY (k := k) j).val = k + 1 + j.val := by
  simp [idxY, configIdxEquiv]

/--
@isnad1 id=lt.0h3v.s5.3d83e6a1448e from=translated src=- shape=4c32680f vocab=d667ef27
-/
lemma idxZ0_lt_idxZ (i : Fin k) : (idxZ0 : ConfigIdx k p) < idxZ i := by
  rw [Fin.lt_def, idxZ0_eq]
  simp [idxZ_val]

/--
@isnad1 id=lt.0h3v.s5.b583bfac5338 from=translated src=- shape=3fb7ab04 vocab=682e6169
-/
lemma idxZ0_lt_idxY (j : Fin p) : (idxZ0 : ConfigIdx k p) < idxY j := by
  rw [Fin.lt_def, idxZ0_eq]
  simp [idxY_val]

/--
@isnad1 id=lt.0h4v.s5.9690f00e3ce2 from=translated src=- shape=95248ef9 vocab=ea307eea
-/
lemma idxZ_lt_idxY (i : Fin k) (j : Fin p) : idxZ i < (idxY j : ConfigIdx k p) := by
  rw [Fin.lt_def]
  simp [idxZ_val, idxY_val]
  omega

/--
@isnad1 id=iff.0h4v.s5.e3d606ab5996 from=translated src=- shape=12f2d131 vocab=86001e93
-/
lemma idxZ_lt_idxZ_iff {i h : Fin k} :
    (idxZ i : ConfigIdx k p) < idxZ h ↔ i < h := by
  rw [Fin.lt_def, Fin.lt_def]
  simp [idxZ_val]

/--
@isnad1 id=ne.0h3v.s4.d3ef4eea9c2e from=translated src=- shape=4c32680f vocab=45e92d10
-/
lemma idxZ0_ne_idxZ (i : Fin k) : (idxZ0 : ConfigIdx k p) ≠ idxZ i :=
  (idxZ0_lt_idxZ i).ne

/--
@isnad1 id=ne.0h3v.s4.f80b6fe6380c from=translated src=- shape=3fb7ab04 vocab=435d2a99
-/
lemma idxZ0_ne_idxY (j : Fin p) : (idxZ0 : ConfigIdx k p) ≠ idxY j :=
  (idxZ0_lt_idxY j).ne

/--
@isnad1 id=ne.0h4v.s4.1cf59b0bd9e2 from=translated src=- shape=95248ef9 vocab=d4a0ded8
-/
lemma idxZ_ne_idxY (i : Fin k) (j : Fin p) : idxZ i ≠ (idxY j : ConfigIdx k p) :=
  (idxZ_lt_idxY i j).ne

/--
@isnad1 id=not.0h3v.s5.7964737e1073 from=translated src=- shape=a9e1c519 vocab=2a667a66
-/
lemma not_lt_idxZ0 (α : ConfigIdx k p) : ¬ α < idxZ0 := by
  rw [idxZ0_eq]
  exact Fin.not_lt_zero α

/--
@isnad1 id=eq.0h3v.s6.1034e371e9e1 from=translated src=- shape=65d57f33 vocab=7768191a
-/
lemma sum_configIdx (f : ConfigIdx k p → ℝ) :
    ∑ α, f α =
      f idxZ0 + ∑ i : Fin k, f (idxZ i) + ∑ j : Fin p, f (idxY j) := by
  rw [Fintype.sum_equiv (configIdxEquiv k p) f
    (fun x => f ((configIdxEquiv k p).symm x))
    (fun α => congrArg f ((configIdxEquiv k p).symm_apply_apply α).symm)]
  rw [Fintype.sum_sum_type, Fintype.sum_option]
  rfl

/-! ### MX06 — configuration vectors and Gram matrix -/

/-- Feature vector `z₀ = (1, 0)`. -/
def z0 : Fin 2 → ℝ := ![1, 0]

/-- Feature vector `zᵢ = √sᵢ (-1, tᵢ)`. -/
def zVec (s t : Fin k → ℝ) (i : Fin k) : Fin 2 → ℝ :=
  ![ -Real.sqrt (s i), Real.sqrt (s i) * t i ]

/-- Feature vector `yⱼ = √ρⱼ (xⱼ, 1)`. -/
def yVec (ρ x : Fin p → ℝ) (j : Fin p) : Fin 2 → ℝ :=
  ![ Real.sqrt (ρ j) * x j, Real.sqrt (ρ j) ]

/--
@isnad1 id=eq.0h0v.s4.3f170a65c582 from=translated src=- shape=012516b9 vocab=9302eb5e
-/
@[simp] lemma z0_zero : z0 0 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.347473094ff6 from=translated src=- shape=012516b9 vocab=9302eb5e
-/
@[simp] lemma z0_one : z0 1 = 0 := by simp [z0]
/--
@isnad1 id=eq.0h4v.s5.31b5460d755f from=translated src=- shape=9ee1bdcf vocab=43686387
-/
@[simp] lemma zVec_zero (s t : Fin k → ℝ) (i : Fin k) :
    zVec s t i 0 = -Real.sqrt (s i) := rfl
/--
@isnad1 id=eq.0h4v.s5.9e29a2101250 from=translated src=- shape=dcbf01a8 vocab=17e3a496
-/
@[simp] lemma zVec_one (s t : Fin k → ℝ) (i : Fin k) :
    zVec s t i 1 = Real.sqrt (s i) * t i := by simp [zVec]
/--
@isnad1 id=eq.0h4v.s5.a1a612d74f14 from=translated src=- shape=dcbf01a8 vocab=5ed41511
-/
@[simp] lemma yVec_zero (ρ x : Fin p → ℝ) (j : Fin p) :
    yVec ρ x j 0 = Real.sqrt (ρ j) * x j := rfl
/--
@isnad1 id=eq.0h4v.s5.c6c9585a0040 from=translated src=- shape=72b696a3 vocab=6efe7585
-/
@[simp] lemma yVec_one (ρ x : Fin p → ℝ) (j : Fin p) :
    yVec ρ x j 1 = Real.sqrt (ρ j) := by simp [yVec]

/-- The assembled configuration on `ConfigIdx`. -/
def configVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    ConfigIdx k p → Fin 2 → ℝ :=
  fun α =>
    match configIdxEquiv k p α with
    | Sum.inl none => z0
    | Sum.inl (some i) => zVec s t i
    | Sum.inr j => yVec ρ x j

/--
@isnad1 id=eq.0h6v.s5.a2df887d1229 from=translated src=- shape=7f0ea505 vocab=40cd454f
-/
lemma configVec_z0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    configVec s t ρ x idxZ0 = z0 := by
  simp [configVec, idxZ0]

/--
@isnad1 id=eq.0h7v.s5.f002e5e8cbbd from=translated src=- shape=96b8502f vocab=f664a2ff
-/
lemma configVec_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    configVec s t ρ x (idxZ i) = zVec s t i := by
  simp [configVec, idxZ]

/--
@isnad1 id=eq.0h7v.s5.1c64ee13d5f9 from=translated src=- shape=fa3b8692 vocab=98948ccf
-/
lemma configVec_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin p) :
    configVec s t ρ x (idxY j) = yVec ρ x j := by
  simp [configVec, idxY]

/-- Rows of the configuration, as a `ι × 2` matrix. -/
def configMat (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (Fin 2) ℝ :=
  fun α c => configVec s t ρ x α c

/-- Gram matrix of the configuration. -/
def Xconfig (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun a b => configVec s t ρ x a ⬝ᵥ configVec s t ρ x b

/--
@isnad1 id=eq.0h8v.s6.28e95717407b from=translated src=- shape=60b0a0db vocab=b4928855
-/
lemma Xconfig_apply (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (a b : ConfigIdx k p) :
    Xconfig s t ρ x a b = configVec s t ρ x a ⬝ᵥ configVec s t ρ x b :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.c6935bcf171f from=translated src=- shape=61e5c1ab vocab=15eeaae8
-/
lemma Xconfig_eq_mul_transpose (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Xconfig s t ρ x = configMat s t ρ x * (configMat s t ρ x)ᵀ := by
  ext a b
  simp [Xconfig, configMat, mul_apply, transpose_apply, dotProduct]

/--
@isnad1 id=issymm.0h6v.s5.edc2b0240078 from=translated src=- shape=848d3809 vocab=d3e7bcf8
-/
lemma Xconfig_isSymm (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (Xconfig s t ρ x).IsSymm := by
  rw [Xconfig_eq_mul_transpose]
  ext a b
  simp [mul_apply, transpose_apply, mul_comm]

/--
@isnad1 id=possemid.0h6v.s5.1b6eff3a9fc6 from=translated src=- shape=0b7cf1c0 vocab=97139ea6
-/
lemma Xconfig_posSemidef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (Xconfig s t ρ x).PosSemidef := by
  rw [Xconfig_eq_mul_transpose]
  have h :=
    (PosSemidef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef).mul_mul_conjTranspose_same
      (configMat s t ρ x)
  simpa [conjTranspose_eq_transpose_of_trivial] using h

/-! ### Inner products of configuration vectors -/

/--
@isnad1 id=eq.0h0v.s4.cd46efe99082 from=translated src=- shape=7df33ff6 vocab=39e67982
-/
lemma z0_dot_z0 : z0 ⬝ᵥ z0 = 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h4v.s5.869eb4e768fc from=translated src=- shape=2e4c0ad3 vocab=0adc595d
-/
lemma z0_dot_zVec (s t : Fin k → ℝ) (i : Fin k) :
    z0 ⬝ᵥ zVec s t i = -Real.sqrt (s i) := by
  simp [dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h4v.s5.d75a59d68aee from=translated src=- shape=caf16b39 vocab=2f6a2199
-/
lemma z0_dot_yVec (ρ x : Fin p → ℝ) (j : Fin p) :
    z0 ⬝ᵥ yVec ρ x j = Real.sqrt (ρ j) * x j := by
  simp [dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h5v.s6.899eda8bd226 from=translated src=- shape=1c1ba080 vocab=eacdcf5e
-/
lemma zVec_dot_zVec (s t : Fin k → ℝ) (i h : Fin k) :
    zVec s t i ⬝ᵥ zVec s t h =
      Real.sqrt (s i) * Real.sqrt (s h) * (1 + t i * t h) := by
  simp [dotProduct, Fin.sum_univ_two]
  ring

/--
@isnad1 id=eq.0h8v.s6.dc8606635fc8 from=translated src=- shape=286c1555 vocab=32dd6f2f
-/
lemma zVec_dot_yVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) (j : Fin p) :
    zVec s t i ⬝ᵥ yVec ρ x j =
      Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) := by
  simp [dotProduct, Fin.sum_univ_two]
  ring

/--
@isnad1 id=eq.0h6v.s5.3b5ed2e38f02 from=translated src=- shape=a0a42bdf vocab=f3d2a9ea
-/
lemma Xconfig_z0_z0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Xconfig s t ρ x idxZ0 idxZ0 = 1 := by
  rw [Xconfig_apply, configVec_z0, z0_dot_z0]

/--
@isnad1 id=eq.0h7v.s5.ba51d860dc11 from=translated src=- shape=45196024 vocab=51b9b87d
-/
lemma Xconfig_z0_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    Xconfig s t ρ x idxZ0 (idxZ i) = -Real.sqrt (s i) := by
  rw [Xconfig_apply, configVec_z0, configVec_z, z0_dot_zVec]

/--
@isnad1 id=eq.0h7v.s5.7c15d670f84d from=translated src=- shape=1afbb1d9 vocab=68378443
-/
lemma Xconfig_z0_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin p) :
    Xconfig s t ρ x idxZ0 (idxY j) = Real.sqrt (ρ j) * x j := by
  rw [Xconfig_apply, configVec_z0, configVec_y, z0_dot_yVec]

/--
@isnad1 id=eq.0h8v.s6.e0a62889b54d from=translated src=- shape=7b0bfc7d vocab=22842b67
-/
lemma Xconfig_z_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i h : Fin k) :
    Xconfig s t ρ x (idxZ i) (idxZ h) =
      Real.sqrt (s i) * Real.sqrt (s h) * (1 + t i * t h) := by
  rw [Xconfig_apply, configVec_z, configVec_z, zVec_dot_zVec]

/--
@isnad1 id=eq.0h8v.s6.fd89a3868fd2 from=translated src=- shape=c332dcdc vocab=b32ee712
-/
lemma Xconfig_z_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) (j : Fin p) :
    Xconfig s t ρ x (idxZ i) (idxY j) =
      Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) := by
  rw [Xconfig_apply, configVec_z, configVec_y, zVec_dot_yVec]

/-! ### MX07 — auxiliary scalars -/

/-- `Hᵢ = ∑ⱼ ρⱼ (xⱼ - tᵢ)₊²`. -/
def configH (t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) : ℝ :=
  ∑ j, ρ j * (max (x j - t i) 0) ^ 2

/-- `dᵢ = 1 + Hᵢ`. -/
def configD (t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) : ℝ :=
  1 + configH t ρ x i

/-- `σ = ∑ᵢ sᵢ`. -/
def configσ (s : Fin k → ℝ) : ℝ :=
  ∑ i, s i

/--
@isnad1 id=le.1h6v.s5.0aaeb8c894d5 from=translated src=- shape=e7f77a69 vocab=ae12cecf
-/
lemma configH_nonneg (t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) (i : Fin k) : 0 ≤ configH t ρ x i :=
  sum_nonneg fun j _ =>
    mul_nonneg (hρ j).le (sq_nonneg _)

/--
@isnad1 id=lt.1h6v.s5.0f0c04c149da from=translated src=- shape=e1593386 vocab=4f5f6392
-/
lemma configD_pos (t : Fin k → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 < ρ j)
    (x : Fin p → ℝ) (i : Fin k) : 0 < configD t ρ x i :=
  lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (configH_nonneg t hρ x i))

/--
@isnad1 id=le.1h2v.s5.ebbc5dc9e618 from=translated src=- shape=00c9b24f vocab=1d0be145
-/
lemma configσ_nonneg {s : Fin k → ℝ} (hs : ∀ i, 0 < s i) : 0 ≤ configσ s :=
  sum_nonneg fun i _ => (hs i).le

/-! ### Diagonal expansion of `M` -/

/--
@isnad1 id=eq.0h4v.s7.092821736c5f from=translated src=- shape=a06052b3 vocab=99103e0e
-/
lemma vecMulVec_sub_single_diag {n : Type*} [DecidableEq n] (u v a : n) :
    vecMulVec (e u - e v) (e u - e v) a a =
      if u = v then (0 : ℝ) else if a = u ∨ a = v then 1 else 0 := by
  rcases eq_or_ne u v with huv | huv
  · subst huv
    simp [vecMulVec_apply]
  · rw [vecMulVec_sub_single_apply huv]
    have : ¬ (a = u ∧ a = v) := fun h => huv (h.1.symm.trans h.2)
    split_ifs <;> simp_all

/--
@isnad1 id=eq.0h3v.s8.de5b8ad0ace3 from=translated src=- shape=b57b1e75 vocab=cf4d4a52
-/
lemma M_diag {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (X : Matrix n n ℝ) (a : n) :
    M X a a =
      X a a ^ 2 +
        ∑ q, (if a < q ∧ X a q < 0 then X a q ^ 2 else 0) +
          ∑ u, (if u < a ∧ X u a < 0 then X u a ^ 2 else 0) := by
  rw [M_apply]
  have hdecomp (u v : n) :
      laplacianCoeff X u v * vecMulVec (e u - e v) (e u - e v) a a =
        (if u = a ∧ a < v ∧ X a v < 0 then X a v ^ 2 else 0) +
          (if v = a ∧ u < a ∧ X u a < 0 then X u a ^ 2 else 0) := by
    unfold laplacianCoeff
    rw [vecMulVec_sub_single_diag]
    by_cases huv : u = v
    · subst huv
      have h1 : ¬ (u = a ∧ a < u ∧ X a u < 0) := by
        rintro ⟨rfl, hlt, _⟩
        exact lt_irrefl _ hlt
      have h2 : ¬ (u = a ∧ u < a ∧ X u a < 0) := by
        rintro ⟨rfl, hlt, _⟩
        exact lt_irrefl _ hlt
      simp [h1, h2]
    · simp only [huv, ite_false]
      by_cases hau : a = u
      · subst hau
        have hva : ¬ v = a := fun h => huv h.symm
        simp [hva]
      · by_cases hav : a = v
        · subst hav
          have hua : ¬ u = a := huv
          simp [hua]
        · have : ¬ (a = u ∨ a = v) := not_or.mpr ⟨hau, hav⟩
          simp [this, Ne.symm hau, Ne.symm hav]
  simp_rw [hdecomp, sum_add_distrib]
  have hs1 :
      ∑ u, ∑ v, (if u = a ∧ a < v ∧ X a v < 0 then X a v ^ 2 else 0) =
        ∑ v, (if a < v ∧ X a v < 0 then X a v ^ 2 else 0) := by
    simp [ite_and, sum_ite_eq']
  have hs2 :
      ∑ u, ∑ v, (if v = a ∧ u < a ∧ X u a < 0 then X u a ^ 2 else 0) =
        ∑ u, (if u < a ∧ X u a < 0 then X u a ^ 2 else 0) := by
    rw [sum_comm]
    simp [ite_and, sum_ite_eq']
  rw [hs1, hs2]
  ring

/-! ### MX08 — block entries -/

variable (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)

/--
@isnad1 id=lt.1h7v.s6.5b026309d63a from=translated src=- shape=dadcef73 vocab=d2d23fdc
-/
lemma Xconfig_z0_z_neg (hs : ∀ i, 0 < s i) (i : Fin k) :
    Xconfig s t ρ x idxZ0 (idxZ i) < 0 := by
  rw [Xconfig_z0_z]
  linarith [Real.sqrt_pos.mpr (hs i)]

/--
@isnad1 id=le.1h7v.s6.640d2147f78a from=translated src=- shape=28c34ca9 vocab=874186ae
-/
lemma Xconfig_z0_y_nonneg (hx : ∀ j, 0 ≤ x j) (j : Fin p) :
    0 ≤ Xconfig s t ρ x idxZ0 (idxY j) := by
  rw [Xconfig_z0_y]
  exact mul_nonneg (Real.sqrt_nonneg _) (hx j)

/--
@isnad1 id=lt.2h8v.s6.da6a5bec9315 from=translated src=- shape=2e272611 vocab=2694c60d
-/
lemma Xconfig_z_z_pos (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (i h : Fin k) :
    0 < Xconfig s t ρ x (idxZ i) (idxZ h) := by
  rw [Xconfig_z_z]
  have h1 : 0 < Real.sqrt (s i) := Real.sqrt_pos.mpr (hs i)
  have h2 : 0 < Real.sqrt (s h) := Real.sqrt_pos.mpr (hs h)
  have h3 : 0 < 1 + t i * t h := by nlinarith [ht i, ht h]
  positivity

/-- `M_{00} = 1 + σ`.
@isnad1 id=eq.2h6v.s7.a0525c20dbff from=translated src=- shape=64f18802 vocab=8b85a9ea
-/
lemma MX_z0_z0 (hs : ∀ i, 0 < s i) (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) idxZ0 idxZ0 = 1 + configσ s := by
  rw [M_diag, Xconfig_z0_z0]
  have hlt :
      ∑ β : ConfigIdx k p,
        (if β < idxZ0 ∧ Xconfig s t ρ x β idxZ0 < 0 then
          Xconfig s t ρ x β idxZ0 ^ 2 else 0) = 0 := by
    refine Fintype.sum_eq_zero _ fun β => ?_
    simp [not_lt_idxZ0 β]
  rw [hlt, add_zero]
  have hsum :
      ∑ γ : ConfigIdx k p,
        (if idxZ0 < γ ∧ Xconfig s t ρ x idxZ0 γ < 0 then
          Xconfig s t ρ x idxZ0 γ ^ 2 else 0) =
        configσ s := by
    rw [sum_configIdx]
    simp only [lt_irrefl (idxZ0 : ConfigIdx k p), false_and, ite_false, zero_add]
    have hz : ∑ i : Fin k,
        (if (idxZ0 : ConfigIdx k p) < idxZ (p := p) i ∧
            Xconfig s t ρ x idxZ0 (idxZ (p := p) i) < 0 then
          Xconfig s t ρ x idxZ0 (idxZ (p := p) i) ^ 2 else 0) =
        ∑ i, s i := by
      refine Fintype.sum_congr _ _ fun i => ?_
      have hlt' : (idxZ0 : ConfigIdx k p) < idxZ (p := p) i :=
        idxZ0_lt_idxZ (p := p) i
      have hneg : Xconfig s t ρ x idxZ0 (idxZ (p := p) i) < 0 :=
        Xconfig_z0_z_neg s t ρ x hs i
      rw [ite_eq_left (And.intro hlt' hneg), Xconfig_z0_z, neg_sq, Real.sq_sqrt (hs i).le]
    have hy : ∑ j : Fin p,
        (if (idxZ0 : ConfigIdx k p) < idxY (k := k) j ∧
            Xconfig s t ρ x idxZ0 (idxY (k := k) j) < 0 then
          Xconfig s t ρ x idxZ0 (idxY (k := k) j) ^ 2 else 0) = 0 := by
      refine Fintype.sum_eq_zero _ fun j => ?_
      simp [not_lt.mpr (Xconfig_z0_y_nonneg s t ρ x hx j)]
    rw [hz, hy, add_zero]
    rfl
  rw [hsum]
  ring

/-- `M_{0i} = 0`.
@isnad1 id=eq.0h7v.s6.736d69028509 from=translated src=- shape=7bbeb954 vocab=0fb64db6
-/
lemma MX_z0_z (i : Fin k) :
    M (Xconfig s t ρ x) idxZ0 (idxZ i) = 0 := by
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) (idxZ0_ne_idxZ (p := p) i)]
  rw [posPart_apply, Xconfig_z0_z, max_eq_right (neg_nonpos.mpr (Real.sqrt_nonneg _)),
    zero_pow (by decide)]

/-- `M_{0ybar} = ρⱼ xⱼ²`.
@isnad1 id=eq.2h7v.s7.a27ef3e0e313 from=translated src=- shape=cbf97355 vocab=791147bd
-/
lemma MX_z0_y (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) (j : Fin p) :
    M (Xconfig s t ρ x) idxZ0 (idxY j) = ρ j * x j ^ 2 := by
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) (idxZ0_ne_idxY (k := k) j)]
  rw [posPart_apply, Xconfig_z0_y]
  have hnn : 0 ≤ Real.sqrt (ρ j) * x j :=
    mul_nonneg (Real.sqrt_nonneg _) (hx j)
  rw [max_eq_left hnn, mul_pow, Real.sq_sqrt (hρ j).le]

/-- Off-diagonal `z`-block: `M_{ih} = sᵢ sₕ (1 + tᵢ tₕ)²` for `i ≠ h`.
@isnad1 id=eq.3h8v.s7.3bf9ce8a20ef from=translated src=- shape=d991712b vocab=d1769e85
-/
lemma MX_z_z_of_ne (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) {i h : Fin k}
    (hih : i ≠ h) :
    M (Xconfig s t ρ x) (idxZ i) (idxZ h) =
      s i * s h * (1 + t i * t h) ^ 2 := by
  have hidx : (idxZ (p := p) i) ≠ idxZ h := by
    intro hEq
    have hval := congrArg Fin.val hEq
    simp only [idxZ_val, Nat.add_right_cancel_iff] at hval
    exact hih (Fin.ext hval)
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) hidx]
  rw [posPart_apply, Xconfig_z_z]
  have hpos : 0 ≤ Real.sqrt (s i) * Real.sqrt (s h) * (1 + t i * t h) := by
    have := Xconfig_z_z_pos s t ρ x hs ht i h
    rw [Xconfig_z_z] at this
    exact this.le
  rw [max_eq_left hpos, mul_pow, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hs h).le]

/-- `M_{iybar} = sᵢ ρⱼ (tᵢ - xⱼ)₊²`.
@isnad1 id=eq.2h8v.s7.359bb5aefd06 from=translated src=- shape=543d65b5 vocab=cb19bbb1
-/
lemma MX_z_y (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (i : Fin k) (j : Fin p) :
    M (Xconfig s t ρ x) (idxZ i) (idxY j) =
      s i * ρ j * (max (t i - x j) 0) ^ 2 := by
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) (idxZ_ne_idxY (p := p) i j)]
  rw [posPart_apply, Xconfig_z_y]
  set c := Real.sqrt (s i) * Real.sqrt (ρ j)
  have hc : 0 < c :=
    mul_pos (Real.sqrt_pos.mpr (hs i)) (Real.sqrt_pos.mpr (hρ j))
  have hfac : max (c * (t i - x j)) 0 = c * max (t i - x j) 0 := by
    rcases le_total 0 (t i - x j) with htx | htx
    · rw [max_eq_left (mul_nonneg hc.le htx), max_eq_left htx]
    · have : c * (t i - x j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le htx
      rw [max_eq_right this, max_eq_right htx, mul_zero]
  rw [hfac, mul_pow]
  have hc2 : c ^ 2 = s i * ρ j := by
    simp [c, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hρ j).le]
  rw [hc2]

/-- Diagonal `z`-block: `M_{ii} = sᵢ² (1 + tᵢ²)² + sᵢ dᵢ`.
@isnad1 id=eq.3h7v.s7.c202652b8e38 from=translated src=- shape=9f94fdc0 vocab=e41abd3d
-/
lemma MX_z_z_diag (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (i : Fin k) :
    M (Xconfig s t ρ x) (idxZ i) (idxZ i) =
      s i * s i * (1 + t i * t i) ^ 2 + s i * configD t ρ x i := by
  rw [M_diag, Xconfig_z_z]
  have hXii :
      (Real.sqrt (s i) * Real.sqrt (s i) * (1 + t i * t i)) ^ 2 =
        s i * s i * (1 + t i * t i) ^ 2 := by
    rw [Real.mul_self_sqrt (hs i).le, mul_pow, pow_two]
  rw [hXii]
  have hlow :
      ∑ β : ConfigIdx k p,
        (if β < idxZ i ∧ Xconfig s t ρ x β (idxZ i) < 0 then
          Xconfig s t ρ x β (idxZ i) ^ 2 else 0) =
        s i := by
    rw [sum_configIdx]
    have hz0 :
        (if (idxZ0 : ConfigIdx k p) < idxZ (p := p) i ∧
            Xconfig s t ρ x idxZ0 (idxZ (p := p) i) < 0 then
          Xconfig s t ρ x idxZ0 (idxZ (p := p) i) ^ 2 else 0) = s i := by
      have hlt' : (idxZ0 : ConfigIdx k p) < idxZ (p := p) i :=
        idxZ0_lt_idxZ (p := p) i
      have hneg : Xconfig s t ρ x idxZ0 (idxZ (p := p) i) < 0 :=
        Xconfig_z0_z_neg s t ρ x hs i
      rw [ite_eq_left (And.intro hlt' hneg), Xconfig_z0_z, neg_sq, Real.sq_sqrt (hs i).le]
    have hz : ∑ h : Fin k,
        (if idxZ (p := p) h < idxZ (p := p) i ∧
            Xconfig s t ρ x (idxZ (p := p) h) (idxZ (p := p) i) < 0 then
          Xconfig s t ρ x (idxZ (p := p) h) (idxZ (p := p) i) ^ 2 else 0) = 0 := by
      refine Fintype.sum_eq_zero _ fun h => ?_
      simp [not_lt.mpr (Xconfig_z_z_pos s t ρ x hs ht h i).le]
    have hy : ∑ j : Fin p,
        (if idxY (k := k) j < idxZ (p := p) i ∧
            Xconfig s t ρ x (idxY (k := k) j) (idxZ (p := p) i) < 0 then
          Xconfig s t ρ x (idxY (k := k) j) (idxZ (p := p) i) ^ 2 else 0) = 0 := by
      refine Fintype.sum_eq_zero _ fun j => ?_
      simp [not_lt.mpr (idxZ_lt_idxY (p := p) i j).le]
    rw [hz0, hz, hy]
    ring
  have hup :
      ∑ γ : ConfigIdx k p,
        (if idxZ i < γ ∧ Xconfig s t ρ x (idxZ i) γ < 0 then
          Xconfig s t ρ x (idxZ i) γ ^ 2 else 0) =
        s i * configH t ρ x i := by
    rw [sum_configIdx]
    simp only [not_lt.mpr (idxZ0_lt_idxZ (p := p) i).le, false_and, ite_false, zero_add]
    have hz : ∑ h : Fin k,
        (if idxZ (p := p) i < idxZ (p := p) h ∧
            Xconfig s t ρ x (idxZ (p := p) i) (idxZ (p := p) h) < 0 then
          Xconfig s t ρ x (idxZ (p := p) i) (idxZ (p := p) h) ^ 2 else 0) = 0 := by
      refine Fintype.sum_eq_zero _ fun h => ?_
      simp [not_lt.mpr (Xconfig_z_z_pos s t ρ x hs ht i h).le]
    have hy : ∑ j : Fin p,
        (if idxZ (p := p) i < idxY (k := k) j ∧
            Xconfig s t ρ x (idxZ (p := p) i) (idxY (k := k) j) < 0 then
          Xconfig s t ρ x (idxZ (p := p) i) (idxY (k := k) j) ^ 2 else 0) =
        s i * configH t ρ x i := by
      simp only [idxZ_lt_idxY (p := p), true_and, Xconfig_z_y, configH, Finset.mul_sum]
      refine Fintype.sum_congr _ _ fun j => ?_
      have hc : 0 < Real.sqrt (s i) * Real.sqrt (ρ j) :=
        mul_pos (Real.sqrt_pos.mpr (hs i)) (Real.sqrt_pos.mpr (hρ j))
      by_cases htx : t i < x j
      · have hneg : Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) < 0 :=
          mul_neg_of_pos_of_neg hc (sub_neg.mpr htx)
        have hmax : max (x j - t i) 0 = x j - t i :=
          max_eq_left (sub_nonneg.mpr htx.le)
        simp only [hneg, ↓reduceIte, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hρ j).le, hmax]
        have : t i - x j = -(x j - t i) := by ring
        rw [this, neg_sq]
        ring
      · have hnn : ¬ Real.sqrt (s i) * Real.sqrt (ρ j) * (t i - x j) < 0 :=
          not_lt.mpr (mul_nonneg hc.le (sub_nonneg.mpr (le_of_not_gt htx)))
        have hmax : max (x j - t i) 0 = 0 :=
          max_eq_right (sub_nonpos.mpr (le_of_not_gt htx))
        simp [hnn, hmax]
    rw [hz, hy, zero_add]
  rw [hlow, hup, configD]
  ring

/-- Combined `z`-block formula, including the Kronecker term.
@isnad1 id=eq.3h8v.s8.a3c3aa223a21 from=translated src=- shape=5e3f9dc8 vocab=82308904
-/
lemma MX_z_z (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (i h : Fin k) :
    M (Xconfig s t ρ x) (idxZ i) (idxZ h) =
      s i * s h * (1 + t i * t h) ^ 2 +
        (if i = h then s i * configD t ρ x i else 0) := by
  rcases eq_or_ne i h with rfl | hih
  · simp [MX_z_z_diag s t ρ x hs ht hρ i]
  · simp [hih, MX_z_z_of_ne s t ρ x hs ht hih]

/-! ### MX09 — first column -/

/--
@isnad1 id=lt.2h6v.s7.9d6b96a3bccc from=translated src=- shape=7ba1eaab vocab=4aae1d1a
-/
lemma MX_z0_z0_pos (hs : ∀ i, 0 < s i) (hx : ∀ j, 0 ≤ x j) :
    0 < M (Xconfig s t ρ x) idxZ0 idxZ0 := by
  rw [MX_z0_z0 s t ρ x hs hx]
  linarith [configσ_nonneg hs]

/--
@isnad1 id=le.3h7v.s7.22a0068759f8 from=translated src=- shape=64d983c8 vocab=4aae1d1a
-/
lemma MX_z0_nonneg (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    (α : ConfigIdx k p) :
    0 ≤ M (Xconfig s t ρ x) idxZ0 α := by
  rw [← (configIdxEquiv k p).symm_apply_apply α]
  rcases configIdxEquiv k p α with o | j
  · rcases o with _ | i
    · simpa [idxZ0] using (MX_z0_z0_pos s t ρ x hs hx).le
    · simpa [idxZ] using (MX_z0_z s t ρ x i).symm.le
  · change 0 ≤ M (Xconfig s t ρ x) idxZ0 (idxY j)
    rw [MX_z0_y s t ρ x hρ hx]
    exact mul_nonneg (hρ j).le (sq_nonneg _)

end

end BollobasNikiforov
