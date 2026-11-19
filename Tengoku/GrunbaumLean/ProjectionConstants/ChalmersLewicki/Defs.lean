/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.ProjectionConstants.Foundations.OrthProj
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Analysis.MeanInequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Chalmers–Lewicki functional and quasimaximal projection constants

For a finite index set `ι` (think `ι = {1, …, N}`), a weight vector `t ∈ ℝ^ι_+` with `‖t‖₂ = 1`
and an orthogonal projection matrix `P` of rank `m` we consider
`weightedAbsSum t P = ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`. Writing `P = Uᴴ U` with `U Uᴴ = 1`, this is the expression
`∑ᵢⱼ tᵢ tⱼ |(Uᴴ U)ᵢⱼ|` of [Deręgowska–Lewandowska, Theorem 1.1].

* `clConst 𝕜 m ι` : `sup { ∑ tᵢ tⱼ |Pᵢⱼ| }`, the right-hand side of the formula of Chalmers and
  Lewicki (Theorem 1.1): by `ChalmersLewicki.Formula`, it equals `λ_𝕜(m, N)`.
* `quasiRelConst 𝕜 m ι` : the **quasimaximal relative projection constant**
  `μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |Pᵢⱼ| }` (equal weights), see (2) in the paper.
* `quasiMaxConst 𝕜 m` : the **quasimaximal absolute projection constant**
  `μ_𝕜(m) = sup_N μ_𝕜(m, N)`, see (3) in the paper.

The paper phrases these with matrices `U ∈ 𝕜^{m×N}`, `U Uᴴ = I_m`; the equivalence with our
formulation (via `P = Uᴴ U`) is `quasiRelConst_eq_sSup_parseval` and `clConst_eq_sSup_parseval`.

We also prove the elementary bound `∑ tᵢ tⱼ |Pᵢⱼ| ≤ √m` (Cauchy–Schwarz), which later yields
the Kadec–Snobar estimate `λ(m) ≤ √m`.
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- `∑ᵢⱼ |Pᵢⱼ|`.-/
noncomputable def absSum (P : Matrix ι ι 𝕜) : ℝ := ∑ i, ∑ j, ‖P i j‖

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`.-/
noncomputable def weightedAbsSum (t : ι → ℝ) (P : Matrix ι ι 𝕜) : ℝ :=
  ∑ i, ∑ j, t i * t j * ‖P i j‖

/-- A nonnegative weight vector of Euclidean norm one.-/
structure IsUnitWeight (t : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ t i
  sum_sq : ∑ i, t i ^ 2 = 1

variable (𝕜 ι) in
/-- The **Chalmers–Lewicki quantity** `sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫ₘ(ι) }`,
the right-hand side of [Deręgowska–Lewandowska, Theorem 1.1].-/
noncomputable def clConst (m : ℕ) : ℝ :=
  sSup {x | ∃ t P, IsUnitWeight t ∧ P ∈ orthProjs 𝕜 ι m ∧ x = weightedAbsSum t P}

variable (𝕜 ι) in
/-- The **quasimaximal relative projection constant**
`μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |Pᵢⱼ| : P ∈ 𝒫ₘ }`, see (2) in [Deręgowska–Lewandowska].-/
noncomputable def quasiRelConst (m : ℕ) : ℝ :=
  sSup {x | ∃ P ∈ orthProjs 𝕜 ι m, x = absSum P / Fintype.card ι}

variable (𝕜) in
/-- The **quasimaximal absolute projection constant** `μ_𝕜(m) = sup_N μ_𝕜(m, N)`, see (3) in
[Deręgowska–Lewandowska].-/
noncomputable def quasiMaxConst (m : ℕ) : ℝ := ⨆ N : ℕ, quasiRelConst 𝕜 (Fin N) m

/-! ### Elementary estimates -/

/--
@isnad1 id=le.0h3v.s4.335416c3460d from=translated src=- shape=a0e4516f vocab=7b815e64
-/
lemma absSum_nonneg (P : Matrix ι ι 𝕜) : 0 ≤ absSum P :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

/--
@isnad1 id=le.1h4v.s5.5990f35ea350 from=translated src=- shape=b73580ce vocab=52394f5f
-/
lemma weightedAbsSum_nonneg {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (P : Matrix ι ι 𝕜) :
    0 ≤ weightedAbsSum t P :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => by have := ht i; have := ht j; positivity

/-- The Frobenius norm of an orthogonal projection of rank `m` is `√m`.
@isnad1 id=eq.1h4v.s6.89bd28f48336 from=translated src=- shape=6c116026 vocab=d6d6ab25
-/
lemma sum_norm_sq_of_mem_orthProjs {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    ∑ i, ∑ j, ‖P i j‖ ^ 2 = m := by
  rw [← sum_re_diag hP]
  exact sum_congr rfl fun i _ => (hP.1.re_diag_eq_sum_row i).symm

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ √m` by the Cauchy–Schwarz inequality.
@isnad1 id=le.2h5v.s6.033250a0fb96 from=translated src=- shape=13f2588c vocab=005ae1c4
-/
theorem weightedAbsSum_le_sqrt {m : ℕ} {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : weightedAbsSum t P ≤ √m := by
  have hcs : (∑ ij : ι × ι, (t ij.1 * t ij.2) * ‖P ij.1 ij.2‖) ^ 2 ≤
      (∑ ij : ι × ι, (t ij.1 * t ij.2) ^ 2) * ∑ ij : ι × ι, ‖P ij.1 ij.2‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq _ _ _
  have h1 : ∑ ij : ι × ι, (t ij.1 * t ij.2) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow, ← mul_sum, ← sum_mul, ht.sum_sq, one_mul]
  have h2 : ∑ ij : ι × ι, ‖P ij.1 ij.2‖ ^ 2 = m := by
    rw [Fintype.sum_prod_type]
    exact sum_norm_sq_of_mem_orthProjs hP
  have h3 : weightedAbsSum t P = ∑ ij : ι × ι, (t ij.1 * t ij.2) * ‖P ij.1 ij.2‖ := by
    rw [Fintype.sum_prod_type]; rfl
  rw [h1, h2, one_mul] at hcs
  rw [h3]
  exact Real.le_sqrt_of_sq_le hcs

/-- The uniform weight `tᵢ = 1/√N`.
@isnad1 id=isunitwe.0h1v.s5.ee854eb5d7f0 from=translated src=- shape=48fd0902 vocab=cf9e72db
-/
lemma isUnitWeight_uniform [Nonempty ι] :
    IsUnitWeight (fun _ : ι => 1 / √(Fintype.card ι : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [div_pow, one_pow, Real.sq_sqrt hN.le, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/--
@isnad1 id=eq.0h3v.s6.f135481b1286 from=translated src=- shape=e235058a vocab=a49ea295
-/
lemma weightedAbsSum_uniform [Nonempty ι] (P : Matrix ι ι 𝕜) :
    weightedAbsSum (fun _ : ι => 1 / √(Fintype.card ι : ℝ)) P = absSum P / Fintype.card ι := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h : 1 / √(Fintype.card ι : ℝ) * (1 / √(Fintype.card ι : ℝ)) = 1 / Fintype.card ι := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hN.le]
  unfold weightedAbsSum absSum
  simp only [Finset.sum_div]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [h]
  ring

/-- `(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ √m`.
@isnad1 id=le.1h4v.s6.19f608e72926 from=translated src=- shape=6c954884 vocab=047f1e65
-/
theorem absSum_div_card_le_sqrt {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    absSum P / Fintype.card ι ≤ √m := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [← weightedAbsSum_uniform]
    exact weightedAbsSum_le_sqrt isUnitWeight_uniform hP

/-! ### Basic properties of the constants -/

section Constants

variable {m : ℕ}

/--
@isnad1 id=bddabove.0h3v.s6.3c4c664e7864 from=translated src=- shape=b42e7ce9 vocab=a84e2139
-/
lemma bddAbove_clConst_set :
    BddAbove {x | ∃ t P, IsUnitWeight t ∧ P ∈ orthProjs 𝕜 ι m ∧ x = weightedAbsSum t P} :=
  ⟨√m, by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_le_sqrt ht hP⟩

/--
@isnad1 id=bddabove.0h3v.s6.2beaf1268260 from=translated src=- shape=a263c7a9 vocab=c15f884e
-/
lemma bddAbove_quasiRelConst_set :
    BddAbove {x | ∃ P ∈ orthProjs 𝕜 ι m, x = absSum P / Fintype.card ι} :=
  ⟨√m, by rintro _ ⟨P, hP, rfl⟩; exact absSum_div_card_le_sqrt hP⟩

/--
@isnad1 id=le.2h5v.s6.0b4acd2d66d4 from=translated src=- shape=49412fe8 vocab=5aeb0e5d
-/
lemma le_clConst {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : weightedAbsSum t P ≤ clConst 𝕜 ι m :=
  le_csSup bddAbove_clConst_set ⟨t, P, ht, hP, rfl⟩

/--
@isnad1 id=le.0h3v.s4.6dd2040110d9 from=translated src=- shape=535d864d vocab=616c345d
-/
lemma clConst_le_sqrt : clConst 𝕜 ι m ≤ √m :=
  Real.sSup_le (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_le_sqrt ht hP)
    (Real.sqrt_nonneg _)

/--
@isnad1 id=le.0h3v.s4.807c30f2f761 from=translated src=- shape=f8cabb17 vocab=659bfbef
-/
lemma clConst_nonneg : 0 ≤ clConst 𝕜 ι m :=
  Real.sSup_nonneg (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_nonneg ht.nonneg P)

/--
@isnad1 id=le.2h4v.s6.d0eb07a2b752 from=translated src=- shape=963f41e1 vocab=5aeb0e5d
-/
lemma clConst_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t P, IsUnitWeight t → P ∈ orthProjs 𝕜 ι m → weightedAbsSum t P ≤ c) :
    clConst 𝕜 ι m ≤ c :=
  Real.sSup_le (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact h t P ht hP) hc

/--
@isnad1 id=le.1h4v.s6.3ba7995b6265 from=translated src=- shape=da5c6d91 vocab=d98380ad
-/
lemma le_quasiRelConst {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    absSum P / Fintype.card ι ≤ quasiRelConst 𝕜 ι m :=
  le_csSup bddAbove_quasiRelConst_set ⟨P, hP, rfl⟩

/--
@isnad1 id=le.0h3v.s4.132b8564d924 from=translated src=- shape=535d864d vocab=bec4ba8e
-/
lemma quasiRelConst_le_sqrt : quasiRelConst 𝕜 ι m ≤ √m :=
  Real.sSup_le (by rintro _ ⟨P, hP, rfl⟩; exact absSum_div_card_le_sqrt hP) (Real.sqrt_nonneg _)

/--
@isnad1 id=le.0h3v.s4.f5cb12d3cd0d from=translated src=- shape=f8cabb17 vocab=4f848352
-/
lemma quasiRelConst_nonneg : 0 ≤ quasiRelConst 𝕜 ι m :=
  Real.sSup_nonneg (by rintro _ ⟨P, -, rfl⟩; exact div_nonneg (absSum_nonneg P) (by positivity))

/--
@isnad1 id=le.2h4v.s6.1d7897ec86d9 from=translated src=- shape=1f269b32 vocab=d98380ad
-/
lemma quasiRelConst_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ P ∈ orthProjs 𝕜 ι m, absSum P / Fintype.card ι ≤ c) : quasiRelConst 𝕜 ι m ≤ c :=
  Real.sSup_le (by rintro _ ⟨P, hP, rfl⟩; exact h P hP) hc

/-- `μ(m, N) ≤ λ`-formula: equal weights are a special case.
@isnad1 id=le.0h3v.s4.3545d2e47b04 from=translated src=- shape=ada6dc4a vocab=c413371a
-/
lemma quasiRelConst_le_clConst : quasiRelConst 𝕜 ι m ≤ clConst 𝕜 ι m := by
  refine quasiRelConst_le clConst_nonneg fun P hP => ?_
  cases isEmpty_or_nonempty ι
  · simp [absSum, clConst_nonneg]
  · rw [← weightedAbsSum_uniform]
    exact le_clConst isUnitWeight_uniform hP

/--
@isnad1 id=bddabove.0h2v.s4.b85dfcf58407 from=translated src=- shape=0a1f8f2d vocab=2f6ce053
-/
lemma bddAbove_range_quasiRelConst : BddAbove (Set.range fun N : ℕ => quasiRelConst 𝕜 (Fin N) m) :=
  ⟨√m, by rintro _ ⟨N, rfl⟩; exact quasiRelConst_le_sqrt⟩

/--
@isnad1 id=le.0h3v.s4.f1ade01b5fa8 from=translated src=- shape=0f634831 vocab=9881c7f1
-/
lemma quasiRelConst_le_quasiMaxConst (N : ℕ) : quasiRelConst 𝕜 (Fin N) m ≤ quasiMaxConst 𝕜 m :=
  le_ciSup bddAbove_range_quasiRelConst N

/--
@isnad1 id=le.0h2v.s4.f6a73e1e21e9 from=translated src=- shape=20503de9 vocab=e1e75921
-/
lemma quasiMaxConst_le_sqrt : quasiMaxConst 𝕜 m ≤ √m :=
  Real.iSup_le (fun _ => quasiRelConst_le_sqrt) (Real.sqrt_nonneg _)

/--
@isnad1 id=le.0h2v.s4.fe41de225bb3 from=translated src=- shape=47213694 vocab=4da2d577
-/
lemma quasiMaxConst_nonneg : 0 ≤ quasiMaxConst 𝕜 m :=
  Real.iSup_nonneg fun _ => quasiRelConst_nonneg

/--
@isnad1 id=le.2h3v.s5.60cba0b70dd9 from=translated src=- shape=f514e3a7 vocab=9881c7f1
-/
lemma quasiMaxConst_le {c : ℝ} (hc : 0 ≤ c) (h : ∀ N, quasiRelConst 𝕜 (Fin N) m ≤ c) :
    quasiMaxConst 𝕜 m ≤ c :=
  Real.iSup_le h hc

end Constants

/-! ### Relabelling the index set -/

section Reindex

variable {κ : Type*} [Fintype κ]

/--
@isnad1 id=mem.1h6v.s6.fa1cdddc6e6f from=translated src=- shape=d51e5725 vocab=c18da9f0
-/
lemma submatrix_mem_orthProjs {m : ℕ} (e : κ ≃ ι) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : P.submatrix e e ∈ orthProjs 𝕜 κ m := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, hP.1.herm]
  · rw [Matrix.submatrix_mul_equiv, hP.1.idem]
  · rw [← hP.2]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun x => P x x)

/--
@isnad1 id=eq.0h5v.s6.f0aa0e25eae6 from=translated src=- shape=5f99eed6 vocab=8ce77d3d
-/
lemma absSum_submatrix (e : κ ≃ ι) (P : Matrix ι ι 𝕜) : absSum (P.submatrix e e) = absSum P := by
  simp only [absSum, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun i => ∑ j, ‖P i (e j)‖)]
  exact sum_congr rfl fun i _ => Equiv.sum_comp e (fun j => ‖P i j‖)

/--
@isnad1 id=le.0h5v.s5.4d32b52e5097 from=translated src=- shape=42c6cb9b vocab=dd167595
-/
lemma quasiRelConst_le_of_equiv {m : ℕ} (e : κ ≃ ι) :
    quasiRelConst 𝕜 ι m ≤ quasiRelConst 𝕜 κ m := by
  refine quasiRelConst_le quasiRelConst_nonneg fun P hP => ?_
  have h := le_quasiRelConst (submatrix_mem_orthProjs e hP)
  rwa [absSum_submatrix, Fintype.card_congr e] at h

/--
@isnad1 id=eq.0h5v.s5.3d0b1f4ab91c from=translated src=- shape=3d16668b vocab=106c3683
-/
lemma quasiRelConst_congr {m : ℕ} (e : κ ≃ ι) : quasiRelConst 𝕜 κ m = quasiRelConst 𝕜 ι m :=
  le_antisymm (quasiRelConst_le_of_equiv e.symm) (quasiRelConst_le_of_equiv e)

/-- `μ(m, ι) ≤ μ(m)` for every finite index type `ι`.
@isnad1 id=le.0h3v.s4.2cf1af2d92d3 from=translated src=- shape=c1d8cc7f vocab=4442e15a
-/
lemma quasiRelConst_le_quasiMaxConst' {m : ℕ} : quasiRelConst 𝕜 ι m ≤ quasiMaxConst 𝕜 m := by
  rw [← quasiRelConst_congr (Fintype.equivFin ι).symm]
  exact quasiRelConst_le_quasiMaxConst _

end Reindex

/-! ### The formulation of the paper, with `U Uᴴ = I` -/

section Paper

variable [DecidableEq ι]

/-- **(2)** in the paper: `μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |(Uᴴ U)ᵢⱼ| : U ∈ 𝕜^{m×N}, U Uᴴ = I_m }`.
@isnad1 id=eq.0h3v.s8.dbe931309847 from=translated src=- shape=b2142bcc vocab=c28e23c2
-/
theorem quasiRelConst_eq_sSup_parseval (m : ℕ) :
    quasiRelConst 𝕜 ι m = sSup {x | ∃ U : Matrix (Fin m) ι 𝕜, U * Uᴴ = 1 ∧
      x = (1 / Fintype.card ι) * ∑ i, ∑ j, ‖(Uᴴ * U) i j‖} := by
  unfold quasiRelConst
  congr 1
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
    exact ⟨U, hU, by rw [absSum, one_div_mul_eq_div]⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨_, conjTranspose_mul_self_mem_orthProjs hU, by rw [absSum, one_div_mul_eq_div]⟩

/-- The right-hand side of **Theorem 1.1**, in the formulation of the paper.
@isnad1 id=eq.0h3v.s8.dccd3eee8d52 from=translated src=- shape=fbeeee54 vocab=345786cb
-/
theorem clConst_eq_sSup_parseval (m : ℕ) :
    clConst 𝕜 ι m = sSup {x | ∃ (t : ι → ℝ) (U : Matrix (Fin m) ι 𝕜), (∀ i, 0 ≤ t i) ∧
      ∑ i, t i ^ 2 = 1 ∧ U * Uᴴ = 1 ∧ x = ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖} := by
  unfold clConst
  congr 1
  ext x
  constructor
  · rintro ⟨t, P, ht, hP, rfl⟩
    obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
    exact ⟨t, U, ht.nonneg, ht.sum_sq, hU, rfl⟩
  · rintro ⟨t, U, ht0, ht1, hU, rfl⟩
    exact ⟨t, _, ⟨ht0, ht1⟩, conjTranspose_mul_self_mem_orthProjs hU, rfl⟩

end Paper

end ProjectionConstants
