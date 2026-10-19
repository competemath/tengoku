/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Algebra.Polynomial.Degree.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hankel minors of holomorphic families of sequences

A sequence `s : ℕ → ℂ` satisfies a linear recurrence with characteristic polynomial `p ≠ 0` if
`∑ j, p_j s (k + j) = 0` for all `k`. Then every square minor of the Hankel matrix `(s (i + j))`
of size larger than the degree of `p`, with columns `0, …, m`, vanishes.

For a family `μ k b` of sequences depending holomorphically on `b` in a connected open set `D`,
satisfying such recurrences for all `b` in a nonempty open subset, Baire's theorem and the
identity theorem produce a size `d` and rows `I` such that the minor with rows `I` and columns
`0, …, d - 1` does not vanish identically, while all minors of size `d + 1` with columns
`0, …, d` vanish identically on `D`. Expanding the determinant of the minor with rows `I`,
completed by a last row `(t ^ j)_j`, then gives a polynomial in `t` with holomorphic
coefficients satisfying the recurrence for every `b ∈ D`.

## Main definitions

- `hankelMinor μ I b`: the determinant of `(μ (I i + j) b)_{i, j < m}`.
- `hankelCof μ I j b`: the cofactors of the last row of the matrix obtained from the minor with
  rows `I` by adding a last row.

## Main results

- `Matrix.det_of_snoc`: expansion of a determinant along an added last row.
- `hankelMinor_eq_zero_of_recurrence`: large minors of a recurrent sequence vanish.
- `sum_hankelCof_mul`: the cofactors satisfy the recurrence given by the vanishing of the larger
  minors.
- `exists_hankelMinor_ne_zero_forall_eq_zero`: the choice of `d` and `I` for holomorphic families.
-/

open Set Filter Polynomial
open scoped Topology

/-- The Hankel minor `det (μ (I i + j) b)_{i, j < m}` with rows `I` and columns `0, …, m - 1`. -/
noncomputable def hankelMinor {X : Type*} (μ : ℕ → X → ℂ) {m : ℕ} (I : Fin m → ℕ) (b : X) : ℂ :=
  (Matrix.of fun i j : Fin m ↦ μ (I i + j) b).det

/-- The cofactor at position `j` of the last row of the matrix with rows `(μ (I i + ·) b)_i` and
an added last row. -/
noncomputable def hankelCof {X : Type*} (μ : ℕ → X → ℂ) {d : ℕ} (I : Fin d → ℕ) (j : Fin (d + 1))
    (b : X) : ℂ :=
  (-1) ^ (d + (j : ℕ)) * (Matrix.of fun i j' : Fin d ↦ μ (I i + j.succAbove j') b).det

/-- Expansion of a determinant along an added last row. -/
theorem Matrix.det_of_snoc {R : Type*} [CommRing R] {d : ℕ} (A : Fin d → Fin (d + 1) → R)
    (r : Fin (d + 1) → R) :
    (Matrix.of (Fin.snoc A r : Fin (d + 1) → Fin (d + 1) → R)).det =
      ∑ j, r j * ((-1) ^ (d + (j : ℕ)) * (Matrix.of fun i j' ↦ A i (j.succAbove j')).det) := by
  rw [Matrix.det_succ_row _ (Fin.last d)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsub : (Matrix.of (Fin.snoc A r : Fin (d + 1) → Fin (d + 1) → R)).submatrix
      (Fin.last d).succAbove j.succAbove = Matrix.of fun i j' ↦ A i (j.succAbove j') := by
    ext i j'
    simp [Fin.succAbove_last]
  rw [hsub]
  simp only [Matrix.of_apply, Fin.snoc_last, Fin.val_last]
  ring

section Sequence

variable {X : Type*} {μ : ℕ → X → ℂ}

/-- If `μ · b` satisfies a linear recurrence with characteristic polynomial `p ≠ 0`, then the
Hankel minors of size `m + 1 > deg p` vanish at `b`. -/
theorem hankelMinor_eq_zero_of_recurrence {b : X} {p : ℂ[X]} (hp : p ≠ 0)
    (hrec : ∀ k, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * μ (k + j) b = 0) {m : ℕ}
    (hm : p.natDegree ≤ m) (J : Fin (m + 1) → ℕ) : hankelMinor μ J b = 0 := by
  classical
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun j ↦ p.coeff j, fun h ↦ ?_, ?_⟩
  · have := congrFun h ⟨p.natDegree, by omega⟩
    exact hp (leadingCoeff_eq_zero.mp this)
  · funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ μ (J i + j) b * p.coeff j),
      ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : p.natDegree + 1 ≤ m + 1))]
    · rw [← hrec (J i)]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    · intro j _ hj
      rw [coeff_eq_zero_of_natDegree_lt (by simpa using hj), mul_zero]

/-- The cofactor of the last position is the Hankel minor with rows `I`. -/
theorem hankelCof_last {d : ℕ} (I : Fin d → ℕ) (b : X) :
    hankelCof μ I (Fin.last d) b = hankelMinor μ I b := by
  simp [hankelCof, hankelMinor, Fin.succAbove_last, ← two_mul, pow_mul]

/-- The cofactors of the last row, paired with a shifted row of the Hankel matrix, give a Hankel
minor of size `d + 1`. -/
theorem sum_hankelCof_mul {d : ℕ} (I : Fin d → ℕ) (b : X) (k : ℕ) :
    ∑ j : Fin (d + 1), hankelCof μ I j b * μ (k + j) b =
      hankelMinor μ (Fin.snoc I k : Fin (d + 1) → ℕ) b := by
  have hM : (Matrix.of fun i j : Fin (d + 1) ↦ μ ((Fin.snoc I k : Fin (d + 1) → ℕ) i + j) b) =
      Matrix.of (Fin.snoc (fun i j ↦ μ (I i + j) b) (fun j ↦ μ (k + j) b) :
        Fin (d + 1) → Fin (d + 1) → ℂ) := by
    ext i j
    induction i using Fin.lastCases <;> simp
  rw [hankelMinor, hM, Matrix.det_of_snoc]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hankelCof, mul_comm]

end Sequence

section Holomorphic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] {D : Set B}

/-- The determinant of a matrix whose entries are holomorphic is holomorphic. -/
theorem differentiableOn_det {m : ℕ} (M : B → Matrix (Fin m) (Fin m) ℂ)
    (hM : ∀ i j, DifferentiableOn ℂ (fun b ↦ M b i j) D) :
    DifferentiableOn ℂ (fun b ↦ (M b).det) D := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp_rw [Matrix.det_succ_row_zero]
    refine DifferentiableOn.fun_sum fun j _ ↦ ((hM 0 j).const_mul _).mul ?_
    exact ih (fun b ↦ (M b).submatrix Fin.succ j.succAbove) fun i j' ↦ hM _ _

variable {μ : ℕ → B → ℂ}

/-- The Hankel minors of a holomorphic family of sequences are holomorphic. -/
theorem differentiableOn_hankelMinor (hμ : ∀ k, DifferentiableOn ℂ (μ k) D) {m : ℕ}
    (I : Fin m → ℕ) : DifferentiableOn ℂ (hankelMinor μ I) D :=
  differentiableOn_det (fun b ↦ Matrix.of fun i j : Fin m ↦ μ (I i + j) b) fun _ _ ↦ hμ _

/-- The cofactors `hankelCof` of a holomorphic family of sequences are holomorphic. -/
theorem differentiableOn_hankelCof (hμ : ∀ k, DifferentiableOn ℂ (μ k) D) {d : ℕ}
    (I : Fin d → ℕ) (j : Fin (d + 1)) : DifferentiableOn ℂ (hankelCof μ I j) D :=
  (differentiableOn_det (fun b ↦ Matrix.of fun i j' : Fin d ↦ μ (I i + j.succAbove j') b)
    fun _ _ ↦ hμ _).const_mul _

variable [FiniteDimensional ℂ B]

/-- **Choice of the Hankel minor.** Let `μ k` be holomorphic on the connected open set `D` and
suppose that at every point of a nonempty open subset `O ⊆ D` the sequence `μ · b` satisfies a
linear recurrence. Then there are `d` and rows `I` such that the minor with rows `I` and columns
`0, …, d - 1` does not vanish identically on `D`, while all minors of size `d + 1` with columns
`0, …, d` vanish on `D`. -/
theorem exists_hankelMinor_ne_zero_forall_eq_zero (hD : IsOpen D) (hDc : IsPreconnected D)
    (hμ : ∀ k, DifferentiableOn ℂ (μ k) D) {O : Set B} (hO : IsOpen O) (hOD : O ⊆ D)
    (hOne : O.Nonempty)
    (hrec : ∀ b ∈ O, ∃ p : ℂ[X], p ≠ 0 ∧
      ∀ k, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * μ (k + j) b = 0) :
    ∃ (d : ℕ) (I : Fin d → ℕ), (∃ b ∈ D, hankelMinor μ I b ≠ 0) ∧
      ∀ J : Fin (d + 1) → ℕ, ∀ b ∈ D, hankelMinor μ J b = 0 := by
  classical
  haveI := FiniteDimensional.complete ℂ B
  have hana : ∀ {m} (J : Fin m → ℕ), AnalyticOnNhd ℂ (hankelMinor μ J) D := fun J b hb ↦
    analyticAt_of_differentiableOn_of_finiteDimensional hD (differentiableOn_hankelMinor hμ J) hb
  set G : ℕ → Set B := fun m ↦ {b ∈ O | ∀ J : Fin (m + 1) → ℕ, hankelMinor μ J b = 0} ∪ Oᶜ
  have hGc : ∀ m, IsClosed (G m) := fun m ↦ by
    rw [← isOpen_compl_iff]
    have : (G m)ᶜ = ⋃ J : Fin (m + 1) → ℕ, O ∩ hankelMinor μ J ⁻¹' {0}ᶜ := by
      ext b
      simp only [G, compl_union, compl_compl, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
        not_and, not_forall, mem_iUnion, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨h₁, h₂⟩ ↦ (h₁ h₂).imp fun J hJ ↦ ⟨h₂, hJ⟩,
        fun ⟨J, h₂, hJ⟩ ↦ ⟨fun _ ↦ ⟨J, hJ⟩, h₂⟩⟩
    rw [this]
    exact isOpen_iUnion fun J ↦ ((differentiableOn_hankelMinor hμ J).continuousOn.mono
      hOD).isOpen_inter_preimage hO isOpen_compl_singleton
  have hGu : ⋃ m, G m = univ := by
    refine eq_univ_of_forall fun b ↦ ?_
    by_cases hb : b ∈ O
    · obtain ⟨p, hp, hpr⟩ := hrec b hb
      exact mem_iUnion.mpr ⟨p.natDegree, Or.inl ⟨hb,
        hankelMinor_eq_zero_of_recurrence hp hpr le_rfl⟩⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hb⟩
  obtain ⟨b₀, hb₀O, hb₀⟩ := (dense_iUnion_interior_of_closed hGc hGu).inter_open_nonempty O hO
    hOne
  obtain ⟨m, hm⟩ := mem_iUnion.mp hb₀
  have hP : ∃ m, ∀ J : Fin (m + 1) → ℕ, ∀ b ∈ D, hankelMinor μ J b = 0 := by
    refine ⟨m, fun J b hb ↦ ?_⟩
    refine hana J |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hOD hb₀O) ?_ hb
    filter_upwards [isOpen_interior.mem_nhds hm, hO.mem_nhds hb₀O] with b' hb' hb'O
    rcases interior_subset hb' with h | h
    · exact h.2 J
    · exact absurd hb'O h
  obtain ⟨b₁, hb₁⟩ := hOne
  have hs := Nat.find_spec hP
  rcases hd : Nat.find hP with _ | m
  · refine ⟨0, Fin.elim0, ⟨b₁, hOD hb₁, by simp [hankelMinor]⟩, ?_⟩
    rw [hd] at hs
    exact hs
  · refine ⟨m + 1, ?_⟩
    have hmin := Nat.find_min hP (hd ▸ Nat.lt_succ_self m : m < Nat.find hP)
    push Not at hmin
    obtain ⟨J, b, hb, hJ⟩ := hmin
    rw [hd] at hs
    exact ⟨J, ⟨b, hb, hJ⟩, hs⟩

end Holomorphic
