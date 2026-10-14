/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Finite polynomial charts for Zhou's property-(T) detector. Paper: §4.
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Construction

/-!
The finite charts component of the Connes rigidity formalization.
-/

@[expose] public section

namespace Connes
namespace PaperFiniteCharts

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `F` construction used in the Connes rigidity formalization.
-/
abbrev F := Construction.k
/--
The `R` construction used in the Connes rigidity formalization.
-/
abbrev R := Construction.R
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C

noncomputable instance paperFintype : Fintype F := by
  let _ : NeZero (2 : ℕ) := ⟨by decide⟩
  infer_instance

/- The finite polynomial model for ℘_N. Paper: Lemma 4.2.
-/
/--
The `polynomialChart` construction used in the Connes rigidity formalization.
-/
def polynomialChart (N : ℕ) : Finset R :=
  (Finset.univ : Finset (Fin N → F)).image (Polynomial.ofFn N)

/--
@isnad1 id=iff.0h2v.s9.1d4e240a8367 from=translated src=- shape=df020136 vocab=37fa9a54
-/
theorem mem_polynomialChart_iff (N : ℕ) (p : R) :
    p ∈ polynomialChart N ↔
      ∃ v : Fin N → F, Polynomial.ofFn N v = p := by
  simp [polynomialChart]

/--
@isnad1 id=eq.0h1v.s4.39a402f44855 from=translated src=- shape=7eb8f539 vocab=1ffa48d2
-/
theorem polynomialChart_card (N : ℕ) :
    (polynomialChart N).card = Fintype.card (Fin N → F) := by
  classical
  rw [polynomialChart, Finset.card_image_of_injective _
    (Polynomial.injective_ofFn N)]
  simp

/-- Coefficient extension preserves the represented polynomial. Paper: Lemma 4.2.
-/
def extendCoefficients {N M : ℕ} (_hNM : N ≤ M) (v : Fin N → F) : Fin M → F :=
  fun i => if hi : i.val < N then v ⟨i.val, hi⟩ else 0

/--
@isnad1 id=eq.1h3v.s9.7b571951f10c from=translated src=- shape=6d8ca742 vocab=9a74f35d
-/
theorem ofFn_extendCoefficients {N M : ℕ} (hNM : N ≤ M)
    (v : Fin N → F) :
    Polynomial.ofFn M (extendCoefficients hNM v) =
      Polynomial.ofFn N v := by
  ext i
  by_cases hi : i < N
  · simp only [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
    simp [extendCoefficients, hi,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (lt_of_lt_of_le hi hNM)]
  · have hiN : N ≤ i := Nat.le_of_not_gt hi
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hiN]
    by_cases hiM : M ≤ i
    · exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hiM
    · have hiM' : i < M := Nat.lt_of_not_ge hiM
      rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hiM']
      simp [extendCoefficients, hi]

/--
@isnad1 id=le.1h2v.s4.ad54e8c3a0d1 from=translated src=- shape=49beed39 vocab=808e4561
-/
theorem polynomialChart_mono {N M : ℕ} (hNM : N ≤ M) :
    polynomialChart N ⊆ polynomialChart M := by
  intro p hp
  obtain ⟨v, rfl⟩ := (mem_polynomialChart_iff N _).mp hp
  exact (mem_polynomialChart_iff M _).mpr ⟨extendCoefficients hNM v,
    ofFn_extendCoefficients hNM v⟩

/-- The cyclic coordinate order used for the three paper charts. Paper: Lemma 4.2.
-/
def next (s : Fin 3) : Fin 3 :=
  ⟨(s.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/--
The `nextNext` construction used in the Connes rigidity formalization.
-/
def nextNext (s : Fin 3) : Fin 3 := next (next s)

/--
@isnad1 id=ne.0h1v.s4.7a85f6b625a9 from=translated src=- shape=ca8e04de vocab=2be49710
-/
theorem next_ne (s : Fin 3) : next s ≠ s := by
  fin_cases s <;> decide

/--
@isnad1 id=ne.0h1v.s4.6eff8ca534b0 from=translated src=- shape=ca8e04de vocab=ace2ab0b
-/
theorem nextNext_ne (s : Fin 3) : nextNext s ≠ s := by
  fin_cases s <;> decide

/--
@isnad1 id=ne.0h1v.s4.6bf7f13b5ac9 from=translated src=- shape=f8a55601 vocab=bd535fb7
-/
theorem next_nextNext_ne (s : Fin 3) : next s ≠ nextNext s := by
  fin_cases s <;> decide

/-- The standard basis vector in A. Paper: Lemma 4.2.
-/
def basisVector (s : Fin 3) : A := Pi.single s 1

/-- A point in one of the three finite charts. Paper: Lemma 4.2.
-/
def chartVector (s : Fin 3) (f h : R) : A :=
  basisVector s + f • basisVector (next s) + h • basisVector (nextNext s)

/--
The `ChartIndex` construction used in the Connes rigidity formalization.
-/
abbrev ChartIndex (N : ℕ) := Fin 3 × (Fin N → F) × (Fin N → F)

/--
The `chartPoint` construction used in the Connes rigidity formalization.
-/
def chartPoint (N : ℕ) (i : ChartIndex N) : A :=
  chartVector i.1 (Polynomial.ofFn N i.2.1) (Polynomial.ofFn N i.2.2)

/--
The `chartSquare` construction used in the Connes rigidity formalization.
-/
def chartSquare (N : ℕ) (i : ChartIndex N) : C :=
  PaperKernel.diagonal (chartPoint N i)

/-- The chart span C_N. Paper: Lemma 4.2.
-/
def chartSubmodule (N : ℕ) : Submodule k C :=
  Submodule.span k (Set.range (chartSquare N))

/-- Coordinate basis for the two polynomial parameters. Paper: Lemma 4.2.
-/
def polynomialBasis (N : ℕ) (i : Fin N) : R :=
  Polynomial.ofFn N (Pi.single i 1)

/--
@isnad1 id=eq.0h2v.s9.e8f9d282854d from=translated src=- shape=52f6d5b0 vocab=6a2f09ff
-/
theorem ofFn_eq_sum_polynomialBasis (N : ℕ) (v : Fin N → F) :
    Polynomial.ofFn N v = ∑ i, v i • polynomialBasis N i := by
  have hv : v = ∑ i, v i • (Pi.single i 1) := by
    funext j
    simp [Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul]
  simp [polynomialBasis, Pi.single_apply]

/--
The `CoeffIndex` construction used in the Connes rigidity formalization.
-/
abbrev CoeffIndex (N : ℕ) := Fin N ⊕ Fin N

/--
The `coefficientVector` construction used in the Connes rigidity formalization.
-/
def coefficientVector (N : ℕ) (s : Fin 3) : CoeffIndex N → A
  | Sum.inl i => polynomialBasis N i • basisVector (next s)
  | Sum.inr i => polynomialBasis N i • basisVector (nextNext s)

/--
@isnad1 id=eq.0h4v.s8.5789004d4f7d from=translated src=- shape=924e0f86 vocab=1caf8a45
-/
theorem chartPoint_eq_affine_sum (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) :
    chartPoint N (s, f, h) =
      basisVector s +
        ∑ i, f i • coefficientVector N s (Sum.inl i) +
        ∑ i, h i • coefficientVector N s (Sum.inr i) := by
  simp only [chartPoint, chartVector, coefficientVector]
  rw [ofFn_eq_sum_polynomialBasis N f,
    ofFn_eq_sum_polynomialBasis N h]
  simp only [Finset.sum_smul, smul_assoc]

/--
@isnad1 id=eq.0h4v.s6.31489b15b47e from=translated src=- shape=e742d5c2 vocab=47074590
-/
theorem chartPoint_apply_self (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) : chartPoint N (s, f, h) s = 1 := by
  fin_cases s <;>
    simp [chartPoint, chartVector, basisVector, next, nextNext]

/--
@isnad1 id=mem.0h2v.s13.78b29d007bfb from=translated src=- shape=07ad6df9 vocab=0dc8b3ec
-/
theorem chartPoint_mem_span (N : ℕ) (i : ChartIndex N) :
    chartSquare N i ∈ chartSubmodule N := by
  exact Submodule.subset_span ⟨i, rfl⟩

/--
@isnad1 id=le.1h2v.s13.1638e9fa7213 from=translated src=- shape=dd1ee09f vocab=4967c843
-/
theorem chartSubmodule_mono {N M : ℕ} (hNM : N ≤ M) :
    chartSubmodule N ≤ chartSubmodule M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let j : ChartIndex M :=
    (i.1, extendCoefficients hNM i.2.1,
      extendCoefficients hNM i.2.2)
  have hpoint : chartPoint M j = chartPoint N i := by
    simp [j, chartPoint, chartVector,
      ofFn_extendCoefficients hNM i.2.1,
      ofFn_extendCoefficients hNM i.2.2]
  change PaperKernel.diagonal (chartPoint N i) ∈ chartSubmodule M
  rw [← hpoint]
  exact Submodule.subset_span ⟨j, rfl⟩

/- Every polynomial occurs in a finite chart. Paper: Lemma 4.2. -/
/--
@isnad1 id=ex.0h1v.s4.9b690f83db11 from=translated src=- shape=9837e571 vocab=114f9828
-/
theorem polynomial_mem_some_chart (p : R) :
    ∃ N, p ∈ polynomialChart N := by
  refine ⟨p.natDegree + 1, ?_⟩
  apply (mem_polynomialChart_iff _ _).mpr
  refine ⟨Polynomial.toFn (p.natDegree + 1) p, ?_⟩
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
    (Nat.lt_succ_self p.natDegree)

end
end PaperFiniteCharts
end Connes
