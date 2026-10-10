import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.StrongClosure

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def betaSymbol (n : ℤ) : DiagonalSymbol :=
  ⟨fun x j => (explicitBeta x (j+n):ℂ),
    ⟨fun j => Complex.continuous_ofReal.measurable.comp (measurable_explicitBeta (j+n)),
      Real.exp (-10), (Real.exp_pos _).le, fun x j => by
        simpa only [Complex.norm_real,Real.norm_of_nonneg (explicitBeta_pos _ _).le] using explicitBeta_le x (j+n)⟩⟩
@[simp] lemma betaSymbol_apply (n : ℤ) (x : Base) (j : ℤ) :
    betaSymbol n x j = (explicitBeta x (j+n):ℂ) := rfl
lemma betaSymbol_star (n : ℤ) : star (betaSymbol n) = betaSymbol n := by
  apply Subtype.ext
  funext x j
  simp

def polarDiagonal (n : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert := diagonalOperator (betaSymbol n)

def projectionSymbol (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) : DiagonalSymbol :=
  ⟨fun x j => (E j).indicator (fun _ => (1:ℂ)) x,
    ⟨fun j => measurable_const.indicator (hE j), 1, zero_le_one, fun x j => by
      by_cases hx : x ∈ E j <;> simp [hx]⟩⟩
@[simp] lemma projectionSymbol_apply (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j))
    (x : Base) (j : ℤ) : projectionSymbol E hE x j = if x ∈ E j then 1 else 0 := rfl
lemma projectionSymbol_norm_le (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j))
    (x : Base) (j : ℤ) : ‖projectionSymbol E hE x j‖ ≤ 1 := by
  by_cases hx : x ∈ E j <;> simp [hx]
lemma projectionSymbol_star (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    star (projectionSymbol E hE) = projectionSymbol E hE := by
  apply Subtype.ext
  funext x j
  change star (projectionSymbol E hE x j) = projectionSymbol E hE x j
  by_cases hx : x ∈ E j <;> simp [hx]
lemma projectionSymbol_idempotent (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    projectionSymbol E hE * projectionSymbol E hE = projectionSymbol E hE := by
  apply Subtype.ext
  funext x j
  change projectionSymbol E hE x j * projectionSymbol E hE x j = projectionSymbol E hE x j
  by_cases hx : x ∈ E j <;> simp [hx]

def diagonalProjection (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalOperator (projectionSymbol E hE)

lemma explicitBeta_le_one (x : Base) (j : ℤ) : explicitBeta x j ≤ 1 :=
  (explicitBeta_le x j).trans (Real.exp_le_one_iff.mpr (by norm_num))

def levelProjection (n : ℤ) (t : ℝ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun j => {x | explicitBeta x (j+n) = t})
    (fun j => measurableSet_eq_fun (measurable_explicitBeta (j+n)) measurable_const)

lemma peak_nonneg {b t : ℝ} (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ 1-(b-t)^2 := by
  have h₁ : 0 ≤ (1-(b-t))*(1+(b-t)) := mul_nonneg (by linarith) (by linarith)
  nlinarith
lemma peak_le_one (b t : ℝ) : 1-(b-t)^2 ≤ 1 := by nlinarith [sq_nonneg (b-t)]
lemma peak_lt_one {b t : ℝ} (h : b ≠ t) : 1-(b-t)^2 < 1 := by
  have h' : 0 < (b-t)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  linarith

def peakSymbol (n : ℤ) (t : ℝ) : DiagonalSymbol := 1-(betaSymbol n - (t:ℂ) • 1)^2
@[simp] lemma peakSymbol_apply (n : ℤ) (t : ℝ) (x : Base) (j : ℤ) :
    peakSymbol n t x j = ((1-(explicitBeta x (j+n)-t)^2:ℝ):ℂ) := by
  simp [peakSymbol,Complex.ofReal_sub,Complex.ofReal_pow]
lemma peakSymbol_bound (n : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (x : Base) (j : ℤ) :
    ‖peakSymbol n t x j‖ ≤ 1 := by
  rw [peakSymbol_apply,Complex.norm_real,Real.norm_of_nonneg
    (peak_nonneg (explicitBeta_pos _ _).le (explicitBeta_le_one _ _) ht₀ ht₁)]
  exact peak_le_one _ _
lemma peakSymbol_powers_tendsto (n : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (x : Base) (j : ℤ) :
    Tendsto (fun k : ℕ => (peakSymbol n t ^k) x j) atTop
      (𝓝 (if explicitBeta x (j+n)=t then (1:ℂ) else 0)) := by
  simp only [DiagonalSymbol.pow_apply,peakSymbol_apply]
  by_cases he : explicitBeta x (j+n)=t
  · simp [he]
  · simp only [he,↓reduceIte]
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [Complex.norm_real,Real.norm_of_nonneg
      (peak_nonneg (explicitBeta_pos _ _).le (explicitBeta_le_one _ _) ht₀ ht₁)]
    exact peak_lt_one he

def baseProjection (E : Set Base) (hE : MeasurableSet E) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun _ => E) (fun _ => hE)

def columnSymbol (T : GlobalHilbert →L[ℂ] GlobalHilbert) : DiagonalSymbol :=
  ⟨fun x j => if ‖T (constantBasis j) x j‖ ≤ ‖T‖ then T (constantBasis j) x j else 0,
    ⟨fun j => by
      have hm : Measurable (fun x => T (constantBasis j) x j) :=
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous.comp_stronglyMeasurable
          (Lp.stronglyMeasurable (T (constantBasis j)))).measurable
      exact hm.ite (measurableSet_le hm.norm measurable_const) measurable_const,
      ‖T‖,norm_nonneg T,fun x j => by dsimp only; split_ifs with h <;> simp_all⟩⟩

end
end BackwardIntertwiners

end OAI
