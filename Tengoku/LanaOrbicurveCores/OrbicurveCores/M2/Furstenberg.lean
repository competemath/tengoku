/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.Setup
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.FurstenbergLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2, part F: the Furstenberg boundary map

For a lattice `Γ ≤ SL(2, ℝ)` with a good fundamental set (`GoodLattice`) acting on a compact
metrizable space `Y` through `α`, we construct a measurable `ψ : OnePoint ℝ → Prob(Y)` which is
`Γ`-equivariant almost everywhere (`GoodLattice.exists_boundaryMap`). See `Blueprint.md`, §2.3b,
part F.

1. `phiM z`: a `Γ`-equivariant measurable family of probability measures on `Y`, indexed by
   `z ∈ ℍ`: the average of the Dirac masses at `α γ y₀` over the finitely many `γ ∈ Γ` with
   `γ⁻¹ z ∈ F`.
2. `theta n g`: the average of `phiM (g a_s n_u • I)` over the left Følner set
   `(s, u) ∈ [0, n + 1] × [-(n + 1), n + 1]` of `P° = {a_s n_u}`. It is exactly `Γ`-equivariant
   and asymptotically right-`P`-invariant, uniformly in `g`.
3. The abstract limit theorem `exists_tailWeights_ae_tendsto` gives tail convex combinations
   converging at `σ x = !![x, -1; 1, 0]` for almost every `x ∈ ℝ`. The convergence set is exactly
   left-`Γ`- and right-`P`-invariant, and the limit descends to `ℝ ⊆ OnePoint ℝ` via `σ`.

No Haar measure on `SL(2, ℝ)` is needed, and the lattice property enters only through the
fundamental set.
-/

open MeasureTheory Filter Topology Matrix UpperHalfPlane OnePoint BoundedContinuousFunction Set
open scoped MatrixGroups ENNReal NNReal ProbabilityTheory

namespace OrbicurveCores.M2

/-! ### Matrices -/

/-- `a_s n_u = [[e^s, e^s u], [0, e^{-s}]]`. -/
noncomputable def an (s u : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp s, Real.exp s * u; 0, Real.exp (-s)], by
    simp [det_fin_two, ← Real.exp_add]⟩

lemma continuous_an : Continuous fun q : ℝ × ℝ ↦ an q.1 q.2 := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun q : ℝ × ℝ ↦ !![Real.exp q.1, Real.exp q.1 * q.2; 0, Real.exp (-q.1)]
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [of_apply, cons_val', empty_val', cons_val_fin_one] <;> fun_prop

/-- The section `σ x = [[x, -1], [1, 0]]` of `SL(2, ℝ) → OnePoint ℝ`, `σ x • ∞ = x`. -/
def sec (x : ℝ) : SL(2, ℝ) :=
  ⟨!![x, -1; 1, 0], by simp [det_fin_two]⟩

/-- The upper triangular matrix `[[t, v], [0, t⁻¹]]`. -/
noncomputable def ptri (t v : ℝ) (ht : t ≠ 0) : SL(2, ℝ) :=
  ⟨!![t, v; 0, t⁻¹], by simp [det_fin_two, ht]⟩

/-! ### Averages over intervals -/

/-- The uniform probability measure on `[a, b]`. -/
noncomputable def unif (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

lemma isProbabilityMeasure_unif {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (unif a b) := by
  constructor
  rw [unif, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, smul_eq_mul, ENNReal.inv_mul_cancel (by simpa using hab) (by simp)]

/-! ### The equivariant family `phiM` on `ℍ` -/

section Phi

variable (Γ : Subgroup SL(2, ℝ)) (F : Set ℍ)

/-- The number of `γ ∈ Γ` with `γ⁻¹ z ∈ F`. -/
noncomputable def cnt (z : ℍ) : ℝ≥0∞ :=
  ∑' γ : Γ, F.indicator 1 ((γ : SL(2, ℝ))⁻¹ • z)

/-- The weight of `γ` at `z`: `1 / cnt z` if `γ⁻¹ z ∈ F`, else `0`. -/
noncomputable def wt (γ : Γ) (z : ℍ) : ℝ≥0∞ :=
  F.indicator 1 ((γ : SL(2, ℝ))⁻¹ • z) / cnt Γ F z

lemma indicator_le_one (z : ℍ) : F.indicator (1 : ℍ → ℝ≥0∞) z ≤ 1 := by
  unfold Set.indicator; split_ifs <;> simp

variable {Γ F}

lemma cnt_ne_zero (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) (z : ℍ) : cnt Γ F z ≠ 0 := by
  obtain ⟨γ, hγ, h⟩ := hcov z
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum (⟨γ⁻¹, inv_mem hγ⟩ : Γ)))
  simp [h]

lemma cnt_ne_top (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (z : ℍ) :
    cnt Γ F z ≠ ⊤ := by
  classical
  have hS : {γ : Γ | (γ : SL(2, ℝ))⁻¹ • z ∈ F}.Finite := by
    refine ((hfin z).preimage (f := fun γ : Γ ↦ (γ : SL(2, ℝ))⁻¹) ?_).subset ?_
    · intro a _ b _ hab
      exact Subtype.ext (inv_injective hab)
    · intro γ hγ
      exact ⟨inv_mem γ.2, hγ⟩
  rw [cnt, tsum_eq_sum (s := hS.toFinset) (fun γ hγ ↦ by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hγ
    simp [hγ])]
  exact ENNReal.sum_ne_top.2 fun γ _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
    (indicator_le_one F _)

lemma tsum_wt (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
    (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (z : ℍ) :
    ∑' γ : Γ, wt Γ F γ z = 1 := by
  simp only [wt, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel (cnt_ne_zero hcov z) (cnt_ne_top hfin z)

variable (Γ F) {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

/-- The `Γ`-equivariant family of measures `z ↦ ∑_γ wt γ z • δ_{α γ y₀}`. -/
noncomputable def phiM (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (z : ℍ) : Measure Y :=
  Measure.sum fun γ : Γ ↦ wt Γ F γ z • Measure.dirac (α γ y₀)

variable {Γ F}

lemma phiM_apply (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (z : ℍ) {A : Set Y} (hA : MeasurableSet A) :
    phiM Γ F α y₀ z A = ∑' γ : Γ, wt Γ F γ z * Measure.dirac (α γ y₀) A := by
  simp [phiM, Measure.sum_apply _ hA]

lemma isProbabilityMeasure_phiM (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
    (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y)
    (z : ℍ) : IsProbabilityMeasure (phiM Γ F α y₀ z) := by
  constructor
  rw [phiM_apply α y₀ z MeasurableSet.univ]
  simpa using tsum_wt hcov hfin z

variable [Countable Γ]

lemma measurable_indicator_smul (hF : MeasurableSet F) (g : SL(2, ℝ)) :
    Measurable fun z : ℍ ↦ F.indicator (1 : ℍ → ℝ≥0∞) (g • z) :=
  (measurable_one.indicator hF).comp (Fuchsian.measurable_smul_SL g)

lemma measurable_cnt (hF : MeasurableSet F) : Measurable (cnt Γ F) :=
  Measurable.tsum fun _ ↦ measurable_indicator_smul hF _

lemma measurable_wt (hF : MeasurableSet F) (γ : Γ) : Measurable (wt Γ F γ) :=
  (measurable_indicator_smul hF _).div (measurable_cnt hF)

lemma measurable_phiM (hF : MeasurableSet F) (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) :
    Measurable (phiM Γ F α y₀) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [phiM_apply α y₀ _ hA]
  exact Measurable.tsum fun γ ↦ (measurable_wt hF γ).mul_const _

end Phi

/-! ### Averaging over Følner sets of `P` -/

/-- A measurable fundamental set of finite multiplicity. -/
structure FundSet (Γ : Subgroup SL(2, ℝ)) where
  /-- The set. -/
  F : Set ℍ
  meas : MeasurableSet F
  cover : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F
  fin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite

instance (n : ℕ) : IsProbabilityMeasure (unif 0 (n + 1)) :=
  isProbabilityMeasure_unif (by positivity)

instance (n : ℕ) : IsProbabilityMeasure (unif (-(n + 1)) (n + 1)) :=
  isProbabilityMeasure_unif (by linarith)

/-- The normalised Haar measure of the left Følner set `[0, n + 1] × [-(n + 1), n + 1]` of `P°`,
in the coordinates `(s, u) ↦ a_s n_u`. -/
noncomputable def box (n : ℕ) : Measure (ℝ × ℝ) :=
  (unif 0 (n + 1)).prod (unif (-(n + 1)) (n + 1))

instance (n : ℕ) : IsProbabilityMeasure (box n) := by
  unfold box; infer_instance

/-- The point `g a_s n_u • I` of `ℍ`. -/
noncomputable def orbitPt (g : SL(2, ℝ)) (q : ℝ × ℝ) : ℍ := (g * an q.1 q.2) • I

lemma continuous_orbitPt : Continuous fun p : SL(2, ℝ) × (ℝ × ℝ) ↦ orbitPt p.1 p.2 :=
  (continuous_fst.mul (continuous_an.comp continuous_snd)).smul continuous_const

lemma measurable_orbitPt (g : SL(2, ℝ)) : Measurable (orbitPt g) :=
  (continuous_orbitPt.comp (Continuous.prodMk_right g)).measurable

section Theta

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y)

/-- `phiM` as a Markov kernel. -/
noncomputable def phiK : ProbabilityTheory.Kernel ℍ Y :=
  ⟨phiM Γ D.F α y₀, measurable_phiM D.meas α y₀⟩

instance : ProbabilityTheory.IsMarkovKernel (phiK D α y₀) :=
  ⟨fun z ↦ isProbabilityMeasure_phiM D.cover D.fin α y₀ z⟩

/-- The average of `phiM (g a_s n_u • I)` over the Følner set `box n`. -/
noncomputable def thetaM (n : ℕ) (g : SL(2, ℝ)) : Measure Y :=
  (phiK D α y₀).comap (orbitPt g) (measurable_orbitPt g) ∘ₘ box n

/-- `thetaM` as a probability measure. -/
noncomputable def theta (n : ℕ) (g : SL(2, ℝ)) : ProbabilityMeasure Y :=
  ⟨thetaM D α y₀ n g, by unfold thetaM; infer_instance⟩

end Theta

/-! ### Asymptotic `P`-invariance -/

/-- Elements of `P = {± a_s n_u}`. -/
def IsP (p : SL(2, ℝ)) : Prop :=
  ∃ s₀ u₀ : ℝ, p = an s₀ 0 * an 0 u₀ ∨ p = -(an s₀ 0 * an 0 u₀)

section Estimates

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (f : Y →ᵇ ℝ)

/-- The integral of `f` against `phiM z`. -/
noncomputable def phiInt (z : ℍ) : ℝ := ∫ y, f y ∂(phiM Γ D.F α y₀ z)

/-- The inner average `s ↦ ⨍_u phiInt (h (s, u))` over `u ∈ [-(n + 1), n + 1]`. -/
noncomputable def avgU (n : ℕ) (h : ℝ × ℝ → ℍ) (s : ℝ) : ℝ :=
  ∫ u, phiInt D α y₀ f (h (s, u)) ∂unif (-(n + 1)) (n + 1)

end Estimates

/-! ### The limit and its descent to the boundary -/

section Limit

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (W : TailWeights)

end Limit

lemma measurable_onePoint_elim {Z : Type*} [MeasurableSpace Z] {c : Z} {f : ℝ → Z}
    (hf : Measurable f) : Measurable fun p : OnePoint ℝ ↦ p.elim c f := by
  classical
  intro B hB
  have hemb : MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have : (fun p : OnePoint ℝ ↦ p.elim c f) ⁻¹' B =
      (((↑) : ℝ → OnePoint ℝ) '' (f ⁻¹' B)) ∪ ({(∞ : OnePoint ℝ)} ∩ {_p | c ∈ B}) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp
    | coe x => simp
  rw [this]
  exact (hemb.measurableSet_image.2 (hf hB)).union
    ((measurableSet_singleton _).inter (MeasurableSet.const _))

end OrbicurveCores.M2
