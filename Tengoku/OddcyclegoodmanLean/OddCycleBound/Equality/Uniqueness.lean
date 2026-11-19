import Tengoku.OddcyclegoodmanLean.OddCycleBound.Equality.Cliques
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.Regularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness of the extremal graphon (Proposition 6.2 and Corollary 1.2)

"Unique up to graphon equivalence" is formalised as: `W` is, almost everywhere, the pullback of
`completePartite k` along a measurable measure-preserving map `φ : Ω → Fin k`.
Conversely, edge and cycle densities are invariant under such pullbacks.
-/

open MeasureTheory

namespace OddCycleBound

open Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-! ### Densities are invariant under measure-preserving pullback -/

section Pullback

variable {k : ℕ} {φ : Ω → Fin k}

omit [IsProbabilityMeasure μ] in
lemma isGraphon_pullback (hφ : Measurable φ) :
    IsGraphon (fun x y => completePartite k (φ x) (φ y)) μ where
  meas := (measurable_of_finite (Function.uncurry (completePartite k))).comp
    ((hφ.comp measurable_fst).prodMk (hφ.comp measurable_snd))
  nonneg _ _ := (isGraphon_completePartite k).nonneg _ _
  le_one _ _ := (isGraphon_completePartite k).le_one _ _
  symm _ _ := (isGraphon_completePartite k).symm _ _

/-- Kernel powers of a.e. equal graphons agree a.e.-/
lemma compPow_ae_eq {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) :
    ∀ n, ∀ᵐ p ∂(μ.prod μ), compPow μ W n p.1 p.2 = compPow μ W' n p.1 p.2
  | 0 => h
  | n + 1 => by
      have hG := goodK_of_isGraphon hW
      have hG' := goodK_of_isGraphon hW'
      have ih := compPow_ae_eq hW hW' h n
      have hset : MeasurableSet
          {p : Ω × Ω | compPow μ W (n + 1) p.1 p.2 = compPow μ W' (n + 1) p.1 p.2} :=
        measurableSet_eq_fun (goodK_compPow hG (n + 1)).meas (goodK_compPow hG' (n + 1)).meas
      rw [Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
      filter_upwards [Measure.ae_ae_of_ae_prod ih] with y hy
      show ∫ z, W x z * compPow μ W n z y ∂μ = ∫ z, W' x z * compPow μ W' n z y ∂μ
      refine integral_congr_ae ?_
      filter_upwards [hx, hy] with z hz1 hz2
      rw [hz1, compPow_symm hG hW.symm n z y, compPow_symm hG' hW'.symm n z y]
      exact congrArg _ hz2

omit [IsProbabilityMeasure μ] in
lemma hsInner_congr_ae {A A' B B' : Ω → Ω → ℝ}
    (hA : ∀ᵐ p ∂(μ.prod μ), A p.1 p.2 = A' p.1 p.2)
    (hB : ∀ᵐ p ∂(μ.prod μ), B p.1 p.2 = B' p.1 p.2) :
    hsInner μ A B = hsInner μ A' B' := by
  unfold hsInner
  refine integral_congr_ae ?_
  filter_upwards [hA, hB] with p h1 h2
  rw [h1, h2]

/-- Cycle densities (`m ≥ 2`) of a.e. equal graphons agree.-/
lemma cycleDensity_congr_ae {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) {m : ℕ} (hm : 2 ≤ m) :
    cycleDensity μ W m = cycleDensity μ W' m := by
  have hG := goodK_of_isGraphon hW
  have hG' := goodK_of_isGraphon hW'
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [cycleDensity, cycleDensity, show n + 2 - 1 = n + 1 by omega,
    show compPow μ W (n + 1) = comp μ W (compPow μ W n) from rfl,
    show compPow μ W' (n + 1) = comp μ W' (compPow μ W' n) from rfl,
    trace_comp_eq_hsInner hG (goodK_compPow hG n) (compPow_symm hG hW.symm n),
    trace_comp_eq_hsInner hG' (goodK_compPow hG' n) (compPow_symm hG' hW'.symm n)]
  exact hsInner_congr_ae h (compPow_ae_eq hW hW' h n)

lemma edgeDensity_congr_ae {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) :
    edgeDensity W μ = edgeDensity W' μ := by
  rw [← integral_prod_eq_edgeDensity hW, ← integral_prod_eq_edgeDensity hW']
  exact integral_congr_ae h

end Pullback

/-! ### Equality in Theorem 1.1 -/

end OddCycleBound
