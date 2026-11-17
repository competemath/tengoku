import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.WeightedDeterminantBound
import Tengoku.Seed.Analysis.Normed.Module.Bases
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.Order.Hom.PowersetCard
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summability of the sorted determinant family

For an unconditional Schauder basis `b`, the terms
`det (b.coord (t i) (x j)) • g (b ∘ t)`, indexed by increasing `n`-tuples `t` of indices,
tend to zero along the cofinite filter. Over a complete ultrametric target they are
therefore summable.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace AlternatingAnalytic

/-- A product `∏ j, a j (t j)` of null families is null on the space of tuples `t`.
@isnad1 id=tendsto.1h3v.s6.2b8841df825a from=translated src=- shape=33c49d5f vocab=b2e0221d
-/
theorem tendsto_fin_product_cofinite_zero {I : Type*} (n : ℕ)
    (a : Fin n → I → ℝ) (ha : ∀ j, Tendsto (a j) cofinite (𝓝 0)) :
    Tendsto (fun t : Fin n → I => ∏ j, a j (t j)) cofinite (𝓝 0) := by
  induction n with
  | zero => simp only [Filter.cofinite_eq_bot, tendsto_bot]
  | succ n ih =>
    have h := tendsto_mul_cofinite_nhds_zero (ha 0)
      (ih (fun j => a j.succ) (fun j => ha j.succ))
    have hc := h.comp (Fin.consEquiv (fun _ : Fin (n + 1) => I)).symm.injective.tendsto_cofinite
    simpa only [Function.comp_def, Fin.consEquiv_symm_apply, Fin.tail_def,
      Fin.prod_univ_succ] using hc

variable {K I E F : Type*} [NontriviallyNormedField K]
  [LinearOrder I] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

omit [LinearOrder I] in
/-- The norm-weighted coordinates of each basis expansion form a null family.
@isnad1 id=tendsto.0h5v.s8.10be8d93176e from=translated src=- shape=8e52e12a vocab=0d19207b
-/
theorem tendsto_schauder_weighted_coord (b : UnconditionalSchauderBasis I K E) (x : E) :
    Tendsto (fun i => ‖b.coord i x‖ * ‖b i‖) cofinite (𝓝 0) := by
  simpa only [norm_smul, norm_zero] using (b.expansion x).summable.tendsto_cofinite_zero.norm

/-- The determinant term indexed by an `n`-element set of basis indices.-/
def sortedBasisTerm (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) (s : Set.powersetCard I n) : F :=
  let t := Set.powersetCard.ofFinEmbEquiv.symm s
  (Matrix.of fun i j => b.coord (t i) (x j)).det • g (b ∘ t)

/-- A permuted increasing enumeration is injective on `n`-element sets.
@isnad1 id=injectiv.0h3v.s8.05a6b55d5100 from=translated src=- shape=cd11fe67 vocab=81da8744
-/
theorem sortedEnumeration_perm_injective (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun s : Set.powersetCard I n =>
      fun j => Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) := by
  intro s t h
  apply Set.powersetCard.ofFinEmbEquiv.symm.injective
  ext j
  simpa only [Equiv.apply_symm_apply] using congrFun h (σ.symm j)

/-- Every weighted permutation product in the determinant is a null family.
@isnad1 id=tendsto.0h7v.s9.e06d5b9d85be from=translated src=- shape=37539287 vocab=4d8799c1
-/
theorem tendsto_sorted_weighted_product (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (x : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    Tendsto (fun s : Set.powersetCard I n =>
      ∏ j, ‖b.coord (Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) (x j)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s (σ j))‖) cofinite (𝓝 0) :=
  (tendsto_fin_product_cofinite_zero n
    (fun j i => ‖b.coord i (x j)‖ * ‖b i‖)
    (fun j => tendsto_schauder_weighted_coord b (x j))).comp
      (sortedEnumeration_perm_injective (I := I) n σ).tendsto_cofinite

/-- The determinant family is bounded by the finite sum of its weighted permutation products.
@isnad1 id=le.0h9v.s9.f03513809c8e from=translated src=- shape=4765b9c9 vocab=f137fb20
-/
theorem norm_sortedBasisTerm_le (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) (s : Set.powersetCard I n) :
    ‖sortedBasisTerm b n g x s‖ ≤ ‖g‖ *
      ∑ σ : Equiv.Perm (Fin n), ∏ j,
        ‖b.coord (Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) (x j)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s (σ j))‖ := by
  classical
  let t := Set.powersetCard.ofFinEmbEquiv.symm s
  let a : Matrix (Fin n) (Fin n) K := fun i j => b.coord (t i) (x j)
  have hdet : ‖a.det‖ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ j, ‖a (σ j) j‖ := by
    rw [Matrix.det_apply]
    simpa only [norm_units_zsmul, norm_prod] using
      (norm_sum_le Finset.univ (fun σ : Equiv.Perm (Fin n) =>
        Equiv.Perm.sign σ • ∏ j, a (σ j) j))
  change ‖a.det • g (b ∘ t)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ (∑ σ : Equiv.Perm (Fin n), ∏ j, ‖a (σ j) j‖) *
        (‖g‖ * ∏ j, ‖b (t j)‖) :=
      mul_le_mul hdet (g.le_opNorm _) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ‖g‖ * ∑ σ : Equiv.Perm (Fin n),
        ∏ j, ‖a (σ j) j‖ * ‖b (t (σ j))‖ := by
      rw [mul_left_comm, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_mul_distrib]
      exact congrArg (fun z : ℝ => (∏ j, ‖a (σ j) j‖) * z)
        (Equiv.prod_comp σ (fun j => ‖b (t j)‖)).symm
    _ = _ := rfl

/-- The sorted determinant terms tend to zero.
@isnad1 id=tendsto.0h8v.s7.0f65218f12bc from=translated src=- shape=cc5984b5 vocab=5e920d39
-/
theorem tendsto_sortedBasisTerm (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) :
    Tendsto (sortedBasisTerm b n g x) cofinite (𝓝 0) := by
  classical
  apply squeeze_zero_norm (fun s => norm_sortedBasisTerm_le b n g x s)
  have h := tendsto_finsetSum Finset.univ (fun σ _ => tendsto_sorted_weighted_product b n x σ)
  simpa only [Finset.sum_const_zero, mul_zero] using h.const_mul ‖g‖

/-- Over a complete ultrametric target, the sorted determinant family is summable.
@isnad1 id=summable.0h8v.s7.7a8184f75989 from=translated src=- shape=cdc34eee vocab=52a9794e
-/
theorem summable_sortedBasisTerm [IsUltrametricDist F] [CompleteSpace F]
    (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) :
    Summable (sortedBasisTerm b n g x) :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
    (tendsto_sortedBasisTerm b n g x)

end AlternatingAnalytic
