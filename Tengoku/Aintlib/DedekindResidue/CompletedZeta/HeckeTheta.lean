/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku
public import Tengoku.Aintlib.DedekindResidue.CompletedZeta.IdealLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The multivariable Hecke theta of a fractional ideal  (SP1-AGE-3)

Hecke's functional-equation argument for a number field of unit rank `> 0` uses the
**multivariable** theta of an ideal lattice, with one weight per infinite place, averaged
over a fundamental domain of the unit action. This file builds the per-place weight
machinery and the theta function itself:

* `placeWeights c` — expand per-place weights to the `index K` coordinates (equal on the
  `(re, im)` pair of a complex place — the shape preserved by the unit action, since complex
  multiplication mixes the pair but preserves `re² + im²`);
* `sum_placeWeights_embeddingCoords_sq` — `∑ᵢ c_i·ζ(x)ᵢ² = ∑_w c_w·w(x)²`: the weighted
  square-sum of embedding coordinates is the place-absolute-value form.

The unit equivariance `Θ(c·w(ε)², L_I) = Θ(c, L_I)` and the box-averaged `g_I` follow
(SP1-AGE-3 continuation), then the Mellin definition of `Λ_K` (AGE-4).
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]

/-- The `ℝ`-cast field degree `[K : ℚ]` is positive — the packaged `Module.finrank_pos` used
for the degree denominators throughout the Hecke-weight normalisation.
@isnad1 id=lt.0h1v.s5.f3596797379b from=translated src=- shape=6f759d16 vocab=51b3f8b9
-/
theorem finrank_pos_real : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
  have := Module.finrank_pos (R := ℚ) (M := K)
  positivity

omit [NumberField K] in
/-- The `ℝ`-cast local multiplicity `mult w` is nonzero (`1` at real, `2` at complex places) —
the recurring side goal for the `field_simp`s that divide by `mult w`.
@isnad1 id=ne.0h2v.s4.77f0f60907ad from=translated src=- shape=fd2f49e5 vocab=5c4642b8
-/
theorem mult_ne_zero_real (w : InfinitePlace K) : (mult w : ℝ) ≠ 0 := by
  have := mult_pos (w := w)
  positivity

/-- Expand per-place weights to per-coordinate weights (equal on the `(re, im)` pair of a
complex place).-/
noncomputable def placeWeights (c : InfinitePlace K → ℝ) : index K → ℝ :=
  Sum.elim (fun w => c w) (fun p => c p.1)

open scoped Classical in
/-- The place-weighted square-sum of the embedding coordinates is the weighted sum of squared
place absolute values: `∑ᵢ c_i·ζ(x)ᵢ² = ∑_w c_w·w(x)²`.
@isnad1 id=eq.0h3v.s7.d2bb619c8aa2 from=translated src=- shape=2bd68195 vocab=8d7e39d8
-/
theorem sum_placeWeights_embeddingCoords_sq (c : InfinitePlace K → ℝ) (x : K) :
    (∑ i : index K, placeWeights K c i * embeddingCoords K x i ^ 2)
      = ∑ w : InfinitePlace K, c w * (w x) ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type,
    ← Fintype.sum_subtype_add_sum_subtype IsReal (fun w : InfinitePlace K => c w * (w x) ^ 2)]
  congr 1
  · -- real places
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [embeddingCoords_isReal]
    have h1 : (w : InfinitePlace K) x = ‖(w : InfinitePlace K).embedding x‖ :=
      (norm_embedding_eq _ x).symm
    have h2 : ((w : InfinitePlace K).embedding x) = ((embedding_of_isReal w.2 x : ℝ) : ℂ) :=
      (embedding_of_isReal_apply w.2 x).symm
    rw [h1, h2, Complex.norm_real, placeWeights]
    simp [sq_abs]
  · -- complex places
    have hre : (∑ i : {w : InfinitePlace K // ¬ IsReal w}, c ↑i * ((i : InfinitePlace K) x) ^ 2)
        = ∑ w : {w : InfinitePlace K // IsComplex w}, c ↑w * ((w : InfinitePlace K) x) ^ 2 :=
      Fintype.sum_equiv (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex)) _ _ (fun w => rfl)
    rw [hre]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Fin.sum_univ_two, embeddingCoords_isComplex_fst, embeddingCoords_isComplex_snd]
    have h1 : (w : InfinitePlace K) x = ‖(w : InfinitePlace K).embedding x‖ :=
      (norm_embedding_eq _ x).symm
    have h2 : ‖(w : InfinitePlace K).embedding x‖ ^ 2
        = ((w : InfinitePlace K).embedding x).re ^ 2
          + ((w : InfinitePlace K).embedding x).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [h1, h2, placeWeights]
    simp only [Sum.elim_inr]
    ring

open scoped Classical in
/-- The multivariable Hecke theta of a fractional ideal with per-place weights.-/
noncomputable def heckeTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : InfinitePlace K → ℝ) : ℝ :=
  ∑' v : idealZLattice K I, Real.exp (-π * ∑ i : index K,
    placeWeights K c i * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)

open scoped Classical in
/-- Multiplication by (the mixed embedding of) a field element `x`, as a linear map of the
Euclidean coordinate space (conjugated through the coordinate identifications).-/
noncomputable def mulCoords (x : K) :
    EuclideanSpace ℝ (index K) →ₗ[ℝ] EuclideanSpace ℝ (index K) :=
  ((((euclidean.stdOrthonormalBasis K).repr.toLinearEquiv.toLinearMap).comp
      ((euclidean.toMixed K).symm.toLinearMap)).comp
    (LinearMap.mulLeft ℝ (mixedEmbedding K x))).comp
    (((euclidean.toMixed K).toLinearMap).comp
      ((euclidean.stdOrthonormalBasis K).repr.symm.toLinearEquiv.toLinearMap))

open scoped Classical in
/--
@isnad1 id=eq.0h3v.s8.6c64147464d4 from=translated src=- shape=8fbb0c8f vocab=d3b1247e
-/
theorem mulCoords_embeddingCoords (x a : K) :
    mulCoords K x (embeddingCoords K a) = embeddingCoords K (x * a) := by
  rw [mulCoords, embeddingCoords, embeddingCoords]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearIsometryEquiv.symm_apply_apply]
  show (euclidean.stdOrthonormalBasis K).repr ((euclidean.toMixed K).symm
    (mixedEmbedding K x * ((euclidean.toMixed K) ((euclidean.toMixed K).symm
      (mixedEmbedding K a))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ← map_mul]

open scoped Classical in
/-- Multiplication by the image of a unit permutes the points of an ideal lattice:
the induced self-equivalence of `idealZLattice K I`.-/
noncomputable def unitMulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ε : (𝓞 K)ˣ) :
    idealZLattice K I ≃ idealZLattice K I where
  toFun v := ⟨mulCoords K (algebraMap (𝓞 K) K (ε : 𝓞 K)) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    rw [mem_idealZLattice]
    refine ⟨algebraMap (𝓞 K) K (ε : 𝓞 K) * a, ?_, by rw [← hva, mulCoords_embeddingCoords]⟩
    have := Submodule.smul_mem ((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) (ε : 𝓞 K) ha
    rwa [Algebra.smul_def] at this⟩
  invFun v := ⟨mulCoords K (algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    rw [mem_idealZLattice]
    refine ⟨algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a, ?_,
      by rw [← hva, mulCoords_embeddingCoords]⟩
    have := Submodule.smul_mem ((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ha
    rwa [Algebra.smul_def] at this⟩
  left_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc,
      ← map_mul]
    norm_cast
    rw [inv_mul_cancel ε]
    simp
  right_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc,
      ← map_mul]
    norm_cast
    rw [mul_inv_cancel ε]
    simp

open scoped Classical in
/-- **Unit equivariance of the Hecke theta** (the symmetry making the unit average
well-defined): scaling the place weights by `w(ε)²` for a unit `ε` leaves the theta of the
ideal lattice unchanged — multiplication by `ε` permutes the lattice points.
@isnad1 id=eq.0h4v.s8.e0dfa9299f2a from=translated src=- shape=a3c606c7 vocab=bf63752f
-/
theorem heckeTheta_unit_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ε : (𝓞 K)ˣ)
    (c : InfinitePlace K → ℝ) :
    heckeTheta K I (fun w => (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 * c w)
      = heckeTheta K I c := by
  rw [heckeTheta, heckeTheta]
  conv_rhs => rw [← Equiv.tsum_eq (unitMulLatticeEquiv K I ε)]
  refine tsum_congr (fun v => ?_)
  obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
  congr 1
  have hcoe : ((unitMulLatticeEquiv K I ε v : idealZLattice K I) :
      EuclideanSpace ℝ (index K))
      = embeddingCoords K (algebraMap (𝓞 K) K (ε : 𝓞 K) * a) := by
    show mulCoords K _ (v : EuclideanSpace ℝ (index K)) = _
    rw [← hva, mulCoords_embeddingCoords]
  rw [hcoe, ← hva, sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq]
  refine congrArg (fun r => -π * r) ?_
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, mul_pow]
  ring

open scoped Classical in
/-- The dual place-weights: `c_w⁻¹` at real places and `4·c_w⁻¹` at complex places — the
factor `4 = 2²` is the square of the duality scaling (`dualityWeights`), the archimedean
bookkeeping that ultimately feeds `Γℂ`.-/
noncomputable def dualPlaceWeights (c : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun w => if IsReal w then (c w)⁻¹ else 4 * (c w)⁻¹

open scoped Classical in
omit [NumberField K] in
/--
@isnad1 id=eq.0h3v.s5.c96705f1d058 from=translated src=- shape=474b079f vocab=3104e463
-/
theorem placeWeights_dualPlaceWeights (c : InfinitePlace K → ℝ) (i : index K) :
    placeWeights K (dualPlaceWeights K c) i
      = (placeWeights K c i)⁻¹ * (dualityWeights K i) ^ 2 := by
  rcases i with w | ⟨w, j⟩
  · simp only [placeWeights, Sum.elim_inl, dualPlaceWeights, dualityWeights, ite_eq_left w.2]
    norm_num
  · simp only [placeWeights, Sum.elim_inr, dualPlaceWeights, dualityWeights]
    rw [ite_eq_right (by rw [not_isReal_iff_isComplex]; exact w.2)]
    fin_cases j <;> norm_num <;> ring

open scoped Classical in
/-- **The inversion law of the multivariable Hecke theta** (SP1-AGE-3):
`Θ_I(c) = covol(L_I)⁻¹ · (∏ᵢ c-coords)^{-1/2} · Θ_{I^∨}(dual weights)` — Poisson summation
over the ideal lattice, with the dual side identified as the theta of the trace-dual ideal
via `dualZLattice_idealZLattice` (the duality twist absorbed into the weights).
@isnad1 id=eq.1h3v.s10.4868e61a4953 from=translated src=- shape=b3798d63 vocab=59b5d555
-/
theorem heckeTheta_inversion (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    heckeTheta K I c
      = (ZLattice.covolume (idealZLattice K I) volume)⁻¹
        * (Real.sqrt (∏ i, placeWeights K c i))⁻¹
        * heckeTheta K (dualIdealUnit K I) (dualPlaceWeights K c) := by
  have hpos : ∀ i, 0 < placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hc _
  rw [heckeTheta, weightedThetaLattice_transform (idealZLattice K I) hpos]
  congr 1
  rw [dualZLattice_idealZLattice K I, heckeTheta,
    ← Equiv.tsum_eq (ZLattice.comap_equiv ℝ (idealZLattice K (dualIdealUnit K I))
      ((diagScale (dualityWeights K)
        (dualityWeights_ne_zero K)).symm.toContinuousLinearEquiv.toLinearEquiv)).toEquiv]
  refine tsum_congr (fun v => ?_)
  congr 1
  simp only [LinearEquiv.coe_toEquiv, ZLattice.comap_equiv_apply]
  refine congrArg (fun r => -π * r) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have he : (((diagScale (dualityWeights K)
      (dualityWeights_ne_zero K)).symm.toContinuousLinearEquiv.toLinearEquiv).symm)
        ((v : EuclideanSpace ℝ (index K)))
      = (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
          ((v : EuclideanSpace ℝ (index K))) := rfl
  rw [he, placeWeights_dualPlaceWeights, diagScale_apply, mul_pow]
  ring

open scoped Classical in
/-- Extend hyperplane coordinates `u : logSpace K` (indexed by `w ≠ w₀`) to all infinite
places by the trace-zero condition: the `w₀`-component is `-∑_{w ≠ w₀} u_w`. On the image of
`logEmbedding` this recovers the full unit log-vector (`fullLog_logEmbedding`).-/
noncomputable def fullLog (u : logSpace K) : InfinitePlace K → ℝ := fun w =>
  if h : w = (w₀ : InfinitePlace K) then
    -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'
  else u ⟨w, h⟩

open scoped Classical in
/--
@isnad1 id=eq.0h3v.s9.04d6c60bdb0c from=translated src=- shape=56ae95cb vocab=0cf3ef7f
-/
theorem fullLog_logEmbedding (ε : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullLog K (logEmbedding K (Additive.ofMul ε)) w
      = mult w * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) := by
  rw [fullLog]
  split_ifs with h
  · rw [sum_logEmbedding_component, h]
    ring
  · rw [logEmbedding_component]

open scoped Classical in
/--
@isnad1 id=eq.0h3v.s7.1a1310c8dd87 from=translated src=- shape=e986181e vocab=5fc83a9a
-/
theorem fullLog_add (u v : logSpace K) :
    fullLog K (u + v) = fullLog K u + fullLog K v := by
  funext w
  simp only [fullLog, Pi.add_apply]
  split_ifs with h
  · rw [Finset.sum_add_distrib]
    ring
  · rfl

open scoped Classical in
/-- **The Hecke weight family**: `c(t,u)_w = t^{1/n}·exp(2·(trace-zero extension of u)_w / mult w)`.
Pinned by two requirements: `∏_w c_w^{mult w} = t` (the norm ray, giving `N(𝔞)^{-s}` under the
Mellin transform) and equivariance under `u ↦ u + logEmbedding ε` matching
`heckeTheta_unit_mul` (making the theta integrand periodic modulo the unit lattice).-/
noncomputable def heckeWeights (t : ℝ) (u : logSpace K) : InfinitePlace K → ℝ := fun w =>
  t ^ ((1 : ℝ) / (Module.finrank ℚ K)) * Real.exp (2 * fullLog K u w / mult w)

/--
@isnad1 id=lt.1h4v.s5.ca084a8d1b4e from=translated src=- shape=dba15783 vocab=5bff6430
-/
theorem heckeWeights_pos {t : ℝ} (ht : 0 < t) (u : logSpace K) (w : InfinitePlace K) :
    0 < heckeWeights K t u w := by
  rw [heckeWeights]
  positivity

open scoped Classical in
/-- **Equivariance of the Hecke weights**: translating `u` by the log of a unit scales the
weights by `w(ε)²` — exactly the scaling `heckeTheta_unit_mul` absorbs.
@isnad1 id=eq.0h4v.s9.15a10f7e1478 from=translated src=- shape=33303ede vocab=9c5b84b9
-/
theorem heckeWeights_add_logEmbedding (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) :
    heckeWeights K t (u + logEmbedding K (Additive.ofMul ε))
      = fun w => (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 * heckeWeights K t u w := by
  funext w
  rw [heckeWeights, heckeWeights, fullLog_add, Pi.add_apply, fullLog_logEmbedding]
  have hmult : (mult w : ℝ) ≠ 0 := mult_ne_zero_real K w
  have hpos : 0 < w (algebraMap (𝓞 K) K (ε : 𝓞 K)) := by
    rw [pos_iff]
    simp only [ne_eq, RingOfIntegers.coe_eq_zero_iff]
    exact Units.ne_zero ε
  rw [mul_add, add_div, Real.exp_add]
  have h2 : 2 * ((mult w : ℝ) * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K)))) / (mult w : ℝ)
      = 2 * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) := by
    field_simp
  have h3 : Real.exp (2 * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))))
      = (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hpos]
    ring
  rw [h2, h3]
  ring

open scoped Classical in
/-- **Periodicity of the theta integrand modulo the unit lattice**: the Hecke-weighted theta
is invariant under `u ↦ u + logEmbedding ε` — the equivariance of the weights matches the
unit symmetry of the theta exactly. This makes the unit-box average well-defined.
@isnad1 id=eq.0h5v.s9.6c704931e225 from=translated src=- shape=be7681b0 vocab=8bb617b9
-/
theorem heckeTheta_heckeWeights_periodic (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) :
    heckeTheta K I (heckeWeights K t (u + logEmbedding K (Additive.ofMul ε)))
      = heckeTheta K I (heckeWeights K t u) := by
  rw [heckeWeights_add_logEmbedding]
  exact heckeTheta_unit_mul K I ε _

open scoped Classical in
/--
@isnad1 id=eq.0h2v.s5.475c5e9aba8b from=translated src=- shape=1dc63edc vocab=3933713a
-/
theorem sum_fullLog (u : logSpace K) : ∑ w : InfinitePlace K, fullLog K u w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]
  have h1 : fullLog K u (w₀ : InfinitePlace K)
      = -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w' := by
    rw [fullLog]
    exact dite_eq_left rfl
  have h2 : ∀ w : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)},
      fullLog K u (w : InfinitePlace K) = u w := by
    intro w
    rw [fullLog, dite_eq_right w.2]
  rw [h1, Finset.sum_congr rfl (fun w _ => h2 w)]
  ring

open scoped Classical in
/-- **The norm-ray property**: the place-multiplicity-weighted product of the Hecke weights
is exactly `t` — the Mellin variable. (`∑ mult = n` and the trace-zero sum of `fullLog`.)
@isnad1 id=eq.1h3v.s6.b7bf9bda5e7b from=translated src=- shape=0e5a2fc3 vocab=7931128b
-/
theorem prod_heckeWeights_pow_mult {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ∏ w : InfinitePlace K, (heckeWeights K t u w) ^ mult w = t := by
  have hn : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hexp : ∀ w : InfinitePlace K,
      (Real.exp (2 * fullLog K u w / mult w)) ^ mult w = Real.exp (2 * fullLog K u w) := by
    intro w
    rw [← Real.exp_nat_mul]
    congr 1
    have hm : (mult w : ℝ) ≠ 0 := mult_ne_zero_real K w
    field_simp
  simp_rw [heckeWeights, mul_pow, hexp]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow_eq_pow_sum,
    ← Real.rpow_natCast (t ^ ((1:ℝ) / (Module.finrank ℚ K))), ← Real.rpow_mul ht.le,
    sum_mult_eq]
  rw [show (∑ x : InfinitePlace K, 2 * fullLog K u x) = 0 by
    rw [← Finset.mul_sum, sum_fullLog, mul_zero]]
  rw [Real.exp_zero, mul_one, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one]

open scoped Classical in
/-- **Hecke's unit-averaged theta** `g_I(t)`: the multivariable theta at the Hecke weights,
averaged over the fundamental box of the unit lattice in log-coordinates and divided by the
number of roots of unity. Genuine Lebesgue integral over `logSpace K`; the integrand is
periodic modulo `unitLattice K` (`heckeTheta_heckeWeights_periodic`), so the box choice is
immaterial. The Mellin transform of `g_I` produces the completed partial zeta of the class
of `I` (SP1-AGE-4).-/
noncomputable def heckeG (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ u in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      heckeTheta K I (heckeWeights K t u)

open scoped Classical in
/-- `fullLog` is odd.
@isnad1 id=eq.0h2v.s6.0acba57b84b0 from=translated src=- shape=c2e65a75 vocab=4210de09
-/
theorem fullLog_neg (u : logSpace K) : fullLog K (-u) = -fullLog K u := by
  funext w
  simp only [fullLog, Pi.neg_apply]
  split_ifs with h
  · rw [Finset.sum_neg_distrib]
  · rfl

open scoped Classical in
/-- The duality bookkeeping of the Hecke weights: the dual weights of `c(t,u)` are the
weights `c(1/t, -u)` scaled by `1` at real and `4` at complex places.
@isnad1 id=eq.1h4v.s7.df14d38695d4 from=translated src=- shape=536dc5f7 vocab=674f3fff
-/
theorem dualPlaceWeights_heckeWeights {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    dualPlaceWeights K (heckeWeights K t u) w
      = (if IsReal w then 1 else 4) * heckeWeights K t⁻¹ (-u) w := by
  rw [dualPlaceWeights, heckeWeights, heckeWeights, fullLog_neg]
  have hn : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hinv : (t ^ ((1:ℝ) / (Module.finrank ℚ K)))⁻¹
      = t⁻¹ ^ ((1:ℝ) / (Module.finrank ℚ K)) := by
    rw [← Real.rpow_neg ht.le, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  have hexp : (Real.exp (2 * fullLog K u w / mult w))⁻¹
      = Real.exp (2 * -fullLog K u w / mult w) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [mul_inv, hinv, hexp]
  simp only [Pi.neg_apply]
  split_ifs <;> ring

open scoped Classical in
/-- The coordinate product of place weights is the multiplicity-weighted place product:
real places contribute once, complex places (two coordinates) twice.
@isnad1 id=eq.0h2v.s7.d5b04b1a7d62 from=translated src=- shape=853485ba vocab=5ca11394
-/
theorem prod_placeWeights (c : InfinitePlace K → ℝ) :
    (∏ i : index K, placeWeights K c i) = ∏ w : InfinitePlace K, c w ^ mult w := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type,
    ← Fintype.prod_subtype_mul_prod_subtype IsReal (fun w : InfinitePlace K => c w ^ mult w)]
  congr 1
  · refine Finset.prod_congr rfl (fun w _ => ?_)
    simp only [placeWeights, Sum.elim_inl]
    rw [mult, ite_eq_left w.2, pow_one]
  · have hre : (∏ i : {w : InfinitePlace K // ¬ IsReal w}, c ↑i ^ mult (i : InfinitePlace K))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, c ↑w ^ mult (w : InfinitePlace K) :=
      Fintype.prod_equiv (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex)) _ _ (fun w => rfl)
    rw [hre]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [Fin.prod_univ_two]
    simp only [placeWeights, Sum.elim_inr]
    rw [mult, ite_eq_right (by rw [not_isReal_iff_isComplex]; exact w.2)]
    ring

open scoped Classical in
/-- The coordinate product of the Hecke weights is the Mellin variable `t` — so the middle
factor of `heckeTheta_inversion` at the Hecke weights is exactly `(√t)⁻¹`.
@isnad1 id=eq.1h3v.s7.0ed8d43d6579 from=translated src=- shape=42cb891e vocab=d4b78430
-/
theorem prod_placeWeights_heckeWeights {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    (∏ i : index K, placeWeights K (heckeWeights K t u) i) = t := by
  rw [prod_placeWeights]
  exact prod_heckeWeights_pow_mult K ht u

open scoped Classical in
/-- Every zero-sum place vector is the trace-zero extension of its restriction: `fullLog` is
onto the trace-zero hyperplane.
@isnad1 id=eq.1h2v.s6.219ec91bb8c9 from=translated src=- shape=d56faf2b vocab=26686d1d
-/
theorem fullLog_restrict (y : InfinitePlace K → ℝ) (hy : ∑ w, y w = 0) :
    fullLog K (fun w : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)} => y w) = y := by
  funext w
  rw [fullLog]
  split_ifs with h
  · rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)] at hy
    rw [h]
    linarith
  · rfl

open scoped Classical in
/-- The fixed trace-zero shift in log-coordinates realising the complex-place duality factor
`4` (the trace-zero part of the log-vector `(0; log 4)`).-/
noncomputable def dualShift : logSpace K :=
  fun w => (mult (w : InfinitePlace K) : ℝ) / 2 *
    ((if IsReal (w : InfinitePlace K) then 0 else Real.log 4)
      - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)

open scoped Classical in
/--
@isnad1 id=eq.0h2v.s7.79af1767f6b7 from=translated src=- shape=67fe5480 vocab=25f5aa7b
-/
theorem fullLog_dualShift (w : InfinitePlace K) :
    fullLog K (dualShift K) w
      = (mult w : ℝ) / 2 * ((if IsReal w then 0 else Real.log 4)
          - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K) := by
  have h := fullLog_restrict K (fun w => (mult w : ℝ) / 2 *
    ((if IsReal w then 0 else Real.log 4)
      - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)) ?_
  · exact congrFun h w
  · -- zero-sum computation
    have hsplit : ∀ w : InfinitePlace K, (mult w : ℝ) / 2 *
        ((if IsReal w then 0 else Real.log 4)
          - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)
        = (mult w : ℝ) / 2 * (if IsReal w then 0 else Real.log 4)
          - (mult w : ℝ) * (nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K) := by
      intro w
      ring
    rw [Finset.sum_congr rfl (fun w _ => hsplit w), Finset.sum_sub_distrib]
    have h1 : ∑ w : InfinitePlace K, (mult w : ℝ) / 2 * (if IsReal w then 0 else Real.log 4)
        = nrComplexPlaces K * Real.log 4 := by
      rw [← Fintype.sum_subtype_add_sum_subtype IsReal
        (fun w : InfinitePlace K => (mult w : ℝ) / 2 * (if IsReal w then 0 else Real.log 4))]
      have hz : (∑ w : {w : InfinitePlace K // IsReal w},
          (mult (w : InfinitePlace K) : ℝ) / 2 *
            (if IsReal (w : InfinitePlace K) then 0 else Real.log 4)) = 0 := by
        refine Finset.sum_eq_zero (fun w _ => ?_)
        rw [ite_eq_left w.2, mul_zero]
      have hc : (∑ w : {w : InfinitePlace K // ¬ IsReal w},
          (mult (w : InfinitePlace K) : ℝ) / 2 *
            (if IsReal (w : InfinitePlace K) then 0 else Real.log 4))
          = nrComplexPlaces K * Real.log 4 := by
        have hterm : ∀ w : {w : InfinitePlace K // ¬ IsReal w},
            (mult (w : InfinitePlace K) : ℝ) / 2 *
              (if IsReal (w : InfinitePlace K) then 0 else Real.log 4) = Real.log 4 := by
          intro w
          rw [ite_eq_right w.2, mult, ite_eq_right w.2]
          norm_num
        rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_const, nsmul_eq_mul]
        congr 1
        norm_cast
        exact (Fintype.card_congr (Equiv.subtypeEquivRight
          (fun w : InfinitePlace K => not_isReal_iff_isComplex))).trans rfl
      rw [hz, hc, zero_add]
    have h2 : ∑ w : InfinitePlace K,
        (mult w : ℝ) * (nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)
        = nrComplexPlaces K * Real.log 4 := by
      rw [← Finset.sum_mul]
      have := sum_mult_eq (K := K)
      rw [show (∑ w : InfinitePlace K, (mult w : ℝ)) = (Module.finrank ℚ K : ℝ) by
        exact_mod_cast congrArg Nat.cast this]
      have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos_real K).ne'
      field_simp
    rw [h1, h2, sub_self]

/--
@isnad1 id=eq.2h5v.s7.6780d649ce53 from=translated src=- shape=1b75478c vocab=29963168
-/
theorem heckeWeights_mul_left {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (u : logSpace K)
    (w : InfinitePlace K) :
    heckeWeights K (a * t) u w
      = a ^ ((1 : ℝ) / (Module.finrank ℚ K)) * heckeWeights K t u w := by
  rw [heckeWeights, heckeWeights, Real.mul_rpow ha ht]
  ring

open scoped Classical in
/--
@isnad1 id=eq.0h5v.s7.e0aca50afb68 from=translated src=- shape=67b793bb vocab=5ea0271b
-/
theorem heckeWeights_add_right (t : ℝ) (u v : logSpace K) (w : InfinitePlace K) :
    heckeWeights K t (u + v) w
      = Real.exp (2 * fullLog K v w / mult w) * heckeWeights K t u w := by
  rw [heckeWeights, heckeWeights, fullLog_add, Pi.add_apply]
  rw [show 2 * (fullLog K u w + fullLog K v w) / (mult w : ℝ)
      = 2 * fullLog K u w / mult w + 2 * fullLog K v w / mult w by ring]
  rw [Real.exp_add]
  ring

open scoped Classical in
/-- **The `(1;4)`-absorption identity.** Multiplying the Hecke weights by the duality factor
(`1` at real places, `4` at complex ones) is reabsorbed as a norm-ray scaling by
`4^(2·r₂)` together with the fixed trace-zero log-shift `dualShift`.
@isnad1 id=eq.1h4v.s7.e30636242776 from=translated src=- shape=6066d231 vocab=557eecb0
-/
theorem ite_mul_heckeWeights {t : ℝ} (ht : 0 ≤ t) (u : logSpace K) (w : InfinitePlace K) :
    (if IsReal w then (1 : ℝ) else 4) * heckeWeights K t u w
      = heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t) (u + dualShift K) w := by
  rw [heckeWeights_mul_left K (by positivity) ht, heckeWeights_add_right,
    fullLog_dualShift]
  have hm : (mult w : ℝ) ≠ 0 := mult_ne_zero_real K w
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos_real K).ne'
  have harg : 2 * ((mult w : ℝ) / 2 * ((if IsReal w then 0 else Real.log 4)
        - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)) / mult w
      = (if IsReal w then 0 else Real.log 4)
        - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K := by
    field_simp
  rw [harg]
  have hscal : ((4 : ℝ) ^ (2 * nrComplexPlaces K)) ^ ((1 : ℝ) / (Module.finrank ℚ K))
      * Real.exp ((if IsReal w then 0 else Real.log 4)
          - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)
      = (if IsReal w then (1 : ℝ) else 4) := by
    rw [← Real.rpow_natCast (4 : ℝ) (2 * nrComplexPlaces K),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), ← Real.exp_add]
    have hargsum : Real.log 4 * ((2 * nrComplexPlaces K : ℕ) * ((1 : ℝ) / (Module.finrank ℚ K)))
        + ((if IsReal w then 0 else Real.log 4)
            - 2 * nrComplexPlaces K * Real.log 4 / Module.finrank ℚ K)
        = (if IsReal w then 0 else Real.log 4) := by
      push_cast
      field_simp
      ring
    rw [hargsum]
    split_ifs with hw
    · exact Real.exp_zero
    · exact Real.exp_log (by norm_num)
  rw [← mul_assoc, hscal]

open scoped Classical in
/-- **Weights duality, fully absorbed.** The dual of the Hecke weights at `(t, u)` is the
Hecke weights at `(4^(2r₂)·t⁻¹, -u + dualShift)` — inversion of the norm-ray parameter,
negation in the log-torus, and a fixed translation. This is the exact bookkeeping needed
for the inversion of the unit-averaged theta `heckeG`.
@isnad1 id=eq.1h3v.s7.95ebfed7989a from=translated src=- shape=a144fafa vocab=0d2b60d3
-/
theorem dualPlaceWeights_heckeWeights_eq {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    dualPlaceWeights K (heckeWeights K t u)
      = heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹) (-u + dualShift K) := by
  funext w
  rw [dualPlaceWeights_heckeWeights K ht u w, ite_mul_heckeWeights K (by positivity) (-u) w]

open scoped Classical in
/-- Integrating a lattice-periodic function over a `ZSpan` fundamental box is invariant
under the affine involution `u ↦ -u + s`: the preimage of the box is again a fundamental
domain, and periodic integrals agree on any two fundamental domains.
@isnad1 id=eq.1h5v.s9.669ef3416936 from=translated src=- shape=11c06c89 vocab=12e58255
-/
theorem setIntegral_fundamentalDomain_comp_neg_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → ℝ)
    (hf : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x, f (↑l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain b, f (-u + s)
      = ∫ u in ZSpan.fundamentalDomain b, f u := by
  set τ : (ι → ℝ) → (ι → ℝ) := fun u => -u + s with hτ
  have hmp : MeasurePreserving τ volume volume :=
    (measurePreserving_add_right volume s).comp (Measure.measurePreserving_neg volume)
  have hemb : MeasurableEmbedding τ :=
    ((Homeomorph.neg (ι → ℝ)).trans (Homeomorph.addRight s)).measurableEmbedding
  have hFD := ZSpan.isAddFundamentalDomain b volume
  have hD' : IsAddFundamentalDomain (Submodule.span ℤ (Set.range ⇑b))
      (τ ⁻¹' ZSpan.fundamentalDomain b) volume := by
    refine hFD.preimage_of_equiv hmp.quasiMeasurePreserving
      (e := fun l => -l) neg_involutive.bijective (fun g x => ?_)
    show τ ((-g : Submodule.span ℤ (Set.range ⇑b)) +ᵥ x) = g +ᵥ τ x
    rw [Submodule.vadd_def, Submodule.vadd_def, vadd_eq_add, vadd_eq_add, hτ]
    push_cast
    abel
  have hset : ZSpan.fundamentalDomain b = τ ⁻¹' (τ ⁻¹' ZSpan.fundamentalDomain b) := by
    ext x
    have : τ (τ x) = x := by
      rw [hτ]
      simp only [neg_add_rev, neg_neg]
      abel
    simp [Set.mem_preimage, this]
  conv_lhs => rw [hset]
  rw [hmp.setIntegral_preimage_emb hemb]
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)) (ι → ℝ) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup (ι → ℝ) volume)
  refine hD'.setIntegral_eq hFD (f := f) (fun g x => ?_)
  rw [Submodule.vadd_def, vadd_eq_add]
  exact hf g x

open scoped Classical in
/-- **Inversion for the unit-averaged Hecke theta** `g_I`: the Mellin-ready form of the
theta transformation. The `(1;4)`-duality factor has been absorbed into the norm-ray
parameter (`4^(2r₂)·t⁻¹`) and a fundamental-domain translation, which the box integral
does not see.
@isnad1 id=eq.1h3v.s9.32d32e115386 from=translated src=- shape=4e49798c vocab=721394ae
-/
theorem heckeG_inversion (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    heckeG K I t
      = (ZLattice.covolume (idealZLattice K I) volume)⁻¹ * (Real.sqrt t)⁻¹
        * heckeG K (dualIdealUnit K I) ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹) := by
  have hpt : ∀ u : logSpace K,
      heckeTheta K I (heckeWeights K t u)
        = (ZLattice.covolume (idealZLattice K I) volume)⁻¹ * (Real.sqrt t)⁻¹
          * heckeTheta K (dualIdealUnit K I)
              (heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹)
                (-u + dualShift K)) := by
    intro u
    rw [heckeTheta_inversion K I _ (heckeWeights_pos K ht u),
      prod_placeWeights_heckeWeights K ht u,
      dualPlaceWeights_heckeWeights_eq K ht u]
  rw [heckeG, heckeG]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  have hFDinv : ∫ u in ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
        heckeTheta K (dualIdealUnit K I)
          (heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹) (-u + dualShift K))
      = ∫ u in ZSpan.fundamentalDomain
          ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
          heckeTheta K (dualIdealUnit K I)
            (heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹) u) := by
    refine setIntegral_fundamentalDomain_comp_neg_add
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) (dualShift K)
      (fun u => heckeTheta K (dualIdealUnit K I)
        (heckeWeights K ((4 : ℝ) ^ (2 * nrComplexPlaces K) * t⁻¹) u))
      (fun l x => ?_)
    have hl : (l : logSpace K) ∈ unitLattice K :=
      (le_of_eq ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ)) l.2
    obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hl
    rw [add_comm, ← ha]
    exact heckeTheta_heckeWeights_periodic K (dualIdealUnit K I) _ x (Additive.toMul a)
  rw [hFDinv]
  ring

open scoped Classical in
/-- Translation-only version of `setIntegral_fundamentalDomain_comp_neg_add`: the box
integral of a lattice-periodic function is translation invariant. Derived by applying the
negation lemma twice (with shifts `s` then `0`).
@isnad1 id=eq.1h5v.s9.7a6b466467f5 from=translated src=- shape=43b0f840 vocab=63cb96ce
-/
theorem setIntegral_fundamentalDomain_comp_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (ι → ℝ)) (s : ι → ℝ) (f : (ι → ℝ) → ℝ)
    (hf : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x, f (↑l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain b, f (u + s)
      = ∫ u in ZSpan.fundamentalDomain b, f u := by
  have hneg : ∀ l : Submodule.span ℤ (Set.range ⇑b), ∀ x : ι → ℝ,
      f (-(↑l + x)) = f (-x) := by
    intro l x
    have := hf (-l) (-x)
    rw [show ((↑(-l) : ι → ℝ) + -x) = -(↑l + x) by push_cast; abel] at this
    exact this
  have e1 : ∫ u in ZSpan.fundamentalDomain b, f (u + s)
      = ∫ u in ZSpan.fundamentalDomain b, (fun v => f (-v)) (-u + (-s)) := by
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b) (fun u _ => ?_)
    simp only
    rw [show -(-u + -s) = u + s by abel]
  rw [e1, setIntegral_fundamentalDomain_comp_neg_add b (-s) (fun v => f (-v)) hneg]
  have e2 : ∫ u in ZSpan.fundamentalDomain b, (fun v => f (-v)) u
      = ∫ u in ZSpan.fundamentalDomain b, f (-u + 0) := by
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b) (fun u _ => ?_)
    simp only [add_zero]
  rw [e2, setIntegral_fundamentalDomain_comp_neg_add b 0 f hf]

open scoped Classical in
/-- The trace-zero log-shift by which multiplication by a nonzero `x : K` moves the Hecke
weights: the restriction of `w ↦ mult w · log (w x) − mult w · log |N(x)| / n`.-/
noncomputable def xShift (x : K) : logSpace K :=
  fun w => (mult (w : InfinitePlace K) : ℝ) * Real.log ((w : InfinitePlace K) x)
    - (mult (w : InfinitePlace K) : ℝ) * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ)
        / Module.finrank ℚ K

open scoped Classical in
/--
@isnad1 id=eq.1h2v.s7.ed2217005f5b from=translated src=- shape=7d05bbe8 vocab=c6570785
-/
theorem sum_mult_mul_log (x : K) (hx : x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w x)
      = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hterm : ∀ w : InfinitePlace K, (mult w : ℝ) * Real.log (w x)
      = Real.log (w x ^ mult w) := by
    intro w
    rw [Real.log_pow]
  rw [Finset.sum_congr rfl (fun w _ => hterm w),
    ← Real.log_prod (fun w _ => pow_ne_zero _ ((pos_iff (w := w)).mpr hx).ne'),
    prod_eq_abs_norm]

open scoped Classical in
/--
@isnad1 id=eq.1h3v.s7.2319427a3d1b from=translated src=- shape=fdeba121 vocab=c87a2c3e
-/
theorem fullLog_xShift {x : K} (hx : x ≠ 0) (w : InfinitePlace K) :
    fullLog K (xShift K x) w
      = (mult w : ℝ) * Real.log (w x)
        - (mult w : ℝ) * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K := by
  have h := fullLog_restrict K (fun w => (mult w : ℝ) * Real.log (w x)
    - (mult w : ℝ) * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K) ?_
  · exact congrFun h w
  · rw [Finset.sum_sub_distrib, sum_mult_mul_log K x hx]
    have hsum : ∑ w : InfinitePlace K,
        (mult w : ℝ) * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K
        = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
      rw [show (fun w : InfinitePlace K => (mult w : ℝ)
          * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K)
        = (fun w : InfinitePlace K => (mult w : ℝ)
          * (Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K)) by
          funext w; ring]
      rw [← Finset.sum_mul]
      rw [show (∑ w : InfinitePlace K, (mult w : ℝ)) = (Module.finrank ℚ K : ℝ) by
        exact_mod_cast congrArg Nat.cast (sum_mult_eq (K := K))]
      have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos_real K).ne'
      field_simp
    rw [hsum, sub_self]

open scoped Classical in
/-- **The `x`-absorption identity.** Multiplying the Hecke weights by `(w x)²` (the effect
of the lattice `L_I ↦ L_{xI}`) is reabsorbed as a norm-ray scaling by `|N(x)|²` together
with the trace-zero log-shift `xShift x`.
@isnad1 id=eq.2h5v.s8.7ff6559096d6 from=translated src=- shape=fc2d48a3 vocab=c56b4e88
-/
theorem sq_mul_heckeWeights {x : K} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) (u : logSpace K)
    (w : InfinitePlace K) :
    (w x) ^ 2 * heckeWeights K t u w
      = heckeWeights K (((|Algebra.norm ℚ x| : ℚ) : ℝ) ^ 2 * t) (u + xShift K x) w := by
  have hNx : (0 : ℝ) < ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    rw [Rat.cast_pos, abs_pos]
    exact Algebra.norm_ne_zero_iff.mpr hx
  have hwx : (0 : ℝ) < w x := pos_iff.mpr hx
  have hm : (mult w : ℝ) ≠ 0 := mult_ne_zero_real K w
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos_real K).ne'
  rw [heckeWeights_mul_left K (by positivity) ht, heckeWeights_add_right,
    fullLog_xShift K hx]
  have harg : 2 * ((mult w : ℝ) * Real.log (w x)
        - (mult w : ℝ) * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K)
        / mult w
      = 2 * Real.log (w x)
        - 2 * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K := by
    field_simp
  rw [harg]
  have hscal : (((|Algebra.norm ℚ x| : ℚ) : ℝ) ^ 2) ^ ((1 : ℝ) / (Module.finrank ℚ K))
      * Real.exp (2 * Real.log (w x)
          - 2 * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K)
      = (w x) ^ 2 := by
    rw [← Real.rpow_natCast (((|Algebra.norm ℚ x| : ℚ) : ℝ)) 2,
      ← Real.rpow_mul hNx.le, Real.rpow_def_of_pos hNx, ← Real.exp_add]
    have hargsum : Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) * ((2 : ℕ)
          * ((1 : ℝ) / (Module.finrank ℚ K)))
        + (2 * Real.log (w x)
            - 2 * Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) / Module.finrank ℚ K)
        = 2 * Real.log (w x) := by
      push_cast
      field_simp
      ring
    rw [hargsum, show (2 : ℝ) * Real.log (w x) = (2 : ℕ) * Real.log (w x) by norm_num,
      Real.exp_nat_mul, Real.exp_log hwx]
  rw [← mul_assoc, hscal]

open scoped Classical in
/-- Membership in the lattice of `x·I` (`x ∈ Kˣ` acting through `toPrincipalIdeal`).
@isnad1 id=iff.0h4v.s11.914874630fd9 from=translated src=- shape=12fb2cd6 vocab=0e67a46c
-/
theorem mem_idealZLattice_principal_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Kˣ)
    (v : EuclideanSpace ℝ (index K)) :
    v ∈ idealZLattice K (toPrincipalIdeal (𝓞 K) K x * I)
      ↔ ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), embeddingCoords K ((x : K) * a) = v := by
  rw [mem_idealZLattice]
  constructor
  · rintro ⟨a, ha, hva⟩
    rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨b, hb, hva⟩
  · rintro ⟨a, ha, hva⟩
    refine ⟨(x : K) * a, ?_, hva⟩
    rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul]
    exact ⟨a, ha, rfl⟩

open scoped Classical in
/-- Multiplication by `x ∈ Kˣ` as a bijection from the lattice of `I` to that of `x·I`.-/
noncomputable def smulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Kˣ) :
    idealZLattice K I ≃ idealZLattice K (toPrincipalIdeal (𝓞 K) K x * I) where
  toFun v := ⟨mulCoords K (x : K) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    rw [mem_idealZLattice_principal_mul]
    exact ⟨a, ha, by rw [← hva, mulCoords_embeddingCoords]⟩⟩
  invFun v := ⟨mulCoords K ((x⁻¹ : Kˣ) : K) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice_principal_mul K I x _).mp v.2
    rw [mem_idealZLattice]
    refine ⟨a, ha, ?_⟩
    rw [← hva, mulCoords_embeddingCoords, ← mul_assoc]
    norm_cast
    rw [inv_mul_cancel x]
    simp⟩
  left_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc]
    norm_cast
    rw [inv_mul_cancel x]
    simp
  right_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice_principal_mul K I x _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc,
      ← mul_assoc]
    norm_cast
    rw [mul_inv_cancel x]
    simp

open scoped Classical in
/-- **Principal rescaling of the Hecke theta**: the theta of `x·I` is the theta of `I`
with the place weights scaled by `(w x)²`.
@isnad1 id=eq.0h4v.s10.e1aa9b4dc73c from=translated src=- shape=bda41fd8 vocab=7427322e
-/
theorem heckeTheta_principal_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Kˣ)
    (c : InfinitePlace K → ℝ) :
    heckeTheta K (toPrincipalIdeal (𝓞 K) K x * I) c
      = heckeTheta K I (fun w => (w (x : K)) ^ 2 * c w) := by
  rw [heckeTheta, heckeTheta]
  conv_lhs => rw [← Equiv.tsum_eq (smulLatticeEquiv K I x)]
  refine tsum_congr (fun v => ?_)
  obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
  congr 1
  have hcoe : ((smulLatticeEquiv K I x v : idealZLattice K
        (toPrincipalIdeal (𝓞 K) K x * I)) : EuclideanSpace ℝ (index K))
      = embeddingCoords K ((x : K) * a) := by
    show mulCoords K _ (v : EuclideanSpace ℝ (index K)) = _
    rw [← hva, mulCoords_embeddingCoords]
  rw [hcoe, ← hva, sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq]
  refine congrArg (fun r => -π * r) ?_
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, mul_pow]
  ring

open scoped Classical in
/-- **Principal rescaling of the unit-averaged theta**: `g_{x·I}(t) = g_I(|N(x)|²·t)`.
This is what makes the normalised class theta `Ĝ_C` well-defined on ideal classes.
@isnad1 id=eq.1h4v.s11.fa92ce73297e from=translated src=- shape=19b10399 vocab=d220e595
-/
theorem heckeG_principal_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Kˣ) {t : ℝ}
    (ht : 0 ≤ t) :
    heckeG K (toPrincipalIdeal (𝓞 K) K x * I) t
      = heckeG K I (((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) ^ 2 * t) := by
  rw [heckeG, heckeG]
  congr 1
  have hpt : ∀ u : logSpace K,
      heckeTheta K (toPrincipalIdeal (𝓞 K) K x * I) (heckeWeights K t u)
        = heckeTheta K I (heckeWeights K (((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) ^ 2 * t)
            (u + xShift K (x : K))) := by
    intro u
    rw [heckeTheta_principal_mul]
    congr 1
    funext w
    exact sq_mul_heckeWeights K (Units.ne_zero x) ht u w
  simp only [hpt]
  refine setIntegral_fundamentalDomain_comp_add
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) (xShift K (x : K))
    (fun u => heckeTheta K I
      (heckeWeights K (((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) ^ 2 * t) u))
    (fun l v => ?_)
  have hl : (l : logSpace K) ∈ unitLattice K :=
    (le_of_eq ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ)) l.2
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hl
  rw [add_comm, ← ha]
  exact heckeTheta_heckeWeights_periodic K I _ v (Additive.toMul a)

end

end DedekindResidue
