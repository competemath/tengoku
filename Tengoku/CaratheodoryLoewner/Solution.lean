import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

-- Lean 4.33 makes several bundled additive and tangent-space instances non-reducible.  The
-- compatibility mode keeps the pre-4.33 definitional equalities used throughout this development.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Proofs of the smooth Loewner and Carathéodory counterexamples

-/

scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped EuclideanGeometry
open Matrix

noncomputable instance Module.orientedEuclideanSpaceFinThree : Module.Oriented ℝ ℝ³ (Fin 3) :=
  ⟨Basis.orientation <| PiLp.basisFun ..⟩

namespace EuclideanHypersurface

noncomputable def euclideanCross : ℝ³ →L[ℝ] ℝ³ →L[ℝ] ℝ³ :=
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  let f :=
    ((crossProduct.comp e.toLinearMap).compl₂ e.toLinearMap).compr₂ e.symm.toLinearMap
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp f)

open Set Metric
open scoped ContDiff EuclideanSpace Manifold RealInnerProductSpace

variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def firstFundamentalFormAt (dF : V →L[ℝ] E) : LinearMap.BilinForm ℝ V :=
  LinearMap.BilinForm.comp (innerₗ E) dF.toLinearMap dF.toLinearMap

noncomputable def secondFundamentalFormAt (dn dF : V →L[ℝ] E) :
    LinearMap.BilinForm ℝ V :=
  -(LinearMap.BilinForm.comp (innerₗ E) dn.toLinearMap dF.toLinearMap)

def IsUmbilic (V E : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (dF dn : V →L[ℝ] E) : Prop :=
  ∃ κ : ℝ, secondFundamentalFormAt dn dF = κ • firstFundamentalFormAt dF

noncomputable def sphereTangentBasis (p : sphere (0 : ℝ³) 1) :
    Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) p) :=
  (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) p).basisAt
    (PiLp.basisFun 2 ℝ (Fin 2)) (FiberBundle.mem_baseSet_trivializationAt' p)

noncomputable def sphereNormalRaw
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) : ℝ³ :=
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ := mvfderiv (𝓡 2) F p
  inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) •
    euclideanCross (dF (b 0)) (dF (b 1))

noncomputable def sphereNormal
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) : ℝ³ :=
  NormedSpace.normalize (sphereNormalRaw F p)

end EuclideanHypersurface

open Set Metric
open scoped ContDiff EuclideanSpace Manifold RealInnerProductSpace

namespace LoewnerConjecture

/-- The trace-free Hessian of `f : ℂ → ℝ`, encoded so its argument is twice the principal-line
angle. Its zeros are exactly the points where the Hessian has a repeated eigenvalue.-/
noncomputable def traceFreeHessian (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  let H := iteratedFDeriv ℝ 2 f z
  H ![1, 1] - H ![Complex.I, Complex.I] + 2 * H ![1, Complex.I] * Complex.I

/-- A complex-valued function `q` has an isolated zero at `z` with winding number `m`.

Continuity on the witness ball makes the winding number independent of the sufficiently small
circle; `θ` is an argument lift on one such circle. For a trace-free Hessian, the principal-line
index is `m / 2`.-/
def HasIsolatedZeroIndex (q : ℂ → ℂ) (z : ℂ) (m : ℤ) : Prop :=
  ∃ ε > 0,
    ContinuousOn q (ball z ε) ∧ q z = 0 ∧
      (∀ w, w ≠ z → dist w z < ε → q w ≠ 0) ∧
      ∃ r, 0 < r ∧ r < ε ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
          NormedSpace.normalize (q (z + r * Complex.exp ((t : ℂ) * Complex.I)))) ∧
        θ (2 * Real.pi) - θ 0 = 2 * Real.pi * m

/-- Loewner's conjecture for functions of class `C^k` near an isolated umbilic. The integer `m`
is twice the principal-line index, so the bound `m ≤ 2` says that this index is at most one.-/
def LoewnerConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ (f : ℂ → ℝ) (z : ℂ) (m : ℤ), ContDiffAt ℝ k f z →
    HasIsolatedZeroIndex (traceFreeHessian f) z m → m ≤ 2

end LoewnerConjecture

namespace CaratheodoryConjecture

def IsConvexSphereOfClass (k : WithTop ℕ∞) (F : sphere (0 : ℝ³) 1 → ℝ³) : Prop :=
  ContMDiff (𝓡 2) (𝓡 3) (k + 1) F ∧
    Topology.IsEmbedding F ∧
    (∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) ∧
    ∃ K : ConvexBody ℝ³,
      (interior (K : Set ℝ³)).Nonempty ∧ range F = frontier (K : Set ℝ³)

def CaratheodoryConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ F : sphere (0 : ℝ³) 1 → ℝ³, IsConvexSphereOfClass k F →
    ∃ p₁ p₂, p₁ ≠ p₂ ∧
      EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p₁) ℝ³
        (mvfderiv (𝓡 2) F p₁)
        (mvfderiv (𝓡 2) (EuclideanHypersurface.sphereNormal F) p₁) ∧
      EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p₂) ℝ³
        (mvfderiv (𝓡 2) F p₂)
        (mvfderiv (𝓡 2) (EuclideanHypersurface.sphereNormal F) p₂)

end CaratheodoryConjecture

/-! ## Flattened from `FormalConjecturesForMathlib/Analysis/SpecialFunctions/FlatRpowExp.lean` -/

section FlatRpowExpSection

noncomputable section

open Filter Function Topology

namespace ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A smooth function on the punctured space whose every iterated derivative is little-oh of the
distance to the origin extends smoothly across the origin, with zero Taylor series there.
@isnad1 id=contdiff.3h4v.s8.10fbb090f020 from=translated src=- shape=1d5affa5 vocab=55885844
-/
theorem at_zero_of_iteratedFDeriv_isLittleO {f : E → F}
    (hf : ∀ x ≠ 0, ContDiffAt 𝕜 ∞ f x) (hzero : f 0 = 0)
    (hflat : ∀ m : ℕ, (iteratedFDeriv 𝕜 m f) =o[𝓝[≠] 0] (id : E → E)) :
    ContDiffAt 𝕜 ∞ f 0 := by
  classical
  let p : E → FormalMultilinearSeries 𝕜 E F := fun x m ↦
    if x = 0 then 0 else iteratedFDeriv 𝕜 m f x
  have hp_flat (m : ℕ) : (fun x ↦ p x m) =o[𝓝 0] (id : E → E) := by
    have heq : iteratedFDeriv 𝕜 m f =ᶠ[𝓝[≠] 0] fun x ↦ p x m := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      simp [p, hx]
    rw [← nhdsNE_sup_pure (0 : E)]
    refine ((hflat m).congr' heq EventuallyEq.rfl).sup <|
      Asymptotics.isLittleO_iff.2 fun c hc ↦ ?_
    rw [eventually_pure]
    simp [p]
  have hp_deriv (m : ℕ) (x : E) :
      HasFDerivAt (p · m) (p x m.succ).curryLeft x := by
    by_cases hx : x = 0
    · subst x
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      have hfun : (fun h : E ↦ p h m - p 0 m - (p 0 m.succ).curryLeft h) =
          fun h ↦ p h m := by
        funext h
        have hp0 (i : ℕ) : p 0 i = 0 := by simp [p]
        rw [hp0 m, hp0 m.succ]
        have hz : (0 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + 1) ↦ E) F).curryLeft h =
            0 := by
          ext v
          rfl
        rw [hz, sub_zero, sub_zero]
      simp only [zero_add]
      rw [hfun]
      exact hp_flat m
    · have heq (i : ℕ) : (fun y ↦ p y i) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 i f := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        simp [p, hy]
      have hd := ((hf x hx).differentiableAt_iteratedFDeriv (m := m)
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).hasFDerivAt
      rw [fderiv_iteratedFDeriv, Function.comp_apply] at hd
      refine (hd.congr_of_eventuallyEq (heq m)).congr_fderiv ?_
      simp only [p, hx, ite_false, Nat.succ_eq_add_one]
      rfl
  have hp : HasFTaylorSeriesUpToOn ∞ f p Set.univ := by
    rw [hasFTaylorSeriesUpToOn_top_iff' le_rfl]
    constructor
    · intro x _
      by_cases hx : x = 0
      · subst x
        simp [p, hzero]
      · simp [p, hx]
    · intro m x _
      simpa only [hasFDerivWithinAt_univ] using hp_deriv m x
  exact hp.contDiffOn.contDiffAt univ_mem

/-- A smooth function with zero Taylor series at the origin is little-oh of every power of the
distance to the origin.
@isnad1 id=islittle.2h5v.s9.6796777aeb39 from=translated src=- shape=0cf6651e vocab=c8bbe7f3
-/
theorem isLittleO_norm_pow_of_iteratedFDeriv_zero [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (m n : ℕ) :
    iteratedFDeriv ℝ m f =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
  induction n generalizing m with
  | zero =>
      rw [show (fun x : E ↦ ‖x‖ ^ 0) = fun _ ↦ (1 : ℝ) by simp]
      rw [Asymptotics.isLittleO_one_iff]
      rw [← hzero m]
      exact hf.continuous_iteratedFDeriv (m := m)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.continuousAt
  | succ n ih =>
      have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m f) :=
        hf.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)
      have hderiv : fderiv ℝ (iteratedFDeriv ℝ m f) =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
        rw [Asymptotics.isLittleO_iff] at ⊢
        intro c hc
        filter_upwards [(ih (m + 1)).bound hc] with x hx
        rw [norm_fderiv_iteratedFDeriv]
        exact hx
      have h := (convex_univ : Convex ℝ (Set.univ : Set E)).isLittleO_pow_succ
        (Set.mem_univ 0) (fun x _ ↦ hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (by simpa using hderiv)
      simpa [hzero m] using h

/-- Composing on the right preserves a zero Taylor series at the origin, provided the inner
function fixes the origin.
@isnad1 id=eq.4h6v.s9.5e15f06b7cda from=translated src=- shape=a8574a7c vocab=1f87f6f3
-/
theorem iteratedFDeriv_comp_zero_of_outer [NormedSpace ℝ E] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {f : E → F}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m g 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (g ∘ f) 0 = 0 := by
  let D := 1 + ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i f 0‖
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_comp_le hg hf (mod_cast le_top) 0
      (C := 0) (D := D) ?_ ?_).trans ?_
    · intro i hi
      rw [hf0, hzero i]
      simp only [norm_zero]
      exact le_rfl
    · intro i hi hin
      have hD_one : 1 ≤ D := by
        simp only [D, le_add_iff_nonneg_right]
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      calc
        ‖iteratedFDeriv ℝ i f 0‖ ≤ D := by
          simp only [D]
          exact le_add_of_nonneg_of_le zero_le_one <|
            Finset.single_le_sum (f := fun j ↦ ‖iteratedFDeriv ℝ j f 0‖)
              (fun j _ ↦ norm_nonneg _)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
        _ ≤ D ^ i := le_self_pow₀ hD_one (Nat.ne_of_gt hi)
    · simp
  · exact norm_nonneg _

/-- Multiplying a smooth scalar-valued function with zero Taylor series by another smooth
function preserves its zero Taylor series.
@isnad1 id=eq.3h4v.s9.b43fcd5ca408 from=translated src=- shape=1e6e7184 vocab=43ce6882
-/
theorem iteratedFDeriv_mul_zero_of_left [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ f x * g x) 0 = 0 := by
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_mul_le hf hg 0 (mod_cast le_top) (n := n)).trans ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    simp
  · exact norm_nonneg _

end ContDiff

namespace Real

/-- The extension by zero of `x ↦ exp (-c * x ^ (-a))` from the positive half-line.-/
def flatRpowExp (a c x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-c * x ^ (-a))

namespace flatRpowExp

/--
@isnad1 id=eq.1h3v.s4.dc6c1cbe4633 from=translated src=- shape=84fcc214 vocab=0bc2bacf
-/
theorem zero_of_nonpos (a c : ℝ) {x : ℝ} (hx : x ≤ 0) : flatRpowExp a c x = 0 := by
  simp [flatRpowExp, hx]

/--
@isnad1 id=eq.0h2v.s4.e8d23cdb8737 from=translated src=- shape=9bf57cd7 vocab=3d9cbecd
-/
@[simp]
theorem zero (a c : ℝ) : flatRpowExp a c 0 = 0 := zero_of_nonpos a c le_rfl

/--
@isnad1 id=eq.1h3v.s5.e5c086776dad from=translated src=- shape=d765327e vocab=e2bdbe43
-/
theorem of_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) :
    flatRpowExp a c x = exp (-c * x ^ (-a)) := by
  simp [flatRpowExp, hx.not_ge]

/-- Exponential decay at zero dominates every real power.
@isnad1 id=tendsto.2h3v.s6.3ca86a7651d4 from=translated src=- shape=49c633e5 vocab=13ecd6d6
-/
theorem tendsto_rpow_mul_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ s * flatRpowExp a c x) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ ↦ x ^ (-a)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos ha)
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-s / a) c hc).comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (x ^ (-a)) ^ (-s / a) * exp (-c * x ^ (-a)) =
    x ^ s * flatRpowExp a c x
  rw [of_pos a c hx, ← Real.rpow_mul hx.le]
  congr 2
  field_simp [ha.ne']

/-- A single generalized Laurent monomial times `flatRpowExp`.-/
private def term (a c ν d x : ℝ) : ℝ := d * x ^ ν * flatRpowExp a c x

private theorem term_tendsto_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d : ℝ) :
    Tendsto (term a c ν d) (𝓝 0) (𝓝 0) := by
  have hinner : Tendsto (fun x : ℝ ↦ x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0) := by
    simp only [flatRpowExp, mul_ite, mul_zero]
    refine tendsto_const_nhds.if ?_
    simp only [not_le]
    refine (tendsto_rpow_mul_zero ha hc ν).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [of_pos a c hx]
  change Tendsto (fun x : ℝ ↦ d * x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0)
  simpa only [mul_assoc, mul_zero] using
    (tendsto_const_nhds.mul hinner :
      Tendsto (fun x : ℝ ↦ d * (x ^ ν * flatRpowExp a c x)) (𝓝 0) (𝓝 (d * 0)))

private theorem term_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d x : ℝ) :
    HasDerivAt (term a c ν d)
      (term a c (ν - 1) (d * ν) x + term a c (ν - a - 1) (d * c * a) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : term a c ν d =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [term, zero_of_nonpos a c hy.le]
    simpa [term, zero_of_nonpos a c hx.le] using
      (hasDerivAt_const x 0).congr_of_eventuallyEq heq
  · simp only [term, zero a c, mul_zero, add_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((term_tendsto_zero ha hc (ν - 1) d).mono_left inf_le_left).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    by_cases hypos : 0 < y
    · simp [slope_def_field, term, zero a c, of_pos a c hypos, div_eq_mul_inv]
      rw [Real.rpow_sub_one hypos.ne']
      ring
    · have hynonpos : y ≤ 0 := le_of_not_gt hypos
      simp [slope_def_field, term, zero a c, zero_of_nonpos a c hynonpos]
  · have hpow : HasDerivAt (fun y : ℝ ↦ y ^ ν) (ν * x ^ (ν - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hpow' : HasDerivAt (fun y : ℝ ↦ y ^ (-a))
        ((-a) * x ^ (-a - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hinner : HasDerivAt (fun y : ℝ ↦ -c * y ^ (-a))
        (c * a * x ^ (-a - 1)) x := by
      have h := hpow'.const_mul (-c)
      have hcoef : (-c) * ((-a) * x ^ (-a - 1)) = c * a * x ^ (-a - 1) := by ring
      rw [hcoef] at h
      exact h
    have hexp : HasDerivAt (fun y : ℝ ↦ exp (-c * y ^ (-a)))
        (exp (-c * x ^ (-a)) * (c * a * x ^ (-a - 1))) x := hinner.exp
    have heq : term a c ν d =ᶠ[𝓝 x]
        fun y ↦ (d * y ^ ν) * exp (-c * y ^ (-a)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [term, of_pos a c hy]
    have hderiv := ((hpow.const_mul d).mul hexp).congr_of_eventuallyEq heq
    have hrpow : x ^ (ν - a - 1) = x ^ ν * x ^ (-a - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hcoef :
        term a c (ν - 1) (d * ν) x + term a c (ν - a - 1) (d * c * a) x =
          d * (ν * x ^ (ν - 1)) * exp (-c * x ^ (-a)) +
            d * x ^ ν * (exp (-c * x ^ (-a)) * (c * a * x ^ (-a - 1))) := by
      simp only [term, of_pos a c hx]
      rw [hrpow]
      ring
    rw [hcoef]
    exact hderiv

/-- A finite sum of generalized Laurent monomials times `flatRpowExp`.-/
private def sum (a c : ℝ) (p : Multiset (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (p.map fun q ↦ term a c q.1 q.2 x).sum

private theorem sum_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) : ∃ q : Multiset (ℝ × ℝ),
      ∀ x, HasDerivAt (sum a c p) (sum a c q x) x := by
  induction p using Multiset.induction_on with
  | empty =>
      refine ⟨0, fun x ↦ ?_⟩
      change HasDerivAt (fun _ : ℝ ↦ 0) 0 x
      exact hasDerivAt_const x 0
  | @cons head tail ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨(head.1 - 1, head.2 * head.1) ::ₘ
        (head.1 - a - 1, head.2 * c * a) ::ₘ q, fun x ↦ ?_⟩
      have h := (term_hasDerivAt ha hc head.1 head.2 x).add (hq x)
      rw [show sum a c (head ::ₘ tail) = term a c head.1 head.2 + sum a c tail by
        funext y
        simp [sum]]
      simpa [sum, add_assoc] using h

private theorem sum_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) {n : ℕ∞} : ContDiff ℝ n (sum a c p) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
      exact contDiff_zero.2 <| continuous_iff_continuousAt.2 fun x ↦
        ((sum_hasDerivAt ha hc p).choose_spec x).continuousAt
  | succ m ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.2 ⟨fun x ↦ (hq x).differentiableAt, by simp, ?_⟩
      have hderiv : deriv (sum a c p) = sum a c q := funext fun x ↦ (hq x).deriv
      rw [hderiv]
      exact ih q

private theorem sum_iteratedDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) (n : ℕ) : iteratedDeriv n (sum a c p) 0 = 0 := by
  induction n generalizing p with
  | zero => simp [sum, term]
  | succ n ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [iteratedDeriv_succ']
      have hderiv : deriv (sum a c p) = sum a c q := funext fun x ↦ (hq x).deriv
      rw [hderiv]
      exact ih q

/-- Multiplying `flatRpowExp a c` by an arbitrary real power preserves smoothness.
@isnad1 id=contdiff.2h4v.s6.c3cf946a14cc from=translated src=- shape=c90532f2 vocab=7539a38d
-/
@[fun_prop]
theorem rpow_mul_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) := by
  convert sum_contDiff (n := n) ha hc ({(s, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]

/-- Every iterated derivative of `x ^ s * flatRpowExp a c x` vanishes at the origin.
@isnad1 id=eq.2h4v.s8.ac2443d15d1b from=translated src=- shape=cc90e0b6 vocab=42a1d1f9
-/
theorem rpow_mul_iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ)
    (n : ℕ) : iteratedFDeriv ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) 0 = 0 := by
  have hfun : (fun x ↦ x ^ s * flatRpowExp a c x) =
      sum a c ({(s, 1)} : Multiset (ℝ × ℝ)) := by
    funext x
    simp [sum, term]
  rw [hfun, ← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    sum_iteratedDeriv_zero ha hc]
  simp

/-- Every iterated derivative of `flatRpowExp a c` vanishes at the origin.
@isnad1 id=eq.2h3v.s8.7b80f5f6d9e4 from=translated src=- shape=c19b8472 vocab=129c4c9e
-/
theorem iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    iteratedFDeriv ℝ n (flatRpowExp a c) 0 = 0 := by
  simpa using rpow_mul_iteratedFDeriv_zero ha hc 0 n

/-- `flatRpowExp a c` is smooth when both parameters are positive.
@isnad1 id=contdiff.2h3v.s5.5f137266acd4 from=translated src=- shape=b4b3c75f vocab=c09f58ab
-/
@[fun_prop]
theorem contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ∞} :
    ContDiff ℝ n (flatRpowExp a c) := by
  convert sum_contDiff (n := n) ha hc ({(0, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]

end flatRpowExp

end Real

end

end FlatRpowExpSection

/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/3d.lean` -/

section GeometryThreeSection

/-!
# Three-dimensional Euclidean geometry

This file defines the preferred orientation and bundled continuous cross product on `ℝ³`.
-/

open scoped EuclideanGeometry
open Matrix

namespace EuclideanHypersurface

/-- The bundled Euclidean cross product agrees with the coordinate cross product.
@isnad1 id=eq.0h2v.s12.c83e4602d9b0 from=translated src=- shape=72464970 vocab=5e3c532d
-/
theorem euclideanCross_apply (a b : ℝ³) :
    euclideanCross a b =
      WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) :=
  rfl

/-- Swapping the arguments of the cross product negates it.
@isnad1 id=eq.0h2v.s13.b471c6adb107 from=translated src=- shape=de7c690f vocab=3a950fd4
-/
@[simp]
theorem euclideanCross_anticomm (a b : ℝ³) :
    -euclideanCross a b = euclideanCross b a := by
  rw [euclideanCross_apply, euclideanCross_apply]
  change WithLp.toLp 2 (-crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) = _
  exact congrArg (WithLp.toLp 2) (cross_anticomm (WithLp.ofLp a) (WithLp.ofLp b))

/-- A vector has zero cross product with itself.
@isnad1 id=eq.0h1v.s12.e40be2b2b434 from=translated src=- shape=b41eaf4a vocab=d455bbea
-/
@[simp]
theorem euclideanCross_self (a : ℝ³) : euclideanCross a a = 0 := by
  simp [euclideanCross_apply]

/-- The cross product is orthogonal to its left input.
@isnad1 id=eq.0h2v.s12.6d4ee51472b2 from=translated src=- shape=f137e54e vocab=bcb74676
-/
@[simp]
theorem euclideanCross_inner_left (a b : ℝ³) : inner ℝ (euclideanCross a b) a = 0 := by
  simp [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dot_self_cross]

/-- The cross product is orthogonal to its right input.
@isnad1 id=eq.0h2v.s12.4d5baaf9902e from=translated src=- shape=e04a6401 vocab=bcb74676
-/
@[simp]
theorem euclideanCross_inner_right (a b : ℝ³) : inner ℝ (euclideanCross a b) b = 0 := by
  simp [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dot_cross_self]

/-- The inner product of two cross products is the corresponding Gram-determinant expression.
@isnad1 id=eq.0h4v.s13.c11b457dc810 from=translated src=- shape=105d4d76 vocab=f07fc8cc
-/
theorem inner_euclideanCross_euclideanCross (a b c d : ℝ³) :
    inner ℝ (euclideanCross a b) (euclideanCross c d) =
      inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp only [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    cross_dot_cross]
  rw [mul_comm (WithLp.ofLp c ⬝ᵥ WithLp.ofLp b)]

/-- The right-nested vector triple-product identity.
@isnad1 id=eq.0h3v.s13.a17d630b3247 from=translated src=- shape=8bab245b vocab=6c96e2e5
-/
theorem euclideanCross_cross (u v w : ℝ³) :
    euclideanCross u (euclideanCross v w) =
      inner ℝ u w • v - inner ℝ u v • w := by
  change WithLp.toLp 2
    (crossProduct (WithLp.ofLp u) (crossProduct (WithLp.ofLp v) (WithLp.ofLp w))) = _
  rw [cross_cross_eq_smul_sub_smul']
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (WithLp.ofLp w) (WithLp.ofLp u),
    dotProduct_comm (WithLp.ofLp v) (WithLp.ofLp u)]
  rfl

/-- A cross product is nonzero exactly when its two inputs are linearly independent.
@isnad1 id=iff.0h2v.s12.3aaaa905fa55 from=translated src=- shape=6f4d3a1c vocab=cfe1fe9c
-/
theorem euclideanCross_ne_zero_iff_linearIndependent (a b : ℝ³) :
    euclideanCross a b ≠ 0 ↔ LinearIndependent ℝ ![a, b] := by
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hne : euclideanCross a b ≠ 0 ↔ crossProduct (e a) (e b) ≠ 0 := by
    rw [euclideanCross]
    exact e.symm.injective.ne_iff
  rw [hne, crossProduct_ne_zero_iff_linearIndependent]
  have hf : e.toLinearMap ∘ ![a, b] = ![e a, e b] := by
    funext i
    fin_cases i <;> simp
  exact hf ▸ e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn

/-- The cross product of two vectors orthogonal to a unit vector is parallel to that vector.
@isnad1 id=eq.3h3v.s13.a59bdb068f7a from=translated src=- shape=fd252fac vocab=7f46aade
-/
theorem euclideanCross_eq_inner_smul_of_orthogonal
    (p x y : ℝ³) (hp : ‖p‖ = 1) (hx : inner ℝ p x = 0) (hy : inner ℝ p y = 0) :
    euclideanCross x y = inner ℝ (euclideanCross x y) p • p := by
  let c := euclideanCross x y
  have hpc : euclideanCross p c = 0 := by
    dsimp only [c]
    simp [euclideanCross_cross, hy, hx]
  have hsecond := euclideanCross_cross p p c
  rw [hpc, map_zero, show inner ℝ p p = 1 by simp [hp], one_smul] at hsecond
  simpa [c, real_inner_comm] using (sub_eq_zero.mp hsecond.symm).symm

end EuclideanHypersurface

end GeometryThreeSection

/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/EuclideanHypersurface.lean` -/

section EuclideanHypersurfaceSection

/-!
# Extrinsic fundamental forms in Euclidean space

The second fundamental form uses `II(v, w) = -⟪dn(v), dF(w)⟫`, so `dn = c • dF` corresponds
to `II = (-c) • I`.
-/

open scoped RealInnerProductSpace

namespace EuclideanHypersurface

variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
@isnad1 id=eq.0h5v.s9.1772ba531625 from=translated src=- shape=c817dc6b vocab=7c0e8083
-/
@[simp]
theorem firstFundamentalFormAt_apply (dF : V →L[ℝ] E) (v w : V) :
    firstFundamentalFormAt dF v w = inner ℝ (dF v) (dF w) :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.df0668f10bbf from=translated src=- shape=f5b74a4a vocab=25f4e698
-/
@[simp]
theorem secondFundamentalFormAt_apply (dn dF : V →L[ℝ] E) (v w : V) :
    secondFundamentalFormAt dn dF v w = -inner ℝ (dn v) (dF w) :=
  rfl

/-- If `dn = c • dF`, the point is umbilic with scalar `-c` under our sign convention.
@isnad1 id=isumbili.1h5v.s8.ab708c7fab91 from=translated src=- shape=37a12761 vocab=745c0fba
-/
theorem isUmbilic_of_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (c : ℝ) (h : dn = c • dF) :
    IsUmbilic V E dF dn := by
  refine ⟨-c, ?_⟩
  ext v w
  change -inner ℝ (dn v) (dF w) = -c * inner ℝ (dF v) (dF w)
  rw [h, _root_.smul_apply, real_inner_smul_left, neg_mul]

/-- If `dn` is tangent to the immersion, umbilicity is equivalent to `dn` being a scalar multiple
of `dF`.
@isnad1 id=iff.1h4v.s9.7acc4202ba6c from=translated src=- shape=746bfb81 vocab=6eb990c9
-/
theorem isUmbilic_iff_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (htangent : dn.range ≤ dF.range) :
    IsUmbilic V E dF dn ↔ ∃ c : ℝ, dn = c • dF := by
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨-κ, ?_⟩
    ext v
    obtain ⟨u, hu⟩ := htangent ⟨v, rfl⟩
    have horth (w : V) : inner ℝ (dn v + κ • dF v) (dF w) = 0 := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ V ↦ B v w) hκ
      change -inner ℝ (dn v) (dF w) = κ * inner ℝ (dF v) (dF w) at h
      rw [inner_add_left, real_inner_smul_left, ← h, add_neg_cancel]
    have hrange : dn v + κ • dF v = dF (u + κ • v) := by
      change dF u = dn v at hu
      rw [map_add, map_smul, ← hu]
    have hzero := horth (u + κ • v)
    rw [← hrange, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hzero
    simpa [_root_.smul_apply] using
      eq_neg_of_add_eq_zero_left hzero
  · exact fun ⟨c, hc⟩ ↦ isUmbilic_of_normal_deriv_eq_smul dF dn c hc

end EuclideanHypersurface

end EuclideanHypersurfaceSection

/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SphereImmersion.lean` -/

section SphereImmersionSection

/-!
# A canonical normal for immersed two-spheres in three-space

Mathlib models each sphere tangent space on a fixed copy of `ℝ²`. We orient the cross product
using the standard sphere inclusion; changing the model frame then contributes a squared
determinant, which disappears after normalization.
-/

open Metric
open scoped EuclideanGeometry EuclideanSpace Manifold RealInnerProductSpace

namespace EuclideanHypersurface

/-- The basis induced by the tangent-bundle trivialization at its base point agrees with the
standard model basis.
@isnad1 id=eq.0h2v.s13.973c51a13d1c from=translated src=- shape=66c413dd vocab=f16d0ead
-/
theorem sphereTangentBasis_apply (p : sphere (0 : ℝ³) 1) (i : Fin 2) :
    sphereTangentBasis p i = PiLp.basisFun 2 ℝ (Fin 2) i := by
  simp only [sphereTangentBasis, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply]
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) p)
    (FiberBundle.mem_baseSet_trivializationAt' p)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source _ p)]
  simpa using! (tangentBundleCore (𝓡 2) _).coordChange_self
    (achart _ p) p (mem_chart_source _ p) (PiLp.basisFun 2 ℝ (Fin 2) i)

private theorem mfderiv_inclusion_sphereTangentBasis_apply
    (p : sphere (0 : ℝ³) 1) (i : Fin 2) :
    (mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p :
      TangentSpace (𝓡 2) p →L[ℝ] ℝ³)
        (sphereTangentBasis p i) =
      let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-p))).repr
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) :
        (ℝ ∙ (↑(-p) : ℝ³))ᗮ) : ℝ³) := by
  rw [((contMDiff_coe_sphere p).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  rw [sphereTangentBasis_apply]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-p))).repr
  change
    (fderiv ℝ ((stereoInvFunAux (-p : ℝ³) ∘
      (Subtype.val : (ℝ ∙ (↑(-p) : ℝ³))ᗮ → ℝ³)) ∘ U.symm)
        (stereographic' 2 (-p) p)) (PiLp.basisFun 2 ℝ (Fin 2) i) =
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) : (ℝ ∙ (↑(-p) : ℝ³))ᗮ) : ℝ³)
  have hp0 : stereographic' 2 (-p) p = 0 := by
    change U (stereographic (norm_eq_of_mem_sphere (-p)) p) = 0
    rw [stereographic_neg_apply, map_zero]
  rw [hp0]
  have h :
      HasFDerivAt (stereoInvFunAux (-p : ℝ³) ∘
        (Subtype.val : (ℝ ∙ (↑(-p) : ℝ³))ᗮ → ℝ³))
        (ℝ ∙ (↑(-p) : ℝ³))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-p : ℝ³)
    simp
  rw [(h.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv]
  rfl

/-- The standard model basis maps to an orthonormal frame under the derivative of the sphere
inclusion.
@isnad1 id=eq.0h3v.s15.67a66b3bd7e5 from=translated src=- shape=bba0865d vocab=8311745d
-/
@[simp]
theorem inner_mfderiv_inclusion_sphereTangentBasis
    (p : sphere (0 : ℝ³) 1) (i j : Fin 2) :
    inner ℝ
      (show ℝ³ from mvfderiv (𝓡 2)
        (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p (sphereTangentBasis p i))
      (show ℝ³ from mvfderiv (𝓡 2)
        (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p (sphereTangentBasis p j)) =
      if i = j then 1 else 0 := by
  rw [mfderiv_inclusion_sphereTangentBasis_apply p i,
    mfderiv_inclusion_sphereTangentBasis_apply p j]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-p))).repr
  change inner ℝ
    ((ℝ ∙ ((-p : sphere (0 : ℝ³) 1) : ℝ³))ᗮ.subtypeₗᵢ
      (U.symm (PiLp.basisFun 2 ℝ (Fin 2) i)))
    ((ℝ ∙ ((-p : sphere (0 : ℝ³) 1) : ℝ³))ᗮ.subtypeₗᵢ
      (U.symm (PiLp.basisFun 2 ℝ (Fin 2) j))) = _
  rw [LinearIsometry.inner_map_map, U.symm.inner_map_map]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal i j

/-- The derivative of the sphere inclusion maps the standard model basis to an orthonormal
family.
@isnad1 id=orthonor.0h1v.s14.a5b6b91f4151 from=translated src=- shape=5ee2c2bd vocab=7cc9575d
-/
theorem orthonormal_mfderiv_inclusion_sphereTangentBasis (p : sphere (0 : ℝ³) 1) :
    Orthonormal ℝ fun i : Fin 2 ↦
      (show ℝ³ from mvfderiv (𝓡 2)
        (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p (sphereTangentBasis p i)) :=
  orthonormal_iff_ite.mpr (inner_mfderiv_inclusion_sphereTangentBasis p)

private theorem sphere_inclusion_cross_eq_smul (p : sphere (0 : ℝ³) 1) :
    let b := sphereTangentBasis p
    let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
      mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
    euclideanCross (dι (b 0)) (dι (b 1)) =
      inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) • (p : ℝ³) := by
  dsimp only
  refine euclideanCross_eq_inner_smul_of_orthogonal _ _ _
    (norm_eq_of_mem_sphere p) ?_ ?_
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
      range_mvfderiv_subtypeVal (n := 2) p ▸ ⟨sphereTangentBasis p 0, rfl⟩
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
      range_mvfderiv_subtypeVal (n := 2) p ▸ ⟨sphereTangentBasis p 1, rfl⟩

private theorem sphere_inclusion_orientation_factor_sq (p : sphere (0 : ℝ³) 1) :
    let b := sphereTangentBasis p
    let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
      mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
    inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) ^ 2 = 1 := by
  dsimp only
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_mfderiv_inclusion_sphereTangentBasis p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : ℝ³)
  change s ^ 2 = 1
  calc
    s ^ 2 = inner ℝ c c := by
      simp [show c = s • (p : ℝ³) from sphere_inclusion_cross_eq_smul p,
        norm_smul, norm_eq_of_mem_sphere p, pow_two]
    _ = 1 := by
      dsimp only [c]
      rw [inner_euclideanCross_euclideanCross]
      simp [hON.norm_eq_one, hON.inner_eq_zero]

/-- The raw canonical normal of the standard sphere inclusion is the radial vector.
@isnad1 id=eq.0h1v.s9.3f88b823c3cf from=translated src=- shape=648041c5 vocab=16e5b320
-/
@[simp]
theorem sphereNormalRaw_inclusion (p : sphere (0 : ℝ³) 1) :
    sphereNormalRaw (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p = (p : ℝ³) := by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : ℝ³)
  change s • c = (p : ℝ³)
  rw [show c = s • (p : ℝ³) from sphere_inclusion_cross_eq_smul p,
    smul_smul, ← pow_two,
    show s ^ 2 = 1 from sphere_inclusion_orientation_factor_sq p, one_smul]

/-- The raw canonical normal is orthogonal to every image tangent vector.
@isnad1 id=eq.0h3v.s13.731d331aa165 from=translated src=- shape=098c76d0 vocab=ae4bc1ff
-/
@[simp]
theorem inner_sphereNormalRaw_mfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormalRaw F p)
      (show ℝ³ from mvfderiv (𝓡 2) F p v) = 0 := by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ := mvfderiv (𝓡 2) F p
  change inner ℝ
    (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) •
      euclideanCross (dF (b 0)) (dF (b 1))) (dF v) = 0
  rw [real_inner_smul_left, ← b.sum_repr v, map_sum]
  simp [Fin.sum_univ_two, map_smul, inner_add_right, real_inner_smul_right]

/-- The canonical normal is orthogonal to every image tangent vector, even at a non-immersion.
@isnad1 id=eq.0h3v.s13.737b98e44a82 from=translated src=- shape=098c76d0 vocab=77b7e01d
-/
@[simp]
theorem inner_sphereNormal_mfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormal F p)
      (show ℝ³ from mvfderiv (𝓡 2) F p v) = 0 := by
  rw [sphereNormal, NormedSpace.normalize, real_inner_smul_left,
    inner_sphereNormalRaw_mfderiv, mul_zero]

private theorem sphereNormalRaw_ne_zero_iff
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphereNormalRaw F p ≠ 0 ↔ Function.Injective (mvfderiv (𝓡 2) F p) := by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ := mvfderiv (𝓡 2) F p
  have hfactor : inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) ≠ 0 := by
    intro h
    simpa [b, dι, h] using sphere_inclusion_orientation_factor_sq p
  rw [sphereNormalRaw, smul_ne_zero_iff, and_iff_right hfactor,
    euclideanCross_ne_zero_iff_linearIndependent]
  have hfamily : dF.toLinearMap ∘ b = ![dF (b 0), dF (b 1)] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · exact fun hLI ↦ LinearMap.injective_of_linearIndependent b.span_eq (hfamily.symm ▸ hLI)
  · exact fun hF ↦ hfamily ▸ b.linearIndependent.map' dF.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hF)

/-- The canonical normal is nonzero exactly at the points where the manifold derivative is
injective.
@isnad1 id=iff.0h2v.s13.a6d6bf486ac7 from=translated src=- shape=51b8930a vocab=590dfb93
-/
theorem sphereNormal_ne_zero_iff
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphereNormal F p ≠ 0 ↔ Function.Injective (mvfderiv (𝓡 2) F p) := by
  simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using
    sphereNormalRaw_ne_zero_iff F p

/-- At an immersion point, the canonical normal has unit length.
@isnad1 id=eq.1h2v.s13.69f3b4e0abcc from=translated src=- shape=5768d028 vocab=243e0908
-/
theorem norm_sphereNormal_of_injective
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ‖sphereNormal F p‖ = 1 := by
  simpa [sphereNormal] using
    NormedSpace.norm_normalize ((sphereNormalRaw_ne_zero_iff F p).mpr hF)

/-- Normalizing a positive multiple of the radial vector recovers the radial vector.
@isnad1 id=eq.2h3v.s9.dac43205edfa from=translated src=- shape=e92094e3 vocab=3d0aed6a
-/
theorem sphereNormal_eq_of_raw_eq_pos_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) (c : ℝ) (hc : 0 < c)
    (hraw : sphereNormalRaw F p = c • (p : ℝ³)) :
    sphereNormal F p = (p : ℝ³) := by
  rw [sphereNormal, hraw, NormedSpace.normalize_smul_of_pos hc,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]

/-- A radially tangent map whose derivative is positively coercive relative to the standard
sphere inclusion has the outward radial canonical normal.
@isnad1 id=eq.3h3v.s15.3c9c3817a20b from=translated src=- shape=6e88e144 vocab=1aa5aa4d
-/
theorem sphereNormal_eq_radial_of_coercive
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) (c : ℝ) (hc : 0 < c)
    (hnormal : ∀ v, inner ℝ (p : ℝ³)
      (show ℝ³ from mvfderiv (𝓡 2) F p v) = 0)
    (hcoercive : ∀ v,
      c * ‖(show ℝ³ from mvfderiv (𝓡 2)
        (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v)‖ ^ 2 ≤
        inner ℝ (show ℝ³ from mvfderiv (𝓡 2) F p v)
          (show ℝ³ from mvfderiv (𝓡 2)
            (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v)) :
    sphereNormal F p = (p : ℝ³) := by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ := mvfderiv (𝓡 2) F p
  let u := dι (b 0)
  let v := dι (b 1)
  let x := dF (b 0)
  let y := dF (b 1)
  let A := inner ℝ x u
  let D := inner ℝ y v
  let P := inner ℝ x v
  let Q := inner ℝ y u
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_mfderiv_inclusion_sphereTangentBasis p
  have hcoercive0 : c * ‖dι (b 0)‖ ^ 2 ≤ inner ℝ (dF (b 0)) (dι (b 0)) :=
    hcoercive (b 0)
  rw [hON.norm_eq_one 0, one_pow, mul_one] at hcoercive0
  have hApos : 0 < A := hc.trans_le <| by simpa [A, x, u] using hcoercive0
  let s := P + Q
  let t := s • b 0 - (2 * A) • b 1
  have ht : t ≠ 0 := by
    intro ht
    have htCoord := congrArg (fun z ↦ b.repr z 1) ht
    simp [t] at htCoord
    linarith
  have hdιt : dι t ≠ 0 :=
    (map_ne_zero_iff dι (injective_mvfderiv_subtypeVal_sphere p)).mpr ht
  have hquadpos : 0 < inner ℝ (dF t) (dι t) :=
    (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hdιt))).trans_le (hcoercive t)
  simp only [t, map_sub, map_smul] at hquadpos
  change 0 < inner ℝ (s • x - (2 * A) • y) (s • u - (2 * A) • v) at hquadpos
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, s, A, P, Q] at hquadpos
  have hdetAux : 0 < 4 * A * D - (P + Q) ^ 2 := by
    nlinarith
  have hdet : 0 < A * D - P * Q := by
    nlinarith [sq_nonneg (P - Q)]
  have hcrossPos : 0 < inner ℝ (euclideanCross u v) (euclideanCross x y) := by
    rw [inner_euclideanCross_euclideanCross, ← real_inner_comm u x,
      ← real_inner_comm v y, ← real_inner_comm u y,
      ← real_inner_comm v x]
    change 0 < A * D - Q * P
    simpa [mul_comm Q P] using hdet
  apply sphereNormal_eq_of_raw_eq_pos_smul F p
    (inner ℝ (euclideanCross u v) (euclideanCross x y)) hcrossPos
  change inner ℝ (euclideanCross u v) (p : ℝ³) • euclideanCross x y =
    inner ℝ (euclideanCross u v) (euclideanCross x y) • (p : ℝ³)
  rw [euclideanCross_eq_inner_smul_of_orthogonal (p : ℝ³) x y
      (norm_eq_of_mem_sphere p) (hnormal (b 0)) (hnormal (b 1)),
    real_inner_smul_right, smul_smul, mul_comm]

/-- The canonical normal of the standard sphere inclusion points radially outward.
@isnad1 id=eq.0h1v.s9.d6c6eac1d837 from=translated src=- shape=648041c5 vocab=60d8c0e9
-/
@[simp]
theorem sphereNormal_inclusion (p : sphere (0 : ℝ³) 1) :
    sphereNormal (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p = (p : ℝ³) := by
  rw [sphereNormal, sphereNormalRaw_inclusion,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]

end EuclideanHypersurface

end SphereImmersionSection

/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SphereImmersionRegularity.lean` -/

section SphereImmersionRegularitySection

/-!
# Regularity of the canonical normal of a sphere immersion

Although the sphere charts do not give a continuous global tangent frame, `sphereNormal` is
regular. In local tangent coordinates, a frame change scales its raw normal by a positive square,
which normalization removes. Thus a `C^(m + 1)` immersion has a `C^m` canonical normal.
-/

open Metric
open scoped EuclideanGeometry EuclideanSpace Manifold RealInnerProductSpace

namespace EuclideanHypersurface

private theorem euclideanCross_comp_basis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 2) ℝ V) (L : V →L[ℝ] ℝ³) (A : V →L[ℝ] V) :
    euclideanCross (L (A (b 0))) (L (A (b 1))) =
      LinearMap.det A.toLinearMap • euclideanCross (L (b 0)) (L (b 1)) := by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two,
    ← b.sum_repr (A (b 0)), ← b.sum_repr (A (b 1))]
  simp only [Fin.sum_univ_two, map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, euclideanCross_self, smul_zero, add_zero,
    LinearMap.toMatrix_apply]
  rw [← euclideanCross_anticomm (L (b 0)) (L (b 1))]
  module

private theorem contMDiffAt_normalize
    {m : WithTop ℕ∞} {f : sphere (0 : ℝ³) 1 → ℝ³} {p : sphere (0 : ℝ³) 1}
    (hf : ContMDiffAt (𝓡 2) (𝓡 3) m f p) (h0 : f p ≠ 0) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (fun q ↦ NormedSpace.normalize (f q)) p := by
  change ContMDiffAt (𝓡 2) (𝓡 3) m (fun q ↦ ‖f q‖⁻¹ • f q) p
  exact (((contDiffAt_norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).comp_contMDiffAt hf).smul hf

private theorem inTangentCoordinates_sphere_eq_comp
    (G : sphere (0 : ℝ³) 1 → ℝ³) (p q : sphere (0 : ℝ³) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    inTangentCoordinates (𝓡 2) (𝓡 3) id G
        (mfderiv (𝓡 2) (𝓡 3) G) p q =
      mfderiv (𝓡 2) (𝓡 3) G q ∘L
        (tangentCoordChange (𝓡 2) p q q :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  rw [inTangentCoordinates_eq _ _ _ (by simpa [extChartAt_source] using hq) (by simp),
    tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp]
  rfl

private theorem tangentCoordChange_injective
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    Function.Injective (tangentCoordChange (𝓡 2) p q q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  intro u v huv
  have hmem : q ∈ (extChartAt (𝓡 2) p).source ∩
      (extChartAt (𝓡 2) q).source ∩ (extChartAt (𝓡 2) p).source :=
    ⟨⟨hq, mem_extChartAt_source q⟩, hq⟩
  simpa only [tangentCoordChange_comp hmem, tangentCoordChange_self hq] using
    congrArg (tangentCoordChange (𝓡 2) q p q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) huv

private noncomputable def sphereNormalRawInCoordinates
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphere (0 : ℝ³) 1 → ℝ³ :=
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι := inTangentCoordinates (𝓡 2) (𝓡 3) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (mfderiv (𝓡 2) (𝓡 3) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) (𝓡 3) id F
    (mfderiv (𝓡 2) (𝓡 3) F) p
  fun q ↦ inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : ℝ³) •
    euclideanCross (dF q e0) (dF q e1)

private theorem contMDiffAt_sphereNormalRawInCoordinates
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) (𝓡 3) n F p) (hmn : m + 1 ≤ n) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormalRawInCoordinates F p) p := by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι := inTangentCoordinates (𝓡 2) (𝓡 3) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (mfderiv (𝓡 2) (𝓡 3) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) (𝓡 3) id F
    (mfderiv (𝓡 2) (𝓡 3) F) p
  have hdι : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dι p :=
    (contMDiff_coe_sphere (n := 2) (m := ⊤) p).mfderiv_const le_top
  have hdF : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dF p :=
    hF.mfderiv_const hmn
  have hdι0 := hdι.clm_apply (contMDiffAt_const (c := e0))
  have hdι1 := hdι.clm_apply (contMDiffAt_const (c := e1))
  have hdF0 := hdF.clm_apply (contMDiffAt_const (c := e0))
  have hdF1 := hdF.clm_apply (contMDiffAt_const (c := e1))
  have hcι := (euclideanCross.contMDiffAt.comp p hdι0).clm_apply hdι1
  have hcF := (euclideanCross.contMDiffAt.comp p hdF0).clm_apply hdF1
  have hinner : ContDiff ℝ m (fun x : ℝ³ × ℝ³ ↦ inner ℝ x.1 x.2) := contDiff_inner
  have hraw := (hinner.comp_contMDiffAt
    (hcι.prodMk_space (contMDiff_coe_sphere p))).smul hcF
  apply hraw.congr_of_eventuallyEq
  filter_upwards with q
  simp [sphereNormalRawInCoordinates, b, e0, e1, dι, dF, Function.comp_def]

private theorem sphereNormalRawInCoordinates_eq_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p q : sphere (0 : ℝ³) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    sphereNormalRawInCoordinates F p q =
      LinearMap.det (tangentCoordChange (𝓡 2) p q q :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ^ 2 •
        sphereNormalRaw F q := by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let A := tangentCoordChange (𝓡 2) p q q
  let dι : TangentSpace (𝓡 2) q →L[ℝ] ℝ³ :=
    mvfderiv (𝓡 2) (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) q
  let dF : TangentSpace (𝓡 2) q →L[ℝ] ℝ³ := mvfderiv (𝓡 2) F q
  let dιc := inTangentCoordinates (𝓡 2) (𝓡 3) id
    (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))
    (mfderiv (𝓡 2) (𝓡 3) (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))) p q
  let dFc := inTangentCoordinates (𝓡 2) (𝓡 3) id F
    (mfderiv (𝓡 2) (𝓡 3) F) p q
  rw [sphereNormalRaw]
  rw [sphereTangentBasis_apply q 0, sphereTangentBasis_apply q 1]
  change inner ℝ (euclideanCross (dιc (b 0)) (dιc (b 1))) (q : ℝ³) •
      euclideanCross (dFc (b 0)) (dFc (b 1)) =
      LinearMap.det A.toLinearMap ^ 2 •
        (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (q : ℝ³) •
          euclideanCross (dF (b 0)) (dF (b 1)))
  rw [show dιc = dι.comp A from inTangentCoordinates_sphere_eq_comp
      (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) p q hq,
    show dFc = dF.comp A from inTangentCoordinates_sphere_eq_comp F p q hq]
  calc
    _ = inner ℝ (LinearMap.det A.toLinearMap • euclideanCross (dι (b 0)) (dι (b 1)))
          (q : ℝ³) •
        (LinearMap.det A.toLinearMap • euclideanCross (dF (b 0)) (dF (b 1))) :=
      congrArg₂ (fun (s : ℝ) (x : ℝ³) ↦ s • x)
        (congrArg (fun x ↦ inner ℝ x (q : ℝ³)) (euclideanCross_comp_basis b dι A))
        (euclideanCross_comp_basis b dF A)
    _ = _ := by
      rw [real_inner_smul_left]
      module

private theorem det_tangentCoordChange_ne_zero
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    LinearMap.det (tangentCoordChange (𝓡 2) p q q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ≠ 0 := by
  simpa [LinearMap.det_eq_zero_iff_ker_ne_bot] using
    LinearMap.ker_eq_bot_of_injective (tangentCoordChange_injective p q hq)

/-- At an immersion point, a locally `C^n` map has a locally `C^m` canonical unit normal when
`m + 1 ≤ n`.
@isnad1 id=contmdif.3h4v.s13.080afdea8f5a from=translated src=- shape=6cf90ceb vocab=cede9c12
-/
theorem contMDiffAt_sphereNormal_of_le
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) (𝓡 3) n F p) (hmn : m + 1 ≤ n)
    (himm : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormal F) p := by
  have hp : p ∈ (extChartAt (𝓡 2) p).source := mem_extChartAt_source p
  have hlocal : sphereNormalRawInCoordinates F p p ≠ 0 := by
    rw [sphereNormalRawInCoordinates_eq_smul F p p hp]
    refine smul_ne_zero (pow_ne_zero 2 (det_tangentCoordChange_ne_zero p p hp)) ?_
    simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using
      (sphereNormal_ne_zero_iff F p).2 himm
  apply (contMDiffAt_normalize
    (contMDiffAt_sphereNormalRawInCoordinates F p hF hmn) hlocal).congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 2) p] with q hq
  rw [sphereNormal, sphereNormalRawInCoordinates_eq_smul F p q hq,
    NormedSpace.normalize_smul_of_pos
      (sq_pos_of_ne_zero (det_tangentCoordChange_ne_zero p q hq))]

/-- At an immersion point, a locally `C^(m + 1)` map has a locally `C^m` canonical unit normal.
@isnad1 id=contmdif.2h3v.s13.95afe3a44caf from=translated src=- shape=b1159d09 vocab=e51eef24
-/
theorem contMDiffAt_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) (𝓡 3) (m + 1) F p)
    (himm : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormal F) p :=
  contMDiffAt_sphereNormal_of_le F p hF le_rfl himm

/-- A `C^n` immersion of the unit two-sphere has a `C^m` canonical unit normal when
`m + 1 ≤ n`.
@isnad1 id=contmdif.3h3v.s13.a8050524c971 from=translated src=- shape=bd0c7c16 vocab=76049baa
-/
theorem contMDiff_sphereNormal_of_le
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hF : ContMDiff (𝓡 2) (𝓡 3) n F) (hmn : m + 1 ≤ n)
    (himm : ∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiff (𝓡 2) (𝓡 3) m (sphereNormal F) :=
  fun p ↦ contMDiffAt_sphereNormal_of_le F p (hF p) hmn (himm p)

/-- A `C^(m + 1)` immersion of the unit two-sphere has a `C^m` canonical unit normal.
@isnad1 id=contmdif.2h2v.s13.5feda3cd67cb from=translated src=- shape=9e77da4d vocab=336bb9ba
-/
theorem contMDiff_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hF : ContMDiff (𝓡 2) (𝓡 3) (m + 1) F)
    (himm : ∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiff (𝓡 2) (𝓡 3) m (sphereNormal F) :=
  contMDiff_sphereNormal_of_le F hF le_rfl himm

end EuclideanHypersurface

namespace CaratheodoryConjecture

end CaratheodoryConjecture

end SphereImmersionRegularitySection

/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SupportFunctionSphere.lean` -/

section SupportFunctionSphereSection

open Metric Set
open scoped Gradient Topology

namespace SphereSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Classical in
/-- The degree-one radial extension of a function on the unit sphere.-/
noncomputable def radialExtension (h : sphere (0 : E) 1 → ℝ) (x : E) : ℝ :=
  if hx : x = 0 then 0
  else ‖x‖ * h ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

/-- The radial extension restricts to the original function on the unit sphere.
@isnad1 id=eq.0h3v.s7.dc6b8c524f2b from=translated src=- shape=46c02b59 vocab=72f7c674
-/
@[simp]
theorem radialExtension_coe (h : sphere (0 : E) 1 → ℝ) (p : sphere (0 : E) 1) :
    radialExtension h (p : E) = h p := by
  simp [radialExtension, ne_zero_of_mem_unit_sphere p, norm_eq_of_mem_sphere p]

/-- The radial extension is positively homogeneous of degree one.
@isnad1 id=eq.1h4v.s7.5b4193c37370 from=translated src=- shape=3e98545a vocab=4d180ffe
-/
theorem radialExtension_smul_of_pos (h : sphere (0 : E) 1 → ℝ) (x : E) {t : ℝ}
    (ht : 0 < t) : radialExtension h (t • x) = t * radialExtension h x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hunit (z : E) (hz : z ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
  have hnormalized :
      (⟨‖t • x‖⁻¹ • (t • x), by
        rw [mem_sphere, dist_zero_right]
        exact hunit (t • x) htx⟩ : sphere (0 : E) 1) =
        ⟨‖x‖⁻¹ • x, by
          rw [mem_sphere, dist_zero_right]
          exact hunit x hx⟩ := by
    apply Subtype.ext
    simp only [hnorm, smul_smul]
    congr 1
    field_simp [ht.ne']
  simp only [radialExtension, dite_eq_right htx, dite_eq_right hx]
  rw [hnormalized, hnorm]
  ring

/-- The contact map associated to a differentiable positively homogeneous function on the
ambient vector space.-/
noncomputable def homogeneousGradient [CompleteSpace E]
    (H : E → ℝ) (p : sphere (0 : E) 1) : E :=
  ∇ H (p : E)

/-- Euler's identity for a differentiable function that is positively homogeneous of degree
one. This is the contact identity underlying the support-gradient construction.
@isnad1 id=eq.2h3v.s8.aa6d7b7812b4 from=translated src=- shape=65032d4d vocab=4ea6b795
-/
theorem inner_homogeneousGradient [CompleteSpace E] (H : E → ℝ) (p : sphere (0 : E) 1)
    (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) (p : E) = H p := by
  rw [homogeneousGradient, inner_gradient_left]
  have hline : HasDerivAt (fun t : ℝ ↦ H ((p : E) + t • (p : E)))
      (fderiv ℝ H (p : E) (p : E)) 0 := by
    have harg : HasDerivAt (fun t : ℝ ↦ (p : E) + t • (p : E)) (p : E) 0 :=
      by
        simpa only [id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (p : E)).const_add (p : E)
    simpa [Function.comp_def] using
      hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
  have heq : (fun t : ℝ ↦ H ((p : E) + t • (p : E))) =ᶠ[𝓝 0]
      fun t : ℝ ↦ (1 + t) * H p := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    calc
      H ((p : E) + t • (p : E)) = H ((1 + t) • (p : E)) := by rw [add_smul, one_smul]
      _ = (1 + t) * H p := hhom (1 + t) (by linarith [(abs_lt.mp ht).1])
  have hright : HasDerivAt (fun t : ℝ ↦ (1 + t) * H p) (H p) 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_add 1).mul_const (H p)
  exact (hline.congr_of_eventuallyEq heq.symm).unique hright

/-- A differentiable positively homogeneous majorant has a unique contact point: its gradient.
This is the ambient form of the first-variation argument for support functions.-/
theorem eq_homogeneousGradient_of_global_support [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (x : E) (hH : DifferentiableAt ℝ H (p : E))
    (hmajor : ∀ y : E, inner ℝ x y ≤ H y) (hcontact : inner ℝ x (p : E) = H p) :
    x = homogeneousGradient H p := by
  let G : E → ℝ := fun y ↦ H y - inner ℝ x y
  have hmin : IsMinOn G univ (p : E) := by
    intro y _
    dsimp [G]
    rw [hcontact]
    linarith [hmajor y]
  have hlinear : DifferentiableAt ℝ (fun y : E ↦ inner ℝ x y) (p : E) :=
    (innerSL ℝ x).differentiableAt
  have hderiv : fderiv ℝ H (p : E) = innerSL ℝ x := by
    have hzero := (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
    have hinner_deriv :
        fderiv ℝ (fun y : E ↦ inner ℝ x y) (p : E) = innerSL ℝ x := by
      rw [show (fun y : E ↦ inner ℝ x y) = (innerSL ℝ x : E → ℝ) by funext y; rfl]
      exact (innerSL ℝ x).hasFDerivAt.fderiv
    rw [show G = fun y : E ↦ H y - inner ℝ x y by rfl,
      fderiv_fun_sub hH hlinear, hinner_deriv] at hzero
    exact sub_eq_zero.mp hzero
  apply ext_inner_right ℝ
  intro y
  rw [homogeneousGradient, inner_gradient_left, hderiv, innerSL_apply_apply]

/-- The gradient of a differentiable convex function that is positively homogeneous of degree
one lies below that function in every direction.
@isnad1 id=le.3h4v.s8.84f2d28d260c from=translated src=- shape=91f6f2ed vocab=483490f0
-/
theorem inner_homogeneousGradient_le [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (y : E)
    (hconvex : ConvexOn ℝ univ H) (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) y ≤ H y := by
  let e : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (p : E) y
  have hline_convex : ConvexOn ℝ univ (H ∘ e) := by
    simpa [e] using hconvex.comp_affineMap e
  have he0 : e 0 = (p : E) := by simp [e]
  have he1 : e 1 = y := by simp [e]
  have he_deriv : HasDerivAt e (y - (p : E)) (0 : ℝ) := by
    simpa [e] using (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ) (E := E)
      (a := (p : E)) (b := y) (x := (0 : ℝ)))
  have hline_deriv : HasDerivAt (H ∘ e) (fderiv ℝ H (p : E) (y - (p : E))) 0 := by
    exact hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) he_deriv he0.symm
  have hslope := hline_convex.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hline_deriv
  have heuler : fderiv ℝ H (p : E) (p : E) = H p := by
    rw [← inner_homogeneousGradient H p hH hhom, homogeneousGradient,
      inner_gradient_left]
  have hslope' : fderiv ℝ H (p : E) (y - (p : E)) ≤ H y - H p := by
    simpa [slope, Function.comp_apply, he0, he1] using hslope
  rw [map_sub, heuler] at hslope'
  rw [homogeneousGradient, inner_gradient_left]
  linarith

/-- Stereographic charts based at antipodal unit vectors are related by radial inversion.
@isnad1 id=eq.3h3v.s10.df3bc2917798 from=translated src=- shape=d60abc2e vocab=8c5e04ac
-/
theorem stereoToFun_stereoInvFunAux_neg {v w : E} (hv : ‖v‖ = 1)
    (hw : w ∈ (ℝ ∙ v)ᗮ) (hw0 : w ≠ 0) :
    stereoToFun v (stereoInvFunAux (-v) w) =
      (4 / ‖w‖ ^ 2) • (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) := by
  rw [stereoToFun_apply, stereoInvFunAux_apply]
  have hprojw : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto w = ⟨w, hw⟩ := by
    simpa using (ℝ ∙ v)ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨w, hw⟩ : (ℝ ∙ v)ᗮ)
  have hprojneg : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (-v) = 0 := by
    rw [map_neg, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    exact neg_zero
  have hinnerw : inner ℝ v w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hinnerv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  simp only [map_smul, map_add, hprojw, hprojneg, smul_zero, add_zero, innerSL_apply_apply,
    hinnerw, hinnerv, inner_neg_right, smul_smul]
  have hwsub : (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) ≠ 0 := by
    intro h
    exact hw0 (congr_arg Subtype.val h)
  rw [smul_left_inj hwsub]
  simp only [smul_eq_mul]
  have hdenom :
      1 - (‖w‖ ^ 2 + 4)⁻¹ * ((‖w‖ ^ 2 - 4) * -1) =
        2 * ‖w‖ ^ 2 / (‖w‖ ^ 2 + 4) := by
    field_simp
    ring
  simp only [zero_add]
  rw [hdenom]
  field_simp [norm_ne_zero_iff.mpr hw0]

/-- The closed convex set cut out by the supporting half-spaces prescribed by `h`.-/
def body (h : sphere (0 : E) 1 → ℝ) : Set E :=
  {x | ∀ p : sphere (0 : E) 1, inner ℝ (p : E) x ≤ h p}

/-- A support-function body is convex.
@isnad1 id=convex.0h2v.s7.7c45519b7320 from=translated src=- shape=f625b513 vocab=6b21b844
-/
theorem body_convex (h : sphere (0 : E) 1 → ℝ) : Convex ℝ (body h) := by
  rw [body, ofPred_forall]
  exact convex_iInter fun p ↦
    convex_halfSpace_le (innerSL ℝ (p : E)).toLinearMap.isLinear (h p)

/-- A support-function body is closed.
@isnad1 id=isclosed.0h2v.s6.af4a2d83c93b from=translated src=- shape=f99a8314 vocab=4224935e
-/
theorem body_isClosed (h : sphere (0 : E) 1 → ℝ) : IsClosed (body h) := by
  rw [body, ofPred_forall]
  exact isClosed_iInter fun p ↦ isClosed_Iic.preimage (innerSL ℝ (p : E)).continuous

/-- If `h` is bounded below by a positive constant, its support-function body has nonempty
interior.
@isnad1 id=nonempty.2h3v.s6.cc2f187357ee from=translated src=- shape=0a23f98a vocab=9acc4d13
-/
theorem body_interior_nonempty (h : sphere (0 : E) 1 → ℝ) {r : ℝ} (hr : 0 < r)
    (hlower : ∀ p, r ≤ h p) : (interior (body h)).Nonempty := by
  have hball : ball (0 : E) r ⊆ body h := by
    intro x hx p
    calc
      inner ℝ (p : E) x ≤ ‖(p : E)‖ * ‖x‖ := real_inner_le_norm _ _
      _ = ‖x‖ := by rw [norm_eq_of_mem_sphere p, one_mul]
      _ ≤ r := (by simpa [mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
      _ ≤ h p := hlower p
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (ball_mem_nhds 0 hr) hball

/-- A uniform upper bound on `h` bounds its support-function body.
@isnad1 id=isbounde.1h3v.s6.523949874923 from=translated src=- shape=233d3d89 vocab=dddc81ba
-/
theorem body_isBounded (h : sphere (0 : E) 1 → ℝ) {R : ℝ} (hupper : ∀ p, h p ≤ R) :
    Bornology.IsBounded (body h) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
  refine ⟨max R 0, ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    let p : sphere (0 : E) 1 := ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, hxnorm]⟩
    have hp : inner ℝ (p : E) x ≤ h p := hx p
    have hinner : inner ℝ (p : E) x = ‖x‖ := by
      change inner ℝ (‖x‖⁻¹ • x) x = ‖x‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      calc
        ‖x‖⁻¹ * (‖x‖ * ‖x‖) = (‖x‖⁻¹ * ‖x‖) * ‖x‖ := by ring
        _ = ‖x‖ := by rw [inv_mul_cancel₀ hxnorm, one_mul]
    rw [hinner] at hp
    exact (hp.trans (hupper p)).trans (le_max_left _ _)

/-- In a proper real inner-product space, a uniformly upper-bounded support function cuts out a
compact body.
@isnad1 id=iscompac.1h3v.s6.832f9e5a11c7 from=translated src=- shape=52908ba9 vocab=735b1aee
-/
theorem body_isCompact [ProperSpace E] (h : sphere (0 : E) 1 → ℝ) {R : ℝ}
    (hupper : ∀ p, h p ≤ R) : IsCompact (body h) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨body_isClosed h, body_isBounded h hupper⟩

/-- A continuous function on the unit sphere cuts out a compact support-function body.
@isnad1 id=iscompac.1h2v.s7.24b1ce0adb84 from=translated src=- shape=bf03007f vocab=05b13dda
-/
theorem body_isCompact_of_continuous [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (hh : Continuous h) : IsCompact (body h) := by
  obtain ⟨R, hR⟩ := (isCompact_range hh).bddAbove
  exact body_isCompact h fun p ↦ hR ⟨p, rfl⟩

/-- Every boundary point of a closed convex body with nonempty interior admits an outward unit
supporting normal.
@isnad1 id=ex.4h3v.s8.f7f9db954283 from=translated src=- shape=c95bb830 vocab=0e849af9
-/
theorem exists_unit_supporting_normal {K : Set E} (hconvex : Convex ℝ K)
    [CompleteSpace E] (hclosed : IsClosed K) (hinterior : (interior K).Nonempty) {x : E}
    (hx : x ∈ frontier K) :
    ∃ p : sphere (0 : E) 1, ∀ y ∈ K, inner ℝ (p : E) y ≤ inner ℝ (p : E) x := by
  have hx_not_interior : x ∉ interior K := by
    rw [frontier] at hx
    exact hx.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconvex.interior isOpen_interior
    hx_not_interior
  have hf0 : f ≠ 0 := by
    intro hzero
    obtain ⟨y, hy⟩ := hinterior
    simpa [hzero] using hf y hy
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hv0 : v ≠ 0 := (InnerProductSpace.toDual ℝ E).symm.map_ne_zero_iff.mpr hf0
  let p : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
    simp [norm_smul, hv0]⟩
  refine ⟨p, fun y hy ↦ ?_⟩
  have hhalf_closed : IsClosed {z : E | f z ≤ f x} :=
    isClosed_Iic.preimage f.continuous
  have hhalf : closure (interior K) ⊆ {z : E | f z ≤ f x} :=
    closure_minimal (fun z hz ↦ (hf z hz).le) hhalf_closed
  have hclosure : closure (interior K) = K := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior,
      hclosed.closure_eq]
  have hfy : f y ≤ f x := hhalf (hclosure.symm ▸ hy)
  change inner ℝ (‖v‖⁻¹ • v) y ≤ inner ℝ (‖v‖⁻¹ • v) x
  simpa only [real_inner_smul_left, v, InnerProductSpace.toDual_symm_apply] using
    mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr (norm_nonneg v))

/-- Pointwise contact and cross-support inequalities place every parametrized point in the
support-function body and make it attain the corresponding supporting hyperplane.
@isnad1 id=and.2h4v.s8.4c6218940a8a from=translated src=- shape=8a7c7ca2 vocab=fe937487
-/
theorem contact_mem_body (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ body h ∧ inner ℝ (F p) (p : E) = h p ∧
      ∀ x ∈ body h, inner ℝ x (p : E) ≤ h p := by
  intro p
  refine ⟨fun q ↦ ?_, hcontact p, fun x hx ↦ ?_⟩
  · simpa [real_inner_comm] using hcross p q
  · simpa [real_inner_comm] using hx p

/-- A parametrized contact point lies on the frontier of the support-function body.
@isnad1 id=mem.2h4v.s8.f12bed0f946e from=translated src=- shape=87e2d048 vocab=34108f02
-/
theorem contact_mem_frontier (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ frontier (body h) := by
  intro p
  rw [frontier, (body_isClosed h).closure_eq]
  refine ⟨(contact_mem_body h F hcontact hcross p).1, ?_⟩
  intro hpinterior
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hpinterior) with
    ⟨ε, hε, hball⟩
  let y := F p + (ε / 2) • (p : E)
  have hyball : y ∈ ball (F p) ε := by
    rw [mem_ball, dist_eq_norm]
    simp [y, norm_smul, norm_eq_of_mem_sphere p]
    rw [abs_of_pos hε]
    linarith
  have hybody : y ∈ body h := hball hyball
  have hy_support := hybody p
  have hpp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
    norm_num
  have hcontact' : inner ℝ (p : E) (F p) = h p := by
    rw [real_inner_comm]
    exact hcontact p
  have hy_inner : inner ℝ (p : E) y = h p + ε / 2 := by
    rw [show y = F p + (ε / 2) • (p : E) by rfl, inner_add_right,
      hcontact', real_inner_smul_right, hpp, mul_one]
  rw [hy_inner] at hy_support
  linarith

/-- If every exposed contact face is the prescribed singleton, the contact parametrization covers
the whole frontier of its support-function body.
@isnad1 id=eq.4h3v.s9.2e266ff30e11 from=translated src=- shape=1bbe2d96 vocab=afa5e87d
-/
theorem range_eq_frontier_of_unique_contact [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hunique : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → x = F p) :
    range F = frontier (body h) := by
  apply Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    exact contact_mem_frontier h F hcontact hcross p
  · intro x hx
    obtain ⟨p, hp⟩ := exists_unit_supporting_normal (body_convex h) (body_isClosed h)
      hinterior hx
    have hxbody : x ∈ body h := by
      rw [frontier, (body_isClosed h).closure_eq] at hx
      exact hx.1
    have hFpbody := (contact_mem_body h F hcontact hcross p).1
    have hle : h p ≤ inner ℝ (p : E) x := by
      rw [← hcontact p, real_inner_comm]
      exact hp (F p) hFpbody
    have hxeq : inner ℝ (p : E) x = h p :=
      le_antisymm (hxbody p) hle
    exact ⟨p, (hunique p x hxbody hxeq).symm⟩

/-- A contact point is uniquely determined once its displacement from the prescribed point is
orthogonal to every tangent vector. This is the linear-algebra step in the first-variation
argument for support parametrizations.-/
theorem eq_contact_of_tangent_orthogonal (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    {p : sphere (0 : E) 1} {x : E} (hxeq : inner ℝ (p : E) x = h p)
    (htangent : ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ → inner ℝ (x - F p) v = 0) :
    x = F p := by
  have hdisplacement : x - F p ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, hxeq]
    have hpcontact : inner ℝ (p : E) (F p) = h p := by
      rw [real_inner_comm]
      exact hcontact p
    rw [hpcontact, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp
    (htangent (x - F p) hdisplacement))

/-- First variation at every exposed contact point, together with contact and cross-support,
forces a parametrization to cover the whole frontier.
@isnad1 id=eq.4h3v.s9.d203a48d3e40 from=translated src=- shape=f32dbdec vocab=5b94b006
-/
theorem range_eq_frontier_of_first_variation [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    range F = frontier (body h) :=
  range_eq_frontier_of_unique_contact h F hcontact hcross hinterior fun p x hx hxeq ↦
    eq_contact_of_tangent_orthogonal h F hcontact hxeq (hstationary p x hx hxeq)

/-- Contact, cross-support, and first variation produce the compact convex body represented by a
support function. This packages the set-theoretic part of the support-gradient construction.
@isnad1 id=ex.6h4v.s10.daa3a7ef865f from=translated src=- shape=a700f185 vocab=1f7da1a5
-/
theorem exists_compact_body_of_first_variation [ProperSpace E] [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hh : Continuous h) {r : ℝ} (hr : 0 < r) (hlower : ∀ p, r ≤ h p)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    ∃ K : Set E, Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      range F = frontier K ∧ ∀ p, F p ∈ K ∧ inner ℝ (F p) (p : E) = h p ∧
        ∀ x ∈ K, inner ℝ x (p : E) ≤ h p := by
  refine ⟨body h, body_convex h, body_isCompact_of_continuous h hh,
    body_interior_nonempty h hr hlower,
    range_eq_frontier_of_first_variation h F hcontact hcross
      (body_interior_nonempty h hr hlower) hstationary, ?_⟩
  exact contact_mem_body h F hcontact hcross

/-- Strict cross-support separates the parametrizing normals, so the contact map is injective.
@isnad1 id=injectiv.2h3v.s8.ef9acd66f0ba from=translated src=- shape=8012c8eb vocab=42831107
-/
theorem injective_of_strictCross (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Function.Injective F := by
  intro p q hpq
  by_contra hpne
  have hpq_strict := hstrict p q hpne
  rw [hpq, hcontact q] at hpq_strict
  exact (lt_irrefl _ hpq_strict)

/-- A continuous strict contact parametrization of the unit sphere is a topological embedding.
@isnad1 id=isembedd.3h3v.s9.cc7aa84575e5 from=translated src=- shape=094d5365 vocab=8e116475
-/
theorem isEmbedding_of_strictCross [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E) (hF : Continuous F)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Topology.IsEmbedding F :=
  (hF.isClosedEmbedding (injective_of_strictCross h F hcontact hstrict)).isEmbedding

end SphereSupport

end SupportFunctionSphereSection

/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Defs.lean` -/

section CounterexampleDefsSection

/-!
# Definitions for the announced smooth Carathéodory–Loewner counterexamples

This file records the explicit planar family, its stereographic chart, and the support-function
predicate used in the counterexample announced by Levent Alpöge on 19 August 2026.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open scoped ContDiff EuclideanGeometry Manifold
open Set Metric

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture LoewnerConjecture

/-- The periodic real-valued function used in the announced counterexample.-/
noncomputable def counterexampleSeed (z : ℂ) : ℝ :=
  -Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
    Real.cos (4 * z.im) / 32 + Real.sin z.re * Real.sin z.im

/-- The seed is invariant under the sign ambiguity of a square root.
@isnad1 id=eq.0h1v.s3.037de67e7048 from=translated src=- shape=8fc7e33b vocab=da56f22b
-/
theorem counterexampleSeed_neg (z : ℂ) : counterexampleSeed (-z) = counterexampleSeed z := by
  simp [counterexampleSeed]

/-- The announced family `g_k` of smooth functions on the complex plane.

The use of the principal complex power chooses a square-root branch when `k` is odd. The seed is
even, so the resulting real-valued expression is independent of the sign of that square root.-/
noncomputable def counterexample (k : ℕ) (z : ℂ) : ℝ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
      counterexampleSeed w / (1 + r ^ 2) + 10 ^ 10

/-- Every member of the family takes the constant support value at the origin.
@isnad1 id=eq.0h1v.s5.b223fcdf2f53 from=translated src=- shape=915aef48 vocab=8872b834
-/
theorem counterexample_zero (k : ℕ) : counterexample k 0 = 10 ^ 10 := by
  simp [counterexample]

/-- The north pole used to fix the stereographic chart for the global counterexample.-/
noncomputable def counterexampleNorthPole : sphere (0 : ℝ³) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere, dist_zero_right]
    simp⟩

/-- The inverse stereographic chart in which the formula `counterexample 2` is written.

Mathlib's stereographic coordinate has a conventional factor of two. Scaling its target
coordinate by two makes the pullback of the round metric equal to
`4 / (1 + ‖z‖ ^ 2) ^ 2` times the Euclidean metric.-/
noncomputable def counterexampleSphereChart (z : ℂ) : sphere (0 : ℝ³) 1 :=
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  (stereographic' 2 counterexampleNorthPole).symm
    (2 • Complex.orthonormalBasisOneI.repr z)

/-- The origin of the planar chart represents the south pole. This test fixes the scale and sign
convention in `counterexampleSphereChart`.
@isnad1 id=eq.0h0v.s9.1cd48e602570 from=translated src=- shape=3671f725 vocab=ca4b6d67
-/
theorem counterexampleSphereChart_zero :
    counterexampleSphereChart 0 = -counterexampleNorthPole := by
  apply Subtype.ext
  simp [counterexampleSphereChart, stereographic'_symm_apply]

/-- `F` parametrizes the supporting point of `K` with outer unit normal `p`, and `h p` is
the corresponding support value.

The final inequality says that the hyperplane through `F p` perpendicular to `p` supports
the whole body. Requiring `F p ∈ K` makes the supremum attained and avoids conventions for
`sSup ∅`.-/
def IsSupportParametrization (h : sphere (0 : ℝ³) 1 → ℝ)
    (F : sphere (0 : ℝ³) 1 → ℝ³) (K : Set ℝ³) : Prop :=
  ∀ p, F p ∈ K ∧ inner ℝ (F p) (p : ℝ³) = h p ∧
    ∀ x ∈ K, inner ℝ x (p : ℝ³) ≤ h p

end CaratheodoryLoewnerCounterexample

end CounterexampleDefsSection

/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Smooth.lean` -/

section CounterexampleSmoothSection

/-!
# Smoothness of the announced Carathéodory–Loewner counterexamples

The proof is split between the punctured plane, where branch independence is the main issue, and
the origin, where the flat exponential dominates every derivative.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Filter Topology
open scoped ContDiff

namespace CaratheodoryLoewnerCounterexample

noncomputable section

/-- The trigonometric seed is smooth as a real-valued function of the complex variable.
@isnad1 id=contdiff.0h0v.s5.bfd5e551f766 from=translated src=- shape=352d7a74 vocab=86956fc0
-/
theorem counterexampleSeed_contDiff : ContDiff ℝ ∞ counterexampleSeed := by
  unfold counterexampleSeed
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.contDiff
  fun_prop

@[fun_prop]
private theorem sin_hasTemperateGrowth : Function.HasTemperateGrowth Real.sin := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_sin_le_one n x

@[fun_prop]
private theorem cos_hasTemperateGrowth : Function.HasTemperateGrowth Real.cos := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_cos_le_one n x

private theorem counterexampleSeed_hasTemperateGrowth :
    Function.HasTemperateGrowth counterexampleSeed := by
  unfold counterexampleSeed
  have hre : Function.HasTemperateGrowth (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.hasTemperateGrowth
  have him : Function.HasTemperateGrowth (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.hasTemperateGrowth
  simp only [div_eq_mul_inv]
  fun_prop

private def cpowFalling : ℂ → ℕ → ℂ
  | _, 0 => 1
  | c, n + 1 => c * cpowFalling (c - 1) n

private theorem iteratedDeriv_cpow_const (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun w : ℂ ↦ w ^ c) z = cpowFalling c n * z ^ (c - n) := by
  induction n generalizing c with
  | zero => simp [cpowFalling]
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun w : ℂ ↦ w ^ c) =ᶠ[𝓝 z] fun w ↦ c * w ^ (c - 1) := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        simpa using ((hasDerivAt_id w).cpow_const hw).deriv
      rw [hderiv.iteratedDeriv_eq n]
      have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c - 1)) z :=
        (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
      rw [iteratedDeriv_const_mul c hsmooth, ih (c - 1)]
      have hexp : c - 1 - (n : ℂ) = c - ((n + 1 : ℕ) : ℂ) := by
        norm_num [Nat.cast_add]
        ring
      change c * (cpowFalling (c - 1) n * z ^ (c - 1 - (n : ℂ))) =
        (c * cpowFalling (c - 1) n) * z ^ (c - ((n + 1 : ℕ) : ℂ))
      rw [mul_assoc, hexp]

private theorem norm_iteratedFDeriv_cpow_const (c : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (fun w : ℂ ↦ w ^ (c : ℂ)) z‖ =
      ‖cpowFalling (c : ℂ) n‖ * ‖z‖ ^ (c - n) := by
  have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c : ℂ)) z :=
    (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
  rw [← hsmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cpow_const (c : ℂ) n hz,
    norm_mul]
  congr 1
  convert Complex.norm_cpow_real z (c - n) using 1
  push_cast
  ring

private theorem cpow_pos_mul (r : ℝ) (hr : 0 < r) {z c : ℂ} (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ c = (r : ℂ) ^ c * z ^ c := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, add_mul, Complex.exp_add,
    Complex.ofReal_log hr.le]

private theorem div_cpow_eq (k : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (100 / z) ^ ((k : ℂ) / 2) =
      (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2)) := by
  rw [div_eq_mul_inv]
  change (((100 : ℝ) : ℂ) * z⁻¹) ^ ((k : ℂ) / 2) =
    ((100 : ℂ) ^ ((k : ℂ) / 2)) * z ^ (-((k : ℂ) / 2))
  rw [cpow_pos_mul 100 (by norm_num)
      (inv_ne_zero (Complex.slitPlane_ne_zero hz)),
    Complex.inv_cpow z _ (Complex.slitPlane_arg_ne_pi hz), Complex.cpow_neg]
  norm_num

private def negConjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

@[simp]
private theorem negConjLIE_apply (z : ℂ) : negConjLIE z = -star z := by
  rfl

private def branchPhase (k : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  a * (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2))

private theorem norm_iteratedFDeriv_branchPhase (k n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (branchPhase k a) z‖ =
      ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) n‖ * ‖z‖ ^ (-(k : ℝ) / 2 - n) := by
  have hsmooth : ContDiffAt ℝ n (fun w : ℂ ↦ w ^ (-((k : ℂ) / 2))) z :=
    ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt).of_le
      (mod_cast le_top)
  have hc : -((k : ℂ) / 2) = ((-(k : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [show branchPhase k a = fun w ↦
      (a * (100 : ℂ) ^ ((k : ℂ) / 2)) • w ^ (-((k : ℂ) / 2)) by
        funext w; simp [branchPhase],
    iteratedFDeriv_const_smul_apply' hsmooth, norm_smul, hc,
    norm_iteratedFDeriv_cpow_const (-(k : ℝ) / 2) n hz]
  push_cast
  ring

private theorem branchOscillatory_iteratedFDeriv_polynomial_bound (k n : ℕ) (a : ℂ)
    (ha : ‖a‖ = 1) (e : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, e z ∈ Complex.slitPlane → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖ ≤
        C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨d, C, hC, hseed⟩ :=
    counterexampleSeed_hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
  let P := k + n
  let B := 1 + ‖(100 : ℂ) ^ ((k : ℂ) / 2)‖ *
    ∑ i ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) i‖
  refine ⟨P * (d + n), Nat.factorial n * C * (1 + B) ^ d * B ^ n,
    by positivity, ?_⟩
  intro z hz hz_one
  have hz0 : z ≠ 0 := fun h ↦ Complex.slitPlane_ne_zero hz (by simp [h])
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hB : 1 ≤ B := by
    simp only [B, le_add_iff_nonneg_right]
    positivity
  let R : ℝ := ‖z‖ ^ (-(P : ℝ))
  have hR : 1 ≤ R := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hz_one
      (neg_nonpos.mpr (Nat.cast_nonneg P))
  let Q := B * R
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hB hR
  have hphase (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (branchPhase k a ∘ e) z‖ ≤ Q := by
    rw [e.norm_iteratedFDeriv_comp_right]
    rw [norm_iteratedFDeriv_branchPhase k i a hz]
    rw [LinearIsometryEquiv.norm_map]
    have hcoeff : ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤ B := by
      rw [norm_mul, ha, one_mul]
      have hi_mem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
      have hsum : ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤
          ∑ j ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖cpowFalling (-((k : ℂ) / 2)) j‖)
          (fun _ _ ↦ norm_nonneg _) hi_mem
      dsimp only [B]
      nlinarith [mul_le_mul_of_nonneg_left hsum (norm_nonneg ((100 : ℂ) ^ ((k : ℂ) / 2)))]
    have hexp : ‖z‖ ^ (-(k : ℝ) / 2 - i) ≤ R := by
      apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
      dsimp only [R, P]
      have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      linarith
    dsimp only [Q]
    exact mul_le_mul hcoeff hexp (Real.rpow_nonneg (norm_nonneg z) _) (by positivity)
  let s := e ⁻¹' Complex.slitPlane
  have hs : IsOpen s := Complex.isOpen_slitPlane.preimage e.continuous
  have hzs : z ∈ s := hz
  have hinner : ContDiffOn ℝ ∞ (branchPhase k a ∘ e) s := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.comp x ?_ e.contDiff.contDiffAt
    unfold branchPhase
    exact (contDiffAt_const.mul
      ((analyticAt_id.cpow analyticAt_const hx).restrictScalars.contDiffAt))
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i counterexampleSeed Set.univ
          ((branchPhase k a ∘ e) z)‖ ≤ C * (1 + Q) ^ d := by
    rw [iteratedFDerivWithin_univ]
    refine (hseed i hi _).trans ?_
    gcongr
    simpa only [norm_iteratedFDeriv_zero] using hphase 0 (Nat.zero_le n)
  have hinner_bound (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (branchPhase k a ∘ e) s z‖ ≤ Q ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hs hzs]
    exact (hphase i hin).trans (le_self_pow₀ hQ (Nat.ne_of_gt hi))
  have hcomp := norm_iteratedFDerivWithin_comp_le
    counterexampleSeed_contDiff.contDiffOn hinner (mod_cast le_top)
    uniqueDiffOn_univ hs.uniqueDiffOn (fun _ _ ↦ Set.mem_univ _) hzs houter hinner_bound
  rw [iteratedFDerivWithin_of_isOpen n hs hzs] at hcomp
  have h_one_add : 1 + Q ≤ (1 + B) * R := by
    dsimp only [Q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hR)]
  have hRpow : R ^ (d + n) = ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  calc
    ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖
        ≤ Nat.factorial n * (C * (1 + Q) ^ d) * Q ^ n := hcomp
    _ ≤ Nat.factorial n * (C * ((1 + B) * R) ^ d) * (B * R) ^ n := by
      gcongr
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * (R ^ d * R ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * R ^ (d + n) := by
      rw [pow_add]
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) *
        ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by rw [hRpow]

private def oscillatoryFactor (k : ℕ) (z : ℂ) : ℝ :=
  counterexampleSeed (Complex.cpow (100 / star z) ((k : ℂ) / 2))

private theorem oscillatoryFactor_eq_plus (k : ℕ) {z : ℂ}
    (hz : star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k 1 ∘ Complex.conjLIE) z) := by
  simpa [oscillatoryFactor, Function.comp_apply, Complex.conjLIE_apply, branchPhase] using
    congrArg counterexampleSeed (div_cpow_eq k hz)

private def radialArgument (z : ℂ) : ℝ :=
  Complex.normSq z * Real.exp (8 * Complex.normSq z)

private def radialFlat (z : ℂ) : ℝ :=
  Real.flatRpowExp (1 / 8 : ℝ) 1 (radialArgument z)

private theorem normSq_contDiff : ContDiff ℝ ∞ Complex.normSq := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.contDiff
  rw [show Complex.normSq = fun z : ℂ ↦ z.re * z.re + z.im * z.im by
    funext z; exact Complex.normSq_apply z]
  convert! hre.mul hre |>.add (him.mul him) using 1

private theorem radialArgument_contDiff : ContDiff ℝ ∞ radialArgument := by
  unfold radialArgument
  exact normSq_contDiff.mul <| Real.contDiff_exp.comp <| contDiff_const.mul normSq_contDiff

private theorem radialArgument_zero : radialArgument 0 = 0 := by
  simp [radialArgument]

private theorem radialFlat_contDiff : ContDiff ℝ ∞ radialFlat := by
  unfold radialFlat
  exact (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)).comp radialArgument_contDiff

private theorem radialFlat_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialFlat 0 = 0 := by
  unfold radialFlat
  exact ContDiff.iteratedFDeriv_comp_zero_of_outer
    (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)) radialArgument_contDiff
    radialArgument_zero (Real.flatRpowExp.iteratedFDeriv_zero (by norm_num) (by norm_num)) n

private def radialAmplitude (z : ℂ) : ℝ :=
  radialFlat z * (Complex.normSq z / (1 + Complex.normSq z))

private theorem radialAmplitude_contDiff : ContDiff ℝ ∞ radialAmplitude := by
  unfold radialAmplitude
  apply radialFlat_contDiff.mul
  exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
    ne_of_gt (by have := Complex.normSq_nonneg z; linarith)

private theorem radialAmplitude_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialAmplitude 0 = 0 := by
  unfold radialAmplitude
  apply ContDiff.iteratedFDeriv_mul_zero_of_left radialFlat_contDiff
  · exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
      ne_of_gt (by have := Complex.normSq_nonneg z; linarith)
  · exact radialFlat_iteratedFDeriv_zero

private theorem radialAmplitude_isLittleO_norm_pow (m n : ℕ) :
    iteratedFDeriv ℝ m radialAmplitude =o[𝓝 0] fun z : ℂ ↦ ‖z‖ ^ n :=
  ContDiff.isLittleO_norm_pow_of_iteratedFDeriv_zero radialAmplitude_contDiff
    radialAmplitude_iteratedFDeriv_zero m n

private theorem radialFlat_eq (z : ℂ) (hz : z ≠ 0) :
    radialFlat z =
      Real.exp (-‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hx : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  rw [radialFlat, radialArgument,
    Real.flatRpowExp.of_pos _ _ (mul_pos hx (Real.exp_pos _))]
  have hpow : Complex.normSq z ^ (-(1 / 8 : ℝ)) = ‖z‖ ^ (-(1 : ℝ) / 4) := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    ring
  have hexp : Real.exp (8 * Complex.normSq z) ^ (-(1 / 8 : ℝ)) =
      Real.exp (-‖z‖ ^ 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Complex.normSq_eq_norm_sq]
    congr 1
    ring
  rw [Real.mul_rpow hx.le (Real.exp_pos _).le, hpow, hexp]
  congr 1
  ring

private theorem counterexample_eq_radialAmplitude (k : ℕ) (z : ℂ) (hz : z ≠ 0) :
    counterexample k z = radialAmplitude z * oscillatoryFactor k z + 10 ^ 10 := by
  have hexp :
      Real.exp (-(Real.rpow ‖z‖ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2))) =
        Real.exp (-(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))) := by
    congr 1
    change -(‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) =
      -(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))
    ring
  rw [counterexample, radialAmplitude, oscillatoryFactor, radialFlat_eq z hz,
    Complex.normSq_eq_norm_sq]
  ring_nf
  all_goals rw [hexp]
  all_goals ring

private lemma cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    (z ^ ((k : ℂ) / 2)) ^ 2 = z ^ k := by
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast]
  congr 1
  push_cast
  ring

private lemma alt_cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) ^ 2 = z ^ k := by
  rw [mul_pow, cpow_half_nat_sq, ← pow_mul]
  conv_lhs => lhs; rw [show k * 2 = 2 * k by omega]
  rw [pow_mul, Complex.I_sq]
  rw [neg_pow z k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]

private lemma counterexampleSeed_eq_of_sq_eq_sq {z w : ℂ} (h : z ^ 2 = w ^ 2) :
    counterexampleSeed z = counterexampleSeed w := by
  rcases eq_or_eq_neg_of_sq_eq_sq z w h with h | h
  · rw [h]
  · rw [h, counterexampleSeed_neg]

/-- The seed identifies the principal half-integral power with the smooth alternate branch based
at `-z`. This pointwise identity is useful for differentiating at points on the branch cut.
@isnad1 id=eq.0h2v.s6.4698a9329d1e from=translated src=- shape=e61f3d97 vocab=bb2fea1b
-/
theorem counterexampleSeed_cpow_eq_alt (k : ℕ) (z : ℂ) :
    counterexampleSeed (z ^ ((k : ℂ) / 2)) =
      counterexampleSeed ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) :=
  counterexampleSeed_eq_of_sq_eq_sq <|
    (cpow_half_nat_sq z k).trans (alt_cpow_half_nat_sq z k).symm

private theorem oscillatoryFactor_eq_minus (k : ℕ) {z : ℂ}
    (hz : -star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
  have hneg : -(100 / star z) = 100 / (-star z) := by ring
  calc
    oscillatoryFactor k z =
        counterexampleSeed ((Complex.I ^ k) * ((-(100 / star z)) ^ ((k : ℂ) / 2))) := by
      simpa [oscillatoryFactor] using counterexampleSeed_cpow_eq_alt k (100 / star z)
    _ = counterexampleSeed
        ((Complex.I ^ k) * ((100 / (-star z)) ^ ((k : ℂ) / 2))) := by rw [hneg]
    _ = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
      rw [div_cpow_eq k hz]
      simp only [Function.comp_apply, negConjLIE_apply, branchPhase]
      ring_nf

private theorem oscillatoryFactor_iteratedFDeriv_polynomial_bound (k n : ℕ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (oscillatoryFactor k) z‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨Np, Cp, hCp, hp⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n 1 (by simp) Complex.conjLIE
  obtain ⟨Nm, Cm, hCm, hm⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n (Complex.I ^ k)
      (by simp) negConjLIE
  refine ⟨Np + Nm, Cp + Cm, add_nonneg hCp hCm, ?_⟩
  intro z hz hz_one
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpowp : ‖z‖ ^ (-(Np : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  have hpowm : ‖z‖ ^ (-(Nm : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane (star_ne_zero.mpr hz) with hslit | hslit
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k 1 ∘ Complex.conjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage Complex.continuous_conj |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_plus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cp * ‖z‖ ^ (-(Np : ℝ)) := hp z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowp hCp).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCm)
            (Real.rpow_nonneg (norm_nonneg z) _)
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k (Complex.I ^ k) ∘ negConjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage negConjLIE.continuous |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_minus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cm * ‖z‖ ^ (-(Nm : ℝ)) := hm z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowm hCm).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCp)
            (Real.rpow_nonneg (norm_nonneg z) _)

private theorem counterexampleSeed_cpow_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : ℂ ↦ counterexampleSeed (w ^ ((k : ℂ) / 2))) z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hz | hz
  · exact counterexampleSeed_contDiff.contDiffAt.comp z
      ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt)
  · have hq : ContDiffAt ℝ ∞
        (fun w : ℂ ↦ (Complex.I ^ k) * ((-w) ^ ((k : ℂ) / 2))) z :=
      ((analyticAt_const.mul
        (analyticAt_id.neg.cpow analyticAt_const hz)).restrictScalars.contDiffAt)
    apply (counterexampleSeed_contDiff.contDiffAt.comp z hq).congr_of_eventuallyEq
    filter_upwards
    intro w
    exact counterexampleSeed_cpow_eq_alt k w

private theorem oscillatoryFactor_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (oscillatoryFactor k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    rw [show (fun w : ℂ ↦ star w) = (Complex.conjLIE : ℂ → ℂ) by funext w; rfl]
    exact Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  unfold oscillatoryFactor
  exact (counterexampleSeed_cpow_contDiffAt k
    (div_ne_zero (by norm_num) hstar_ne)).comp z hinv

private theorem radialAmplitude_mul_oscillatory_flatness (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 ∧
      ∀ m, iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
  let s : Set ℂ := {0}ᶜ
  have hs : IsOpen s := isClosed_singleton.isOpen_compl
  have hosc : ContDiffOn ℝ ∞ (oscillatoryFactor k) s := by
    intro z hz
    exact (oscillatoryFactor_contDiffAt k (by simpa [s] using hz)).contDiffWithinAt
  have hflat : ∀ m, iteratedFDeriv ℝ m
      (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
    intro m
    have hsum' : (∑ i ∈ Finset.range (m + 1), fun z : ℂ ↦
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
        fun z ↦ ‖z‖ := by
      apply Asymptotics.IsLittleO.sum
      intro i hi
      obtain ⟨N, C, hC, hpoly⟩ :=
        oscillatoryFactor_iteratedFDeriv_polynomial_bound k (m - i)
      have hoscO : (iteratedFDeriv ℝ (m - i) (oscillatoryFactor k)) =O[𝓝[≠] 0]
          fun z : ℂ ↦ ‖z‖ ^ (-(N : ℝ)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 1 :=
          Filter.Eventually.filter_mono inf_le_left (Metric.ball_mem_nhds 0 one_pos)
        filter_upwards [self_mem_nhdsWithin, hball] with z hz hball
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hz_one : ‖z‖ ≤ 1 := by
          rw [Metric.mem_ball, dist_zero_right] at hball
          exact hball.le
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
        exact hpoly z hz hz_one
      have hamp := (radialAmplitude_isLittleO_norm_pow i (N + 1)).mono
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
      have hprod : (fun z : ℂ ↦
          ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
            ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
          fun z ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ)) :=
        hamp.norm_left.mul_isBigO hoscO.norm_left
      have htarget : (fun z : ℂ ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ))) =ᶠ[𝓝[≠] 0]
          fun z ↦ ‖z‖ := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [← Real.rpow_natCast, ← Real.rpow_add hr]
        have hN : ((N + 1 : ℕ) : ℝ) + -(N : ℝ) = 1 := by
          push_cast
          ring
        rw [hN, Real.rpow_one]
      simpa only [mul_assoc] using
        (hprod.congr' EventuallyEq.rfl htarget).const_mul_left (m.choose i : ℝ)
    have hsum : (fun z : ℂ ↦ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
        fun z ↦ ‖z‖ := by
      have heq : (∑ i ∈ Finset.range (m + 1), fun z : ℂ ↦
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
            ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =
          fun z ↦ ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
              ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖ := by
        funext z
        classical
        induction Finset.range (m + 1) using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => simp [ha, ih]
      rw [← heq]
      exact hsum'
    rw [Asymptotics.isLittleO_iff] at hsum ⊢
    intro c hc
    filter_upwards [hsum hc, self_mem_nhdsWithin] with z hbound hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    have hmul := norm_iteratedFDerivWithin_mul_le
      radialAmplitude_contDiff.contDiffOn hosc hs.uniqueDiffOn (show z ∈ s by simpa [s] using hz)
      (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
    rw [iteratedFDerivWithin_of_isOpen m hs (show z ∈ s by simpa [s] using hz)] at hmul
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs (show z ∈ s by simpa [s] using hz)] at hmul
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖ := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [Real.norm_of_nonneg hsum_nonneg] at hbound
    exact hmul.trans (by simpa using hbound)
  refine ⟨?_, hflat⟩
  apply ContDiff.at_zero_of_iteratedFDeriv_isLittleO
  · intro z hz
    exact radialAmplitude_contDiff.contDiffAt.mul (oscillatoryFactor_contDiffAt k hz)
  · simp [radialAmplitude, radialFlat, radialArgument]
  · exact hflat

private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
      (id : ℂ → ℂ) :=
  (radialAmplitude_mul_oscillatory_flatness k).2 m

private theorem radialAmplitude_mul_oscillatory_contDiffAt_zero (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 :=
  (radialAmplitude_mul_oscillatory_flatness k).1

private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 = 0 := by
  have hcontinuous := (radialAmplitude_mul_oscillatory_contDiffAt_zero k)
    |>.continuousAt_iteratedFDeriv (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
  have hcontinuous' : Tendsto
      (iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z))
      (𝓝[≠] 0) (𝓝 (iteratedFDeriv ℝ m
        (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0)) :=
    hcontinuous.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  have hzero := (radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO k m).trans_tendsto
    (tendsto_id.mono_left inf_le_left)
  exact tendsto_nhds_unique' (NormedField.nhdsNE_neBot (0 : ℂ)) hcontinuous' hzero

/-- Away from the origin the principal-power formula is smooth. For odd `k`, evenness of the seed
removes the sign jump of the chosen square-root branch.
@isnad1 id=contdiff.1h2v.s5.8070c9a9c636 from=translated src=- shape=88ae26cb vocab=57f9ccea
-/
theorem counterexample_contDiffAt_of_ne_zero (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (counterexample k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    rw [show (fun w : ℂ ↦ star w) = (Complex.conjLIE : ℂ → ℂ) by funext w; rfl]
    exact Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  have hseed : ContDiffAt ℝ ∞
      (fun w : ℂ ↦ counterexampleSeed ((100 / star w) ^ ((k : ℂ) / 2))) z :=
    by
      simpa [Function.comp_def] using
        (counterexampleSeed_cpow_contDiffAt k (div_ne_zero (by norm_num) hstar_ne)).comp z hinv
  apply (radialAmplitude_contDiff.contDiffAt.mul hseed).add contDiffAt_const
    |>.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact counterexample_eq_radialAmplitude k w hw

private theorem counterexample_contDiffAt_zero_all (k : ℕ) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  have hconstant : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (10 : ℝ) ^ 10) 0 := contDiffAt_const
  apply (radialAmplitude_mul_oscillatory_contDiffAt_zero k).add hconstant
    |>.congr_of_eventuallyEq
  filter_upwards
  intro z
  by_cases hz : z = 0
  · subst z
    simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
  · exact counterexample_eq_radialAmplitude k z hz

/-- At the origin the nonconstant part of `counterexample k` is flat: exponential decay dominates
the algebraic growth of every derivative of the oscillatory factor.
@isnad1 id=contdiff.1h1v.s5.30b92fbdba40 from=translated src=- shape=dd49c729 vocab=84257de5
-/
theorem counterexample_contDiffAt_zero (k : ℕ) (hk : 0 < k) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_contDiffAt_zero_all (k + 1)

/-- The first Fréchet derivative of the counterexample vanishes at the origin.
@isnad1 id=eq.1h1v.s9.789e6a6b6b01 from=translated src=- shape=72b01d78 vocab=edd5387c
-/
theorem counterexample_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (counterexample k) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hfun : counterexample (Nat.succ k) = fun z ↦
        radialAmplitude z * oscillatoryFactor (Nat.succ k) z + (10 : ℝ) ^ 10 := by
      funext z
      by_cases hz : z = 0
      · subst z
        simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
      · exact counterexample_eq_radialAmplitude (Nat.succ k) z hz
    rw [hfun]
    simp only [fderiv_add_const]
    ext v
    have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (Nat.succ k) 1
    have happ := congrArg (fun L : ℂ [×1]→L[ℝ] ℝ ↦ L ![v]) hzero
    simpa only [iteratedFDeriv_one_apply, _root_.zero_apply,
      Matrix.cons_val_zero] using happ

private theorem counterexample_fderiv_fderiv_zero_all (k : ℕ) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  have hfun : counterexample k = fun z ↦
      radialAmplitude z * oscillatoryFactor k z + (10 : ℝ) ^ 10 := by
    funext z
    by_cases hz : z = 0
    · subst z
      simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
    · exact counterexample_eq_radialAmplitude k z hz
  rw [hfun]
  simp only [fderiv_add_const]
  ext v w
  have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero k 2
  have happ := congrArg (fun L : ℂ [×2]→L[ℝ] ℝ ↦ L ![v, w]) hzero
  simpa only [iteratedFDeriv_two_apply, _root_.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using happ

/-- The second Fréchet derivative of the counterexample vanishes at the origin. This is the
flatness consequence used in the index computation.
@isnad1 id=eq.1h1v.s11.ba6ca576cdc4 from=translated src=- shape=422c373f vocab=1213aa9e
-/
theorem counterexample_fderiv_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_fderiv_fderiv_zero_all (k + 1)

/-- Each positive member of the announced family is smooth on the whole complex plane, including
at the origin. The flat exponential factor is essential at the origin.
@isnad1 id=contdiff.1h1v.s5.5ea5cfd94aa4 from=translated src=- shape=8772077c vocab=5e483bc4
-/
theorem counterexample_contDiff (k : ℕ) (hk : 0 < k) : ContDiff ℝ ∞ (counterexample k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · simpa [hz] using counterexample_contDiffAt_zero k hk
  · exact counterexample_contDiffAt_of_ne_zero k hz

end

end CaratheodoryLoewnerCounterexample

end CounterexampleSmoothSection

/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Index.lean` -/

section CounterexampleIndexSection

/-!
# Index of the announced Carathéodory–Loewner counterexamples

This file computes the winding number of the trace-free Hessian near the origin.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Metric
open Filter
open scoped ContDiff Topology unitInterval

namespace CaratheodoryLoewnerCounterexample

open LoewnerConjecture

/-- The explicit trace-free Hessian of the seed. Keeping this local avoids adding another
public synonym for a one-line expression.-/
private noncomputable def seedTraceFreeHessianModel (z : ℂ) : ℂ :=
  ((Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
      1 / 2 * Real.cos (4 * z.im) : ℝ) : ℂ) +
    ((2 * Real.cos z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I

private noncomputable def seedGradient (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im) • Complex.reCLM +
    (-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im) • Complex.imCLM

private noncomputable def seedHessian (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((Real.cos (2 * z.re) - Real.sin z.re * Real.sin z.im) • Complex.reCLM +
      (Real.cos z.re * Real.cos z.im) • Complex.imCLM).smulRight Complex.reCLM +
    ((Real.cos z.re * Real.cos z.im) • Complex.reCLM +
      (-6 / 5 * Real.cos (2 * z.im) + 1 / 2 * Real.cos (4 * z.im) -
        Real.sin z.re * Real.sin z.im) • Complex.imCLM).smulRight Complex.imCLM

private noncomputable def seedWirtingerModel (z : ℂ) : ℂ :=
  (((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ) -
    ((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I) / 2

/-- The radial amplitude in the counterexample, separated from the oscillatory seed.-/
private noncomputable def counterexampleRadialAmplitude (r : ℝ) : ℝ :=
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) /
    (1 + r ^ 2)

/-- The logarithmic derivative of the radial amplitude on the positive real axis.-/
private noncomputable def counterexampleRadialLogDerivOne (r : ℝ) : ℝ :=
  2 / r - 2 * r / (1 + r ^ 2) + Real.exp (-(r ^ 2)) *
    (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))

/-- The derivative of `counterexampleRadialLogDerivOne` on the positive real axis.-/
private noncomputable def counterexampleRadialLogDerivTwo (r : ℝ) : ℝ :=
  -2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2 + Real.exp (-(r ^ 2)) *
    (Real.rpow r (-(1 : ℝ) / 4) - 5 / 16 * Real.rpow r (-(9 : ℝ) / 4) -
      4 * Real.rpow r (7 / 4))

/-- The dominant part of the trace-free Hessian on the punctured plane.-/
private noncomputable def counterexampleHessianLeading (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  (counterexampleRadialAmplitude r : ℂ) * star (seedTraceFreeHessianModel w) *
    (-((k : ℂ) / 2) * w / star z) ^ 2

/-- The lower-order part of the trace-free Hessian on a local analytic branch.-/
private noncomputable def counterexampleHessianError (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  let wbar := -((k : ℂ) / 2) * w / star z
  let wbarbar := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2
  let A := counterexampleRadialAmplitude r
  let L₁ := counterexampleRadialLogDerivOne r
  let L₂ := counterexampleRadialLogDerivTwo r
  let Abar : ℂ := (A * L₁ : ℝ) * z / (2 * r)
  let Abarbar : ℂ :=
    (A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2) -
      (A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)
  4 * A * seedWirtingerModel w * wbarbar +
    8 * Abar * seedWirtingerModel w * wbar +
    4 * Abarbar * counterexampleSeed w

end CaratheodoryLoewnerCounterexample

end CounterexampleIndexSection

/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Global.lean` -/

section CounterexampleGlobalSection

/-!
# The global smooth Carathéodory counterexample

This file extends `counterexample 2` across the sphere and realizes it as the support function of
a smooth strictly convex body with a unique umbilic.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open scoped ContDiff EuclideanGeometry Manifold
open Set Metric

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture EuclideanHypersurface LoewnerConjecture

private local instance : Fact (Module.finrank ℝ ℝ³ = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The ambient-codomain manifold derivative used throughout this proof file.-/
private noncomputable def sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
  mvfderiv (𝓡 2) F p

/-- The complex coordinate inverse to `counterexampleSphereChart` away from the north pole.-/
private noncomputable def counterexampleSphereCoord
    (p : sphere (0 : ℝ³) 1) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm
    ((2 : ℝ)⁻¹ • (stereographic' 2 counterexampleNorthPole) p)

/-- The pointwise extension of `counterexample 2` obtained by assigning its limiting value at the
north pole. Smoothness at that point is the substantive content of the extension theorem.-/
private noncomputable def counterexampleTwoSphereExtension
    (p : sphere (0 : ℝ³) 1) : ℝ :=
  if p = counterexampleNorthPole then 10 ^ 10 + 3 / 160
  else counterexample 2 (counterexampleSphereCoord p)

/-- The flat scalar appearing in the reciprocal chart at the north pole. On the nonnegative
half-line this is `(s / 10000) ^ (1 / 8) * exp (-10000 / s)`.-/
private noncomputable def counterexampleTwoReciprocalExponent (s : ℝ) : ℝ :=
  (10000 : ℝ) ^ (-(1 : ℝ) / 8) *
    (s ^ ((1 : ℝ) / 8) * Real.flatRpowExp 1 10000 s)

/-- The positive radial coefficient multiplying the seed in the reciprocal chart.-/
private noncomputable def counterexampleTwoReciprocalDamping (w : ℂ) : ℝ :=
  let s := ‖w‖ ^ 2
  10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)

/-- The smooth representative of `counterexample 2` in its reciprocal chart.-/
private noncomputable def counterexampleTwoReciprocal (w : ℂ) : ℝ :=
  10 ^ 10 + counterexampleTwoReciprocalDamping w * counterexampleSeed w

/-- The real-linear reciprocal coordinate associated to the standard chart at the north pole.
The two orthonormal bases account for the fixed basis choice in mathlib's opposite
stereographic charts.-/
private noncomputable def counterexampleTwoReciprocalLinearCoord
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  50 • Complex.orthonormalBasisOneI.repr.symm
    (Upos ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjectionOnto
      (Uneg.symm x : ℝ³)))

/-- The fixed isometry from the complex reciprocal coordinate to the tangent plane at the
north pole.-/
private noncomputable def counterexampleTwoTangentEquiv :
    ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ :=
  Complex.orthonormalBasisOneI.repr.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
      (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr.symm

/-- The reciprocal complex chart on the sphere. Its origin is the north pole and, away from
the origin, its finite coordinate is `100 / star w`.-/
private noncomputable def counterexampleTwoReciprocalSphereChart
    (w : ℂ) : sphere (0 : ℝ³) 1 :=
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : ℝ³), by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent := Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  (stereographic' 2 (-counterexampleNorthPole)).symm (Uneg u)

/-- The first anti-holomorphic derivative, in the normalization for which the repository's
`traceFreeHessian` is four times its second iterate.-/
private noncomputable def complexBarDeriv (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  ((fderiv ℝ u w 1 : ℂ) + (fderiv ℝ u w Complex.I : ℂ) * Complex.I) / 2

/-- The trace-free spherical Hessian in a stereographic chart whose metric denominator is
`‖w‖² + a`. Its vanishing is the coordinate form of the umbilic equation.-/
private noncomputable def sphericalTraceFreeHessian (a : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  traceFreeHessian u w + 8 * w / (‖w‖ ^ 2 + a) * complexBarDeriv u w

/-- The Euclidean chart Laplacian, encoded using the same second Fréchet derivative as the
trace-free Hessian.-/
private noncomputable def chartLaplacian (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  let H := fderiv ℝ (fun z ↦ fderiv ℝ u z) w
  H 1 1 + H Complex.I Complex.I

/- The product-rule part of the radius computation is kept separate from the subsequent
coordinate algebra.  Apart from making the two mathematical steps explicit, this prevents
the elaborator from retaining all of the smoothness witnesses while normalizing the final
complex expression. -/

end CaratheodoryLoewnerCounterexample

end CounterexampleGlobalSection

/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample.lean` -/

section CounterexampleMainSection

/-!
# The announced smooth counterexamples to the Carathéodory and Loewner conjectures

This module collects the formalization of the explicit counterexample family announced by Levent
Alpöge on 19 August 2026; the announcement credits John-Paul Smith and Claude with checking the
construction. The accompanying file `CaratheodoryLoewnerCounterexample.md` gives the
formalization-oriented informal proof.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open scoped ContDiff EuclideanGeometry Manifold

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture LoewnerConjecture

end CaratheodoryLoewnerCounterexample

end CounterexampleMainSection

open scoped ContDiff

namespace LoewnerConjecture

end LoewnerConjecture

namespace CaratheodoryConjecture

end CaratheodoryConjecture
