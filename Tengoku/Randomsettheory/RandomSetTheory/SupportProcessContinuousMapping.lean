/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.FiniteDirectionalCLT
import Tengoku.Randomsettheory.RandomSetTheory.SupportProcessModulus
import Tengoku.Seed.Topology.ContinuousMap.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous-mapping consequences for random-set support processes

This file isolates the consequences of the continuous mapping theorem that
are available once weak convergence of a support process is known.

* convergence in law in a normed space implies convergence of its norm;
* for continuous paths on a compact space this is convergence of the uniform
  norm;
* the uniform norm of the (possibly scaled) difference of two support
  functions is the support Hausdorff gap, hence Hausdorff distance for
  compact nonempty convex sets;
* the joint finite-direction CLT implies convergence of the maximum absolute
  error over those directions.

The functional statements deliberately assume convergence in law of the
whole continuous process.  They prove neither tightness nor a Donsker theorem.
-/

open Real Set Metric MeasureTheory ProbabilityTheory Filter WithLp
open scoped BigOperators InnerProductSpace ProbabilityTheory Topology

noncomputable section

namespace MeasureTheory

/-- Continuous-mapping transfer from a normed-space-valued weak limit to
the norm of the process.
@isnad1 id=tendstoi.1h11v.s7.3edf35c51cf2 from=translated src=- shape=2e120374 vocab=18f2f1a4
-/
theorem TendstoInDistribution.norm_comp
    {I F Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    {X : (i : I) → Omega i → F} {Z : Omega' → F} {l : Filter I}
    (h : TendstoInDistribution X l Z mu mu') :
    TendstoInDistribution
      (fun i => (fun x : F => ‖x‖) ∘ X i) l
      ((fun x : F => ‖x‖) ∘ Z) mu mu' :=
  h.continuous_comp continuous_norm

/-- For continuous real processes on a compact index space, convergence in
law of the process implies convergence in law of its uniform norm.  This is
only a continuous-mapping theorem: it assumes, rather than proves, process
convergence.
@isnad1 id=tendstoi.1h11v.s8.3a6af62f6b1f from=translated src=- shape=f2897bbb vocab=8f06ad5d
-/
theorem TendstoInDistribution.continuousMap_supNorm
    {I T Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
    {X : (i : I) → Omega i → C(T, ℝ)} {Z : Omega' → C(T, ℝ)}
    {l : Filter I} (h : TendstoInDistribution X l Z mu mu') :
    TendstoInDistribution
      (fun i => (fun f : C(T, ℝ) => ‖f‖) ∘ X i) l
      ((fun f : C(T, ℝ) => ‖f‖) ∘ Z) mu mu' :=
  h.norm_comp

end MeasureTheory

namespace RandomSetTheory

variable {kappa : Type*} [Fintype kappa]

/-- Maximum absolute coordinate of a finite Euclidean vector.  It is written
as the sup norm of the underlying function, so the empty index type gives
zero without a separate convention.-/
def finiteMaxAbs (x : EuclideanSpace ℝ kappa) : ℝ :=
  ‖x.ofLp‖

/--
@isnad1 id=eq.0h2v.s5.303e3d26da77 from=translated src=- shape=e0887e03 vocab=b11141e7
-/
@[simp]
theorem finiteMaxAbs_toLp (f : kappa → ℝ) :
    finiteMaxAbs (toLp 2 f) = ‖f‖ := rfl

/-- `finiteMaxAbs` is continuous for the Euclidean topology.
@isnad1 id=continuo.0h1v.s5.de136f25ec54 from=translated src=- shape=61250228 vocab=332a60df
-/
theorem continuous_finiteMaxAbs :
    Continuous (finiteMaxAbs : EuclideanSpace ℝ kappa → ℝ) := by
  exact continuous_norm.comp (PiLp.continuous_ofLp 2 (fun _ : kappa => ℝ))

/-- Continuous-mapping transfer from a finite-dimensional weak limit to the
maximum absolute coordinate.
@isnad1 id=tendstoi.1h11v.s7.cfe3e4eb4309 from=translated src=- shape=8daf0074 vocab=63df20ce
-/
theorem TendstoInDistribution.finiteMaxAbs
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    {X : (i : I) → Omega i → EuclideanSpace ℝ kappa}
    {Z : Omega' → EuclideanSpace ℝ kappa} {l : Filter I}
    (h : TendstoInDistribution X l Z mu mu') :
    TendstoInDistribution
      (fun i => finiteMaxAbs ∘ X i) l
      (finiteMaxAbs ∘ Z) mu mu' :=
  h.continuous_comp continuous_finiteMaxAbs

section SupportContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Difference of two compact-set support functions on the closed unit ball,
bundled as a continuous real function.-/
def supportDifferenceContinuousMap
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    C(Metric.closedBall (0 : E) 1, ℝ) where
  toFun u := supportFunction K u - supportFunction L u
  continuous_toFun := by
    obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
    obtain ⟨RL, hRL⟩ := hL.isBounded.exists_norm_le
    have hRK0 : 0 ≤ RK := by
      obtain ⟨x, hx⟩ := hKne
      exact (norm_nonneg x).trans (hRK x hx)
    have hRL0 : 0 ≤ RL := by
      obtain ⟨y, hy⟩ := hLne
      exact (norm_nonneg y).trans (hRL y hy)
    let C : NNReal := ⟨RK + RL, add_nonneg hRK0 hRL0⟩
    have hC : (C : ℝ) = RK + RL := rfl
    have hlip : LipschitzWith C
        (fun u : E => supportFunction K u - supportFunction L u) := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [hC]
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
        (abs_supportFunctionDifference_sub_le
          hK hL hKne hLne hRK hRL u v)
    exact hlip.continuous.comp continuous_subtype_val

/--
@isnad1 id=eq.4h4v.s8.0e2fed3a3f9a from=translated src=- shape=f99eb735 vocab=8edfe149
-/
@[simp]
theorem supportDifferenceContinuousMap_apply
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (u : Metric.closedBall (0 : E) 1) :
    supportDifferenceContinuousMap K L hK hL hKne hLne u =
      supportFunction K u - supportFunction L u := rfl

/-- For compact nonempty convex sets in finite dimension, the uniform norm
of the support-difference path is exactly Hausdorff distance.
@isnad1 id=eq.6h3v.s8.f30cdc6cf870 from=translated src=- shape=5fe6258d vocab=46d5e4ba
-/
theorem norm_supportDifferenceContinuousMap_eq_hausdorffDist
    [FiniteDimensional ℝ E]
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    ‖supportDifferenceContinuousMap K L hK hL hKne hLne‖ =
      hausdorffDist K L := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ hausdorffDist_nonneg]
    intro u
    simp only [supportDifferenceContinuousMap_apply, Real.norm_eq_abs]
    have hu : ‖(u : E)‖ ≤ 1 := by
      have hu' := u.property
      change dist (u : E) 0 ≤ 1 at hu'
      simpa only [dist_zero_right] using hu'
    calc
      |supportFunction K u - supportFunction L u| ≤
          ‖(u : E)‖ * hausdorffDist K L :=
        abs_supportFunction_sub_le_hausdorffDist hK hL hKne hLne u
      _ ≤ 1 * hausdorffDist K L :=
        mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
      _ = hausdorffDist K L := one_mul _
  · apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
      hK hL hKne hLne hKconv hLconv (norm_nonneg _)
    intro u hu
    let us : Metric.closedBall (0 : E) 1 :=
      ⟨u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu⟩
    have hnorm := ContinuousMap.norm_coe_le_norm
      (supportDifferenceContinuousMap K L hK hL hKne hLne) us
    simpa only [supportDifferenceContinuousMap_apply, Real.norm_eq_abs] using hnorm

/-- The support gap is the norm of the bundled support-difference path.
@isnad1 id=eq.6h3v.s8.c5fee1ee35f7 from=translated src=- shape=5fe6258d vocab=4c83f983
-/
theorem norm_supportDifferenceContinuousMap_eq_supportHausdorffGap
    [FiniteDimensional ℝ E]
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    ‖supportDifferenceContinuousMap K L hK hL hKne hLne‖ =
      supportHausdorffGap K L := by
  rw [supportHausdorffGap_eq_hausdorffDist
    hK hL hKne hLne hKconv hLconv]
  exact norm_supportDifferenceContinuousMap_eq_hausdorffDist
    K L hK hL hKne hLne hKconv hLconv

/-- A support-difference path multiplied by a deterministic scale.-/
def scaledSupportDifferenceContinuousMap
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    C(Metric.closedBall (0 : E) 1, ℝ) :=
  c • supportDifferenceContinuousMap K L hK hL hKne hLne

/--
@isnad1 id=eq.4h5v.s8.affe0e5c3a54 from=translated src=- shape=5cc85ae4 vocab=e832b3e7
-/
@[simp]
theorem scaledSupportDifferenceContinuousMap_apply
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (u : Metric.closedBall (0 : E) 1) :
    scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne u =
      c * (supportFunction K u - supportFunction L u) := by
  simp [scaledSupportDifferenceContinuousMap]

/-- Uniform norm of a scaled support-difference path, expressed as support
gap.
@isnad1 id=eq.6h4v.s8.dd0a309ce313 from=translated src=- shape=968eaef0 vocab=96f3dd59
-/
theorem norm_scaledSupportDifferenceContinuousMap_eq_supportHausdorffGap
    [FiniteDimensional ℝ E]
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    ‖scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne‖ =
      |c| * supportHausdorffGap K L := by
  rw [scaledSupportDifferenceContinuousMap, norm_smul, Real.norm_eq_abs,
    norm_supportDifferenceContinuousMap_eq_supportHausdorffGap
      K L hK hL hKne hLne hKconv hLconv]

/-- Uniform norm of a scaled support-difference path, expressed as Hausdorff
distance.
@isnad1 id=eq.6h4v.s8.acddd431901a from=translated src=- shape=968eaef0 vocab=7bbce64d
-/
theorem norm_scaledSupportDifferenceContinuousMap_eq_hausdorffDist
    [FiniteDimensional ℝ E]
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) :
    ‖scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne‖ =
      |c| * hausdorffDist K L := by
  rw [scaledSupportDifferenceContinuousMap, norm_smul, Real.norm_eq_abs,
    norm_supportDifferenceContinuousMap_eq_hausdorffDist
      K L hK hL hKne hLne hKconv hLconv]

/-- Functional continuous-mapping bridge for the support gap.  The premise
is convergence in law of the entire continuous support process; no process
CLT or tightness claim is made here.
@isnad1 id=tendstoi.7h13v.s10.502c94b1951c from=translated src=- shape=c9f2b814 vocab=373dbd79
-/
theorem tendstoInDistribution_absScale_mul_supportHausdorffGap_of_process
    [FiniteDimensional ℝ E]
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Omega' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hKcompact : ∀ i omega, IsCompact (K i omega))
    (hKne : ∀ i omega, (K i omega).Nonempty)
    (hKconv : ∀ i omega, Convex ℝ (K i omega))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i omega => scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne)
      l Z mu mu') :
    TendstoInDistribution
      (fun i omega => |c i| * supportHausdorffGap (K i omega) L)
      l (fun omega => ‖Z omega‖) mu mu' := by
  have hnorm := hprocess.continuousMap_supNorm
  apply hnorm.congr
  · intro i
    filter_upwards [] with omega
    change ‖scaledSupportDifferenceContinuousMap
      (c i) (K i omega) L (hKcompact i omega) hLcompact
        (hKne i omega) hLne‖ =
      |c i| * supportHausdorffGap (K i omega) L
    exact norm_scaledSupportDifferenceContinuousMap_eq_supportHausdorffGap
      (c i) (K i omega) L (hKcompact i omega) hLcompact
        (hKne i omega) hLne (hKconv i omega) hLconv
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Functional continuous-mapping bridge for Hausdorff distance.  It turns
a functional weak-convergence theorem, if supplied separately, into the
corresponding weak limit of the scaled Hausdorff error.
@isnad1 id=tendstoi.7h13v.s10.c9f5e23d5dbc from=translated src=- shape=c9f2b814 vocab=be46073d
-/
theorem tendstoInDistribution_absScale_mul_hausdorffDist_of_process
    [FiniteDimensional ℝ E]
    {I Omega' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Omega'} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Omega' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hKcompact : ∀ i omega, IsCompact (K i omega))
    (hKne : ∀ i omega, (K i omega).Nonempty)
    (hKconv : ∀ i omega, Convex ℝ (K i omega))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    {l : Filter I}
    (hprocess : TendstoInDistribution
      (fun i omega => scaledSupportDifferenceContinuousMap
        (c i) (K i omega) L (hKcompact i omega) hLcompact
          (hKne i omega) hLne)
      l Z mu mu') :
    TendstoInDistribution
      (fun i omega => |c i| * hausdorffDist (K i omega) L)
      l (fun omega => ‖Z omega‖) mu mu' := by
  have hnorm := hprocess.continuousMap_supNorm
  apply hnorm.congr
  · intro i
    filter_upwards [] with omega
    change ‖scaledSupportDifferenceContinuousMap
      (c i) (K i omega) L (hKcompact i omega) hLcompact
        (hKne i omega) hLne‖ = |c i| * hausdorffDist (K i omega) L
    exact norm_scaledSupportDifferenceContinuousMap_eq_hausdorffDist
      (c i) (K i omega) L (hKcompact i omega) hLcompact
        (hKne i omega) hLne (hKconv i omega) hLconv
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end SupportContinuousMap

section FiniteDirectionalMaximum

variable {Omega : Type*} [MeasurableSpace Omega]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The joint finite-direction support CLT implies convergence of the
largest absolute directional error on that finite family.
@isnad1 id=tendstoi.7h10v.s9.522dcb6d2909 from=translated src=- shape=71076b41 vocab=f364eb58
-/
theorem tendstoInDistribution_finiteMaxAbs_support_minkowskiAverage
    [DecidableEq kappa]
    {Omega' : Type*} [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (Y : Omega' → EuclideanSpace ℝ kappa)
    (hScompact : ∀ i omega, IsCompact (S i omega))
    (hSne : ∀ i omega, (S i omega).Nonempty)
    (hY : HasLaw Y
      (multivariateGaussian 0
        (finiteDirectionalSupportCovariance S L u mu)) mu')
    (hL2 : MemLp (finiteDirectionalSupportDeviation S L u 0) 2 mu)
    (hindep : iIndepFun (finiteDirectionalSupportDeviation S L u) mu)
    (hident : ∀ i, IdentDistrib
      (finiteDirectionalSupportDeviation S L u i)
      (finiteDirectionalSupportDeviation S L u 0) mu mu)
    (hcenter : ∀ j, mu[directionalSupportDeviation S L (u j) 0] = 0) :
    TendstoInDistribution
      (fun (n : ℕ) omega => ‖fun j =>
        √((n + 1 : ℕ) : ℝ) *
          (supportFunction
              (minkowskiAverage (Finset.range (n + 1))
                (fun i => S i omega)) (u j) -
            supportFunction L (u j))‖)
      atTop (fun omega => finiteMaxAbs (Y omega)) (fun _ => mu) mu' := by
  have hclt := tendstoInDistribution_finiteDirectionalSupport_minkowskiAverage
    S L u Y hScompact hSne hY hL2 hindep hident hcenter
  have hmax := RandomSetTheory.TendstoInDistribution.finiteMaxAbs hclt
  apply hmax.congr
  · intro n
    filter_upwards [] with omega
    change finiteMaxAbs (toLp 2 (fun j =>
      √((n + 1 : ℕ) : ℝ) *
        (supportFunction
            (minkowskiAverage (Finset.range (n + 1))
              (fun i => S i omega)) (u j) -
          supportFunction L (u j)))) = _
    exact finiteMaxAbs_toLp _
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end FiniteDirectionalMaximum

end RandomSetTheory
