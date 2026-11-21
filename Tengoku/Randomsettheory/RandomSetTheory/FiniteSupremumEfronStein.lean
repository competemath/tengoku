/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumMartingaleBernstein
import Tengoku.Seed.Probability.Moments.Variance
import Tengoku.Seed.Probability.Kernel.CondDistrib

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A ghost-coordinate Efron--Stein bound for finite suprema

This file formalizes the product/ghost calculation which is needed before a
finite empirical supremum can be fed to a variance-sensitive Doob-martingale
inequality.

Fix all observations except one.  Their contribution to every coordinate of
the process is an arbitrary deterministic function `r`.  If the remaining
observation contributes `X z t`, with scalar envelope `A z`, then replacing
`z` by an independent ghost value `z'` changes the finite supremum by at most
`A z + A z'`.  Squaring and integrating the two copies proves

`Var_z (sup_t (r t + X z t)) <= 2 * E[A^2]`.

This is a genuine coordinatewise Efron--Stein estimate: `r` is completely
arbitrary and can therefore contain both the revealed past and an integral
over the unrevealed future.  In particular, the bound does not contain the
cardinality of the finite class.

It is not, by itself, Marchina's maximal Fuk--Nagaev theorem.  The file does
prove the conditional-expectation formula needed to transport the pointwise
ghost estimate through one independent revealed-past/current-coordinate
split.  Ordinary Bernstein/Freedman concentration nevertheless retains a
linear bounded-increment term; Marchina removes the corresponding logarithmic
loss by a stronger CVaR/quantile comparison, which is not proved here.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-! ## Conditional distributions of an independent ghost coordinate -/

/-- The regular conditional law of `Y` given an independent variable `X` is
the constant kernel with value `law(Y)`.  This small product identity is the
measure-theoretic part of the ghost-coordinate bridge which was missing from
the finite-supremum martingale API.
@isnad1 id=eventual.3h6v.s7.85303df5d682 from=translated src=- shape=fdfc4058 vocab=978a3ee8
-/
theorem IndepFun.condDistrib_ae_eq_const
    {Omega Beta Gamma : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [MeasurableSpace Gamma] [StandardBorelSpace Gamma] [Nonempty Gamma]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega -> Beta} {Y : Omega -> Gamma}
    (hXY : IndepFun X Y mu)
    (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu) :
    condDistrib Y X mu =ᵐ[mu.map X] Kernel.const Beta (mu.map Y) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd X hY
  rw [Measure.compProd_const]
  exact hXY.map_prod_eq_prod_map_map hX hY

/-- Conditional expectation formula under independence: after conditioning
on `X`, integrating a function of `(X,Y)` amounts to keeping `X` fixed and
integrating only the independent `Y` coordinate against its ordinary law.
@isnad1 id=eventual.5h7v.s7.098dd220b573 from=translated src=- shape=77a68608 vocab=17052d99
-/
theorem IndepFun.condExp_prod_ae_eq_integral_map
    {Omega Beta Gamma : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [MeasurableSpace Gamma] [StandardBorelSpace Gamma] [Nonempty Gamma]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega -> Beta} {Y : Omega -> Gamma}
    (hXY : IndepFun X Y mu)
    (hX : Measurable X) (hY : Measurable Y)
    (f : Beta × Gamma -> Real) (hf : StronglyMeasurable f)
    (hfint : Integrable (fun omega => f (X omega, Y omega)) mu) :
    mu[fun omega => f (X omega, Y omega) |
        MeasurableSpace.comap X inferInstance] =ᵐ[mu]
      fun omega => integral (mu.map Y) (fun y => f (X omega, y)) := by
  have hbase := condExp_prod_ae_eq_integral_condDistrib
    hX hY.aemeasurable hf hfint
  have hkernelMap := hXY.condDistrib_ae_eq_const
    hX.aemeasurable hY.aemeasurable
  have hkernel : ∀ᵐ omega ∂mu,
      condDistrib Y X mu (X omega) = mu.map Y := by
    have hcomp := ae_of_ae_map hX.aemeasurable hkernelMap
    filter_upwards [hcomp] with omega homega
    simpa only [Kernel.const_apply] using homega
  filter_upwards [hbase, hkernel] with omega hbaseOmega hkernelOmega
  rw [hbaseOmega, hkernelOmega]

variable {Z T : Type*} [MeasurableSpace Z]
  {nu : Measure Z}

/-- The finite supremum after freezing every observation except one.-/
def finiteReplaceOneSupremum (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (z : Z) : Real :=
  s.sup' hs (fun t => r t + X z t)

/-- One-coordinate supremum centred with respect to the law of the free
coordinate.  The first component represents an arbitrary revealed past.-/
def finiteReplaceOneCenteredSupremum
    {Beta : Type*} [MeasurableSpace Beta]
    (nu : Measure Z) (s : Finset T) (hs : s.Nonempty)
    (r : Beta -> T -> Real) (X : Z -> T -> Real)
    (bz : Beta × Z) : Real :=
  finiteReplaceOneSupremum s hs (r bz.1) X bz.2 -
    integral nu (finiteReplaceOneSupremum s hs (r bz.1) X)

/-- Measurability of the one-coordinate finite supremum.
@isnad1 id=measurab.2h5v.s5.8e094b17923f from=translated src=- shape=6243b433 vocab=a3b263ab
-/
theorem measurable_finiteReplaceOneSupremum
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t)) :
    Measurable (finiteReplaceOneSupremum s hs r X) := by
  exact measurable_finiteProcessSupremum s hs
    (fun t z => r t + X z t)
    (fun t ht => measurable_const.add (hX t ht))

/-- Joint strong measurability of the centred fibre.  This supplies the
measurability side condition needed by the conditional-distribution formula.
@isnad1 id=strongly.3h7v.s6.d7fc3c7c7eb6 from=translated src=- shape=589bde59 vocab=e059ba78
-/
theorem stronglyMeasurable_finiteReplaceOneCenteredSupremum
    {Beta : Type*} [MeasurableSpace Beta]
    [IsFiniteMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : Beta -> T -> Real) (X : Z -> T -> Real)
    (hr : forall t, t ∈ s -> Measurable (fun b => r b t))
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t)) :
    StronglyMeasurable
      (finiteReplaceOneCenteredSupremum nu s hs r X) := by
  let G : Beta × Z -> Real := fun bz =>
    finiteReplaceOneSupremum s hs (r bz.1) X bz.2
  have hG : Measurable G := by
    apply measurable_finiteProcessSupremum s hs
    intro t ht
    exact ((hr t ht).comp measurable_fst).add
      ((hX t ht).comp measurable_snd)
  have hmean : StronglyMeasurable
      (fun b => integral nu (fun z => G (b, z))) :=
    hG.stronglyMeasurable.integral_prod_right'
  exact hG.stronglyMeasurable.sub
    (hmean.comp_measurable measurable_fst)

/-- The centred free-coordinate supremum is conditionally centred given an
independent revealed past.
@isnad1 id=eventual.8h10v.s8.de9841ffb1b0 from=translated src=- shape=fdb01984 vocab=91f43080
-/
theorem condExp_finiteReplaceOneCenteredSupremum_ae_eq_zero
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega -> Beta) (Y : Omega -> Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (s : Finset T) (hs : s.Nonempty)
    (r : Beta -> T -> Real) (X : Z -> T -> Real)
    (hr : forall t, t ∈ s -> Measurable (fun b => r b t))
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hFiberInt : forall b, Integrable
      (finiteReplaceOneSupremum s hs (r b) X) (mu.map Y))
    (hDint : Integrable (fun omega =>
      finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X
        (P omega, Y omega)) mu) :
    mu[fun omega =>
        finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X
          (P omega, Y omega) |
        MeasurableSpace.comap P inferInstance] =ᵐ[mu] 0 := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hstrong := stronglyMeasurable_finiteReplaceOneCenteredSupremum
    (nu := mu.map Y) s hs r X hr hX
  have hbase := hPY.condExp_prod_ae_eq_integral_map hP hY
    (finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X)
    hstrong hDint
  filter_upwards [hbase] with omega hbaseOmega
  rw [hbaseOmega]
  unfold finiteReplaceOneCenteredSupremum
  simp only [Pi.zero_apply]
  rw [integral_sub (hFiberInt (P omega)) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_self]

omit [MeasurableSpace Z] in
/-- Replacing the free coordinate changes the supremum by at most the sum of
the old and ghost envelopes.
@isnad1 id=le.2h8v.s6.d16e47ca2b39 from=translated src=- shape=2e3584ef vocab=ba6f9492
-/
theorem abs_finiteReplaceOneSupremum_sub_le_add_envelopes
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (z z' : Z) :
    |finiteReplaceOneSupremum s hs r X z -
        finiteReplaceOneSupremum s hs r X z'| <= A z + A z' := by
  exact abs_finset_sup'_sum_replace_one_le_add_envelopes
    s hs r (X z) (X z') (hdom z) (hdom z')

omit [MeasurableSpace Z] in
/-- Squared replace-one form.  The factor `2` is the elementary inequality
`(a+b)^2 <= 2a^2+2b^2`.
@isnad1 id=le.3h8v.s7.95215bd3bd18 from=translated src=- shape=3ac048f0 vocab=72f78c3a
-/
theorem sq_finiteReplaceOneSupremum_sub_le_two_mul_add
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (z z' : Z) :
    (finiteReplaceOneSupremum s hs r X z -
        finiteReplaceOneSupremum s hs r X z') ^ 2 <=
      2 * A z ^ 2 + 2 * A z' ^ 2 := by
  have hreplace := abs_finiteReplaceOneSupremum_sub_le_add_envelopes
    s hs r X A hdom z z'
  have hsum : 0 <= A z + A z' := add_nonneg (hA z) (hA z')
  have hsq :
      (finiteReplaceOneSupremum s hs r X z -
          finiteReplaceOneSupremum s hs r X z') ^ 2 <=
        (A z + A z') ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg hsum] using hreplace
  calc
    (finiteReplaceOneSupremum s hs r X z -
        finiteReplaceOneSupremum s hs r X z') ^ 2 <=
        (A z + A z') ^ 2 := hsq
    _ <= 2 * A z ^ 2 + 2 * A z' ^ 2 := by
      nlinarith [sq_nonneg (A z - A z')]

/-- Every one-coordinate supremum lies in `L2` when its coordinate envelope
does.  The frozen contribution `r` costs only a finite deterministic
constant.
@isnad1 id=memlp.5h7v.s7.35c02e01c739 from=translated src=- shape=088756d6 vocab=b05fcd98
-/
theorem memLp_finiteReplaceOneSupremum_two
    [IsFiniteMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu) :
    MemLp (finiteReplaceOneSupremum s hs r X) 2 nu := by
  let C : Real := s.sup' hs (fun t => |r t|)
  have hC : 0 <= C := by
    let t0 : T := hs.choose
    have ht0 : t0 ∈ s := hs.choose_spec
    exact (abs_nonneg (r t0)).trans
      (Finset.le_sup' (fun t => |r t|) ht0)
  have henv : MemLp (fun z => C + A z) 2 nu :=
    (memLp_const C).add hA2
  apply henv.mono'
    (measurable_finiteReplaceOneSupremum s hs r X hX).aestronglyMeasurable
  filter_upwards [] with z
  have hbound : |finiteReplaceOneSupremum s hs r X z| <= C + A z := by
    have hraw := abs_finiteProcessSupremum_le s hs
      (fun t z => r t + X z t) (fun z => C + A z) (fun z' t ht => by
        have henvnonneg' : 0 <= C + A z' := add_nonneg hC (hA z')
        rw [abs_of_nonneg henvnonneg']
        calc
          |r t + X z' t| <= |r t| + |X z' t| := abs_add_le _ _
          _ <= C + A z' := add_le_add
            (Finset.le_sup' (fun u => |r u|) ht) (hdom z' t ht)) z
    change |finiteProcessSupremum s hs (fun t z => r t + X z t) z| <=
      C + A z
    exact hraw.trans_eq (abs_of_nonneg (add_nonneg hC (hA z)))
  have henvnonneg : 0 <= C + A z := add_nonneg hC (hA z)
  simpa only [Real.norm_eq_abs, abs_of_nonneg henvnonneg] using hbound

/-- Exact independent-ghost identity: the mean squared difference of two
copies is twice the variance.
@isnad1 id=eq.1h3v.s7.0f18945a01dc from=translated src=- shape=4d75f5c7 vocab=bed30455
-/
theorem integral_sq_sub_ghost_eq_two_mul_variance
    [IsProbabilityMeasure nu]
    (F : Z -> Real) (hF : MemLp F 2 nu) :
    integral (nu.prod nu) (fun zz : Z × Z => (F zz.1 - F zz.2) ^ 2) =
      2 * variance F nu := by
  let D : Z × Z -> Real := fun zz => F zz.1 - F zz.2
  have hD : MemLp D 2 (nu.prod nu) := by
    exact (hF.comp_fst nu).sub (hF.comp_snd nu)
  have hDmean : integral (nu.prod nu) D = 0 := by
    have hDint : Integrable D (nu.prod nu) := hD.integrable (by norm_num)
    rw [integral_prod D hDint]
    have hFint : Integrable F nu := hF.integrable (by norm_num)
    have hinner : (fun x => integral nu (fun y => D (x, y))) =
        fun x => F x - integral nu F := by
      funext x
      simp only [D]
      rw [integral_sub (integrable_const _) hFint]
      simp only [integral_const, probReal_univ, one_smul]
    rw [hinner, integral_sub hFint (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have hvarD : variance D (nu.prod nu) = 2 * variance F nu := by
    have hbase := variance_add_prod (μ := nu) (ν := nu) hF hF.neg
    calc
      variance D (nu.prod nu) =
          variance (fun p : Z × Z => F p.1 + (-F) p.2) (nu.prod nu) := by
            rfl
      _ = variance F nu + variance (-F) nu := hbase
      _ = 2 * variance F nu := by rw [variance_neg]; ring
  rw [← hvarD, variance_of_integral_eq_zero hD.aemeasurable hDmean]

/-- Abstract one-coordinate Efron--Stein estimate.  The finite-supremum
structure is used only to prove the replace-one inequality; once a scalar
fibre `F` satisfies that inequality, its variance obeys the same bound.

This formulation is important for Doob martingales: after integrating out
the unrevealed future, the current fibre need no longer be literally a
supremum, but its replace-one modulus is unchanged.
@isnad1 id=le.4h4v.s7.a494ebbc6eb9 from=translated src=- shape=9128089d vocab=f4e8a3bd
-/
theorem variance_le_two_mul_integral_sq_of_abs_sub_le_add_envelopes
    [IsProbabilityMeasure nu]
    (F A : Z -> Real) (hF2 : MemLp F 2 nu) (hA2 : MemLp A 2 nu)
    (hA : forall z, 0 <= A z)
    (hreplace : forall z z', |F z - F z'| <= A z + A z') :
    variance F nu <= 2 * integral nu (fun z => A z ^ 2) := by
  have hghostInt : Integrable
      (fun zz : Z × Z => (F zz.1 - F zz.2) ^ 2) (nu.prod nu) :=
    ((hF2.comp_fst nu).sub (hF2.comp_snd nu)).integrable_sq
  have hAint : Integrable (fun z => A z ^ 2) nu := hA2.integrable_sq
  have hpoint : forall z z',
      (F z - F z') ^ 2 <= 2 * A z ^ 2 + 2 * A z' ^ 2 := by
    intro z z'
    have hsum : 0 <= A z + A z' := add_nonneg (hA z) (hA z')
    have hsq : (F z - F z') ^ 2 <= (A z + A z') ^ 2 := by
      rw [sq_le_sq]
      simpa only [abs_of_nonneg hsum] using hreplace z z'
    calc
      (F z - F z') ^ 2 <= (A z + A z') ^ 2 := hsq
      _ <= 2 * A z ^ 2 + 2 * A z' ^ 2 := by
        nlinarith [sq_nonneg (A z - A z')]
  have hboundInt :
      integral (nu.prod nu) (fun zz : Z × Z => (F zz.1 - F zz.2) ^ 2) <=
        integral (nu.prod nu) (fun zz : Z × Z =>
          2 * A zz.1 ^ 2 + 2 * A zz.2 ^ 2) := by
    apply integral_mono hghostInt
    · exact ((hAint.comp_fst nu).const_mul 2).add
        ((hAint.comp_snd nu).const_mul 2)
    · exact fun zz => hpoint zz.1 zz.2
  have hrhs :
      integral (nu.prod nu) (fun zz : Z × Z =>
          2 * A zz.1 ^ 2 + 2 * A zz.2 ^ 2) =
        4 * integral nu (fun z => A z ^ 2) := by
    rw [integral_add
      ((hAint.comp_fst nu).const_mul 2)
      ((hAint.comp_snd nu).const_mul 2),
      integral_const_mul, integral_const_mul]
    have hfst : integral (nu.prod nu) (fun zz : Z × Z => A zz.1 ^ 2) =
        integral nu (fun z => A z ^ 2) := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_fst (μ := nu) (ν := nu) (fun z => A z ^ 2))
    have hsnd : integral (nu.prod nu) (fun zz : Z × Z => A zz.2 ^ 2) =
        integral nu (fun z => A z ^ 2) := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_snd (μ := nu) (ν := nu) (fun z => A z ^ 2))
    rw [hfst, hsnd]
    ring
  have hghost := integral_sq_sub_ghost_eq_two_mul_variance F hF2
  rw [hghost, hrhs] at hboundInt
  linarith

/-- Abstract conditional Efron--Stein bridge for a revealed past and one
independent current coordinate.  It applies in particular when `G b z` is a
future-integrated empirical supremum.
@isnad1 id=eventual.9h8v.s9.9eb5144fd3f5 from=translated src=- shape=010a055a vocab=3cee3a2e
-/
theorem condExp_sq_centeredGhostFiber_le
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega -> Beta) (Y : Omega -> Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (G : Beta -> Z -> Real) (A : Z -> Real)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hG2 : forall b, MemLp (G b) 2 (mu.map Y))
    (hA2 : MemLp A 2 (mu.map Y)) (hA : forall z, 0 <= A z)
    (hreplace : forall b z z', |G b z - G b z'| <= A z + A z')
    (hD2 : MemLp (fun omega =>
      G (P omega) (Y omega) - integral (mu.map Y) (G (P omega))) 2 mu) :
    ∀ᵐ omega ∂mu,
      mu[fun omega' =>
          (G (P omega') (Y omega') -
            integral (mu.map Y) (G (P omega'))) ^ 2 |
          MeasurableSpace.comap P inferInstance] omega <=
        2 * integral (mu.map Y) (fun z => A z ^ 2) := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmean : StronglyMeasurable
      (fun b => integral (mu.map Y) (G b)) :=
    hG.integral_prod_right
  have hcentered : StronglyMeasurable (fun bz : Beta × Z =>
      G bz.1 bz.2 - integral (mu.map Y) (G bz.1)) :=
    hG.sub (hmean.comp_measurable measurable_fst)
  have hbase := hPY.condExp_prod_ae_eq_integral_map hP hY
    (fun bz : Beta × Z =>
      (G bz.1 bz.2 - integral (mu.map Y) (G bz.1)) ^ 2)
    (hcentered.pow 2) hD2.integrable_sq
  filter_upwards [hbase] with omega hbaseOmega
  rw [hbaseOmega]
  have hvar := variance_le_two_mul_integral_sq_of_abs_sub_le_add_envelopes
    (nu := mu.map Y) (G (P omega)) A (hG2 (P omega)) hA2 hA
      (hreplace (P omega))
  rw [variance_eq_integral (hG2 (P omega)).aemeasurable] at hvar
  exact hvar

/-- Product/ghost Efron--Stein bound for a finite supremum with one free
coordinate.  It is uniform in the frozen process `r` and in the cardinality
of the finite class.
@isnad1 id=le.5h7v.s7.6b21869a8690 from=translated src=- shape=33acd561 vocab=d26ea43a
-/
theorem variance_finiteReplaceOneSupremum_le_two_mul_integral_sq
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu) :
    variance (finiteReplaceOneSupremum s hs r X) nu <=
      2 * integral nu (fun z => A z ^ 2) := by
  let F : Z -> Real := finiteReplaceOneSupremum s hs r X
  have hF2 : MemLp F 2 nu :=
    memLp_finiteReplaceOneSupremum_two s hs r X A hX hA hdom hA2
  have hghostInt : Integrable
      (fun zz : Z × Z => (F zz.1 - F zz.2) ^ 2) (nu.prod nu) :=
    ((hF2.comp_fst nu).sub (hF2.comp_snd nu)).integrable_sq
  have hAint : Integrable (fun z => A z ^ 2) nu := hA2.integrable_sq
  have hboundInt :
      integral (nu.prod nu) (fun zz : Z × Z => (F zz.1 - F zz.2) ^ 2) <=
        integral (nu.prod nu) (fun zz : Z × Z =>
          2 * A zz.1 ^ 2 + 2 * A zz.2 ^ 2) := by
    apply integral_mono hghostInt
    · exact ((hAint.comp_fst nu).const_mul 2).add
        ((hAint.comp_snd nu).const_mul 2)
    · intro zz
      exact sq_finiteReplaceOneSupremum_sub_le_two_mul_add
        s hs r X A hA hdom zz.1 zz.2
  have hrhs :
      integral (nu.prod nu) (fun zz : Z × Z =>
          2 * A zz.1 ^ 2 + 2 * A zz.2 ^ 2) =
        4 * integral nu (fun z => A z ^ 2) := by
    rw [integral_add
      ((hAint.comp_fst nu).const_mul 2)
      ((hAint.comp_snd nu).const_mul 2)]
    rw [integral_const_mul, integral_const_mul]
    have hfst : integral (nu.prod nu) (fun zz : Z × Z => A zz.1 ^ 2) =
        integral nu (fun z => A z ^ 2) := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_fst (μ := nu) (ν := nu) (fun z => A z ^ 2))
    have hsnd : integral (nu.prod nu) (fun zz : Z × Z => A zz.2 ^ 2) =
        integral nu (fun z => A z ^ 2) := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_snd (μ := nu) (ν := nu) (fun z => A z ^ 2))
    rw [hfst, hsnd]
    ring
  have hghost := integral_sq_sub_ghost_eq_two_mul_variance F hF2
  rw [hghost, hrhs] at hboundInt
  linarith

/-- **Conditional ghost Efron--Stein inequality.**  If the revealed past `P`
and the free coordinate `Y` are independent, the conditional second moment
of the centred replace-one supremum is bounded by twice the ordinary second
moment of the coordinate envelope.

The right-hand side is deterministic and contains no cardinality of `s`.
For an empirical average, applying the scaled replace-one theorem to
`X/n` gives the per-coordinate bound `2*K2^2/n^2`.
@isnad1 id=eventual.10h11v.s8.08dbd1c7c2e5 from=translated src=- shape=9d95ce91 vocab=49b1d090
-/
theorem condExp_sq_finiteReplaceOneCenteredSupremum_le
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega -> Beta) (Y : Omega -> Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (s : Finset T) (hs : s.Nonempty)
    (r : Beta -> T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hr : forall t, t ∈ s -> Measurable (fun b => r b t))
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 (mu.map Y))
    (hD2 : MemLp (fun omega =>
      finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X
        (P omega, Y omega)) 2 mu) :
    ∀ᵐ omega ∂mu,
      mu[fun omega' =>
          finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X
            (P omega', Y omega') ^ 2 |
          MeasurableSpace.comap P inferInstance] omega <=
        2 * integral (mu.map Y) (fun z => A z ^ 2) := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hstrong := stronglyMeasurable_finiteReplaceOneCenteredSupremum
    (nu := mu.map Y) s hs r X hr hX
  have hbase := hPY.condExp_prod_ae_eq_integral_map hP hY
    (fun bz => finiteReplaceOneCenteredSupremum (mu.map Y) s hs r X bz ^ 2)
    (hstrong.pow 2) hD2.integrable_sq
  filter_upwards [hbase] with omega hbaseOmega
  rw [hbaseOmega]
  have hvar := variance_finiteReplaceOneSupremum_le_two_mul_integral_sq
    (nu := mu.map Y) s hs (r (P omega)) X A hX hA hdom hA2
  rw [variance_eq_integral
    (measurable_finiteReplaceOneSupremum
      s hs (r (P omega)) X hX).aemeasurable] at hvar
  simpa only [finiteReplaceOneCenteredSupremum] using hvar

/-- Scaled conditional Efron--Stein bound.  With `c = 1/n` and
`E[A^2] <= K2^2`, this is the deterministic conditional-variance input
`2*K2^2/n^2` for one Doob increment.
@isnad1 id=eventual.10h12v.s9.098f78ac4bcd from=translated src=- shape=62adf9b7 vocab=49b1d090
-/
theorem condExp_sq_finiteReplaceOneCenteredSupremum_const_mul_le
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega -> Beta) (Y : Omega -> Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (s : Finset T) (hs : s.Nonempty)
    (r : Beta -> T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (c : Real)
    (hr : forall t, t ∈ s -> Measurable (fun b => r b t))
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 (mu.map Y))
    (hD2 : MemLp (fun omega =>
      finiteReplaceOneCenteredSupremum (mu.map Y) s hs r
        (fun z t => c * X z t) (P omega, Y omega)) 2 mu) :
    ∀ᵐ omega ∂mu,
      mu[fun omega' =>
          finiteReplaceOneCenteredSupremum (mu.map Y) s hs r
            (fun z t => c * X z t) (P omega', Y omega') ^ 2 |
          MeasurableSpace.comap P inferInstance] omega <=
        2 * c ^ 2 * integral (mu.map Y) (fun z => A z ^ 2) := by
  let Ac : Z -> Real := fun z => |c| * A z
  have hXc : forall t, t ∈ s ->
      Measurable (fun z => c * X z t) := by
    intro t ht
    exact measurable_const.mul (hX t ht)
  have hAc : forall z, 0 <= Ac z := by
    intro z
    exact mul_nonneg (abs_nonneg c) (hA z)
  have hdomc : forall z t, t ∈ s -> |c * X z t| <= Ac z := by
    intro z t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hdom z t ht) (abs_nonneg c)
  have hAc2 : MemLp Ac 2 (mu.map Y) := by
    simpa only [Ac] using hA2.const_mul |c|
  have hbase := condExp_sq_finiteReplaceOneCenteredSupremum_le
    P Y hPY hP hY s hs r (fun z t => c * X z t) Ac
      hr hXc hAc hdomc hAc2 hD2
  have hint : integral (mu.map Y) (fun z => Ac z ^ 2) =
      c ^ 2 * integral (mu.map Y) (fun z => A z ^ 2) := by
    simp only [Ac, mul_pow, sq_abs]
    rw [integral_const_mul]
  filter_upwards [hbase] with omega hbaseOmega
  rw [hint] at hbaseOmega
  simpa only [mul_assoc] using hbaseOmega

/-- Scaled empirical-coordinate form of the ghost Efron--Stein bound.  For an
empirical average one takes `c = 1 / n`, so one coordinate contributes at
most `2 * K2^2 / n^2` to the conditional quadratic variation.
@isnad1 id=le.5h8v.s8.15f5d49b55a6 from=translated src=- shape=a7234a48 vocab=d26ea43a
-/
theorem variance_finiteReplaceOneSupremum_const_mul_le
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (c : Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu) :
    variance
        (finiteReplaceOneSupremum s hs r (fun z t => c * X z t)) nu <=
      2 * c ^ 2 * integral nu (fun z => A z ^ 2) := by
  let Ac : Z -> Real := fun z => |c| * A z
  have hXc : forall t, t ∈ s ->
      Measurable (fun z => c * X z t) := by
    intro t ht
    exact measurable_const.mul (hX t ht)
  have hAc : forall z, 0 <= Ac z := by
    intro z
    exact mul_nonneg (abs_nonneg c) (hA z)
  have hdomc : forall z t, t ∈ s -> |c * X z t| <= Ac z := by
    intro z t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hdom z t ht) (abs_nonneg c)
  have hAc2 : MemLp Ac 2 nu := by
    simpa only [Ac] using hA2.const_mul |c|
  have hbase :=
    variance_finiteReplaceOneSupremum_le_two_mul_integral_sq
      s hs r (fun z t => c * X z t) Ac hXc hAc hdomc hAc2
  have hint : integral nu (fun z => Ac z ^ 2) =
      c ^ 2 * integral nu (fun z => A z ^ 2) := by
    have hAint : Integrable (fun z => A z ^ 2) nu := hA2.integrable_sq
    simp only [Ac, mul_pow, sq_abs]
    rw [integral_const_mul]
  rw [hint] at hbase
  nlinarith

/-- Deterministic `K2` specialization of the scaled coordinate variance.
@isnad1 id=le.6h9v.s8.05346b6d2f13 from=translated src=- shape=52783b23 vocab=d26ea43a
-/
theorem variance_finiteReplaceOneSupremum_const_mul_le_two_mul_sq
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (c K2 : Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu)
    (hsecond : integral nu (fun z => A z ^ 2) <= K2 ^ 2) :
    variance
        (finiteReplaceOneSupremum s hs r (fun z t => c * X z t)) nu <=
      2 * c ^ 2 * K2 ^ 2 := by
  calc
    variance
        (finiteReplaceOneSupremum s hs r (fun z t => c * X z t)) nu <=
        2 * c ^ 2 * integral nu (fun z => A z ^ 2) :=
      variance_finiteReplaceOneSupremum_const_mul_le
        s hs r X A c hX hA hdom hA2
    _ <= 2 * c ^ 2 * K2 ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsecond (mul_nonneg (by norm_num) (sq_nonneg c))

/-- A bounded coordinate envelope bounds the centred one-coordinate
supremum by its replace-one diameter, independently of the frozen term `r`.
This is sharper than bounding the terminal supremum itself, whose size also
contains all the frozen observations.
@isnad1 id=le.6h9v.s7.d1533b6b80c7 from=translated src=- shape=2ba0d096 vocab=02c72989
-/
theorem abs_finiteReplaceOneSupremum_sub_integral_le_two_mul
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu)
    {B : Real} (hAbound : forall z, A z <= B)
    (z : Z) :
    |finiteReplaceOneSupremum s hs r X z -
        integral nu (finiteReplaceOneSupremum s hs r X)| <= 2 * B := by
  let F : Z -> Real := finiteReplaceOneSupremum s hs r X
  have hF2 : MemLp F 2 nu :=
    memLp_finiteReplaceOneSupremum_two s hs r X A hX hA hdom hA2
  have hFint : Integrable F nu := hF2.integrable (by norm_num)
  have hdiffInt : Integrable (fun z' => F z - F z') nu :=
    (integrable_const _).sub hFint
  have heq : F z - integral nu F = integral nu (fun z' => F z - F z') := by
    rw [integral_sub (integrable_const _) hFint]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq]
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := nu) (f := fun z' => F z - F z') (C := 2 * B)
    (ae_of_all nu fun z' => by
      rw [Real.norm_eq_abs]
      calc
        |F z - F z'| <= A z + A z' :=
          abs_finiteReplaceOneSupremum_sub_le_add_envelopes
            s hs r X A hdom z z'
        _ <= B + B := add_le_add (hAbound z) (hAbound z')
        _ = 2 * B := by ring)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

/-- Bernstein MGF for the centred one-coordinate finite supremum.  The
variance proxy is `4*K2^2`, the scale is the replace-one diameter `2*B`, and
neither depends on the finite class cardinality or on the frozen process.

This is the fibrewise concentration statement required in a product
filtration.  Iterating it needs a conditional-expectation/product-filtration
identification, which is intentionally not postulated in this theorem.
@isnad1 id=hasberns.8h9v.s8.87095bbeb89d from=translated src=- shape=625aa090 vocab=c3840b96
-/
theorem hasBernsteinMGF_finiteReplaceOneSupremum_sub_integral
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu)
    {K2 B : Real} (hB : 0 <= B)
    (hAbound : forall z, A z <= B)
    (hsecond : integral nu (fun z => A z ^ 2) <= K2 ^ 2) :
    HasBernsteinMGF
      (fun z => finiteReplaceOneSupremum s hs r X z -
        integral nu (finiteReplaceOneSupremum s hs r X))
      ⟨4 * K2 ^ 2, mul_nonneg (by norm_num) (sq_nonneg K2)⟩
      ⟨2 * B, mul_nonneg (by norm_num) hB⟩ nu := by
  let F : Z -> Real := finiteReplaceOneSupremum s hs r X
  let D : Z -> Real := fun z => F z - integral nu F
  have hF2 : MemLp F 2 nu :=
    memLp_finiteReplaceOneSupremum_two s hs r X A hX hA hdom hA2
  have hFint : Integrable F nu := hF2.integrable (by norm_num)
  have hD2 : MemLp D 2 nu := hF2.sub (memLp_const (integral nu F))
  have hDbound : forall z, |D z| <= 2 * B := by
    intro z
    exact abs_finiteReplaceOneSupremum_sub_integral_le_two_mul
      s hs r X A hX hA hdom hA2 hAbound z
  have hDcenter : integral nu D = 0 := by
    simp only [D]
    rw [integral_sub hFint (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have hDsecond : integral nu (fun z => D z ^ 2) <= 2 * K2 ^ 2 := by
    have hvar := variance_finiteReplaceOneSupremum_le_two_mul_integral_sq
      s hs r X A hX hA hdom hA2
    have hvarK : variance F nu <= 2 * K2 ^ 2 := by
      calc
        variance F nu <= 2 * integral nu (fun z => A z ^ 2) := hvar
        _ <= 2 * K2 ^ 2 := mul_le_mul_of_nonneg_left hsecond (by norm_num)
    rw [← variance_eq_integral hF2.aemeasurable]
    exact hvarK
  have hbase := hasBernsteinMGF_of_memLp_two_of_ae_abs_le_of_integral_eq_zero
    D hD2 (mul_nonneg (by norm_num) (sq_nonneg K2))
      (mul_nonneg (by norm_num) hB) (ae_of_all nu hDbound) hDcenter hDsecond
  convert hbase using 1
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- One-sided tail corresponding to the preceding fibrewise Bernstein MGF.
@isnad1 id=le.10h10v.s8.8bf065a49b9c from=translated src=- shape=7c0d8ffe vocab=cbfd9b9b
-/
theorem measureReal_finiteReplaceOneSupremum_sub_integral_ge_le
    [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty)
    (r : T -> Real) (X : Z -> T -> Real) (A : Z -> Real)
    (hX : forall t, t ∈ s -> Measurable (fun z => X z t))
    (hA : forall z, 0 <= A z)
    (hdom : forall z t, t ∈ s -> |X z t| <= A z)
    (hA2 : MemLp A 2 nu)
    {K2 B epsilon : Real} (hK2 : 0 < K2) (hB : 0 <= B)
    (hAbound : forall z, A z <= B)
    (hsecond : integral nu (fun z => A z ^ 2) <= K2 ^ 2)
    (hepsilon : 0 <= epsilon) :
    nu.real {z | epsilon <=
        finiteReplaceOneSupremum s hs r X z -
          integral nu (finiteReplaceOneSupremum s hs r X)} <=
      exp (-epsilon ^ 2 / (2 * (4 * K2 ^ 2 + 2 * B * epsilon))) := by
  have hmgf := hasBernsteinMGF_finiteReplaceOneSupremum_sub_integral
    s hs r X A hX hA hdom hA2 hB hAbound hsecond
  have hv : 0 < ((⟨4 * K2 ^ 2,
      mul_nonneg (by norm_num) (sq_nonneg K2)⟩ : ℝ≥0) : Real) := by
    change 0 < 4 * K2 ^ 2
    positivity
  have htail := hmgf.measure_ge_le hepsilon hv
  change nu.real {z | epsilon <=
      finiteReplaceOneSupremum s hs r X z -
        integral nu (finiteReplaceOneSupremum s hs r X)} <=
    exp (-epsilon ^ 2 / (2 * (4 * K2 ^ 2 + 2 * B * epsilon))) at htail
  exact htail

end ProbabilityTheory
