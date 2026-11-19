/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite maxima of sparse operators

This file develops the sparse-family and finite-maximal ingredients of Lemma
`l:weak11sparse` in the paper.  In particular, it records measurability in the
definition of a sparse family, proves that a sparse family of nondegenerate
real intervals is countable, makes the infimum defining the sparse norm
usable, and verifies the two quantitative finite-dimensional steps in the
paper's proof: the Hölder estimate for the foliation by the linearizing index
and the logarithmic choice of exponents.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson

namespace L0Infinity

/-- Pointwise addition, retaining the paper's bounded compact-support domain.-/
noncomputable def add (f g : L0Infinity) : L0Infinity where
  toFun := fun x ↦ f x + g x
  measurable_toFun := f.measurable_toFun.add g.measurable_toFun
  bounded_toFun := by
    rcases f.bounded_toFun with ⟨Cf, hCf⟩
    rcases g.bounded_toFun with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x ↦ ?_⟩
    calc
      ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ Cf + Cg := add_le_add (hCf x) (hCg x)
  hasCompactSupport_toFun := by
    change HasCompactSupport (f.toFun + g.toFun)
    exact f.hasCompactSupport_toFun.add g.hasCompactSupport_toFun

/-- The zero member of the paper's test-function space.-/
noncomputable def zero : L0Infinity where
  toFun := 0
  measurable_toFun := measurable_zero
  bounded_toFun := ⟨0, fun _ ↦ by simp⟩
  hasCompactSupport_toFun := HasCompactSupport.zero

/-- Complex scalar multiplication on the paper's test-function space.-/
noncomputable def smul (c : ℂ) (f : L0Infinity) : L0Infinity where
  toFun := fun x ↦ c * f x
  measurable_toFun := measurable_const.mul f.measurable_toFun
  bounded_toFun := by
    rcases f.bounded_toFun with ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun x ↦ ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  hasCompactSupport_toFun := by
    exact f.hasCompactSupport_toFun.comp_left (mul_zero c)

/--
@isnad1 id=eq.0h3v.s4.71b9bf69d711 from=translated src=- shape=c2976164 vocab=a852ad5a
-/
@[simp] theorem smul_apply (c : ℂ) (f : L0Infinity) (x : ℝ) :
    smul c f x = c * f x := rfl

end L0Infinity

/-- An operator on the paper's space `L₀∞(ℝ)`.-/
abbrev TestOperator := L0Infinity → ℝ → ℂ

/-- Sublinearity in the form relevant to the finite-maximal lemma.-/
def IsSublinear (T : TestOperator) : Prop :=
  (∀ f g x, ‖T (L0Infinity.add f g) x‖ ≤ ‖T f x‖ + ‖T g x‖) ∧
    (∀ (c : ℂ) (f : L0Infinity) (x : ℝ),
      ‖T (L0Infinity.smul c f) x‖ = ‖c‖ * ‖T f x‖)

/-- A bounded nondegenerate interval, represented by its left and right endpoints.-/
structure RealInterval where
  left : ℝ
  right : ℝ
  left_lt_right : left < right

/-- The interval itself.  Endpoint choices do not affect any later measure.-/
def RealInterval.carrier (I : RealInterval) : Set ℝ := Ioc I.left I.right

/-- Lebesgue length of an interval.-/
def RealInterval.length (I : RealInterval) : ℝ := I.right - I.left

/--
@isnad1 id=lt.0h1v.s3.1ffb6557a430 from=translated src=- shape=b9369acb vocab=32580006
-/
theorem RealInterval.length_pos (I : RealInterval) : 0 < I.length := by
  exact sub_pos.mpr I.left_lt_right

/--
@isnad1 id=measurab.0h1v.s2.ca46ff5d6ec6 from=translated src=- shape=1a6c1393 vocab=d53d9d39
-/
theorem RealInterval.measurableSet_carrier (I : RealInterval) :
    MeasurableSet I.carrier := measurableSet_Ioc

/--
@isnad1 id=eq.0h1v.s4.c19d95564506 from=translated src=- shape=2d2ddd72 vocab=7ba692f4
-/
@[simp] theorem RealInterval.volume_carrier (I : RealInterval) :
    volume I.carrier = ENNReal.ofReal I.length := by
  simp [RealInterval.carrier, RealInterval.length, Real.volume_Ioc]

/--
@isnad1 id=eq.0h1v.s4.863e25ce8668 from=translated src=- shape=587bb475 vocab=f7605f30
-/
@[simp] theorem RealInterval.volume_carrier_toReal (I : RealInterval) :
    (volume I.carrier).toReal = I.length := by
  rw [RealInterval.volume_carrier, ENNReal.toReal_ofReal I.length_pos.le]

/-- The local `L^p` average appearing in a sparse form.-/
noncomputable def localAverage (p : ℝ) (f : ℝ → ℂ) (I : RealInterval) : ℝ :=
  (I.length⁻¹ * ∫ x in I.carrier, ‖f x‖ ^ p) ^ (1 / p)

/-- The usual measurable, disjoint-major-subsets formulation of `η`-sparseness.

The range restriction `0 < η < 1` is part of the paper's definition, not an
auxiliary assumption.-/
def IsSparse (η : ℝ) (S : Set RealInterval) : Prop :=
  0 < η ∧ η < 1 ∧
    ∃ E : {I : RealInterval // I ∈ S} → Set ℝ,
      (∀ I, MeasurableSet (E I)) ∧
        (∀ I, E I ⊆ I.1.carrier) ∧
          (Pairwise fun I J ↦ Disjoint (E I) (E J)) ∧
            ∀ I, η * I.1.length ≤ (volume (E I)).toReal

/-- Every sparse collection of nondegenerate real intervals is countable.

This is what justifies the paper's unqualified sum over a sparse family.  The
proof uses the major subsets: they are measurable, pairwise disjoint, and
have strictly positive measure in the s-finite Lebesgue measure space.
@isnad1 id=countabl.1h2v.s3.1674d777a711 from=translated src=- shape=b7133ed0 vocab=d914819c
-/
theorem IsSparse.countable {η : ℝ} {S : Set RealInterval} (hS : IsSparse η S) :
    S.Countable := by
  rcases hS with ⟨hη, -, E, hEmeas, -, hEdisj, hEsize⟩
  have hEpos : ∀ I : {I : RealInterval // I ∈ S}, 0 < volume (E I) := by
    intro I
    have hreal : 0 < (volume (E I)).toReal :=
      lt_of_lt_of_le (mul_pos hη I.1.length_pos) (hEsize I)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hcount : Set.Countable
      {I : {I : RealInterval // I ∈ S} | 0 < volume (E I)} :=
    Measure.countable_meas_pos_of_disjoint_iUnion hEmeas hEdisj
  have huniv : {I : {I : RealInterval // I ∈ S} | 0 < volume (E I)} = Set.univ :=
    Set.eq_univ_of_forall hEpos
  rw [huniv, Set.countable_univ_iff] at hcount
  exact hcount

/-- The sparse `(1,p)` form from Section 2.3 of the paper.-/
noncomputable def sparseForm (p : ℝ) (f g : ℝ → ℂ) (S : Set RealInterval) : ℝ≥0∞ :=
  ∑' I : {I : RealInterval // I ∈ S},
    ENNReal.ofReal (I.1.length * localAverage 1 f I.1 * localAverage p g I.1)

/--
@isnad1 id=le.0h3v.s4.84c6c8bf5b08 from=translated src=- shape=1f9ba2d6 vocab=4f2ba287
-/
theorem localAverage_nonneg (p : ℝ) (f : ℝ → ℂ) (I : RealInterval) :
    0 ≤ localAverage p f I := by
  apply Real.rpow_nonneg
  exact mul_nonneg (inv_nonneg.mpr I.length_pos.le)
    (MeasureTheory.integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) p)

/--
@isnad1 id=le.0h4v.s4.48ab0fe5a8ca from=translated src=- shape=effcc421 vocab=8b909271
-/
theorem sparseForm_nonneg (p : ℝ) (f g : ℝ → ℂ) (S : Set RealInterval) :
    0 ≤ sparseForm p f g S := by
  exact bot_le

/-- The uncentered interval maximal average associated to `localAverage`.
Using `ℝ≥0∞` makes this definition meaningful without a prior finiteness or
measurability theorem for the supremum.-/
noncomputable def intervalMaximalAverage (p : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ I : RealInterval, ⨆ _ : x ∈ I.carrier, ENNReal.ofReal (localAverage p f I)

/--
@isnad1 id=le.1h4v.s5.c0ce1c756d66 from=translated src=- shape=e4c155df vocab=6cb044b4
-/
theorem ofReal_localAverage_le_intervalMaximalAverage (p : ℝ) (f : ℝ → ℂ)
    (I : RealInterval) {x : ℝ} (hx : x ∈ I.carrier) :
    ENNReal.ofReal (localAverage p f I) ≤ intervalMaximalAverage p f x := by
  exact le_iSup_of_le I (le_iSup_of_le hx le_rfl)

/-- The basic sparse embedding used in Lemma `l:weak11sparse`:
the sparse form is controlled by the integral of the two interval maximal
averages.  This is the exact consequence of the disjoint major subsets in
the definition of sparseness.
@isnad1 id=le.1h5v.s6.bf93097df20b from=translated src=- shape=54a8a3b0 vocab=d8cd76ac
-/
theorem sparseForm_le_lintegral_intervalMaximalAverage {p η : ℝ}
    {S : Set RealInterval} (hS : IsSparse η S) (f g : ℝ → ℂ) :
    sparseForm p f g S ≤ ENNReal.ofReal η⁻¹ *
      ∫⁻ x, intervalMaximalAverage 1 f x * intervalMaximalAverage p g x := by
  classical
  have hScount : S.Countable := hS.countable
  rcases hS with ⟨hη, -, E, hEmeas, hEsub, hEdisj, hEsize⟩
  let _ : Countable {I : RealInterval // I ∈ S} := hScount.to_subtype
  let M : ℝ → ℝ≥0∞ := fun x ↦
    intervalMaximalAverage 1 f x * intervalMaximalAverage p g x
  have hterm : ∀ I : {I : RealInterval // I ∈ S},
      ENNReal.ofReal
          (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) ≤
        ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x := by
    intro I
    have hIfinite : volume I.1.carrier ≠ ∞ := by simp
    have hEfinite : volume (E I) ≠ ∞ :=
      ne_top_of_le_ne_top hIfinite (measure_mono (hEsub I))
    have hlengthReal : I.1.length ≤ η⁻¹ * (volume (E I)).toReal := by
      calc
        I.1.length = η⁻¹ * (η * I.1.length) := by
          rw [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
        _ ≤ η⁻¹ * (volume (E I)).toReal :=
          mul_le_mul_of_nonneg_left (hEsize I) (inv_nonneg.mpr hη.le)
    have hlength : ENNReal.ofReal I.1.length ≤
        ENNReal.ofReal η⁻¹ * volume (E I) := by
      calc
        ENNReal.ofReal I.1.length ≤
            ENNReal.ofReal (η⁻¹ * (volume (E I)).toReal) :=
          ENNReal.ofReal_le_ofReal hlengthReal
        _ = ENNReal.ofReal η⁻¹ * ENNReal.ofReal (volume (E I)).toReal := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hη.le)]
        _ = ENNReal.ofReal η⁻¹ * volume (E I) := by
          rw [ENNReal.ofReal_toReal hEfinite]
    have hintegral :
        ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) * volume (E I) ≤
          ∫⁻ x in E I, M x := by
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hEmeas I)
      intro x hx
      exact mul_le_mul'
        (ofReal_localAverage_le_intervalMaximalAverage 1 f I.1 (hEsub I hx))
        (ofReal_localAverage_le_intervalMaximalAverage p g I.1 (hEsub I hx))
    rw [ENNReal.ofReal_mul
      (mul_nonneg I.1.length_pos.le (localAverage_nonneg 1 f I.1)),
      ENNReal.ofReal_mul I.1.length_pos.le]
    calc
      ENNReal.ofReal I.1.length * ENNReal.ofReal (localAverage 1 f I.1) *
          ENNReal.ofReal (localAverage p g I.1) ≤
        (ENNReal.ofReal η⁻¹ * volume (E I)) *
          ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) :=
        mul_le_mul' (mul_le_mul' hlength le_rfl) le_rfl
      _ = ENNReal.ofReal η⁻¹ *
          (ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) * volume (E I)) := by
        ac_rfl
      _ ≤ ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x :=
        mul_le_mul' le_rfl hintegral
  rw [sparseForm]
  calc
    ∑' I : {I : RealInterval // I ∈ S},
        ENNReal.ofReal
          (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) ≤
      ∑' I : {I : RealInterval // I ∈ S},
        ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal η⁻¹ * ∫⁻ x in ⋃ I, E I, M x := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun I ↦ hEmeas I) hEdisj]
    _ ≤ ENNReal.ofReal η⁻¹ * ∫⁻ x, M x :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- The scalar-valued form `Λ_T(f,g) = ⟨Tf,g⟩` from Section 2.6.-/
noncomputable def operatorPairing (T : TestOperator) (f g : L0Infinity) : ℂ :=
  ∫ x, T f x * star (g x)

/-- The positive operator denoted by `|T|` in Lemma `l:weak11sparse`.-/
noncomputable def absoluteValueOperator (T : TestOperator) : TestOperator :=
  fun f x ↦ (‖T f x‖ : ℂ)

/--
@isnad1 id=eq.0h3v.s4.fd63afdac644 from=translated src=- shape=fd5af979 vocab=1548a892
-/
@[simp] theorem absoluteValueOperator_apply (T : TestOperator) (f : L0Infinity) (x : ℝ) :
    absoluteValueOperator T f x = (‖T f x‖ : ℂ) := rfl

/-- `C` is an admissible sparse `(1,p)` constant for `T`, using the project's
`1/4` density convention (the convention in Krause--Lacey).-/
def HasSparseOnePBound (C p : ℝ) (T : TestOperator) : Prop :=
  ∀ f g : L0Infinity,
    ∃ S : Set RealInterval, IsSparse (1 / 4) S ∧
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤ ENNReal.ofReal C * sparseForm p f g S

/--
@isnad1 id=hasspars.2h4v.s4.c0c695bb66d3 from=translated src=- shape=8019a7c9 vocab=53ec9baa
-/
theorem HasSparseOnePBound.mono {C D p : ℝ} {T : TestOperator}
    (h : HasSparseOnePBound C p T) (hCD : C ≤ D) : HasSparseOnePBound D p T := by
  intro f g
  rcases h f g with ⟨S, hS, hbound⟩
  exact ⟨S, hS, hbound.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCD) le_rfl)⟩

/-- The sparse form of `T` has at least one finite admissible `(1,p)` constant.-/
def IsSparseOnePBounded (p : ℝ) (T : TestOperator) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ HasSparseOnePBound C p T

/-- The paper's sparse `(1,p)` norm, as the infimum of admissible constants.-/
noncomputable def sparseOnePNorm (p : ℝ) (T : TestOperator) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ HasSparseOnePBound C p T}

/-- Any constant strictly above the sparse norm is admissible.

The boundedness premise is essential over `ℝ`: without it, `sInf ∅ = 0`
would make an operator with no sparse bound appear to have norm zero.
@isnad1 id=hasspars.2h3v.s4.9a044eb91ea5 from=translated src=- shape=707ef3fc vocab=e54347a9
-/
theorem hasSparseOnePBound_of_sparseOnePNorm_lt {C p : ℝ} {T : TestOperator}
    (hbounded : IsSparseOnePBounded p T) (hC : sparseOnePNorm p T < C) :
    HasSparseOnePBound C p T := by
  rcases hbounded with ⟨D, hDnonneg, hD⟩
  let constants : Set ℝ := {K : ℝ | 0 ≤ K ∧ HasSparseOnePBound K p T}
  have hconstants : constants.Nonempty := ⟨D, hDnonneg, hD⟩
  obtain ⟨K, hKmem, hKlt⟩ := exists_lt_of_csInf_lt hconstants hC
  exact hKmem.2.mono hKlt.le

/--
@isnad1 id=le.1h2v.s4.12580d5da712 from=translated src=- shape=4073e6f3 vocab=d1da83b3
-/
theorem sparseOnePNorm_nonneg {p : ℝ} {T : TestOperator}
    (hbounded : IsSparseOnePBounded p T) : 0 ≤ sparseOnePNorm p T := by
  rcases hbounded with ⟨C, hCnonneg, hC⟩
  rw [sparseOnePNorm]
  apply le_csInf (show Set.Nonempty {K : ℝ | 0 ≤ K ∧ HasSparseOnePBound K p T} from
    ⟨C, hCnonneg, hC⟩)
  exact fun _ hK ↦ hK.1

/-- Hölder's conjugate exponent `p'`.-/
noncomputable def holderConjugate (p : ℝ) : ℝ := p / (p - 1)

/--
@isnad1 id=holderco.1h1v.s4.a845b45afd50 from=translated src=- shape=c807ce13 vocab=388967bb
-/
theorem holderConjugate_spec {p : ℝ} (hp : 1 < p) :
    p.HolderConjugate (holderConjugate p) := by
  exact (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl

/-- The finite-dimensional Hölder step used after the paper foliates `E'`
according to the value of the linearizing index `j(x)`.

Applied to `a j = |E'_j|`, this is precisely
`∑_j |E'_j|^(1/r) ≤ |E'|^(1/r) N^(1/r')`, after using disjointness.
@isnad1 id=le.2h3v.s7.07a90f1e5432 from=translated src=- shape=f4f9b881 vocab=67a935ea
-/
theorem sum_rpow_one_div_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j)
    {r : ℝ} (hr : 1 < r) :
    ∑ j, (a j) ^ (1 / r) ≤
      (∑ j, a j) ^ (1 / r) * (N : ℝ) ^ (1 / holderConjugate r) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin N))
    (f := fun j ↦ (a j) ^ (1 / r)) (g := fun _ ↦ 1) (holderConjugate_spec hr)
    (fun j _ ↦ Real.rpow_nonneg (ha j) _) (fun _ _ ↦ zero_le_one)
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hpow : ∀ j, ((a j) ^ r⁻¹) ^ r = a j := fun j ↦
    Real.rpow_inv_rpow (ha j) hr0
  simp_rw [one_div, hpow] at h ⊢
  simpa [holderConjugate] using h

/-- The measure-theoretic specialization of `sum_rpow_one_div_le` used for
the pairwise disjoint sets `E'_j` in the paper.
@isnad1 id=le.5h4v.s8.3c23bf1a93c7 from=translated src=- shape=a03c2c3b vocab=b3468228
-/
theorem sum_measureReal_rpow_one_div_le {N : ℕ} (E : Fin N → Set ℝ) (F : Set ℝ)
    (hEmeas : ∀ j, MeasurableSet (E j))
    (hEdisj : Pairwise fun i j ↦ Disjoint (E i) (E j))
    (hsub : (⋃ j, E j) ⊆ F) (hFfinite : volume F ≠ ∞) {r : ℝ} (hr : 1 < r) :
    ∑ j, (volume (E j)).toReal ^ (1 / r) ≤
      (volume F).toReal ^ (1 / r) * (N : ℝ) ^ (1 / holderConjugate r) := by
  have hsum := sum_rpow_one_div_le (fun j ↦ (volume (E j)).toReal)
    (fun j ↦ MeasureTheory.measureReal_nonneg) hr
  have hunion : (volume (⋃ j, E j)).toReal = ∑ j, (volume (E j)).toReal :=
    MeasureTheory.measureReal_iUnion_fintype hEdisj hEmeas fun j ↦
      ne_top_of_le_ne_top hFfinite (measure_mono ((Set.subset_iUnion E j).trans hsub))
  have hmeasure : ∑ j, (volume (E j)).toReal ≤ (volume F).toReal := by
    rw [← hunion]
    exact MeasureTheory.measureReal_mono hsub hFfinite
  refine hsum.trans ?_
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Finset.sum_nonneg fun j _ ↦ MeasureTheory.measureReal_nonneg)
      hmeasure (one_div_nonneg.mpr (zero_lt_one.trans hr).le))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The paper's explicit exponent `p = L / (L - 2)`, where `L` is the
logarithmic scale.-/
noncomputable def logarithmicP (L : ℝ) : ℝ := L / (L - 2)

/-- The paper's explicit exponent `r = L / (L - 3)`.-/
noncomputable def logarithmicR (L : ℝ) : ℝ := L / (L - 3)

/--
@isnad1 id=lt.1h1v.s4.4057eb1a345b from=translated src=- shape=35bd48ee vocab=ee0e17b1
-/
theorem one_lt_logarithmicP {L : ℝ} (hL : 4 < L) : 1 < logarithmicP L := by
  rw [logarithmicP, lt_div_iff₀ (by linarith : 0 < L - 2)]
  linarith

/--
@isnad1 id=lt.1h1v.s4.5465f73750e4 from=translated src=- shape=3965f485 vocab=ee0e17b1
-/
theorem logarithmicP_lt_two {L : ℝ} (hL : 4 < L) : logarithmicP L < 2 := by
  rw [logarithmicP, div_lt_iff₀ (by linarith : 0 < L - 2)]
  linarith

/--
@isnad1 id=lt.1h1v.s4.0e583fc6a8e0 from=translated src=- shape=7d3b5169 vocab=c6107b1d
-/
theorem logarithmicP_lt_logarithmicR {L : ℝ} (hL : 4 < L) :
    logarithmicP L < logarithmicR L := by
  rw [logarithmicP, logarithmicR, div_lt_div_iff₀ (by linarith : 0 < L - 2)
    (by linarith : 0 < L - 3)]
  nlinarith

/--
@isnad1 id=lt.1h1v.s4.2531c7bc1d4f from=translated src=- shape=35bd48ee vocab=28cb03b5
-/
theorem one_lt_logarithmicR {L : ℝ} (hL : 4 < L) : 1 < logarithmicR L := by
  exact (one_lt_logarithmicP hL).trans (logarithmicP_lt_logarithmicR hL)

/--
@isnad1 id=le.1h1v.s4.84507341b716 from=translated src=- shape=97c35add vocab=5c58440a
-/
theorem logarithmicR_le_four {L : ℝ} (hL : 4 < L) : logarithmicR L ≤ 4 := by
  rw [logarithmicR, div_le_iff₀ (by linarith : 0 < L - 3)]
  linarith

/--
@isnad1 id=eq.1h1v.s5.fadfd71ffb71 from=translated src=- shape=9eb43dc0 vocab=e7196672
-/
theorem holderConjugate_logarithmicP {L : ℝ} (hL : 4 < L) :
    holderConjugate (logarithmicP L) = L / 2 := by
  have h2 : L - 2 ≠ 0 := by linarith
  simp only [holderConjugate, logarithmicP]
  field_simp [h2]
  ring

/--
@isnad1 id=eq.1h1v.s5.43a5a14be5cc from=translated src=- shape=9eb43dc0 vocab=dc8d4b01
-/
theorem holderConjugate_logarithmicR {L : ℝ} (hL : 4 < L) :
    holderConjugate (logarithmicR L) = L / 3 := by
  have h3 : L - 3 ≠ 0 := by linarith
  simp only [holderConjugate, logarithmicR]
  field_simp [h3]
  ring

/--
@isnad1 id=eq.1h1v.s5.70793094ba28 from=translated src=- shape=10d0b1bb vocab=31d1c5e7
-/
theorem logarithmicR_div_sub_logarithmicP {L : ℝ} (hL : 4 < L) :
    logarithmicR L / (logarithmicR L - logarithmicP L) = L - 2 := by
  have h2 : L - 2 ≠ 0 := by linarith
  have h3 : L - 3 ≠ 0 := by linarith
  have hdiff : L / (L - 3) - L / (L - 2) ≠ 0 := by
    have hlt := logarithmicP_lt_logarithmicR hL
    exact sub_ne_zero.mpr hlt.ne'
  simp only [logarithmicP, logarithmicR]
  field_simp [h2, h3, hdiff]
  ring

/-- The four-factor expression at the end of the proof of Lemma
`l:weak11sparse`, before the infimum over `p` and `r` is taken.-/
noncomputable def finiteSparseFactor (N : ℕ) (p r : ℝ) : ℝ :=
  holderConjugate p * r ^ (1 / holderConjugate r) *
    (r / (r - p)) ^ (1 / p) * (N : ℝ) ^ (1 / holderConjugate r)

/--
@isnad1 id=le.1h1v.s5.e49266c61daf from=translated src=- shape=19e070a0 vocab=f68c8914
-/
theorem logarithmicR_rpow_le_four {L : ℝ} (hL : 4 < L) :
    logarithmicR L ^ (1 / holderConjugate (logarithmicR L)) ≤ 4 := by
  have hexponent : 1 / holderConjugate (logarithmicR L) ≤ 1 := by
    rw [holderConjugate_logarithmicR hL]
    rw [div_le_iff₀ (by linarith : 0 < L / 3)]
    linarith
  exact (Real.rpow_le_self_of_one_le (one_lt_logarithmicR hL).le hexponent).trans
    (logarithmicR_le_four hL)

/--
@isnad1 id=le.1h1v.s6.1324dcd46e57 from=translated src=- shape=e4c0f693 vocab=9952ad77
-/
theorem logarithmic_gap_rpow_le {L : ℝ} (hL : 4 < L) :
    (logarithmicR L / (logarithmicR L - logarithmicP L)) ^
        (1 / logarithmicP L) ≤ L := by
  rw [logarithmicR_div_sub_logarithmicP hL]
  have hL0 : L ≠ 0 := by linarith
  have hexponent : 1 / logarithmicP L ≤ 1 := by
    rw [logarithmicP]
    field_simp [hL0]
    linarith
  exact (Real.rpow_le_self_of_one_le (by linarith : 1 ≤ L - 2) hexponent).trans (by linarith)

/--
@isnad1 id=le.2h2v.s6.5feb4660d158 from=translated src=- shape=e813e849 vocab=0ae327f6
-/
theorem nat_rpow_logarithmicR_conjugate_le {N : ℕ} {L : ℝ} (hL : 4 < L)
    (hN : (N : ℝ) ≤ Real.exp L) :
    (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) ≤ Real.exp 3 := by
  have hL0 : L ≠ 0 := by linarith
  have hexponent : 0 ≤ 1 / holderConjugate (logarithmicR L) := by
    rw [holderConjugate_logarithmicR hL]
    positivity
  calc
    (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) ≤
        (Real.exp L) ^ (1 / holderConjugate (logarithmicR L)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg N) hN hexponent
    _ = Real.exp 3 := by
      rw [holderConjugate_logarithmicR hL]
      rw [← Real.exp_mul]
      congr 1
      field_simp [hL0]

/-- The paper's proposed values of `p` and `r` really give the claimed
quadratic logarithmic loss, with an explicit absolute constant.
@isnad1 id=le.2h2v.s6.2d80201239f0 from=translated src=- shape=c477d5b7 vocab=6de87eb0
-/
theorem finiteSparseFactor_logarithmic_le {N : ℕ} {L : ℝ} (hL : 4 < L)
    (hN : (N : ℝ) ≤ Real.exp L) :
    finiteSparseFactor N (logarithmicP L) (logarithmicR L) ≤
      2 * Real.exp 3 * L ^ 2 := by
  rw [finiteSparseFactor, holderConjugate_logarithmicP hL]
  have hLnonneg : 0 ≤ L := by linarith
  have hLhalf : 0 ≤ L / 2 := by positivity
  have hratio : 0 ≤ logarithmicR L / (logarithmicR L - logarithmicP L) :=
    div_nonneg (zero_lt_one.trans (one_lt_logarithmicR hL)).le
      (sub_nonneg.mpr (logarithmicP_lt_logarithmicR hL).le)
  have hmiddle : 0 ≤
      (logarithmicR L / (logarithmicR L - logarithmicP L)) ^
        (1 / logarithmicP L) := Real.rpow_nonneg hratio _
  have hlast : 0 ≤
      (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    L / 2 * logarithmicR L ^ (1 / holderConjugate (logarithmicR L)) *
          (logarithmicR L / (logarithmicR L - logarithmicP L)) ^
              (1 / logarithmicP L) *
        (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) ≤
        L / 2 * 4 * L * Real.exp 3 := by
      calc
        _ ≤ L / 2 * 4 *
              (logarithmicR L / (logarithmicR L - logarithmicP L)) ^
                (1 / logarithmicP L) *
              (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (logarithmicR_rpow_le_four hL) hLhalf)
              hmiddle) hlast
        _ ≤ L / 2 * 4 * L *
              (N : ℝ) ^ (1 / holderConjugate (logarithmicR L)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (logarithmic_gap_rpow_le hL)
              (mul_nonneg hLhalf (by norm_num))) hlast
        _ ≤ L / 2 * 4 * L * Real.exp 3 :=
          mul_le_mul_of_nonneg_left (nat_rpow_logarithmicR_conjugate_le hL hN)
            (mul_nonneg (mul_nonneg hLhalf (by norm_num)) hLnonneg)
    _ = 2 * Real.exp 3 * L ^ 2 := by ring

/--
@isnad1 id=lt.1h1v.s5.6370877cabbf from=translated src=- shape=b6efe7f2 vocab=2fa7f54e
-/
theorem four_lt_paperLog_one {N : ℕ} (hN : 54 ≤ N) : 4 < paperLog 1 N := by
  rw [paperLog_succ, paperLog_zero, Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 10 + N)]
  exact Behrend.exp_four_lt.trans_le (by exact_mod_cast (show 64 ≤ 10 + N by omega))

/-- High-cardinality specialization of the preceding optimization, in the
paper's own `log₁` notation.  The finitely many smaller cardinalities are
absorbed into the absolute implicit constant in the analytic argument.
@isnad1 id=le.1h1v.s6.38e85f698eb5 from=translated src=- shape=e1c095ba vocab=f45da8b2
-/
theorem finiteSparseFactor_paperLog_le {N : ℕ} (hN : 54 ≤ N) :
    finiteSparseFactor N (logarithmicP (paperLog 1 N))
        (logarithmicR (paperLog 1 N)) ≤
      2 * Real.exp 3 * (paperLog 1 N) ^ 2 := by
  apply finiteSparseFactor_logarithmic_le (four_lt_paperLog_one hN)
  rw [paperLog_succ, paperLog_zero, Real.exp_log (by positivity : (0 : ℝ) < 10 + N)]
  norm_num

/-- A uniformly safe logarithmic scale.  It agrees with the paper's scale
once `paperLog 1 N ≥ 5` and handles the finitely many smaller cardinalities
without a separate hypothesis.-/
noncomputable def safeLogScale (N : ℕ) : ℝ := max 5 (paperLog 1 N)

/--
@isnad1 id=le.0h1v.s4.4780c756292b from=translated src=- shape=8388ba16 vocab=cc0f37d8
-/
theorem one_le_paperLog_one (N : ℕ) : 1 ≤ paperLog 1 N := by
  rw [paperLog_succ, paperLog_zero, Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < 10 + N)]
  refine Real.exp_one_lt_three.le.trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/--
@isnad1 id=lt.0h1v.s3.806621b5e8e5 from=translated src=- shape=b9369acb vocab=24baaa9d
-/
theorem four_lt_safeLogScale (N : ℕ) : 4 < safeLogScale N := by
  exact (by norm_num : (4 : ℝ) < 5) |>.trans_le (le_max_left _ _)

/--
@isnad1 id=le.0h1v.s3.62cfba1e404b from=translated src=- shape=b55a211a vocab=7ec7e60b
-/
theorem nat_cast_le_exp_safeLogScale (N : ℕ) :
    (N : ℝ) ≤ Real.exp (safeLogScale N) := by
  calc
    (N : ℝ) ≤ 10 + N := by norm_num
    _ = Real.exp (paperLog 1 N) := by
      rw [paperLog_succ, paperLog_zero, Real.exp_log (by positivity : (0 : ℝ) < 10 + N)]
    _ ≤ Real.exp (safeLogScale N) :=
      Real.exp_le_exp.mpr (le_max_right 5 (paperLog 1 N))

/--
@isnad1 id=le.0h1v.s5.2bd205e318cc from=translated src=- shape=7c291ffd vocab=7ed2d031
-/
theorem safeLogScale_le_five_mul (N : ℕ) :
    safeLogScale N ≤ 5 * paperLog 1 N := by
  rw [safeLogScale]
  apply max_le
  · nlinarith [one_le_paperLog_one N]
  · nlinarith [one_le_paperLog_one N]

/-- The paper's finite-dimensional optimization, now valid for every family
cardinality.  The harmless truncation of the logarithmic scale only changes
the absolute constant.
@isnad1 id=le.0h1v.s6.ce4808084883 from=translated src=- shape=2befd384 vocab=92b01a76
-/
theorem finiteSparseFactor_paperLog_le_all (N : ℕ) :
    finiteSparseFactor N (logarithmicP (safeLogScale N))
        (logarithmicR (safeLogScale N)) ≤
      50 * Real.exp 3 * (paperLog 1 N) ^ 2 := by
  have hscale0 : 0 ≤ safeLogScale N :=
    (by norm_num : (0 : ℝ) ≤ 5) |>.trans (le_max_left _ _)
  have hfive0 : 0 ≤ 5 * paperLog 1 N :=
    mul_nonneg (by norm_num) (zero_le_one.trans (one_le_paperLog_one N))
  have hsquare : (safeLogScale N) ^ 2 ≤ (5 * paperLog 1 N) ^ 2 :=
    (sq_le_sq₀ hscale0 hfive0).2 (safeLogScale_le_five_mul N)
  calc
    finiteSparseFactor N (logarithmicP (safeLogScale N))
          (logarithmicR (safeLogScale N)) ≤
        2 * Real.exp 3 * (safeLogScale N) ^ 2 :=
      finiteSparseFactor_logarithmic_le (four_lt_safeLogScale N)
        (nat_cast_le_exp_safeLogScale N)
    _ ≤ 2 * Real.exp 3 * (5 * paperLog 1 N) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 50 * Real.exp 3 * (paperLog 1 N) ^ 2 := by ring

/-- The pointwise maximum of a finite family, with the empty maximum equal to zero.-/
noncomputable def finiteMax {N : ℕ} (T : Fin N → TestOperator) (f : L0Infinity) (x : ℝ) : ℝ :=
  ↑(Finset.univ.sup fun j ↦ ‖T j f x‖₊)

/--
@isnad1 id=le.0h5v.s4.5dc7bbc16cbf from=translated src=- shape=63bd752f vocab=1e2ce51f
-/
theorem le_finiteMax {N : ℕ} (T : Fin N → TestOperator) (f : L0Infinity) (x : ℝ)
    (j : Fin N) : ‖T j f x‖ ≤ finiteMax T f x := by
  change ↑‖T j f x‖₊ ≤ ↑(Finset.univ.sup fun k ↦ ‖T k f x‖₊)
  have h : ‖T j f x‖₊ ≤ Finset.univ.sup (fun k : Fin N ↦ ‖T k f x‖₊) :=
    Finset.le_sup (s := Finset.univ) (f := fun k : Fin N ↦ ‖T k f x‖₊) (Finset.mem_univ j)
  exact_mod_cast h

/-- A nonempty finite maximum is attained.  This is the pointwise content
behind the paper's linearizing index `j(x)`.
@isnad1 id=ex.1h4v.s5.33ff484d1faf from=translated src=- shape=4b3d3f87 vocab=7a9e6086
-/
theorem exists_norm_eq_finiteMax {N : ℕ} (hN : 0 < N) (T : Fin N → TestOperator)
    (f : L0Infinity) (x : ℝ) : ∃ j : Fin N, ‖T j f x‖ = finiteMax T f x := by
  let j₀ : Fin N := ⟨0, hN⟩
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨j₀, Finset.mem_univ j₀⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
    (fun k ↦ ‖T k f x‖₊)
  refine ⟨j, ?_⟩
  change (↑‖T j f x‖₊ : ℝ) =
    ↑(Finset.univ.sup fun k ↦ ‖T k f x‖₊)
  exact congrArg ((↑·) : ℝ≥0 → ℝ) hj.symm

/-- A choice of maximizing index, used to linearize the finite maximum.-/
noncomputable def maximizingIndex {N : ℕ} (hN : 0 < N) (T : Fin N → TestOperator)
    (f : L0Infinity) (x : ℝ) : Fin N :=
  (exists_norm_eq_finiteMax hN T f x).choose

/--
@isnad1 id=eq.1h4v.s5.f8f99fbfe080 from=translated src=- shape=5fb67241 vocab=c0712471
-/
@[simp] theorem norm_maximizingIndex_eq_finiteMax {N : ℕ} (hN : 0 < N)
    (T : Fin N → TestOperator) (f : L0Infinity) (x : ℝ) :
    ‖T (maximizingIndex hN T f x) f x‖ = finiteMax T f x :=
  (exists_norm_eq_finiteMax hN T f x).choose_spec

/-- Interpret a natural number cyclically as an element of `Fin (n+1)`.
Only inputs at most `n` occur in the measurable maximizer below, so no
wrapping actually takes place there.-/
def cyclicFin (n k : ℕ) : Fin (n + 1) :=
  ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/--
@isnad1 id=eq.1h2v.s5.69d53f0a2085 from=translated src=- shape=0553190f vocab=6786fb9d
-/
theorem cyclicFin_eq_of_le (n k : ℕ) (hk : k ≤ n) :
    cyclicFin n k = ⟨k, Nat.lt_succ_of_le hk⟩ := by
  ext
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk)

/-- A natural index represents a pointwise maximizer of a finite complex
family.-/
def IsPointwiseMaximizer {X : Type*} (n : ℕ) (F : Fin (n + 1) → X → ℂ)
    (x : X) (k : ℕ) : Prop :=
  ∀ i, ‖F i x‖ ≤ ‖F (cyclicFin n k) x‖

/--
@isnad1 id=ex.0h4v.s5.fb07421754af from=translated src=- shape=390289fb vocab=c1afb55e
-/
theorem exists_pointwiseMaximizer {X : Type*} (n : ℕ) (F : Fin (n + 1) → X → ℂ)
    (x : X) : ∃ k ≤ n, IsPointwiseMaximizer n F x k := by
  classical
  have huniv : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ huniv (fun i ↦ ‖F i x‖₊)
  have hjle : j.1 ≤ n := Nat.lt_succ_iff.mp (by simpa only [Nat.succ_eq_add_one] using j.2)
  refine ⟨j.1, hjle, ?_⟩
  intro i
  have hi : ‖F i x‖₊ ≤ Finset.univ.sup (fun q : Fin (n + 1) ↦ ‖F q x‖₊) :=
    Finset.le_sup (s := Finset.univ) (f := fun q : Fin (n + 1) ↦ ‖F q x‖₊)
      (Finset.mem_univ i)
  have hcyclic : cyclicFin n j.1 = j := by
    simpa using cyclicFin_eq_of_le n j.1 hjle
  rw [hj, ← hcyclic] at hi
  exact_mod_cast hi

/-- A canonical pointwise maximizing index.  `Nat.findGreatest` provides a
tie-breaking rule whose level sets can be proved measurable.-/
noncomputable def measurableMaximizingIndex {X : Type*} (n : ℕ)
    (F : Fin (n + 1) → X → ℂ) (x : X) : Fin (n + 1) :=
  by
    classical
    exact ⟨Nat.findGreatest (IsPointwiseMaximizer n F x) n,
      Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩

/--
@isnad1 id=le.0h5v.s5.771be08f4fa9 from=translated src=- shape=caaa3f61 vocab=efeca09c
-/
theorem measurableMaximizingIndex_isMax {X : Type*} (n : ℕ)
    (F : Fin (n + 1) → X → ℂ) (x : X) (i : Fin (n + 1)) :
    ‖F i x‖ ≤ ‖F (measurableMaximizingIndex n F x) x‖ := by
  classical
  rcases exists_pointwiseMaximizer n F x with ⟨k, hk, hmax⟩
  have hchosen := Nat.findGreatest_spec hk hmax
  have hcyclic : cyclicFin n (Nat.findGreatest (IsPointwiseMaximizer n F x) n) =
      measurableMaximizingIndex n F x := by
    simpa [measurableMaximizingIndex] using
      cyclicFin_eq_of_le n (Nat.findGreatest (IsPointwiseMaximizer n F x) n)
        (Nat.findGreatest_le n)
  simpa only [IsPointwiseMaximizer, hcyclic] using hchosen i

/-- The measurable selector genuinely attains the finite supremum of the
pointwise norms.
@isnad1 id=eq.0h4v.s7.b934be5b2ba0 from=translated src=- shape=0483221d vocab=2d59e6df
-/
theorem norm_measurableMaximizingIndex_eq_sup {X : Type*} (n : ℕ)
    (F : Fin (n + 1) → X → ℂ) (x : X) :
    ‖F (measurableMaximizingIndex n F x) x‖₊ =
      Finset.univ.sup (fun i : Fin (n + 1) ↦ ‖F i x‖₊) := by
  apply le_antisymm
  · exact Finset.le_sup (s := Finset.univ) (f := fun i : Fin (n + 1) ↦ ‖F i x‖₊)
      (Finset.mem_univ (measurableMaximizingIndex n F x))
  · apply Finset.sup_le
    intro i _
    exact_mod_cast measurableMaximizingIndex_isMax n F x i

/-- For a nonempty family of test operators, the measurable selector
linearizes `finiteMax` pointwise.
@isnad1 id=eq.0h4v.s6.fdd323b9c808 from=translated src=- shape=a331ae27 vocab=4d409ec3
-/
theorem finiteMax_eq_norm_measurableMaximizingIndex (n : ℕ)
    (T : Fin (n + 1) → TestOperator) (f : L0Infinity) (x : ℝ) :
    finiteMax T f x =
      ‖T (measurableMaximizingIndex n (fun i y ↦ T i f y) x) f x‖ := by
  change (↑(Finset.univ.sup fun i : Fin (n + 1) ↦ ‖T i f x‖₊) : ℝ) =
    ↑‖T (measurableMaximizingIndex n (fun i y ↦ T i f y) x) f x‖₊
  exact_mod_cast
    (norm_measurableMaximizingIndex_eq_sup n (fun i y ↦ T i f y) x).symm

/-- A finite family of measurable functions admits a measurable choice of a
pointwise maximizing index.
@isnad1 id=measurab.1h3v.s6.0e30289936c4 from=translated src=- shape=fbb241cc vocab=fb395ce4
-/
theorem measurable_measurableMaximizingIndex {X : Type*} [MeasurableSpace X] (n : ℕ)
    (F : Fin (n + 1) → X → ℂ) (hF : ∀ i, Measurable (F i)) :
    Measurable (measurableMaximizingIndex n F) := by
  classical
  have hpred : ∀ k ≤ n, MeasurableSet {x | IsPointwiseMaximizer n F x k} := by
    intro k hk
    change MeasurableSet {x | ∀ i, ‖F i x‖ ≤ ‖F (cyclicFin n k) x‖}
    rw [show {x | ∀ i, ‖F i x‖ ≤ ‖F (cyclicFin n k) x‖} =
        ⋂ i, {x | ‖F i x‖ ≤ ‖F (cyclicFin n k) x‖} by ext x; simp]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (hF i).norm (hF _).norm
  have hnat : Measurable fun x ↦ Nat.findGreatest (IsPointwiseMaximizer n F x) n :=
    measurable_findGreatest hpred
  apply measurable_to_countable'
  intro j
  have hj := hnat (measurableSet_singleton j.1)
  rw [show measurableMaximizingIndex n F ⁻¹' {j} =
      (fun x ↦ Nat.findGreatest (IsPointwiseMaximizer n F x) n) ⁻¹' {j.1} by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change (⟨Nat.findGreatest (IsPointwiseMaximizer n F x) n,
      Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩ : Fin (n + 1)) = j ↔ _
    constructor
    · exact fun h ↦ congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h]
  exact hj

/-- A weak `(1,1)` estimate, in distribution-function form.-/
def HasWeakOneOneBound (C : ℝ) (T : L0Infinity → ℝ → ℝ) : Prop :=
  ∀ f : L0Infinity, ∀ a : ℝ, 0 < a →
    ENNReal.ofReal a * volume {x | a < T f x} ≤
      ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ

/--
@isnad1 id=hasweako.2h3v.s4.18ddfd3b4c48 from=translated src=- shape=72f58f4c vocab=c1b56f5c
-/
theorem HasWeakOneOneBound.mono {C D : ℝ} {T : L0Infinity → ℝ → ℝ}
    (h : HasWeakOneOneBound C T) (hCD : C ≤ D) : HasWeakOneOneBound D T := by
  intro f a ha
  exact (h f a ha).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCD) le_rfl)

/-- The weak `L¹` operator norm, expressed as an infimum of distribution bounds.-/
noncomputable def weakOneOneNorm (T : L0Infinity → ℝ → ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ HasWeakOneOneBound C T}

/-- The exact sparse-growth assumption in Lemma `l:weak11sparse`.

`A` packages the absolute implicit constant in `\lesssim 1`; the maximum over
`j = 1, …, N` is represented by universal quantification over `Fin N`.-/
def FiniteSparseMaximalHypothesis {N : ℕ} (T : Fin N → TestOperator) (A : ℝ) : Prop :=
  0 ≤ A ∧
    (∀ j f, LocallyIntegrable (T j f) volume) ∧
      (∀ j, IsSublinear (T j)) ∧
        ∀ p : ℝ, 1 < p → p < 2 → ∀ j : Fin N,
          IsSparseOnePBounded p (absoluteValueOperator (T j)) ∧
            sparseOnePNorm p (absoluteValueOperator (T j)) ≤ A * holderConjugate p

/-- Operational form of the sparse-norm hypothesis: a sparse collection can
be extracted with any positive slack above `A p'`.
@isnad1 id=hasspars.4h6v.s6.efc8573033fb from=translated src=- shape=e357a01a vocab=0492da25
-/
theorem FiniteSparseMaximalHypothesis.hasSparseOnePBound_add {N : ℕ}
    {T : Fin N → TestOperator} {A p ε : ℝ} (h : FiniteSparseMaximalHypothesis T A)
    (hp : 1 < p) (hp2 : p < 2) (j : Fin N) (hε : 0 < ε) :
    HasSparseOnePBound (A * holderConjugate p + ε) p (absoluteValueOperator (T j)) := by
  rcases h.2.2.2 p hp hp2 j with ⟨hbounded, hnorm⟩
  exact hasSparseOnePBound_of_sparseOnePNorm_lt hbounded
    (hnorm.trans_lt (lt_add_of_pos_right _ hε))

/-- The formal proposition corresponding exactly to paper Lemma
`l:weak11sparse`.  The witness `K` is outside the quantifiers over `N`, the
operator family, and its sparse-growth constant, so it is genuinely absolute
rather than being chosen separately for each family.-/
def weak11sparseStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} (T : Fin N → TestOperator) (A : ℝ),
    FiniteSparseMaximalHypothesis T A →
      weakOneOneNorm (finiteMax T) ≤ K * A * (paperLog 1 N) ^ 2

/-- The finite maximum dominates every member of the family pointwise.
@isnad1 id=le.0h5v.s4.5dc7bbc16cbf from=translated src=- shape=63bd752f vocab=1e2ce51f
-/
theorem norm_le_finiteMax {N : ℕ} (T : Fin N → TestOperator) (f : L0Infinity) (x : ℝ)
    (j : Fin N) : ‖T j f x‖ ≤ finiteMax T f x :=
  le_finiteMax T f x j

/-- The paper's `log₁ N` is positive, hence its square is nonnegative.
@isnad1 id=le.0h1v.s5.36b8cbd7b458 from=translated src=- shape=1c645e5b vocab=55c049d3
-/
theorem paperLog_one_sq_nonneg (N : ℕ) : 0 ≤ (paperLog 1 N) ^ 2 := sq_nonneg _

end QuadraticCarleson
