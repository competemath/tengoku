import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardPrelim
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardTaylor
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardSteps
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardMain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sard's theorem on Euclidean spaces, with corollaries

Final statements of Wave 3S:

* `Submission.sard` — for a `C^∞` map `f` on an open set
  `U ⊆ EuclideanSpace ℝ (Fin p)`, the set of critical values
  `f '' {x ∈ U | ¬Surjective (fderivWithin ℝ f U x)}` is Lebesgue-null;
* `Submission.sard_global` — the global-domain version, with `fderiv`;
* `Submission.sard_of_lt` — if `p < q` then the range of a `C¹` map is null;
* `Submission.IsRegularValue`, `Submission.sard_dense_regular_values`,
  `Submission.sard_exists_regular_value_in_ball` — density of regular values;
* `Submission.IsRegularValueOn`, `Submission.sard_dense_regular_values_on` — the
  relative version for a smooth map defined on an open set;
* `Submission.sard_rank_deficient` — Knill's rank-deficient form;
* `Submission.regular_value_ae` — for `f : ℝᵐ → ℝ` smooth, a.e. `c : ℝ` is a
  regular value.

Everything reduces to `Submission.sard_pi` (`SardMain.lean`) via the
volume-preserving identification `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)`.
-/

namespace Submission

noncomputable section

open Function MeasureTheory Metric Set Filter
open scoped ContDiff Topology

variable {p q : ℕ}

/-! ## Transfer between `EuclideanSpace ℝ (Fin n)` and `Fin n → ℝ` -/

/-- Null sets in `Fin q → ℝ` pull back to null sets in `EuclideanSpace ℝ (Fin q)`
along the canonical identification.
@isnad1 id=eq.2h3v.s8.1aa4be2b9970 from=translated src=- shape=ef029f10 vocab=c6780aea
-/
theorem euclidean_null_of_pi_null {A : Set (EuclideanSpace ℝ (Fin q))}
    {B : Set (Fin q → ℝ)} (hAB : ∀ a ∈ A, WithLp.ofLp a ∈ B)
    (hB : volume B = 0) : volume A = 0 := by
  have hsub : A ⊆ WithLp.ofLp ⁻¹' B := fun a ha => hAB a ha
  refine measure_mono_null hsub ?_
  exact (PiLp.volume_preserving_ofLp
    (Fin q)).quasiMeasurePreserving.preimage_null hB

/-! ## Sard's theorem -/

/-- **Sard's theorem.**  Let `U ⊆ ℝ^p` be open and `f : ℝ^p → ℝ^q` a `C^∞` map
on `U`.  The set of critical values of `f` on `U` has Lebesgue measure zero.
@isnad1 id=eq.2h4v.s10.bb262c149c30 from=translated src=- shape=0e26e376 vocab=fc67bcda
-/
theorem sard {U : Set (EuclideanSpace ℝ (Fin p))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x ∈ U | ¬Function.Surjective (fderivWithin ℝ f U x)}) = 0 := by
  -- replace `fderivWithin` by `fderiv`
  have hset : {x ∈ U | ¬Function.Surjective (fderivWithin ℝ f U x)}
      = {x ∈ U | ¬Function.Surjective (fderiv ℝ f x)} := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, by rwa [fderivWithin_of_isOpen hU hxU] at hx⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, by rwa [fderivWithin_of_isOpen hU hxU]⟩
  rw [hset]
  -- transfer to `Fin p → ℝ`
  set eP := EuclideanSpace.equiv (Fin p) ℝ with hePdef
  set eQ := EuclideanSpace.equiv (Fin q) ℝ with heQdef
  set F : (Fin p → ℝ) → Fin q → ℝ := fun x => eQ (f (eP.symm x)) with hFdef
  set U' : Set (Fin p → ℝ) := ⇑eP.symm ⁻¹' U with hU'def
  have hU'open : IsOpen U' := hU.preimage eP.symm.continuous
  have hFsm : ContDiffOn ℝ ∞ F U' :=
    eQ.contDiff.comp_contDiffOn
      (hf.comp eP.symm.contDiff.contDiffOn fun x hx => hx)
  have hmain := sard_pi p q U' F hU'open hFsm
  refine euclidean_null_of_pi_null ?_ hmain
  rintro _ ⟨x, ⟨hxU, hxcrit⟩, rfl⟩
  refine ⟨eP x, ⟨?_, ?_⟩, ?_⟩
  · show eP.symm (eP x) ∈ U
    rw [eP.symm_apply_apply]
    exact hxU
  · -- non-surjectivity transfers
    intro hsurj
    apply hxcrit
    have hfdiff : DifferentiableAt ℝ f x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt infty_ne_zero
    have hFd : HasFDerivAt F
        ((eQ : EuclideanSpace ℝ (Fin q) →L[ℝ] (Fin q → ℝ)).comp
          ((fderiv ℝ f x).comp
            ((eP.symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p))))) (eP x) := by
      have h1 : HasFDerivAt (⇑eP.symm)
          ((eP.symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p))) (eP x) :=
        eP.symm.hasFDerivAt
      have h2 : HasFDerivAt f (fderiv ℝ f x) (eP.symm (eP x)) := by
        rw [eP.symm_apply_apply]
        exact hfdiff.hasFDerivAt
      exact (eQ.hasFDerivAt).comp _ (h2.comp _ h1)
    rw [hFd.fderiv] at hsurj
    intro y
    obtain ⟨ξ, hξ⟩ := hsurj (eQ y)
    refine ⟨eP.symm ξ, ?_⟩
    exact eQ.injective hξ
  · show eQ (f (eP.symm (eP x))) = WithLp.ofLp (f x)
    rw [eP.symm_apply_apply]
    rfl

/-- **Sard's theorem**, global-domain version.
@isnad1 id=eq.1h3v.s10.395f6e67833d from=translated src=- shape=e5cce02e vocab=3c1408e7
-/
theorem sard_global {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬Function.Surjective (fderiv ℝ f x)}) = 0 := by
  have h := sard isOpen_univ hf.contDiffOn
  simpa [fderivWithin_univ, Set.sep_univ] using h

/-! ## The easy case `p < q` -/

/-- **Sard's theorem, easy case.**  The range of a `C¹` map `ℝ^p → ℝ^q` with
`p < q` is Lebesgue-null.
@isnad1 id=eq.2h3v.s9.41e05158c37b from=translated src=- shape=68395597 vocab=8a9880bc
-/
theorem sard_of_lt (hpq : p < q)
    {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiff ℝ 1 f) : volume (Set.range f) = 0 := by
  set eP := EuclideanSpace.equiv (Fin p) ℝ with hePdef
  set eQ := EuclideanSpace.equiv (Fin q) ℝ with heQdef
  set F : (Fin p → ℝ) → Fin q → ℝ := fun x => eQ (f (eP.symm x)) with hFdef
  have hFsm : ContDiff ℝ 1 F := eQ.contDiff.comp (hf.comp eP.symm.contDiff)
  have hdim : dimH (Set.range F) ≤ (p : ENNReal) := by
    have h1 := hFsm.dimH_range_le
    rwa [Module.finrank_fin_fun] at h1
  have hlt : dimH (Set.range F) < ((q : NNReal) : ENNReal) := by
    refine lt_of_le_of_lt hdim ?_
    exact_mod_cast hpq
  have hH : μH[(q : NNReal)] (Set.range F) = 0 := hausdorffMeasure_of_dimH_lt hlt
  have hvol : volume (Set.range F) = 0 := by
    have h2 : (μH[Fintype.card (Fin q)] : Measure (Fin q → ℝ)) = volume :=
      hausdorffMeasure_pi_real
    rw [← h2]
    simpa using hH
  refine euclidean_null_of_pi_null ?_ hvol
  rintro _ ⟨x, rfl⟩
  refine ⟨eP x, ?_⟩
  show eQ (f (eP.symm (eP x))) = WithLp.ofLp (f x)
  rw [eP.symm_apply_apply]
  rfl

/-! ## Regular values -/

/-- `y` is a regular value of `f` if the differential of `f` is surjective at
every preimage of `y`.-/
def IsRegularValue (f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q))
    (y : EuclideanSpace ℝ (Fin q)) : Prop :=
  ∀ x, f x = y → Function.Surjective (fderiv ℝ f x)

/-- `y` is a regular value of `f` relative to the domain `U`.  The within
derivative makes this definition useful before an open-domain map has been
extended to the whole Euclidean space.-/
def IsRegularValueOn (f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q))
    (U : Set (EuclideanSpace ℝ (Fin p))) (y : EuclideanSpace ℝ (Fin q)) : Prop :=
  ∀ x, x ∈ U → f x = y → Function.Surjective (fderivWithin ℝ f U x)

/-- The regular values of a `C^∞` map on an open Euclidean domain are dense.
@isnad1 id=dense.2h4v.s8.26cd23f3a15b from=translated src=- shape=d981088c vocab=5bba8b89
-/
theorem sard_dense_regular_values_on
    {U : Set (EuclideanSpace ℝ (Fin p))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiffOn ℝ ∞ f U) : Dense {y | IsRegularValueOn f U y} := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  have hsub : O ⊆ f '' {x | x ∈ U ∧
      ¬Function.Surjective (fderivWithin ℝ f U x)} := by
    intro y hyO
    have hyreg : ¬IsRegularValueOn f U y := by
      intro hreg
      have : y ∈ O ∩ {y | IsRegularValueOn f U y} := ⟨hyO, hreg⟩
      rw [hemp] at this
      exact this
    rw [IsRegularValueOn] at hyreg
    obtain ⟨x, hx⟩ := not_forall.mp hyreg
    obtain ⟨hxU, hx⟩ := Classical.not_imp.mp hx
    obtain ⟨hfx, hnsurj⟩ := Classical.not_imp.mp hx
    exact ⟨x, ⟨hxU, hnsurj⟩, hfx⟩
  have hpos : 0 < volume O := hO.measure_pos volume hOne
  exact absurd (measure_mono_null hsub (sard hU hf)) hpos.ne'

/-- The set of regular values of a `C^∞` map is dense.
@isnad1 id=dense.1h3v.s7.45b1a67dbba2 from=translated src=- shape=182314a4 vocab=500d4acd
-/
theorem sard_dense_regular_values
    {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiff ℝ ∞ f) : Dense {y | IsRegularValue f y} := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  have hsub : O ⊆ f '' {x | ¬Function.Surjective (fderiv ℝ f x)} := by
    intro y hyO
    have hyreg : ¬IsRegularValue f y := by
      intro hreg
      have : y ∈ O ∩ {y | IsRegularValue f y} := ⟨hyO, hreg⟩
      rw [hemp] at this
      exact this
    rw [IsRegularValue] at hyreg
    obtain ⟨x, hx⟩ := not_forall.1 hyreg
    obtain ⟨hfx, hnsurj⟩ := Classical.not_imp.1 hx
    exact ⟨x, hnsurj, hfx⟩
  have hpos : 0 < volume O := hO.measure_pos volume hOne
  exact absurd (measure_mono_null hsub (sard_global hf)) hpos.ne'

/-- Every ball in the target of a `C^∞` map contains a regular value.
@isnad1 id=ex.2h5v.s8.73b4dfc4c8d5 from=translated src=- shape=2696ee34 vocab=a09f053b
-/
theorem sard_exists_regular_value_in_ball
    {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
    (hf : ContDiff ℝ ∞ f) (z : EuclideanSpace ℝ (Fin q)) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ Metric.ball z r, IsRegularValue f y := by
  obtain ⟨y, hy1, hy2⟩ := (sard_dense_regular_values hf).exists_mem_open
    Metric.isOpen_ball (Metric.nonempty_ball.2 hr)
  exact ⟨y, hy2, hy1⟩

/-! ## Knill's rank-deficient form -/

/-- **Sard's theorem, rank-deficient form** (Knill).  The image of the set of
points where the differential has rank less than both `m` and `n` is null.
(The rank-deficient set is contained in the non-surjectivity critical set.)
@isnad1 id=eq.1h3v.s12.9caf07ce487d from=translated src=- shape=e1a86bf9 vocab=5c8eec24
-/
theorem sard_rank_deficient {m n : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | Module.finrank ℝ
        (LinearMap.range ((fderiv ℝ f x) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n))) < m
      ∧ Module.finrank ℝ
        (LinearMap.range ((fderiv ℝ f x) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n))) < n}) = 0 := by
  refine measure_mono_null (Set.image_mono ?_) (sard_global hf)
  intro x hx
  simp only [mem_ofPred_eq] at hx
  intro hsurj
  have h1 : LinearMap.range ((fderiv ℝ f x) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) = ⊤ :=
    LinearMap.range_eq_top.2 (by exact hsurj)
  rw [h1] at hx
  have h2 : Module.finrank ℝ
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) = n := by
    rw [finrank_top]
    exact finrank_euclideanSpace_fin
  rw [h2] at hx
  exact absurd hx.2 (lt_irrefl n)

/-! ## Almost every real is a regular value of a smooth `f : ℝᵐ → ℝ` -/

/-- **Regular value theorem, a.e. form.**  For a `C^∞` function
`f : ℝᵐ → ℝ`, almost every `c : ℝ` is a regular value: every point of the
level set `f⁻¹(c)` has nonzero derivative.
@isnad1 id=eventual.1h2v.s10.2189737f9f14 from=translated src=- shape=e1592f6e vocab=45f1b7ed
-/
theorem regular_value_ae {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c ∂(volume : Measure ℝ), ∀ x, f x = c → fderiv ℝ f x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  set e1 := EuclideanSpace.equiv (Fin 1) ℝ with he1def
  set L1 : ℝ →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ with hL1def
  set F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 1) :=
    fun x => e1.symm (L1 (f x)) with hFdef
  have hFsm : ContDiff ℝ ∞ F :=
    e1.symm.contDiff.comp (L1.contDiff.comp hf)
  have hnull := sard_global hFsm
  -- the embedding `ℝ → EuclideanSpace ℝ (Fin 1)`, measure-preserving
  set j : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun c => WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm c)
    with hjdef
  have hjmp : MeasurePreserving j volume volume := by
    have h1 : MeasurePreserving
        (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ).symm)
        (volume : Measure ℝ) (volume : Measure (Fin 1 → ℝ)) :=
      (volume_preserving_funUnique (Fin 1) ℝ).symm
    have h2 : MeasurePreserving (WithLp.toLp (V := Fin 1 → ℝ) 2)
        (volume : Measure (Fin 1 → ℝ))
        (volume : Measure (EuclideanSpace ℝ (Fin 1))) :=
      PiLp.volume_preserving_toLp (Fin 1)
    exact h2.comp h1
  -- non-regular values pull back into the critical-value set of `F`
  have hsub : {c : ℝ | ¬∀ x, f x = c → fderiv ℝ f x ≠ 0}
      ⊆ j ⁻¹' (F '' {x | ¬Function.Surjective (fderiv ℝ F x)}) := by
    intro c hc
    simp only [mem_ofPred_eq, not_forall, not_not] at hc
    obtain ⟨x, hfx, hdx⟩ := hc
    have hFx : F x = j c := by
      have h3 : L1 (f x) = (MeasurableEquiv.funUnique (Fin 1) ℝ).symm c := by
        funext i
        show f x = c
        exact hfx
      show e1.symm (L1 (f x))
          = WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm c)
      rw [h3]
      rfl
    refine ⟨x, ?_, hFx⟩
    -- `fderiv F x = 0`, hence not surjective
    have hfd : HasFDerivAt f (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) x := by
      have h4 := (hf.differentiable infty_ne_zero x).hasFDerivAt
      rwa [hdx] at h4
    have hFd : HasFDerivAt F
        (((e1.symm : (Fin 1 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 1))).comp
          (L1.comp (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))) x :=
      e1.symm.hasFDerivAt.comp x (L1.hasFDerivAt.comp x hfd)
    have hFd0 : fderiv ℝ F x = 0 := by
      rw [hFd.fderiv, ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.comp_zero]
    intro hsurj
    rw [hFd0] at hsurj
    exact not_surjective_zero (E := EuclideanSpace ℝ (Fin m))
      (F := EuclideanSpace ℝ (Fin 1)) hsurj
  refine measure_mono_null hsub ?_
  exact hjmp.quasiMeasurePreserving.preimage_null hnull

end

end Submission
