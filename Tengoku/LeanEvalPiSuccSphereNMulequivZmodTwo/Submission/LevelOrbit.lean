import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Framed level sets: flow, periodic orbits, finiteness

For `X : FramedLevelSet n` we construct a globally defined, compactly supported smooth
vector field (`TamedField`) that agrees with the oriented unit kernel field `tauField`
on a neighbourhood of the fiber `M = X.fiber` and annihilates `fderiv X.g` everywhere.
Its flow is globally defined, leaves `M` invariant, and on `M` moves with unit speed
along the kernel line field.

Main results:

* `Submission.FramedLevelSet.exists_tamedField` : existence of the tamed field;
* `Submission.TamedField.exists_flow` : global solutions of `γ' = v (γ)`;
* `Submission.TamedField.flow_unique` : global uniqueness;
* `Submission.TamedField.mem_fiber_of_solution` : invariance of the fiber;
* `Submission.TamedField.exists_flowbox` : the local straightening (flow box) lemma;
* `Submission.TamedField.exists_period` : every solution through the fiber is periodic
  with a period `≥ 1/2`;
* orbit machinery: `orbit`, `orbit_eq_or_disjoint`, `exists_finite_orbit_cover`.
-/

noncomputable section

namespace Submission

open Set Function Metric Module
open scoped RealInnerProductSpace ContDiff Topology

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-- The unit kernel field always has norm at most one (it is either `0` or a unit
vector).
@isnad1 id=le.0h3v.s7.36dfd5f87d29 from=translated src=- shape=1bf990e0 vocab=d3795659
-/
lemma norm_tauField_le_one (g : E → F) (x : E) : ‖tauField g x‖ ≤ 1 := by
  rcases eq_or_ne (kerCross g x) 0 with h | h
  · rw [tauField, h, smul_zero, norm_zero]; norm_num
  · rw [tauField, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- A tamed version of the kernel field: a globally smooth, compactly supported vector
field of norm `≤ 1` that agrees with `tauField` on a `δ`-neighbourhood of the fiber and
annihilates `fderiv X.g` everywhere.-/
structure TamedField (X : FramedLevelSet n) where
  /-- The vector field.-/
  v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))
  /-- Radius of the collar around the fiber on which `v` equals `tauField`.-/
  delta : ℝ
  delta_pos : 0 < delta
  smooth : ContDiff ℝ ∞ v
  norm_le : ∀ x, ‖v x‖ ≤ 1
  eq_tau : ∀ x ∈ Metric.cthickening delta X.fiber, v x = tauField X.g x
  fderiv_zero : ∀ x, fderiv ℝ X.g x (v x) = 0
  lipschitz : ∃ K : NNReal, LipschitzWith K v

namespace FramedLevelSet

/-- Construction of a tamed field via a smooth Urysohn cutoff.
@isnad1 id=nonempty.0h2v.s3.4025a197468b from=translated src=- shape=1f8e965c vocab=c85eea4f
-/
theorem exists_tamedField (X : FramedLevelSet n) : Nonempty (TamedField X) := by
  -- choose a collar inside the regular set
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    X.isCompact_fiber.exists_cthickening_subset_open (isOpen_regularSet X.smooth)
      X.fiber_subset_regularSet
  set δ := δ₂ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = δ₂ := by rw [hδdef]; ring
  have hsub : Metric.cthickening (2 * δ) X.fiber ⊆ regularSet X.g := by
    rw [h2δ]; exact hδ₂sub
  -- smooth Urysohn function: 0 outside the collar, 1 near the fiber
  have hs : IsClosed (Metric.thickening (2 * δ) X.fiber)ᶜ :=
    Metric.isOpen_thickening.isClosed_compl
  have ht : IsClosed (Metric.cthickening δ X.fiber) := Metric.isClosed_cthickening
  have hd : Disjoint (Metric.thickening (2 * δ) X.fiber)ᶜ
      (Metric.cthickening δ X.fiber) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.cthickening_subset_thickening' (by positivity) (by linarith) _ hx')
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + 1))))
      (n := (⊤ : ℕ∞)) hs ht hd
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  -- smoothness of the field
  have hsmooth : ContDiff ℝ ∞ fun x => f x • tauField X.g x := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ regularSet X.g
    · exact hχ.contDiffAt.smul (((contDiffOn_tauField X.smooth) x hx).contDiffAt
        ((isOpen_regularSet X.smooth).mem_nhds hx))
    · -- outside the regular set the field vanishes on a neighbourhood
      have hxC : x ∈ (Metric.cthickening (2 * δ) X.fiber)ᶜ := fun hmem => hx (hsub hmem)
      have hU : IsOpen (Metric.cthickening (2 * δ) X.fiber)ᶜ :=
        Metric.isClosed_cthickening.isOpen_compl
      have hzero : ∀ y ∈ (Metric.cthickening (2 * δ) X.fiber)ᶜ,
          f y • tauField X.g y = 0 := by
        intro y hy
        have hy' : y ∈ (Metric.thickening (2 * δ) X.fiber)ᶜ := fun hmem =>
          hy (Metric.thickening_subset_cthickening _ _ hmem)
        have : f y = 0 := hf0 hy'
        rw [this, zero_smul]
      have hev : (fun y => f y • tauField X.g y) =ᶠ[𝓝 x] (fun _ => (0 : E)) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hxC) hzero
      exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev
  -- compact support
  have hsupp : HasCompactSupport fun x => f x • tauField X.g x := by
    have h1 : support (fun x => f x • tauField X.g x) ⊆
        Metric.thickening (2 * δ) X.fiber := by
      intro x hx
      by_contra hmem
      have : f x = 0 := hf0 hmem
      apply hx
      show f x • tauField X.g x = 0
      rw [this, zero_smul]
    have h2 : tsupport (fun x => f x • tauField X.g x) ⊆
        Metric.cthickening (2 * δ) X.fiber :=
      closure_minimal (h1.trans (Metric.thickening_subset_cthickening _ _))
        Metric.isClosed_cthickening
    exact IsCompact.of_isClosed_subset (X.isCompact_fiber.cthickening)
      isClosed_closure h2
  -- the tamed field
  refine ⟨⟨fun x => f x • tauField X.g x, δ, hδpos, hsmooth, ?_, ?_, ?_, ?_⟩⟩
  · -- norm bound
    intro x
    rw [norm_smul]
    have h1 : ‖f x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
    calc ‖f x‖ * ‖tauField X.g x‖ ≤ 1 * 1 :=
          mul_le_mul h1 (norm_tauField_le_one X.g x) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  · -- equality with `tauField` near the fiber
    intro x hx
    have : f x = 1 := hf1 hx
    rw [this, one_smul]
  · -- the field lies in the kernel of `fderiv X.g` everywhere
    intro x
    rw [map_smul, fderiv_tauField_eq_zero, smul_zero]
  · -- Lipschitz, via compact support
    exact hsmooth.lipschitzWith_of_hasCompactSupport hsupp (by simp)

end FramedLevelSet

/-! ## Global flow of a tamed field -/

namespace TamedField

variable {X : FramedLevelSet n} (V : TamedField X)

/-- Global uniqueness for solutions of the tamed ODE.
@isnad1 id=eq.3h6v.s9.6ea6ede691ac from=translated src=- shape=d8916027 vocab=214fe94c
-/
theorem solution_unique {γ₁ γ₂ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (h₁ : ∀ t, HasDerivAt γ₁ (V.v (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (V.v (γ₂ t)) t)
    {t₀ : ℝ} (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  obtain ⟨K, hK⟩ := V.lipschitz
  exact ODE_solution_unique_univ (v := fun _ x => V.v x) (s := fun _ => univ)
    (t₀ := t₀) (fun _ => hK.lipschitzOnWith)
    (fun t => ⟨h₁ t, mem_univ _⟩) (fun t => ⟨h₂ t, mem_univ _⟩) heq

/-- Global existence for the tamed ODE: the field is bounded and globally Lipschitz,
so Picard–Lindelöf solutions on arbitrarily large intervals can be glued.
@isnad1 id=ex.0h4v.s8.3acb3c4ff33d from=translated src=- shape=e25caec9 vocab=214fe94c
-/
theorem exists_solution (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      γ 0 = p ∧ ∀ t, HasDerivAt γ (V.v (γ t)) t := by
  obtain ⟨K, hK⟩ := V.lipschitz
  -- solutions on `Ioo (-(T+1)) (T+1)` for every `T : ℕ`
  have main : ∀ T : ℕ, ∃ α : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      α 0 = p ∧ ∀ t ∈ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ), HasDerivAt α (V.v (α t)) t := by
    intro T
    have h0mem : (0 : ℝ) ∈ Icc (-(T + 1 : ℝ)) (T + 1 : ℝ) := by
      constructor
      · have : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
      · have : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
    have hpl : IsPicardLindelof (fun (_ : ℝ) x => V.v x)
        (⟨0, h0mem⟩ : Icc (-(T + 1 : ℝ)) (T + 1 : ℝ)) p (T + 2 : ℕ) 0 1 K := by
      constructor
      · exact fun t _ => hK.lipschitzOnWith
      · exact fun x _ => continuousOn_const
      · intro t _ x _
        simpa using V.norm_le x
      · show (1 : ℝ) * max ((T + 1 : ℝ) - 0) (0 - -(T + 1 : ℝ)) ≤ (T + 2 : ℕ) - (0 : ℝ)
        push_cast
        have h0T : (0 : ℝ) ≤ T := T.cast_nonneg
        rw [one_mul]
        apply max_le <;> linarith
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self le_rfl)
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose α hα0 hαs using main
  -- any two of the local solutions agree on the common interval
  have agree : ∀ (T S : ℕ) (t : ℝ), |t| < T + 1 → |t| < S + 1 → α T t = α S t := by
    intro T S t hT hS
    set m : ℕ := min T S with hm
    have hmT : (m : ℝ) + 1 ≤ (T : ℝ) + 1 := by
      have : (m : ℕ) ≤ T := min_le_left T S
      exact_mod_cast by omega
    have hmS : (m : ℝ) + 1 ≤ (S : ℝ) + 1 := by
      have : (m : ℕ) ≤ S := min_le_right T S
      exact_mod_cast by omega
    have htm : |t| < (m : ℝ) + 1 := by
      rcases min_choice T S with h | h <;> rw [hm, h]
      · exact hT
      · exact hS
    have hsub : Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) ⊆ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have hsub' : Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) ⊆ Ioo (-(S + 1 : ℝ)) (S + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have h0m : (0 : ℝ) ∈ Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) := by
      constructor
      · have : (0 : ℝ) ≤ m := m.cast_nonneg
        linarith
      · have : (0 : ℝ) ≤ m := m.cast_nonneg
        linarith
    have := ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) x => V.v x)
      (s := fun _ => univ) (K := K)
      (fun t _ => hK.lipschitzOnWith) h0m
      (fun u hu => ⟨hαs T u (hsub hu), mem_univ _⟩)
      (fun u hu => ⟨hαs S u (hsub' hu), mem_univ _⟩)
      ((hα0 T).trans (hα0 S).symm)
    exact this ⟨(abs_lt.mp htm).1, (abs_lt.mp htm).2⟩
  -- glue: at time `t` use the solution with index `⌊|t|⌋`
  refine ⟨fun t => α (Nat.floor |t|) t, ?_, ?_⟩
  · simpa using hα0 (Nat.floor |(0 : ℝ)|)
  · intro t
    set N : ℕ := Nat.floor |t| with hN
    have htN : |t| < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hev : (fun s => α (Nat.floor |s|) s) =ᶠ[𝓝 t] α N := by
      have hUopen : IsOpen {s : ℝ | |s| < (N : ℝ) + 1} :=
        isOpen_lt (continuous_abs) continuous_const
      refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds htN) fun s hs => ?_
      exact agree (Nat.floor |s|) N s (Nat.lt_floor_add_one _) hs
    have hder : HasDerivAt (α N) (V.v (α N t)) t := by
      apply hαs N t
      have := abs_lt.mp htN
      exact ⟨this.1, this.2⟩
    have : HasDerivAt (fun s => α (Nat.floor |s|) s) (V.v (α N t)) t :=
      (Filter.EventuallyEq.hasDerivAt_iff hev).mpr hder
    simpa [← hN] using this

/-- The canonical global solution through `p`.-/
def flow (p : EuclideanSpace ℝ (Fin (n + 1))) : ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
  Classical.choose (V.exists_solution p)

/--
@isnad1 id=eq.0h4v.s5.9bb8e41ab6ab from=translated src=- shape=4cddb410 vocab=12b25469
-/
@[simp] lemma flow_zero (p : EuclideanSpace ℝ (Fin (n + 1))) : V.flow p 0 = p :=
  (Classical.choose_spec (V.exists_solution p)).1

/--
@isnad1 id=hasderiv.0h5v.s8.6680bc6d668f from=translated src=- shape=b79f9f53 vocab=9d876115
-/
lemma hasDerivAt_flow (p : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    HasDerivAt (V.flow p) (V.v (V.flow p t)) t :=
  (Classical.choose_spec (V.exists_solution p)).2 t

/--
@isnad1 id=continuo.0h4v.s6.04887e0667d7 from=translated src=- shape=7afd15ec vocab=b7fe8557
-/
lemma continuous_flow (p : EuclideanSpace ℝ (Fin (n + 1))) : Continuous (V.flow p) :=
  continuous_iff_continuousAt.mpr fun t => (V.hasDerivAt_flow p t).continuousAt

/-- Invariance: a solution of the tamed ODE starting on the fiber stays on the fiber
(the value of `X.g` is constant along any solution).
@isnad1 id=mem.2h5v.s8.f928f7659005 from=translated src=- shape=aafc6ce8 vocab=9ea74f49
-/
theorem solution_mem_fiber {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : ∀ t, HasDerivAt γ (V.v (γ t)) t) (h0 : γ 0 ∈ X.fiber) :
    ∀ t, γ t ∈ X.fiber := by
  have hcomp : ∀ t, HasDerivAt (fun s => X.g (γ s)) 0 t := by
    intro t
    have hgdiff : HasFDerivAt X.g (fderiv ℝ X.g (γ t)) (γ t) :=
      (X.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have := hgdiff.comp_hasDerivAt t (hγ t)
    rwa [V.fderiv_zero (γ t)] at this
  have hconst : ∀ t, X.g (γ t) = X.g (γ 0) := by
    intro t
    exact is_const_of_deriv_eq_zero
      (fun s => (hcomp s).differentiableAt)
      (fun s => (hcomp s).deriv) t 0
  intro t
  have := hconst t
  rw [show X.g (γ 0) = 0 from h0] at this
  exact this

/--
@isnad1 id=mem.1h5v.s7.7d1deadb5a64 from=translated src=- shape=fe8fe741 vocab=7fbc5723
-/
lemma flow_mem_fiber {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) (t : ℝ) :
    V.flow p t ∈ X.fiber :=
  V.solution_mem_fiber (V.hasDerivAt_flow p) (by rw [V.flow_zero]; exact hp) t

/-- On the fiber, the tamed field agrees with the unit kernel field.
@isnad1 id=eq.1h4v.s6.cf7f7b36f736 from=translated src=- shape=adcd57d7 vocab=17c0499b
-/
lemma v_eq_tau_of_mem_fiber {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ X.fiber) :
    V.v x = tauField X.g x :=
  V.eq_tau x (Metric.self_subset_cthickening _ hx)

end TamedField

/-! ## The flow box lemma -/

/-- The straightening map at `q`: level of `g` paired with the displacement along the
kernel direction.-/
def straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) × ℝ :=
  fun y => (X.g y, ⟪tauField X.g q, y - q⟫)

/-- The derivative of the straightening map at `q`, as a continuous linear map.-/
def straightenDeriv (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
  (fderiv ℝ X.g q).prod (innerSL ℝ (tauField X.g q))

/--
@isnad1 id=bijectiv.1h3v.s10.15926f79abb0 from=translated src=- shape=b83eacb5 vocab=546b0aba
-/
lemma straightenDeriv_bijective (X : FramedLevelSet n)
    {q : EuclideanSpace ℝ (Fin (n + 1))} (hq : q ∈ X.fiber) :
    Function.Bijective (straightenDeriv X q) := by
  have hreg : q ∈ regularSet X.g := X.fiber_subset_regularSet hq
  have hinj : Function.Injective (straightenDeriv X q) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : fderiv ℝ X.g q w = 0 := congrArg Prod.fst hw
    have h2 : ⟪tauField X.g q, w⟫ = 0 := congrArg Prod.snd hw
    have hmem : w ∈ Submodule.span ℝ {tauField X.g q} :=
      (fderiv_eq_zero_iff_mem_span_tauField hreg w).mp h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hnorm : ‖tauField X.g q‖ = 1 := norm_tauField hreg
    rw [← ha, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm] at h2
    have : a = 0 := by simpa using h2
    rw [← ha, this, zero_smul]
  constructor
  · exact hinj
  · have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
        = finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
      rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin,
        Module.finrank_self]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj

/--
@isnad1 id=contdiff.0h3v.s8.15b854cfbaca from=translated src=- shape=f10ee8ae vocab=b1f14e19
-/
lemma contDiff_straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    ContDiff ℝ ∞ (straighten X q) := by
  apply ContDiff.prodMk X.smooth
  exact ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const)

/--
@isnad1 id=hasfderi.0h3v.s9.711498458581 from=translated src=- shape=453fdf29 vocab=f8ecde6d
-/
lemma hasFDerivAt_straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (straighten X q) (straightenDeriv X q) q := by
  apply HasFDerivAt.prodMk
  · exact (X.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  · have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y - q)
        (ContinuousLinearMap.id ℝ _) q := (hasFDerivAt_id q).sub_const q
    have h2 := (innerSL ℝ (tauField X.g q)).hasFDerivAt.comp q h1
    simpa [Function.comp_def] using h2

/-- **Flow box lemma.** Near a fiber point `q`, every fiber point in a small ball lies
on the flow line through `q`, at a time as small as desired.
@isnad1 id=ex.2h5v.s8.43c58d93be00 from=translated src=- shape=7b2ba735 vocab=aae2c461
-/
theorem TamedField.exists_flowbox {X : FramedLevelSet n} (V : TamedField X)
    {q : EuclideanSpace ℝ (Fin (n + 1))} (hq : q ∈ X.fiber) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ x ∈ X.fiber ∩ ball q r, ∃ s : ℝ, |s| < c ∧ V.flow q s = x := by
  classical
  have hreg : q ∈ regularSet X.g := X.fiber_subset_regularSet hq
  set τq := tauField X.g q with hτq
  have hτnorm : ‖τq‖ = 1 := norm_tauField hreg
  -- inverse function theorem for the straightening map
  set L₀ : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    LinearEquiv.ofBijective ((straightenDeriv X q) : _ →ₗ[ℝ] _)
      (straightenDeriv_bijective X hq) with hL₀
  set L : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    L₀.toContinuousLinearEquiv with hL
  have hLcoe : (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ)
      = straightenDeriv X q := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hΦq : HasFDerivAt (straighten X q)
      (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ) q := by
    rw [hLcoe]
    exact hasFDerivAt_straighten X q
  set P := (contDiff_straighten X q).contDiffAt.toOpenPartialHomeomorph
    (straighten X q) hΦq (by simp) with hP
  have hPcoe : ⇑P = straighten X q :=
    (contDiff_straighten X q).contDiffAt.toOpenPartialHomeomorph_coe hΦq (by simp)
  have hqmem : q ∈ P.source :=
    (contDiff_straighten X q).contDiffAt.mem_toOpenPartialHomeomorph_source hΦq (by simp)
  have hPinj : InjOn (straighten X q) P.source := by
    rw [← hPcoe]
    intro a ha b hb hab
    rw [← P.left_inv ha, ← P.left_inv hb, hab]
  -- the flow through `q` and the displacement function
  set γ := V.flow q with hγ
  have hγM : ∀ t, γ t ∈ X.fiber := V.flow_mem_fiber hq
  set h : ℝ → ℝ := fun s => ⟪τq, γ s - q⟫ with hh
  have hh0 : h 0 = 0 := by
    simp [hh, hγ, V.flow_zero]
  have hder : ∀ s, HasDerivAt h ⟪τq, V.v (γ s)⟫ s := by
    intro s
    have h1 : HasDerivAt (fun _ : ℝ => τq) 0 s := hasDerivAt_const s τq
    have h2 : HasDerivAt (fun u => γ u - q) (V.v (γ s)) s :=
      (V.hasDerivAt_flow q s).sub_const q
    have := h1.inner ℝ h2
    simpa using this
  have hcont' : Continuous fun s => ⟪τq, V.v (γ s)⟫ :=
    continuous_const.inner (V.smooth.continuous.comp (V.continuous_flow q))
  have hder0 : ⟪τq, V.v (γ 0)⟫ = 1 := by
    rw [hγ, V.flow_zero, V.v_eq_tau_of_mem_fiber hq, ← hτq,
      real_inner_self_eq_norm_sq, hτnorm]
    norm_num
  -- a small interval on which the flow stays in the chart and moves forward
  have hSopen : IsOpen {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    apply IsOpen.inter
    · exact P.open_source.preimage (V.continuous_flow q)
    · exact isOpen_lt continuous_const hcont'
  have hS0 : (0 : ℝ) ∈ {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    constructor
    · rw [hγ, V.flow_zero]; exact hqmem
    · rw [hder0]; norm_num
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hSopen 0 hS0
  set c' := min (ε / 2) (c / 2) with hc'
  have hc'pos : 0 < c' := lt_min (by linarith) (by linarith)
  have hc'lt : c' < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hIccS : Icc (-c') c' ⊆ {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    intro s hs
    apply hεball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 : |s| ≤ c' := abs_le.mpr ⟨hs.1, hs.2⟩
    have h2 : c' ≤ ε / 2 := min_le_left _ _
    linarith
  -- lower bounds for the displacement at the interval ends
  have hdiff : ∀ s, DifferentiableAt ℝ h s := fun s => (hder s).differentiableAt
  have hderiv_gt : ∀ s ∈ interior (Icc (-c') c'), 1 / 2 < deriv h s := by
    intro s hs
    rw [interior_Icc] at hs
    have hmem : s ∈ Icc (-c') c' := Ioo_subset_Icc_self hs
    rw [(hder s).deriv]
    exact (hIccS hmem).2
  have hbound := Convex.mul_sub_lt_image_sub_of_lt_deriv (convex_Icc (-c') c')
    (fun s _ => (hdiff s).continuousAt.continuousWithinAt)
    (fun s _ => (hdiff s).differentiableWithinAt) hderiv_gt
  have hhc' : c' / 2 < h c' := by
    have := hbound 0 (by constructor <;> [linarith; linarith]) c'
      (by constructor <;> [linarith; linarith]) hc'pos
    rw [hh0] at this
    linarith
  have hhmc' : h (-c') < -(c' / 2) := by
    have := hbound (-c') (by constructor <;> [linarith; linarith]) 0
      (by constructor <;> [linarith; linarith]) (by linarith)
    rw [hh0] at this
    linarith
  -- choose the radius
  obtain ⟨r₀, hr₀pos, hr₀ball⟩ := Metric.isOpen_iff.mp P.open_source q hqmem
  refine ⟨min (c' / 2) r₀, lt_min (by linarith) hr₀pos, ?_⟩
  rintro x ⟨hxM, hxball⟩
  set σ := ⟪τq, x - q⟫ with hσ
  have hσsmall : |σ| < c' / 2 := by
    calc |σ| ≤ ‖τq‖ * ‖x - q‖ := abs_real_inner_le_norm _ _
      _ = ‖x - q‖ := by rw [hτnorm, one_mul]
      _ < min (c' / 2) r₀ := by
          rw [← dist_eq_norm]
          exact hxball
      _ ≤ c' / 2 := min_le_left _ _
  -- IVT for the displacement function
  have hcontIcc : ContinuousOn h (Icc (-c') c') :=
    fun s _ => (hdiff s).continuousAt.continuousWithinAt
  have hσmem : σ ∈ Icc (h (-c')) (h c') := by
    have h1 : -(c' / 2) < σ := by
      have := abs_lt.mp hσsmall
      linarith [this.1]
    have h2 : σ < c' / 2 := (abs_lt.mp hσsmall).2
    constructor
    · linarith
    · linarith
  obtain ⟨s, hsmem, hseq⟩ := intermediate_value_Icc (by linarith : -c' ≤ c') hcontIcc hσmem
  refine ⟨s, ?_, ?_⟩
  · have : |s| ≤ c' := abs_le.mpr ⟨hsmem.1, hsmem.2⟩
    linarith
  -- both points lie in the chart and have the same image
  · have hγsM : γ s ∈ X.fiber := hγM s
    have hγssource : γ s ∈ P.source := (hIccS hsmem).1
    have hxsource : x ∈ P.source := hr₀ball (by
      have : dist x q < min (c' / 2) r₀ := hxball
      exact Metric.mem_ball.mpr (lt_of_lt_of_le this (min_le_right _ _)))
    apply hPinj hγssource hxsource
    show straighten X q (γ s) = straighten X q x
    have e1 : X.g (γ s) = 0 := hγsM
    have e2 : X.g x = 0 := hxM
    show ((X.g (γ s), ⟪τq, γ s - q⟫) : EuclideanSpace ℝ (Fin n) × ℝ)
        = (X.g x, ⟪τq, x - q⟫)
    rw [e1, e2]
    exact congrArg (Prod.mk (0 : EuclideanSpace ℝ (Fin n))) hseq

/-! ## Periodicity -/

namespace TamedField

variable {X : FramedLevelSet n} (V : TamedField X)

/-- Time-shifts of solutions are solutions.
@isnad1 id=hasderiv.1h6v.s9.092e0253264a from=translated src=- shape=9ae3334b vocab=214fe94c
-/
lemma hasDerivAt_shift {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : ∀ t, HasDerivAt γ (V.v (γ t)) t) (a : ℝ) (u : ℝ) :
    HasDerivAt (fun w => γ (a + w)) (V.v (γ (a + u))) u := by
  have h1 : HasDerivAt (fun w : ℝ => a + w) 1 u := (hasDerivAt_id u).const_add a
  have h2 := (hγ (a + u)).scomp u h1
  simpa [Function.comp_def] using h2

/-- The flow shifted in time is the flow of the shifted starting point.
@isnad1 id=eq.0h5v.s6.46980d7354cd from=translated src=- shape=126393eb vocab=12b25469
-/
lemma flow_shift (p : EuclideanSpace ℝ (Fin (n + 1))) (a : ℝ) :
    V.flow (V.flow p a) = fun u => V.flow p (a + u) := by
  apply V.solution_unique (t₀ := 0)
  · exact V.hasDerivAt_flow (V.flow p a)
  · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) a u
  · simp

/-- **Periodicity**: the flow line through any fiber point is periodic, with a period
bounded below by `1/2`.
@isnad1 id=ex.1h4v.s7.520d3be0276e from=translated src=- shape=3570317b vocab=5fded15f
-/
theorem exists_period {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    ∃ T : ℝ, 1 / 2 ≤ T ∧ Function.Periodic (V.flow p) T := by
  classical
  set γ := V.flow p with hγdef
  have hγM : ∀ t, γ t ∈ X.fiber := V.flow_mem_fiber hp
  -- an accumulation point of the integer-time sequence
  obtain ⟨q, hqM, φ, hφmono, hφlim⟩ :=
    X.isCompact_fiber.tendsto_subseq (x := fun k : ℕ => γ k) (fun k => hγM k)
  -- flow box at the accumulation point
  obtain ⟨r, hrpos, hbox⟩ := V.exists_flowbox hqM (c := 1 / 4) (by norm_num)
  have hev : ∀ᶠ m in Filter.atTop, dist (γ (φ m)) q < r := by
    have := Metric.tendsto_nhds.mp hφlim r hrpos
    exact this
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  set k₁ : ℕ := φ K with hk₁
  set k₂ : ℕ := φ (K + 1) with hk₂
  have hk₁₂ : k₁ + 1 ≤ k₂ := by
    have := hφmono (show K < K + 1 by omega)
    omega
  obtain ⟨s₁, hs₁, hγs₁⟩ := hbox (γ k₁) ⟨hγM _, Metric.mem_ball.mpr (hK K le_rfl)⟩
  obtain ⟨s₂, hs₂, hγs₂⟩ := hbox (γ k₂) ⟨hγM _, Metric.mem_ball.mpr (hK (K + 1) (by omega))⟩
  -- unique continuation along the flow through `q`
  have huniq₁ : (fun u => γ (k₁ + u)) = fun u => V.flow q (s₁ + u) := by
    apply V.solution_unique (t₀ := 0)
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) k₁ u
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow q) s₁ u
    · simpa using hγs₁.symm
  have huniq₂ : (fun u => γ (k₂ + u)) = fun u => V.flow q (s₂ + u) := by
    apply V.solution_unique (t₀ := 0)
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) k₂ u
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow q) s₂ u
    · simpa using hγs₂.symm
  set T : ℝ := ((k₂ : ℝ) - k₁) + s₁ - s₂ with hT
  have hTpos : 1 / 2 ≤ T := by
    have hcast : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast hk₁₂
    have h₁ := abs_lt.mp hs₁
    have h₂ := abs_lt.mp hs₂
    rw [hT]
    linarith [h₁.1, h₂.2]
  refine ⟨T, hTpos, ?_⟩
  intro t
  -- γ t = flow q (s₁ + (t - k₁)) and γ (t + T) = flow q (s₂ + (t + T - k₂))
  have e1 : γ t = V.flow q (s₁ + (t - k₁)) := by
    have := congrFun huniq₁ (t - k₁)
    simpa using this
  have e2 : γ (t + T) = V.flow q (s₂ + (t + T - k₂)) := by
    have := congrFun huniq₂ (t + T - k₂)
    have harg : (k₂ : ℝ) + (t + T - k₂) = t + T := by ring
    rw [harg] at this
    exact this
  have e3 : s₂ + (t + T - k₂) = s₁ + (t - k₁) := by rw [hT]; ring
  rw [e2, e3, ← e1]

/-! ## Orbits -/

/-- The orbit of a point: the image of the flow line through it.-/
def orbit (p : EuclideanSpace ℝ (Fin (n + 1))) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  range (V.flow p)

/--
@isnad1 id=mem.0h4v.s6.ac818a03c9bb from=translated src=- shape=b414a93e vocab=947910e8
-/
lemma mem_orbit_self (p : EuclideanSpace ℝ (Fin (n + 1))) : p ∈ V.orbit p :=
  ⟨0, V.flow_zero p⟩

/--
@isnad1 id=mem.0h5v.s6.1ba047558457 from=translated src=- shape=160d1862 vocab=4bdabfd1
-/
lemma flow_mem_orbit (p : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    V.flow p t ∈ V.orbit p := ⟨t, rfl⟩

/--
@isnad1 id=le.1h4v.s6.38ff5ce4eaa8 from=translated src=- shape=5423ac67 vocab=10b923d2
-/
lemma orbit_subset_fiber {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    V.orbit p ⊆ X.fiber := by
  rintro x ⟨t, rfl⟩
  exact V.flow_mem_fiber hp t

/-- Orbits through points of an orbit coincide with the original orbit.
@isnad1 id=eq.1h5v.s7.fcf4f8a2e3e1 from=translated src=- shape=3fd59d1a vocab=947910e8
-/
lemma orbit_eq_of_mem {p x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ V.orbit p) :
    V.orbit x = V.orbit p := by
  obtain ⟨a, rfl⟩ := hx
  have hsh := V.flow_shift p a
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    rw [congrFun hsh u]
    exact ⟨a + u, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - a, ?_⟩
    rw [congrFun hsh (t - a)]
    congr 1
    ring

/-- Orbits of fiber points are compact (continuous periodic image of `[0, T]`).
@isnad1 id=iscompac.1h4v.s7.6f789ce12a1a from=translated src=- shape=fa448f77 vocab=e0cd7488
-/
lemma isCompact_orbit {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    IsCompact (V.orbit p) := by
  obtain ⟨T, hT, hper⟩ := V.exists_period hp
  have himg : V.flow p '' Icc 0 (0 + T) = range (V.flow p) :=
    hper.image_Icc (by linarith) 0
  rw [orbit, ← himg]
  exact (isCompact_Icc).image (V.continuous_flow p)

/-- Orbits of fiber points are relatively open in the fiber.
@isnad1 id=ex.2h5v.s8.7c56ecaa5e0d from=translated src=- shape=7a682892 vocab=8f47b95d
-/
lemma orbit_isOpen_in_fiber {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ X.fiber) (hq : q ∈ V.orbit p) :
    ∃ r > 0, X.fiber ∩ ball q r ⊆ V.orbit p := by
  have hqM : q ∈ X.fiber := V.orbit_subset_fiber hp hq
  obtain ⟨r, hrpos, hbox⟩ := V.exists_flowbox hqM (c := 1) (by norm_num)
  refine ⟨r, hrpos, ?_⟩
  rintro x ⟨hxM, hxball⟩
  obtain ⟨s, _, hs⟩ := hbox x ⟨hxM, hxball⟩
  have : x ∈ V.orbit q := ⟨s, hs⟩
  rwa [V.orbit_eq_of_mem hq] at this

/-- Two orbits of fiber points either coincide or are disjoint.
@isnad1 id=or.0h5v.s8.1876c5923538 from=translated src=- shape=683e5af9 vocab=da345420
-/
theorem orbit_eq_or_disjoint {p q : EuclideanSpace ℝ (Fin (n + 1))} :
    V.orbit p = V.orbit q ∨ Disjoint (V.orbit p) (V.orbit q) := by
  by_cases h : Disjoint (V.orbit p) (V.orbit q)
  · exact Or.inr h
  · left
    obtain ⟨x, hxp, hxq⟩ := Set.not_disjoint_iff.mp h
    rw [← V.orbit_eq_of_mem hxp, ← V.orbit_eq_of_mem hxq]

/-- **Finiteness**: the fiber is a finite union of orbits.
@isnad1 id=ex.0h3v.s8.2467c2f63328 from=translated src=- shape=5ae1577d vocab=7254e7f0
-/
theorem exists_finite_orbit_cover :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ q ∈ s, q ∈ X.fiber) ∧ X.fiber = ⋃ q ∈ s, V.orbit q := by
  classical
  have hkey : ∀ q, q ∈ X.fiber → ∃ r, 0 < r ∧ X.fiber ∩ ball q r ⊆ V.orbit q :=
    fun q hq => by
      obtain ⟨r, hrpos, hsub⟩ := V.orbit_isOpen_in_fiber hq (V.mem_orbit_self q)
      exact ⟨r, hrpos, hsub⟩
  choose! rad hradpos hradsub using hkey
  have hcover : X.fiber ⊆ ⋃ q ∈ X.fiber, ball q (rad q) := by
    intro x hx
    exact mem_biUnion hx (Metric.mem_ball_self (hradpos x hx))
  obtain ⟨b', hb'sub, hb'fin, hb'cover⟩ :=
    X.isCompact_fiber.elim_finite_subcover_image
      (fun q _ => Metric.isOpen_ball) hcover
  refine ⟨hb'fin.toFinset, ?_, ?_⟩
  · intro q hq
    exact hb'sub (hb'fin.mem_toFinset.mp hq)
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hqb', hxball⟩ := mem_iUnion₂.mp (hb'cover hx)
      have hqM : q ∈ X.fiber := hb'sub hqb'
      have : x ∈ V.orbit q := hradsub q hqM ⟨hx, hxball⟩
      exact mem_biUnion (hb'fin.mem_toFinset.mpr hqb') this
    · intro x hx
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
      exact V.orbit_subset_fiber (hb'sub (hb'fin.mem_toFinset.mp hq)) hxq

end TamedField

end Submission
