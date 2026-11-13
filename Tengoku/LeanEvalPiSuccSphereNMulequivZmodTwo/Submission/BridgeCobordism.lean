import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.BridgeLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Framed level cobordisms (Wave 4A)

The cobordism-level counterpart of `FramedLevelSet`: a smooth map
`G : ℝ^{n+2} → ℝⁿ` (last coordinate = time) which is `0`-regular on its fiber,
spatially bounded on the fiber, and constant in time near the two ends, where it
restricts to the presentations `X₀.g` and `X₁.g` of two framed level sets.

Contents:

* `Submission.spaceTime` and its coordinate lemmas — the affine embedding
  `ℝ^{n+1} × ℝ → ℝ^{n+2}` in `Fin.snoc` coordinates;
* `Submission.FramedLevelCobordism` — the data structure (matching the M2
  implementation spec: time collars at `t ≤ 1/4` and `t ≥ 3/4`);
* end-collar lemmas: `Submission.FramedLevelCobordism.slice_eq_zero/one`
  (the time slices near the ends are literally the end presentations) and
  `Submission.surjective_fderiv_of_time_collar` (regularity at end fiber points is
  inherited from end regularity — the derivative of `G` at a collar point contains
  the spatial derivative of the end map);
* `Submission.FramedLevelCobordism.refl` — the constant (cylinder) cobordism of a
  framed level set, a fully verified instance of the structure;
* `Submission.timeInterp` — the smooth-transition time interpolation of two
  presentations, with its collar lemmas (regularity is *not* asserted, as it
  genuinely fails for non-generic pairs);
* `Submission.FramedLevelCobordism.trans` — gluing of cobordisms along a common
  middle level set, via affine (triple-speed) time reparametrizations switching
  inside the common constant slab — fully verified;
* `Submission.CobApproximation` / `Submission.exists_cobApproximation` — the
  space-time smooth approximation of a homotopy between two bridge
  representatives, exact on the time collars and `1/8`-close to the south pole
  over the spatial complement of the cube;
* the plateaued space-time pipeline `nrawCob → prawCob → nprepCob → hMapCob`
  with time-collar identifications, southern collapse (`hMapCob_south`), the
  fiber dichotomy `hMapCob_eq_iff` and the **north/south criterion**
  `nprepCob_eq_northPoint_iff` on the cobordism fiber;
* `Submission.exists_small_regular_value` (Sard in the small punctured ball) and
  the end-regularity inheritance `isRegularValue_left_of_cob` /
  `isRegularValue_right_of_cob` (a Sard value of the space-time map is
  automatically regular for both end maps);
* `Submission.middleCob` / `Submission.exists_middle_cobordism` — the fully
  constructed **common-value cobordism**: homotopic representatives yield a
  common regular value `y` and a framed level cobordism
  `bridgeFLS a₁ y ⇝ bridgeFLS a₂ y`;
* `Submission.exists_valueChange_cobordism` — the value-change cobordism
  (Milnor Lemma B), proved by a flat quotient and relative Sard argument;
* `Submission.exists_bridge_cobordism` — the main homotopy ⟹ cobordism theorem,
  proved by gluing `value-change ⬝ middle ⬝ value-change` with `trans`.
-/

noncomputable section

open scoped Topology unitInterval ContDiff
open Metric Set Function Topology.Homotopy

namespace Submission

variable {n : ℕ}

/-! ### Space-time coordinates -/

/-- The affine embedding of space-time `ℝ^{n+1} × ℝ` into `ℝ^{n+2}`: the last
coordinate is time.-/
def spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)

/--
@isnad1 id=eq.0h3v.s10.e2f9ed548f08 from=translated src=- shape=9186efab vocab=f6e5c580
-/
lemma initCLM_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    initCLM (n + 1) (spaceTime x t) = x := by
  apply (WithLp.equiv 2 _).injective
  funext j
  show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) j.castSucc = x j
  exact Fin.snoc_castSucc _ _ j

/--
@isnad1 id=eq.0h3v.s5.f8b60d050b81 from=translated src=- shape=f5f7f7e1 vocab=80e1a222
-/
lemma vertC_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    vertC (spaceTime x t) = t := by
  show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) (Fin.last (n + 1)) = t
  exact Fin.snoc_last _ _

/-- Space-time embedding as an affine map: linear part plus constant.
@isnad1 id=eq.0h3v.s11.f064efbdcfd8 from=translated src=- shape=0f138a77 vocab=dd7fa1df
-/
lemma spaceTime_eq_affine (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    spaceTime x t = embedCLM (n + 1) x + t • eLast (n + 1) := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
    show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) (Fin.last (n + 1)) = _
    rw [Fin.snoc_last]
    simp [eLast]
  | cast j =>
    have hne : (j.castSucc : Fin (n + 1 + 1)) ≠ Fin.last (n + 1) :=
      (Fin.castSucc_lt_last j).ne
    show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) j.castSucc = _
    rw [Fin.snoc_castSucc]
    simp [eLast, hne]

/--
@isnad1 id=surjecti.0h1v.s10.348f9e2b2a5c from=translated src=- shape=160e8b2a vocab=381c0585
-/
lemma surjective_initCLM_succ :
    Function.Surjective (initCLM (n + 1) :
      EuclideanSpace ℝ (Fin (n + 1 + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :=
  fun x => ⟨spaceTime x 0, initCLM_spaceTime x 0⟩

/-- The space-time embedding at a fixed time has the space embedding as
derivative.
@isnad1 id=hasfderi.0h3v.s9.14ba5a1f4bd1 from=translated src=- shape=29406bae vocab=7009052b
-/
lemma hasFDerivAt_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    HasFDerivAt (fun x' => spaceTime x' t) (embedCLM (n + 1)) x := by
  have h : (fun x' : EuclideanSpace ℝ (Fin (n + 1)) => spaceTime x' t)
      = fun x' => embedCLM (n + 1) x' + t • eLast (n + 1) :=
    funext fun x' => spaceTime_eq_affine x' t
  rw [h]
  exact (embedCLM (n + 1)).hasFDerivAt.add_const _

/-- Reconstruction: every point of space-time is `spaceTime` of its spatial and
time parts.
@isnad1 id=eq.0h2v.s10.d44312e400b2 from=translated src=- shape=4a1965f3 vocab=8fb3356e
-/
lemma spaceTime_init_vert (w : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    spaceTime (initCLM (n + 1) w) (vertC w) = w := by
  apply (WithLp.equiv 2 _).injective
  show Fin.snoc (Fin.init (WithLp.ofLp w)) (vertC w) = WithLp.ofLp w
  exact Fin.snoc_init_self _

/-! ### Affine time reparametrizations -/

/-- The linear part of the time reparametrization `(x, t) ↦ (x, s·t)`.-/
def reparamCLM (n : ℕ) (s : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1 + 1)) :=
  (embedCLM (n + 1)).comp (initCLM (n + 1))
    + s • ((EuclideanSpace.proj (Fin.last (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 1 + 1)) →L[ℝ] ℝ).smulRight (eLast (n + 1)))

/--
@isnad1 id=eq.0h3v.s12.835a3f191e90 from=translated src=- shape=1214eefa vocab=cfd422a1
-/
lemma reparamCLM_apply (s : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    reparamCLM n s v
      = embedCLM (n + 1) (initCLM (n + 1) v) + (s * vertC v) • eLast (n + 1) := by
  have h1 : (EuclideanSpace.proj (Fin.last (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1 + 1)) →L[ℝ] ℝ) v = vertC v := rfl
  simp only [reparamCLM, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, smul_smul]

/-- The affine time reparametrization `(x, t) ↦ (x, s·t + c)`.-/
def reparamMap (n : ℕ) (s c : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) :=
  spaceTime (initCLM (n + 1) v) (s * vertC v + c)

/--
@isnad1 id=eq.0h3v.s11.c078eea5f346 from=translated src=- shape=1858ca75 vocab=52e32edd
-/
lemma reparamMap_eq_affine (s c : ℝ) :
    reparamMap n s c = fun v => reparamCLM n s v + c • eLast (n + 1) := by
  funext v
  rw [reparamMap, spaceTime_eq_affine, reparamCLM_apply, add_smul]
  exact (add_assoc _ _ _).symm

/--
@isnad1 id=contdiff.0h3v.s9.bf1760b9e987 from=translated src=- shape=97785895 vocab=b83b7322
-/
lemma contDiff_reparamMap (s c : ℝ) : ContDiff ℝ ∞ (reparamMap n s c) := by
  rw [reparamMap_eq_affine]
  exact (reparamCLM n s).contDiff.add contDiff_const

/--
@isnad1 id=hasfderi.0h4v.s9.0d0575e11805 from=translated src=- shape=9e4ffccf vocab=9bfb5b04
-/
lemma hasFDerivAt_reparamMap (s c : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    HasFDerivAt (reparamMap n s c) (reparamCLM n s) v := by
  rw [reparamMap_eq_affine]
  exact (reparamCLM n s).hasFDerivAt.add_const _

/--
@isnad1 id=eq.0h4v.s11.185351f01e82 from=translated src=- shape=16273546 vocab=8ae48938
-/
lemma reparamCLM_spaceTime (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) (τ : ℝ) :
    reparamCLM n s (spaceTime x τ) = spaceTime x (s * τ) := by
  rw [reparamCLM_apply, initCLM_spaceTime, vertC_spaceTime,
    spaceTime_eq_affine x (s * τ)]

/--
@isnad1 id=surjecti.1h2v.s11.97b432c81813 from=translated src=- shape=382a5c78 vocab=dcdb63bc
-/
lemma surjective_reparamCLM {s : ℝ} (hs : s ≠ 0) :
    Function.Surjective (reparamCLM n s) := by
  intro ζ
  refine ⟨spaceTime (initCLM (n + 1) ζ) (vertC ζ / s), ?_⟩
  rw [reparamCLM_spaceTime, mul_div_cancel₀ _ hs, spaceTime_init_vert]

/-! ### The cobordism structure -/

/-- A framed level cobordism between two framed level sets: a smooth
`G : ℝ^{n+2} → ℝⁿ`, `0`-regular on its fiber, spatially bounded on the fiber,
with time collars near the ends where it is constant in time and equal to the
respective end presentations.-/
structure FramedLevelCobordism (n : ℕ) where
  /-- The incoming framed level set.-/
  X₀ : FramedLevelSet n
  /-- The outgoing framed level set.-/
  X₁ : FramedLevelSet n
  /-- The defining map on space-time; the last coordinate is time.-/
  G : EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n)
  /-- Smoothness.-/
  smooth : ContDiff ℝ ∞ G
  /-- The fiber is spatially bounded.-/
  spatial_bounded : ∃ R, ∀ v, G v = 0 → ‖initCLM (n + 1) v‖ ≤ R
  /-- `0` is a regular value.-/
  regular : ∀ v, G v = 0 → Function.Surjective (fderiv ℝ G v)
  /-- Incoming time collar: for `t ≤ 1/4` the map is the incoming presentation.-/
  collar_zero : ∀ x t, t ≤ 1 / 4 → G (spaceTime x t) = X₀.g x
  /-- Outgoing time collar: for `t ≥ 3/4` the map is the outgoing presentation.-/
  collar_one : ∀ x t, 3 / 4 ≤ t → G (spaceTime x t) = X₁.g x

namespace FramedLevelCobordism

variable (C : FramedLevelCobordism n)

/-- The time-`t` slice of the cobordism.-/
def slice (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
  fun x => C.G (spaceTime x t)

/--
@isnad1 id=eq.1h3v.s6.530b31cd8456 from=translated src=- shape=843d8d19 vocab=1405bae0
-/
lemma slice_eq_zero {t : ℝ} (ht : t ≤ 1 / 4) : C.slice t = C.X₀.g :=
  funext fun x => C.collar_zero x t ht

/--
@isnad1 id=eq.1h3v.s6.f22a7e4f4f70 from=translated src=- shape=a40b27b5 vocab=072fce04
-/
lemma slice_eq_one {t : ℝ} (ht : 3 / 4 ≤ t) : C.slice t = C.X₁.g :=
  funext fun x => C.collar_one x t ht

/-- Slab form of the incoming collar: on the whole slab `{vert ≤ 1/4}` the map is
the incoming presentation of the spatial part.-/
lemma eq_on_slab_zero {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hv : vertC v ≤ 1 / 4) : C.G v = C.X₀.g (initCLM (n + 1) v) := by
  conv_lhs => rw [← spaceTime_init_vert v]
  exact C.collar_zero _ _ hv

/-- Slab form of the outgoing collar.-/
lemma eq_on_slab_one {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hv : 3 / 4 ≤ vertC v) : C.G v = C.X₁.g (initCLM (n + 1) v) := by
  conv_lhs => rw [← spaceTime_init_vert v]
  exact C.collar_one _ _ hv

/-- The fiber of the cobordism restricted to the time slab `[0, 1]`.-/
def fiber : Set (EuclideanSpace ℝ (Fin (n + 1 + 1))) :=
  {v | C.G v = 0 ∧ 0 ≤ vertC v ∧ vertC v ≤ 1}

/--
@isnad1 id=isbounde.0h2v.s7.0b270ecdee51 from=translated src=- shape=39475db5 vocab=9258c0da
-/
lemma isBounded_fiber : Bornology.IsBounded C.fiber := by
  obtain ⟨R, hR⟩ := C.spatial_bounded
  apply (Metric.isBounded_closedBall
    (x := (0 : EuclideanSpace ℝ (Fin (n + 1 + 1)))) (r := |R| + 1)).subset
  rintro v ⟨hv0, hvt0, hvt1⟩
  rw [mem_closedBall, dist_zero_right]
  have h1 : ‖v‖ ^ 2 = ‖initCLM (n + 1) v‖ ^ 2 + vertC v ^ 2 := norm_sq_split v
  have h2 : ‖initCLM (n + 1) v‖ ≤ |R| := (hR v hv0).trans (le_abs_self R)
  have h3 : vertC v ^ 2 ≤ 1 := by nlinarith
  have h4 : ‖v‖ ^ 2 ≤ (|R| + 1) ^ 2 := by
    have h5 : ‖initCLM (n + 1) v‖ ^ 2 ≤ |R| ^ 2 := by
      nlinarith [norm_nonneg (initCLM (n + 1) v), abs_nonneg R]
    nlinarith [abs_nonneg R]
  nlinarith [norm_nonneg v, abs_nonneg R]

end FramedLevelCobordism

/-! ### End-collar regularity inheritance -/

/-- Chain rule along the fixed-time embedding.
@isnad1 id=eq.1h4v.s11.ca8f34608ac1 from=translated src=- shape=f242064e vocab=ae4f18b1
-/
lemma fderiv_comp_spaceTime {G : EuclideanSpace ℝ (Fin (n + 1 + 1)) →
      EuclideanSpace ℝ (Fin n)} (hG : ContDiff ℝ ∞ G)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    fderiv ℝ (fun x' => G (spaceTime x' t)) x
      = (fderiv ℝ G (spaceTime x t)).comp (embedCLM (n + 1)) := by
  have hGd : HasFDerivAt G (fderiv ℝ G (spaceTime x t)) (spaceTime x t) :=
    (hG.differentiable infty_ne_zero _).hasFDerivAt
  exact (hGd.comp x (hasFDerivAt_spaceTime x t)).fderiv

/-- Regularity at an end-collar fiber point is inherited from the end
presentation: if `G` is constant in time on the collar, equal there to `g₀`, and
`g₀` has surjective differential at `x`, then `G` has surjective differential at
`(x, t)` for any collar time `t`.  This is the mechanism by which a common Sard
value for `G` is automatically regular for both ends.
@isnad1 id=surjecti.4h6v.s12.423009d54c71 from=translated src=- shape=3109daba vocab=3c367781
-/
theorem surjective_fderiv_of_time_collar
    {G : EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n)}
    (hG : ContDiff ℝ ∞ G)
    {g₀ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)} {c : ℝ}
    (hcol : ∀ x' t', t' ≤ c → G (spaceTime x' t') = g₀ x')
    {x : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (ht : t ≤ c)
    (hsurj : Function.Surjective (fderiv ℝ g₀ x)) :
    Function.Surjective (fderiv ℝ G (spaceTime x t)) := by
  have hfun : g₀ = fun x' => G (spaceTime x' t) :=
    funext fun x' => (hcol x' t ht).symm
  have hEq : fderiv ℝ g₀ x
      = (fderiv ℝ G (spaceTime x t)).comp (embedCLM (n + 1)) := by
    rw [hfun]
    exact fderiv_comp_spaceTime hG x t
  rw [hEq, ContinuousLinearMap.coe_comp] at hsurj
  exact hsurj.of_comp

/-- The outgoing-collar analogue of `surjective_fderiv_of_time_collar`.
@isnad1 id=surjecti.4h6v.s12.d2666e0d3b22 from=translated src=- shape=56d65b62 vocab=3c367781
-/
theorem surjective_fderiv_of_time_collar_right
    {G : EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n)}
    (hG : ContDiff ℝ ∞ G)
    {g₁ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)} {c : ℝ}
    (hcol : ∀ x' t', c ≤ t' → G (spaceTime x' t') = g₁ x')
    {x : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (ht : c ≤ t)
    (hsurj : Function.Surjective (fderiv ℝ g₁ x)) :
    Function.Surjective (fderiv ℝ G (spaceTime x t)) := by
  have hfun : g₁ = fun x' => G (spaceTime x' t) :=
    funext fun x' => (hcol x' t ht).symm
  have hEq : fderiv ℝ g₁ x
      = (fderiv ℝ G (spaceTime x t)).comp (embedCLM (n + 1)) := by
    rw [hfun]
    exact fderiv_comp_spaceTime hG x t
  rw [hEq, ContinuousLinearMap.coe_comp] at hsurj
  exact hsurj.of_comp

/-! ### The cylinder cobordism -/

/-- The constant (cylinder) cobordism on a framed level set: a fully verified
instance of `FramedLevelCobordism`.-/
def FramedLevelCobordism.refl (X : FramedLevelSet n) : FramedLevelCobordism n where
  X₀ := X
  X₁ := X
  G := fun v => X.g (initCLM (n + 1) v)
  smooth := X.smooth.comp (initCLM (n + 1)).contDiff
  spatial_bounded := by
    obtain ⟨R, hR⟩ := X.fiber_bounded.subset_closedBall 0
    refine ⟨R, fun v hv => ?_⟩
    have hmem : initCLM (n + 1) v ∈ X.fiber := hv
    have := hR hmem
    rwa [mem_closedBall, dist_zero_right] at this
  regular := by
    intro v hv
    have hgd : HasFDerivAt X.g (fderiv ℝ X.g (initCLM (n + 1) v))
        (initCLM (n + 1) v) :=
      (X.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have hcomp := hgd.comp v (initCLM (n + 1)).hasFDerivAt
    have hEq : fderiv ℝ (fun v => X.g (initCLM (n + 1) v)) v
        = (fderiv ℝ X.g (initCLM (n + 1) v)).comp (initCLM (n + 1)) :=
      hcomp.fderiv
    rw [hEq, ContinuousLinearMap.coe_comp]
    exact (X.regular _ hv).comp surjective_initCLM_succ
  collar_zero := fun x t _ => by rw [initCLM_spaceTime]
  collar_one := fun x t _ => by rw [initCLM_spaceTime]

/-! ### Gluing (composition) of cobordisms -/

/-- The underlying map of the glued cobordism: run `C₁` at triple speed on
`[1/4, 5/12]` and `C₂` at triple speed on `[7/12, 3/4]` via affine time
reparametrizations, switching at `t = 1/2` inside the common constant slab.-/
def transFun (C₁ C₂ : FramedLevelCobordism n) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n) :=
  fun v => if vertC v < 1 / 2 then C₁.G (reparamMap n 3 (-(1 / 2)) v)
    else C₂.G (reparamMap n 3 (-(3 / 2)) v)

/--
@isnad1 id=eq.3h4v.s10.3aa57803c83b from=translated src=- shape=7ad06ed1 vocab=95743f3f
-/
lemma transFun_middle {C₁ C₂ : FramedLevelCobordism n} (h : C₁.X₁ = C₂.X₀)
    {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (h1 : 5 / 12 < vertC v) (h2 : vertC v < 7 / 12) :
    transFun C₁ C₂ v = C₂.X₀.g (initCLM (n + 1) v) := by
  rw [transFun]
  by_cases hv : vertC v < 1 / 2
  · rw [ite_eq_left hv]
    have hcol := C₁.collar_one (initCLM (n + 1) v) (3 * vertC v + -(1 / 2))
      (by linarith)
    rw [reparamMap, hcol, h]
  · rw [ite_eq_right hv]
    exact C₂.collar_zero (initCLM (n + 1) v) (3 * vertC v + -(3 / 2)) (by linarith)

/--
@isnad1 id=isopen.0h2v.s7.48f0c706e63f from=translated src=- shape=3b2170e0 vocab=964736db
-/
lemma isOpen_vert_lt (c : ℝ) :
    IsOpen {w : EuclideanSpace ℝ (Fin (n + 1 + 1)) | vertC w < c} :=
  isOpen_lt contDiff_vertC.continuous continuous_const

/--
@isnad1 id=isopen.0h2v.s7.30d9113fe6e5 from=translated src=- shape=ecbad568 vocab=964736db
-/
lemma isOpen_lt_vert (c : ℝ) :
    IsOpen {w : EuclideanSpace ℝ (Fin (n + 1 + 1)) | c < vertC w} :=
  isOpen_lt continuous_const contDiff_vertC.continuous

/--
@isnad1 id=isopen.0h3v.s7.d58f3f8c67fc from=translated src=- shape=bdecf016 vocab=964736db
-/
lemma isOpen_vert_between (c c' : ℝ) :
    IsOpen {w : EuclideanSpace ℝ (Fin (n + 1 + 1)) | c < vertC w ∧ vertC w < c'} :=
  (isOpen_lt_vert c).inter (isOpen_vert_lt c')

/--
@isnad1 id=contdiff.1h3v.s8.94526f5c8325 from=translated src=- shape=0bff33b2 vocab=adcc5b37
-/
lemma contDiff_transFun {C₁ C₂ : FramedLevelCobordism n} (h : C₁.X₁ = C₂.X₀) :
    ContDiff ℝ ∞ (transFun C₁ C₂) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  rcases lt_trichotomy (vertC v) (1 / 2) with hv | hv | hv
  · refine ((C₁.smooth.comp (contDiff_reparamMap 3 (-(1 / 2)))).contDiffAt).congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem ((isOpen_vert_lt (1 / 2)).mem_nhds hv)
      fun w hw => ite_eq_left hw
  · refine ((C₂.X₀.smooth.comp (initCLM (n + 1)).contDiff).contDiffAt).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      ((isOpen_vert_between (5 / 12) (7 / 12)).mem_nhds ⟨by rw [hv]; norm_num, by rw [hv]; norm_num⟩)
      fun w hw => transFun_middle h hw.1 hw.2
  · refine ((C₂.smooth.comp (contDiff_reparamMap 3 (-(3 / 2)))).contDiffAt).congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem ((isOpen_lt_vert (1 / 2)).mem_nhds hv)
      fun w hw => ite_eq_right (not_lt.mpr (le_of_lt hw))

/--
@isnad1 id=surjecti.2h4v.s11.af703d170f12 from=translated src=- shape=7cd4f201 vocab=76ac0975
-/
lemma transFun_regular {C₁ C₂ : FramedLevelCobordism n} (h : C₁.X₁ = C₂.X₀) :
    ∀ v, transFun C₁ C₂ v = 0 →
      Function.Surjective (fderiv ℝ (transFun C₁ C₂) v) := by
  intro v hv
  rcases lt_trichotomy (vertC v) (1 / 2) with hlt | heq | hgt
  · have hEv : transFun C₁ C₂ =ᶠ[𝓝 v]
        fun w => C₁.G (reparamMap n 3 (-(1 / 2)) w) :=
      Filter.eventuallyEq_of_mem ((isOpen_vert_lt (1 / 2)).mem_nhds hlt)
        fun w hw => ite_eq_left hw
    have hval : C₁.G (reparamMap n 3 (-(1 / 2)) v) = 0 := by
      rw [← hv, transFun, ite_eq_left hlt]
    have hGd : HasFDerivAt C₁.G (fderiv ℝ C₁.G (reparamMap n 3 (-(1 / 2)) v))
        (reparamMap n 3 (-(1 / 2)) v) :=
      (C₁.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have hfd : fderiv ℝ (transFun C₁ C₂) v
        = (fderiv ℝ C₁.G (reparamMap n 3 (-(1 / 2)) v)).comp (reparamCLM n 3) := by
      rw [hEv.fderiv_eq]
      exact (hGd.comp v (hasFDerivAt_reparamMap 3 (-(1 / 2)) v)).fderiv
    rw [hfd, ContinuousLinearMap.coe_comp]
    exact (C₁.regular _ hval).comp (surjective_reparamCLM (by norm_num))
  · have hmem : (5 : ℝ) / 12 < vertC v ∧ vertC v < 7 / 12 :=
      ⟨by rw [heq]; norm_num, by rw [heq]; norm_num⟩
    have hEv : transFun C₁ C₂ =ᶠ[𝓝 v]
        fun w => C₂.X₀.g (initCLM (n + 1) w) :=
      Filter.eventuallyEq_of_mem
        ((isOpen_vert_between (5 / 12) (7 / 12)).mem_nhds hmem)
        fun w hw => transFun_middle h hw.1 hw.2
    have hval : C₂.X₀.g (initCLM (n + 1) v) = 0 := by
      rw [← transFun_middle h hmem.1 hmem.2]
      exact hv
    have hGd : HasFDerivAt C₂.X₀.g (fderiv ℝ C₂.X₀.g (initCLM (n + 1) v))
        (initCLM (n + 1) v) :=
      (C₂.X₀.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have hfd : fderiv ℝ (transFun C₁ C₂) v
        = (fderiv ℝ C₂.X₀.g (initCLM (n + 1) v)).comp (initCLM (n + 1)) := by
      rw [hEv.fderiv_eq]
      exact (hGd.comp v (initCLM (n + 1)).hasFDerivAt).fderiv
    rw [hfd, ContinuousLinearMap.coe_comp]
    exact (C₂.X₀.regular _ hval).comp surjective_initCLM_succ
  · have hEv : transFun C₁ C₂ =ᶠ[𝓝 v]
        fun w => C₂.G (reparamMap n 3 (-(3 / 2)) w) :=
      Filter.eventuallyEq_of_mem ((isOpen_lt_vert (1 / 2)).mem_nhds hgt)
        fun w hw => ite_eq_right (not_lt.mpr (le_of_lt hw))
    have hval : C₂.G (reparamMap n 3 (-(3 / 2)) v) = 0 := by
      rw [← hv, transFun, ite_eq_right (not_lt.mpr (le_of_lt hgt))]
    have hGd : HasFDerivAt C₂.G (fderiv ℝ C₂.G (reparamMap n 3 (-(3 / 2)) v))
        (reparamMap n 3 (-(3 / 2)) v) :=
      (C₂.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have hfd : fderiv ℝ (transFun C₁ C₂) v
        = (fderiv ℝ C₂.G (reparamMap n 3 (-(3 / 2)) v)).comp (reparamCLM n 3) := by
      rw [hEv.fderiv_eq]
      exact (hGd.comp v (hasFDerivAt_reparamMap 3 (-(3 / 2)) v)).fderiv
    rw [hfd, ContinuousLinearMap.coe_comp]
    exact (C₂.regular _ hval).comp (surjective_reparamCLM (by norm_num))

/-- Gluing (composition) of framed level cobordisms along a common middle level
set.-/
def FramedLevelCobordism.trans (C₁ C₂ : FramedLevelCobordism n)
    (h : C₁.X₁ = C₂.X₀) : FramedLevelCobordism n where
  X₀ := C₁.X₀
  X₁ := C₂.X₁
  G := transFun C₁ C₂
  smooth := contDiff_transFun h
  spatial_bounded := by
    obtain ⟨R₁, hR₁⟩ := C₁.spatial_bounded
    obtain ⟨R₂, hR₂⟩ := C₂.spatial_bounded
    refine ⟨max R₁ R₂, fun v hv => ?_⟩
    by_cases hc : vertC v < 1 / 2
    · rw [transFun, ite_eq_left hc] at hv
      have := hR₁ _ hv
      rw [reparamMap, initCLM_spaceTime] at this
      exact this.trans (le_max_left _ _)
    · rw [transFun, ite_eq_right hc] at hv
      have := hR₂ _ hv
      rw [reparamMap, initCLM_spaceTime] at this
      exact this.trans (le_max_right _ _)
  regular := transFun_regular h
  collar_zero := by
    intro x t ht
    have hvt : vertC (spaceTime x t) = t := vertC_spaceTime x t
    rw [transFun, ite_eq_left (by rw [hvt]; linarith)]
    rw [reparamMap, initCLM_spaceTime, hvt]
    exact C₁.collar_zero x _ (by linarith)
  collar_one := by
    intro x t ht
    have hvt : vertC (spaceTime x t) = t := vertC_spaceTime x t
    rw [transFun, ite_eq_right (by rw [hvt]; intro hc; linarith)]
    rw [reparamMap, initCLM_spaceTime, hvt]
    exact C₂.collar_one x _ (by linarith)

/--
@isnad1 id=eq.1h3v.s4.714c2fa85039 from=translated src=- shape=e525c2b3 vocab=dabff7d4
-/
@[simp] lemma FramedLevelCobordism.trans_X₀ (C₁ C₂ : FramedLevelCobordism n)
    (h : C₁.X₁ = C₂.X₀) : (C₁.trans C₂ h).X₀ = C₁.X₀ := rfl

/--
@isnad1 id=eq.1h3v.s4.83482748b58e from=translated src=- shape=85c875f4 vocab=dabff7d4
-/
@[simp] lemma FramedLevelCobordism.trans_X₁ (C₁ C₂ : FramedLevelCobordism n)
    (h : C₁.X₁ = C₂.X₀) : (C₁.trans C₂ h).X₁ = C₂.X₁ := rfl

/-! ### Time interpolation glue -/

/-- The time-transition profile: `0` for `t ≤ 1/4`, `1` for `t ≥ 3/4`.-/
def timeProfile (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

/--
@isnad1 id=eq.1h1v.s5.cef4b44bdeb2 from=translated src=- shape=44469b40 vocab=1f8d506b
-/
lemma timeProfile_of_le {t : ℝ} (ht : t ≤ 1 / 4) : timeProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/--
@isnad1 id=eq.1h1v.s5.e4221255ac58 from=translated src=- shape=c1676f1c vocab=1f8d506b
-/
lemma timeProfile_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : timeProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/--
@isnad1 id=contdiff.0h0v.s5.34a0dad0e7da from=translated src=- shape=3cea26be vocab=517ba14d
-/
lemma contDiff_timeProfile : ContDiff ℝ ∞ timeProfile :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The smooth time interpolation of two presentations `g₀`, `g₁`: satisfies both
collar conditions.  (Regularity is a separate, non-automatic matter.)-/
def timeInterp (g₀ g₁ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n) :=
  fun v => (1 - timeProfile (vertC v)) • g₀ (initCLM (n + 1) v)
    + timeProfile (vertC v) • g₁ (initCLM (n + 1) v)

/--
@isnad1 id=eq.1h5v.s6.513266116f64 from=translated src=- shape=6f4d00ba vocab=430fa04c
-/
lemma timeInterp_collar_zero
    (g₀ g₁ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : t ≤ 1 / 4) :
    timeInterp g₀ g₁ (spaceTime x t) = g₀ x := by
  rw [timeInterp, vertC_spaceTime, timeProfile_of_le ht, initCLM_spaceTime]
  simp

/--
@isnad1 id=eq.1h5v.s6.bf76ff5bfebe from=translated src=- shape=009500c0 vocab=430fa04c
-/
lemma timeInterp_collar_one
    (g₀ g₁ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 3 / 4 ≤ t) :
    timeInterp g₀ g₁ (spaceTime x t) = g₁ x := by
  rw [timeInterp, vertC_spaceTime, timeProfile_of_ge ht, initCLM_spaceTime]
  simp

/-! ### Space-time coordinates on the pi-type domain -/

/-- Spatial part of a pi-type space-time point.-/
def piInit (v : Fin (n + 1 + 1) → ℝ) : Fin (n + 1) → ℝ := Fin.init v

/-- Time part of a pi-type space-time point.-/
def piTime (v : Fin (n + 1 + 1) → ℝ) : ℝ := v (Fin.last (n + 1))

/--
@isnad1 id=contdiff.0h1v.s8.4e4c8bd5c412 from=translated src=- shape=f864da43 vocab=ea06b28f
-/
lemma contDiff_piInit : ContDiff ℝ ∞ (piInit (n := n)) := by
  rw [contDiff_pi]
  intro j
  show ContDiff ℝ ∞ fun v : Fin (n + 1 + 1) → ℝ => v j.castSucc
  exact (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (n + 1 + 1) => ℝ) j.castSucc).contDiff

/--
@isnad1 id=continuo.0h1v.s7.babd523b1b36 from=translated src=- shape=5224432a vocab=9d8348f3
-/
lemma continuous_piInit : Continuous (piInit (n := n)) :=
  contDiff_piInit.continuous

/--
@isnad1 id=continuo.0h1v.s6.118d51cfb71d from=translated src=- shape=d5362c06 vocab=4372145b
-/
lemma continuous_piTime : Continuous (piTime (n := n)) :=
  continuous_apply _

/--
@isnad1 id=eq.0h2v.s6.94ca2b5c841e from=translated src=- shape=72c34198 vocab=8fb5e855
-/
lemma piTime_ofLp (X : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    piTime (WithLp.ofLp X) = vertC X := rfl

/--
@isnad1 id=eq.0h2v.s10.a525cb5b55d3 from=translated src=- shape=2d28573f vocab=0dc6d30f
-/
lemma piInit_ofLp (X : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    piInit (WithLp.ofLp X) = WithLp.ofLp (initCLM (n + 1) X) := rfl

/--
@isnad1 id=eq.0h3v.s6.7a68caca90b5 from=translated src=- shape=240f2c46 vocab=ec5bcfae
-/
lemma piTime_ofLp_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    piTime (WithLp.ofLp (spaceTime x t)) = t := by
  show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) (Fin.last (n + 1)) = t
  exact Fin.snoc_last _ _

/--
@isnad1 id=eq.0h3v.s7.dda71ee53745 from=translated src=- shape=dcc5ae5d vocab=42666f21
-/
lemma piInit_ofLp_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    piInit (WithLp.ofLp (spaceTime x t)) = WithLp.ofLp x := by
  show Fin.init (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t) = WithLp.ofLp x
  exact Fin.init_snoc _ _

/-! ### Clamping and the normalized raw map -/

/-- The normalized raw map does not see the cube clamp.
@isnad1 id=eq.0h4v.s10.cbf36fa59bfe from=translated src=- shape=44cfe02f vocab=a0b2f997
-/
lemma nraw_cubeClamp {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) (x : Fin (n + 1) → ℝ) :
    nraw a (fun i => ((cubeClamp x i : ℝ))) = nraw a x := by
  by_cases hin : ∀ i, 0 ≤ x i ∧ x i ≤ 1
  · have hco : (fun i => ((cubeClamp x i : ℝ))) = x := by
      funext i
      show ((Set.projIcc (0 : ℝ) 1 zero_le_one (x i) : I) : ℝ) = x i
      rw [Set.coe_projIcc, min_eq_right (hin i).2, max_eq_right (hin i).1]
    rw [hco]
  · rw [not_forall] at hin
    obtain ⟨i, hi⟩ := hin
    rcases not_and_or.mp hi with hi | hi
    · rw [not_le] at hi
      have h1 : x ∈ closedAmbientCollar (Fin (n + 1)) := ⟨i, Or.inl (by linarith)⟩
      have h2 : (fun i => ((cubeClamp x i : ℝ))) ∈ closedAmbientCollar (Fin (n + 1)) := by
        refine ⟨i, Or.inl ?_⟩
        show ((Set.projIcc (0 : ℝ) 1 zero_le_one (x i) : I) : ℝ) ≤ 1 / 5
        rw [projIcc_eq_zero (le_of_lt hi), Set.Icc.coe_zero]
        norm_num
      show ‖a.raw _‖⁻¹ • a.raw _ = ‖a.raw x‖⁻¹ • a.raw x
      rw [a.raw_eq_basepoint_on_collar _ h2, a.raw_eq_basepoint_on_collar _ h1]
    · rw [not_le] at hi
      have h1 : x ∈ closedAmbientCollar (Fin (n + 1)) := ⟨i, Or.inr (by linarith)⟩
      have h2 : (fun i => ((cubeClamp x i : ℝ))) ∈ closedAmbientCollar (Fin (n + 1)) := by
        refine ⟨i, Or.inr ?_⟩
        show (4 / 5 : ℝ) ≤ ((Set.projIcc (0 : ℝ) 1 zero_le_one (x i) : I) : ℝ)
        rw [projIcc_eq_one (le_of_lt hi), Set.Icc.coe_one]
        norm_num
      show ‖a.raw _‖⁻¹ • a.raw _ = ‖a.raw x‖⁻¹ • a.raw x
      rw [a.raw_eq_basepoint_on_collar _ h2, a.raw_eq_basepoint_on_collar _ h1]

/-! ### The space-time smooth approximation of a homotopy -/

variable {p₁ p₂ : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)}

/-- The space-time raw data of a smooth approximation of a homotopy between the
representatives of two approximations: a `C^∞` nonvanishing map on `ℝ^{n+2}`,
equal to the ends' normalized raw maps on the time collars, and `1/8`-close to the
south pole over the spatial complement of the open cube.-/
structure CobApproximation (a₁ : Approximation p₁) (a₂ : Approximation p₂) where
  /-- The smooth space-time raw map.-/
  rawC : (Fin (n + 1 + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))
  contDiff_rawC : ContDiff ℝ ∞ rawC
  rawC_ne_zero : ∀ v, rawC v ≠ 0
  rawC_left : ∀ v, piTime v ≤ 1 / 4 → rawC v = nraw a₁ (piInit v)
  rawC_right : ∀ v, 3 / 4 ≤ piTime v → rawC v = nraw a₂ (piInit v)
  rawC_south : ∀ v, (∃ j, piInit v j ≤ 0 ∨ 1 ≤ piInit v j) →
    dist (rawC v) (-eLast n) < 1 / 8

/-- The time schedule of the space-time extension: `0` for `t ≤ 3/8`, `1` for
`t ≥ 5/8`.-/
def cobSchedule (t : ℝ) : I := Set.projIcc 0 1 zero_le_one (4 * t - 3 / 2)

/--
@isnad1 id=eq.1h1v.s5.5244460f452e from=translated src=- shape=ef6b2476 vocab=82990c26
-/
lemma cobSchedule_of_le {t : ℝ} (ht : t ≤ 3 / 8) : cobSchedule t = 0 :=
  projIcc_eq_zero (by linarith)

/--
@isnad1 id=eq.1h1v.s5.d5f92319c484 from=translated src=- shape=53a79c4c vocab=82990c26
-/
lemma cobSchedule_of_ge {t : ℝ} (ht : 5 / 8 ≤ t) : cobSchedule t = 1 :=
  projIcc_eq_one (by linarith)

/--
@isnad1 id=continuo.0h0v.s4.505ed90359f2 from=translated src=- shape=28fc0566 vocab=73d6fa5a
-/
lemma continuous_cobSchedule : Continuous cobSchedule :=
  continuous_projIcc.comp (by fun_prop)

/-- Existence of space-time approximations, from a homotopy rel boundary between
the representatives.
@isnad1 id=nonempty.1h5v.s12.788e7adfbbf4 from=translated src=- shape=4fa774a9 vocab=fad12cc5
-/
theorem exists_cobApproximation {a₁ : Approximation p₁} {a₂ : Approximation p₂}
    (hpq : GenLoop.Homotopic a₁.representative a₂.representative) :
    Nonempty (CobApproximation a₁ a₂) := by
  obtain ⟨H⟩ := hpq
  -- the continuous space-time extension, unit-sphere valued
  set Q : (Fin (n + 1 + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) := fun v =>
    ((H (cobSchedule (piTime v), cubeClamp (piInit v)) :
      UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) :
        EuclideanSpace ℝ (Fin (n + 1))) with hQdef
  have hQc : Continuous Q := by
    apply continuous_subtype_val.comp
    apply (map_continuous H.toHomotopy.toContinuousMap).comp
    exact (continuous_cobSchedule.comp continuous_piTime).prodMk
      (continuous_cubeClamp.comp continuous_piInit)
  have hQnorm : ∀ v, ‖Q v‖ = 1 := fun v => UnitSphere.norm_coe _
  have hQ_left : ∀ v, piTime v ≤ 3 / 8 → Q v = nraw a₁ (piInit v) := by
    intro v hv
    rw [hQdef]
    show ((H (cobSchedule (piTime v), cubeClamp (piInit v)) : _) :
      EuclideanSpace ℝ (Fin (n + 1))) = _
    rw [cobSchedule_of_le hv]
    have h0 : H (0, cubeClamp (piInit v)) = a₁.representative (cubeClamp (piInit v)) :=
      H.apply_zero _
    rw [h0, a₁.representative_coe]
    exact nraw_cubeClamp a₁ (piInit v)
  have hQ_right : ∀ v, 5 / 8 ≤ piTime v → Q v = nraw a₂ (piInit v) := by
    intro v hv
    rw [hQdef]
    show ((H (cobSchedule (piTime v), cubeClamp (piInit v)) : _) :
      EuclideanSpace ℝ (Fin (n + 1))) = _
    rw [cobSchedule_of_ge hv]
    have h1 : H (1, cubeClamp (piInit v)) = a₂.representative (cubeClamp (piInit v)) :=
      H.apply_one _
    rw [h1, a₂.representative_coe]
    exact nraw_cubeClamp a₂ (piInit v)
  have hQ_south : ∀ v, (∃ j, piInit v j ≤ 0 ∨ 1 ≤ piInit v j) → Q v = -eLast n := by
    intro v hj
    obtain ⟨j, hj⟩ := hj
    have hbd : cubeClamp (piInit v) ∈ Cube.boundary (Fin (n + 1)) := by
      rcases hj with hj | hj
      · exact ⟨j, Or.inl (projIcc_eq_zero hj)⟩
      · exact ⟨j, Or.inr (projIcc_eq_one hj)⟩
    have heq : H (cobSchedule (piTime v), cubeClamp (piInit v))
        = a₁.representative (cubeClamp (piInit v)) :=
      H.eq_fst _ hbd
    have hbase : a₁.representative (cubeClamp (piInit v)) = southPole n :=
      a₁.representative.2 _ hbd
    rw [hQdef]
    show ((H (cobSchedule (piTime v), cubeClamp (piInit v)) : _) :
      EuclideanSpace ℝ (Fin (n + 1))) = _
    rw [heq, hbase, southPole_coe]
  -- smoothness off the transition band
  set U : Set (Fin (n + 1 + 1) → ℝ) :=
    {v | piTime v < 3 / 8} ∪ {v | 5 / 8 < piTime v} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_piTime continuous_const).union
      (isOpen_lt continuous_const continuous_piTime)
  set Sc : Set (Fin (n + 1 + 1) → ℝ) :=
    {v | piTime v ≤ 1 / 4} ∪ {v | 3 / 4 ≤ piTime v} with hScdef
  have hScclosed : IsClosed Sc :=
    (isClosed_le continuous_piTime continuous_const).union
      (isClosed_le continuous_const continuous_piTime)
  have hSU : Sc ⊆ U := by
    rintro v (hv | hv)
    · exact Or.inl (by simp only [mem_ofPred_eq] at *; linarith)
    · exact Or.inr (by simp only [mem_ofPred_eq] at *; linarith)
  have hQU : ContDiffOn ℝ ∞ Q U := by
    rintro v (hv | hv)
    · refine (ContDiffAt.congr_of_eventuallyEq
        (((contDiff_nraw a₁).comp contDiff_piInit).contDiffAt) ?_).contDiffWithinAt
      exact Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_piTime continuous_const).mem_nhds hv)
        fun w hw => hQ_left w (le_of_lt hw)
    · refine (ContDiffAt.congr_of_eventuallyEq
        (((contDiff_nraw a₂).comp contDiff_piInit).contDiffAt) ?_).contDiffWithinAt
      exact Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_piTime).mem_nhds hv)
        fun w hw => hQ_right w (le_of_lt hw)
  obtain ⟨g, g_smooth, g_close, g_eq, -⟩ :=
    hQc.exists_contDiff_approx_and_eqOn (ε := fun _ => 1 / 8) ⊤
      continuous_const (fun _ => by norm_num) hScclosed
      (hUopen.mem_nhdsSet.mpr hSU) hQU
  refine ⟨⟨g, g_smooth, ?_, ?_, ?_, ?_⟩⟩
  · intro v h0
    have h := g_close v
    rw [h0, dist_zero_left, hQnorm] at h
    norm_num at h
  · intro v hv
    rw [g_eq (Or.inl hv), hQ_left v (by linarith)]
  · intro v hv
    rw [g_eq (Or.inr hv), hQ_right v (by linarith)]
  · intro v hj
    have h := g_close v
    rwa [hQ_south v hj] at h

/-! ### The plateaued space-time pipeline -/

variable {a₁ : Approximation p₁} {a₂ : Approximation p₂}

/-- The normalized space-time raw map.-/
def nrawCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖c.rawC v‖⁻¹ • c.rawC v

/-- The plateaued space-time raw map.-/
def prawCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  plateauAux (nrawCob c v)

/-- The normalized plateaued space-time map (unit-sphere valued).-/
def nprepCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖prawCob c v‖⁻¹ • prawCob c v

/-- The space-time horizontal-coordinates map.-/
def hMapCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  initCLM n (nprepCob c v)

/-- The space-time horizontal-coordinates map on the Euclidean domain.-/
def hMapCobE (c : CobApproximation a₁ a₂)
    (X : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  hMapCob c (WithLp.ofLp X)

/--
@isnad1 id=eq.0h7v.s11.a90254f24adb from=translated src=- shape=0b7b3f53 vocab=09651248
-/
lemma norm_nrawCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    ‖nrawCob c v‖ = 1 :=
  norm_normalize (c.rawC_ne_zero v)

/--
@isnad1 id=ne.0h7v.s11.747c16898b82 from=translated src=- shape=2b473bef vocab=3a6bb198
-/
lemma prawCob_ne_zero (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    prawCob c v ≠ 0 :=
  plateauAux_ne_zero (norm_nrawCob c v)

/--
@isnad1 id=eq.0h7v.s11.bafbbff23b64 from=translated src=- shape=0b7b3f53 vocab=101f0f67
-/
lemma norm_nprepCob (c : CobApproximation a₁ a₂) (v : Fin (n + 1 + 1) → ℝ) :
    ‖nprepCob c v‖ = 1 :=
  norm_normalize (prawCob_ne_zero c v)

/--
@isnad1 id=contdiff.0h6v.s11.ec79451cce5d from=translated src=- shape=9ef26dc7 vocab=2bd8d227
-/
lemma contDiff_nprepCob (c : CobApproximation a₁ a₂) :
    ContDiff ℝ ∞ (nprepCob c) :=
  contDiff_normalize_comp
    (contDiff_plateauAux.comp
      (contDiff_normalize_comp c.contDiff_rawC c.rawC_ne_zero))
    (prawCob_ne_zero c)

/--
@isnad1 id=contdiff.0h6v.s11.22ac0472e111 from=translated src=- shape=f388c778 vocab=755b8cab
-/
lemma contDiff_hMapCob (c : CobApproximation a₁ a₂) : ContDiff ℝ ∞ (hMapCob c) :=
  (initCLM n).contDiff.comp (contDiff_nprepCob c)

/--
@isnad1 id=contdiff.0h6v.s11.b97dcabd97f1 from=translated src=- shape=7966545e vocab=19eed09a
-/
lemma contDiff_hMapCobE (c : CobApproximation a₁ a₂) :
    ContDiff ℝ ∞ (hMapCobE c) :=
  (contDiff_hMapCob c).comp (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℝ).contDiff

/-- Normalizing a unit vector does nothing.
@isnad1 id=eq.1h2v.s6.60ff8ba4e25b from=translated src=- shape=686dca51 vocab=6a622bb8
-/
lemma normalize_of_norm_one {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] {w : E'} (hw : ‖w‖ = 1) : ‖w‖⁻¹ • w = w := by
  rw [hw]
  simp

/-- On the incoming time collar, the space-time pipeline is the incoming
bridge pipeline.
@isnad1 id=eq.1h7v.s11.ce2904765258 from=translated src=- shape=9e2f87c3 vocab=ec54ac44
-/
lemma nprepCob_left (c : CobApproximation a₁ a₂) {v : Fin (n + 1 + 1) → ℝ}
    (hv : piTime v ≤ 1 / 4) : nprepCob c v = nprep a₁ (piInit v) := by
  have h1 : nrawCob c v = nraw a₁ (piInit v) := by
    rw [nrawCob, c.rawC_left v hv]
    exact normalize_of_norm_one (norm_nraw a₁ (piInit v))
  rw [nprepCob, prawCob, h1]
  rfl

/--
@isnad1 id=eq.1h7v.s11.d83f078bc0b9 from=translated src=- shape=53452d06 vocab=ec54ac44
-/
lemma nprepCob_right (c : CobApproximation a₁ a₂) {v : Fin (n + 1 + 1) → ℝ}
    (hv : 3 / 4 ≤ piTime v) : nprepCob c v = nprep a₂ (piInit v) := by
  have h1 : nrawCob c v = nraw a₂ (piInit v) := by
    rw [nrawCob, c.rawC_right v hv]
    exact normalize_of_norm_one (norm_nraw a₂ (piInit v))
  rw [nprepCob, prawCob, h1]
  rfl

/--
@isnad1 id=eq.1h7v.s11.5289117027ed from=translated src=- shape=0fcf2d7e vocab=3c4a7394
-/
lemma hMapCob_left (c : CobApproximation a₁ a₂) {v : Fin (n + 1 + 1) → ℝ}
    (hv : piTime v ≤ 1 / 4) : hMapCob c v = bridgeHMap a₁ (piInit v) := by
  rw [hMapCob, nprepCob_left c hv]
  rfl

/--
@isnad1 id=eq.1h7v.s11.984e93462711 from=translated src=- shape=0911b552 vocab=3c4a7394
-/
lemma hMapCob_right (c : CobApproximation a₁ a₂) {v : Fin (n + 1 + 1) → ℝ}
    (hv : 3 / 4 ≤ piTime v) : hMapCob c v = bridgeHMap a₂ (piInit v) := by
  rw [hMapCob, nprepCob_right c hv]
  rfl

/-- Quantitative normalization: normalizing moves a point at most twice its
distance to a unit vector.
@isnad1 id=le.2h3v.s7.95ef222d5200 from=translated src=- shape=0421fffc vocab=a366e28c
-/
lemma norm_normalize_sub_le {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] {w s : E'} (hw : w ≠ 0) (hs : ‖s‖ = 1) :
    ‖‖w‖⁻¹ • w - s‖ ≤ 2 * ‖w - s‖ := by
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : ‖‖w‖⁻¹ • w - w‖ = |1 - ‖w‖| := by
    have h2 : ‖w‖⁻¹ • w - w = (‖w‖⁻¹ - 1) • w := by
      rw [sub_smul, one_smul]
    rw [h2, norm_smul, Real.norm_eq_abs]
    rw [show (‖w‖⁻¹ - 1) = (1 - ‖w‖) / ‖w‖ by field_simp]
    rw [abs_div, abs_of_pos hw0, div_mul_cancel₀ _ (ne_of_gt hw0)]
  have h3 : |1 - ‖w‖| ≤ ‖w - s‖ := by
    have h4 : |‖s‖ - ‖w‖| ≤ ‖s - w‖ := abs_norm_sub_norm_le s w
    rw [hs] at h4
    rwa [norm_sub_rev] at h4
  calc ‖‖w‖⁻¹ • w - s‖ ≤ ‖‖w‖⁻¹ • w - w‖ + ‖w - s‖ := by
        have := dist_triangle (‖w‖⁻¹ • w) w s
        simpa [dist_eq_norm] using this
    _ ≤ ‖w - s‖ + ‖w - s‖ := by rw [h1]; linarith [h3]
    _ = 2 * ‖w - s‖ := by ring

/-- Over the spatial complement of the open cube, the space-time horizontal map
vanishes (the plateau collapses everything near the south pole).
@isnad1 id=eq.1h7v.s11.67507f9c557a from=translated src=- shape=808aa659 vocab=4c991577
-/
lemma hMapCob_south (c : CobApproximation a₁ a₂) {v : Fin (n + 1 + 1) → ℝ}
    (hj : ∃ j, piInit v j ≤ 0 ∨ 1 ≤ piInit v j) : hMapCob c v = 0 := by
  have hdist : dist (c.rawC v) (-eLast n) < 1 / 8 := c.rawC_south v hj
  have hnorm : ‖(-eLast n : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    rw [norm_neg, norm_eLast]
  have h2 : ‖nrawCob c v - -eLast n‖ ≤ 2 * ‖c.rawC v - -eLast n‖ :=
    norm_normalize_sub_le (c.rawC_ne_zero v) hnorm
  have h3 : ‖nrawCob c v - -eLast n‖ ≤ 1 / 4 := by
    rw [dist_eq_norm] at hdist
    linarith
  have h4 : |vertC (nrawCob c v) + 1| ≤ 1 / 4 := by
    have h5 : (nrawCob c v - -eLast n) (Fin.last n) = vertC (nrawCob c v) + 1 := by
      have h6 : (nrawCob c v - -eLast n) (Fin.last n)
          = nrawCob c v (Fin.last n) - (-eLast n) (Fin.last n) := rfl
      rw [h6]
      have h7 : (-eLast n : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = -1 := by
        show -(eLast n) (Fin.last n) = -1
        simp [eLast]
      rw [h7, vertC]
      ring
    calc |vertC (nrawCob c v) + 1|
        = |(nrawCob c v - -eLast n) (Fin.last n)| := by rw [h5]
      _ ≤ ‖nrawCob c v - -eLast n‖ := abs_coord_le_norm _ _
      _ ≤ 1 / 4 := h3
  have hvert : vertC (nrawCob c v) ≤ -(1 / 2) := by
    rcases abs_le.mp h4 with ⟨hlo, hhi⟩
    linarith
  have h8 : prawCob c v = -eLast n := plateauAux_of_le hvert
  rw [hMapCob, nprepCob, h8, norm_neg, norm_eLast]
  simp only [inv_one, one_smul, map_neg]
  rw [initCLM_eLast, neg_zero]

/-! ### Fiber dichotomy and the north/south criterion on the cobordism -/

/-! ### Sard for the space-time map and end-regularity inheritance -/

/-- Every smooth map into `ℝⁿ` (`n > 0`) has a regular value `y` with
`0 < ‖y‖ < 1/8`, chosen in the fixed positive coordinate half-space.
@isnad1 id=ex.2h3v.s8.0346d2eb9f0a from=translated src=- shape=e2f09251 vocab=d5a8444f
-/
theorem exists_small_regular_value {m : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) :
    ∃ y : EuclideanSpace ℝ (Fin n),
      0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧ 0 < y ⟨0, hn⟩ ∧ IsRegularValue f y := by
  set z₀ : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ) with hz₀
  have hz₀norm : ‖z₀‖ = 1 / 16 := by
    rw [hz₀, PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  obtain ⟨y, hy_ball, hy_reg⟩ :=
    sard_exists_regular_value_in_ball hf z₀ (by norm_num : (0 : ℝ) < 1 / 32)
  have hdist : ‖y - z₀‖ < 1 / 32 := by
    rw [← dist_eq_norm]
    exact mem_ball.mp hy_ball
  have habs : |‖y‖ - ‖z₀‖| ≤ ‖y - z₀‖ := abs_norm_sub_norm_le y z₀
  rw [abs_le] at habs
  have hcoord : |y ⟨0, hn⟩ - 1 / 16| < 1 / 32 := by
    have hle := PiLp.norm_apply_le (y - z₀) ⟨0, hn⟩
    have hval : (y - z₀) ⟨0, hn⟩ = y ⟨0, hn⟩ - 1 / 16 := by
      simp [hz₀]
    rw [Real.norm_eq_abs, hval] at hle
    exact hle.trans_lt hdist
  refine ⟨y, ?_, ?_, ?_, hy_reg⟩
  · rw [hz₀norm] at habs
    linarith [habs.1]
  · rw [hz₀norm] at habs
    linarith [habs.2]
  · rw [abs_lt] at hcoord
    linarith [hcoord.1]

/-- A regular value of the space-time map is a regular value of the incoming end
map: the space-time map is locally time-constant on the incoming slab.
@isnad1 id=isregula.1h7v.s11.146eec38ebf6 from=translated src=- shape=f635e1ea vocab=d36b818e
-/
theorem isRegularValue_left_of_cob (c : CobApproximation a₁ a₂)
    {y : EuclideanSpace ℝ (Fin n)} (hy : IsRegularValue (hMapCobE c) y) :
    IsRegularValue (bridgeHMapE a₁) y := by
  intro x hx
  set X : EuclideanSpace ℝ (Fin (n + 1 + 1)) := spaceTime x 0 with hXdef
  have hXt : vertC X = 0 := vertC_spaceTime x 0
  have hslab : ∀ X' : EuclideanSpace ℝ (Fin (n + 1 + 1)), vertC X' < 1 / 4 →
      hMapCobE c X' = bridgeHMapE a₁ (initCLM (n + 1) X') := by
    intro X' hX'
    rw [hMapCobE, hMapCob_left c (v := WithLp.ofLp X')
      (by rw [piTime_ofLp]; linarith)]
    rfl
  have hval : hMapCobE c X = y := by
    rw [hslab X (by rw [hXt]; norm_num), initCLM_spaceTime]
    exact hx
  have hsurj := hy X hval
  have hEv : hMapCobE c =ᶠ[𝓝 X]
      fun X' => bridgeHMapE a₁ (initCLM (n + 1) X') :=
    Filter.eventuallyEq_of_mem
      ((isOpen_vert_lt (1 / 4)).mem_nhds (by rw [mem_ofPred_eq, hXt]; norm_num))
      fun X' hX' => hslab X' hX'
  have hgd : HasFDerivAt (bridgeHMapE a₁)
      (fderiv ℝ (bridgeHMapE a₁) (initCLM (n + 1) X)) (initCLM (n + 1) X) :=
    ((contDiff_bridgeHMapE a₁).differentiable infty_ne_zero _).hasFDerivAt
  have hfd : fderiv ℝ (hMapCobE c) X
      = (fderiv ℝ (bridgeHMapE a₁) (initCLM (n + 1) X)).comp (initCLM (n + 1)) := by
    rw [hEv.fderiv_eq]
    exact (hgd.comp X (initCLM (n + 1)).hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.coe_comp] at hsurj
  have := hsurj.of_comp
  rwa [hXdef, initCLM_spaceTime] at this

/-- A regular value of the space-time map is a regular value of the outgoing end
map.
@isnad1 id=isregula.1h7v.s11.5c4776521dc6 from=translated src=- shape=7f0a10b4 vocab=d36b818e
-/
theorem isRegularValue_right_of_cob (c : CobApproximation a₁ a₂)
    {y : EuclideanSpace ℝ (Fin n)} (hy : IsRegularValue (hMapCobE c) y) :
    IsRegularValue (bridgeHMapE a₂) y := by
  intro x hx
  set X : EuclideanSpace ℝ (Fin (n + 1 + 1)) := spaceTime x 1 with hXdef
  have hXt : vertC X = 1 := vertC_spaceTime x 1
  have hslab : ∀ X' : EuclideanSpace ℝ (Fin (n + 1 + 1)), 3 / 4 < vertC X' →
      hMapCobE c X' = bridgeHMapE a₂ (initCLM (n + 1) X') := by
    intro X' hX'
    rw [hMapCobE, hMapCob_right c (v := WithLp.ofLp X')
      (by rw [piTime_ofLp]; linarith)]
    rfl
  have hval : hMapCobE c X = y := by
    rw [hslab X (by rw [hXt]; norm_num), initCLM_spaceTime]
    exact hx
  have hsurj := hy X hval
  have hEv : hMapCobE c =ᶠ[𝓝 X]
      fun X' => bridgeHMapE a₂ (initCLM (n + 1) X') :=
    Filter.eventuallyEq_of_mem
      ((isOpen_lt_vert (3 / 4)).mem_nhds (by rw [mem_ofPred_eq, hXt]; norm_num))
      fun X' hX' => hslab X' hX'
  have hgd : HasFDerivAt (bridgeHMapE a₂)
      (fderiv ℝ (bridgeHMapE a₂) (initCLM (n + 1) X)) (initCLM (n + 1) X) :=
    ((contDiff_bridgeHMapE a₂).differentiable infty_ne_zero _).hasFDerivAt
  have hfd : fderiv ℝ (hMapCobE c) X
      = (fderiv ℝ (bridgeHMapE a₂) (initCLM (n + 1) X)).comp (initCLM (n + 1)) := by
    rw [hEv.fderiv_eq]
    exact (hgd.comp X (initCLM (n + 1)).hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.coe_comp] at hsurj
  have := hsurj.of_comp
  rwa [hXdef, initCLM_spaceTime] at this

/-! ### The middle (common-value) cobordism -/

/-- The framed level cobordism attached to a space-time approximation and a
regular value of its horizontal map: it connects the two bridge level sets of the
ends **at the common value `y`**.-/
def middleCob (c : CobApproximation a₁ a₂) (y : EuclideanSpace ℝ (Fin n))
    (hy0 : y ≠ 0) (hreg : IsRegularValue (hMapCobE c) y) :
    FramedLevelCobordism n where
  X₀ := bridgeFLS a₁ y hy0 (isRegularValue_left_of_cob c hreg)
  X₁ := bridgeFLS a₂ y hy0 (isRegularValue_right_of_cob c hreg)
  G := fun X => hMapCobE c X - y
  smooth := (contDiff_hMapCobE c).sub contDiff_const
  spatial_bounded := by
    refine ⟨n + 1 + 1, fun v hv => ?_⟩
    have hfx : hMapCobE c v = y := sub_eq_zero.mp hv
    have hns : ¬∃ j, piInit (WithLp.ofLp v) j ≤ 0 ∨ 1 ≤ piInit (WithLp.ofLp v) j := by
      intro hj
      apply hy0
      rw [← hfx, hMapCobE, hMapCob_south c hj]
    rw [not_exists] at hns
    have hcoord : ∀ j : Fin (n + 1), |initCLM (n + 1) v j| ≤ 1 := by
      intro j
      have h1 := hns j
      rw [not_or, not_le, not_le] at h1
      have h2 : piInit (WithLp.ofLp v) j = initCLM (n + 1) v j := rfl
      rw [h2] at h1
      exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h1 : ‖initCLM (n + 1) v‖ ^ 2 = ∑ j, initCLM (n + 1) v j ^ 2 :=
      norm_sq_eq_sum _
    have h2 : (∑ j, initCLM (n + 1) v j ^ 2) ≤ ∑ _j : Fin (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have := hcoord j
      nlinarith [abs_nonneg (initCLM (n + 1) v j), sq_abs (initCLM (n + 1) v j)]
    have h3 : (∑ _j : Fin (n + 1), (1 : ℝ)) = n + 1 := by simp
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : ‖initCLM (n + 1) v‖ ^ 2 ≤ ((n : ℝ) + 1 + 1) ^ 2 := by
      calc ‖initCLM (n + 1) v‖ ^ 2 = ∑ j, initCLM (n + 1) v j ^ 2 := h1
        _ ≤ n + 1 := h2.trans_eq h3
        _ ≤ ((n : ℝ) + 1 + 1) ^ 2 := by nlinarith
    nlinarith [norm_nonneg (initCLM (n + 1) v)]
  regular := by
    intro X hX
    have hfx : hMapCobE c X = y := sub_eq_zero.mp hX
    have hderiv : fderiv ℝ (fun X => hMapCobE c X - y) X
        = fderiv ℝ (hMapCobE c) X := fderiv_sub_const y
    rw [hderiv]
    exact hreg X hfx
  collar_zero := by
    intro x t ht
    show hMapCobE c (spaceTime x t) - y = bridgeHMapE a₁ x - y
    congr 1
    rw [hMapCobE, hMapCob_left c (by rw [piTime_ofLp_spaceTime]; exact ht),
      piInit_ofLp_spaceTime]
    rfl
  collar_one := by
    intro x t ht
    show hMapCobE c (spaceTime x t) - y = bridgeHMapE a₂ x - y
    congr 1
    rw [hMapCobE, hMapCob_right c (by rw [piTime_ofLp_spaceTime]; exact ht),
      piInit_ofLp_spaceTime]
    rfl

/-! ### The value-change cobordism (Milnor Lemma B) -/

/-- The open transition slab on which the flattening weight is positive.-/
def valueTransition : Set (EuclideanSpace ℝ (Fin (n + 1 + 1))) :=
  {v | 1 / 4 < vertC v ∧ vertC v < 3 / 4}

/--
@isnad1 id=isopen.0h1v.s7.58f296cfc1db from=translated src=- shape=4d4ec911 vocab=64444598
-/
lemma isOpen_valueTransition : IsOpen (valueTransition (n := n)) :=
  isOpen_vert_between (1 / 4) (3 / 4)

/-- The flat weight `s(1-s)`, where `s` is the collar-compatible time profile.-/
def valueWeight (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : ℝ :=
  timeProfile (vertC v) * (1 - timeProfile (vertC v))

/--
@isnad1 id=contdiff.0h1v.s8.fa2f3ead4a84 from=translated src=- shape=b6c448a7 vocab=c0cab217
-/
lemma contDiff_valueWeight : ContDiff ℝ ∞ (valueWeight (n := n)) := by
  have hs : ContDiff ℝ ∞ fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
      timeProfile (vertC v) := contDiff_timeProfile.comp contDiff_vertC
  exact hs.mul (contDiff_const.sub hs)

/--
@isnad1 id=lt.1h2v.s7.c15436fbdda6 from=translated src=- shape=5be8e986 vocab=4184efb1
-/
lemma valueWeight_pos {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hv : v ∈ valueTransition (n := n)) : 0 < valueWeight v := by
  have hs0 : 0 < timeProfile (vertC v) := by
    apply Real.smoothTransition.pos_of_pos
    change 0 < 2 * vertC v - 1 / 2
    linarith [hv.1]
  have hs1 : timeProfile (vertC v) < 1 := by
    apply Real.smoothTransition.lt_one_of_lt_one
    change 2 * vertC v - 1 / 2 < 1
    linarith [hv.2]
  exact mul_pos hs0 (sub_pos.mpr hs1)

/--
@isnad1 id=le.0h2v.s5.9f0b6a9359d1 from=translated src=- shape=2bc55340 vocab=2b322ef7
-/
lemma valueWeight_nonneg (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    0 ≤ valueWeight v := by
  rw [valueWeight]
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (sub_nonneg.mpr (Real.smoothTransition.le_one _))

/--
@isnad1 id=le.0h2v.s5.053903ba63e2 from=translated src=- shape=799114bf vocab=2b322ef7
-/
lemma valueWeight_le_one (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    valueWeight v ≤ 1 := by
  have hs0 := Real.smoothTransition.nonneg (2 * vertC v - 1 / 2)
  have hs1 := Real.smoothTransition.le_one (2 * vertC v - 1 / 2)
  rw [valueWeight, timeProfile]
  nlinarith [sq_nonneg (Real.smoothTransition (2 * vertC v - 1 / 2))]

/-- The unperturbed flattened numerator.-/
def valueBase
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  bridgeHMapE a (initCLM (n + 1) v) -
    ((1 - timeProfile (vertC v)) • y + timeProfile (vertC v) • y')

/--
@isnad1 id=contdiff.0h5v.s11.b7bb24d70612 from=translated src=- shape=17c830fa vocab=fb506540
-/
lemma contDiff_valueBase
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (valueBase a y y') := by
  have hs : ContDiff ℝ ∞ fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
      timeProfile (vertC v) := contDiff_timeProfile.comp contDiff_vertC
  exact ((contDiff_bridgeHMapE a).comp (initCLM (n + 1)).contDiff).sub
    (((contDiff_const.sub hs).smul contDiff_const).add (hs.smul contDiff_const))

/-- The quotient map used for the relative Sard argument.-/
def valueQuot
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  (valueWeight v)⁻¹ • valueBase a y y' v

/--
@isnad1 id=contdiff.0h5v.s11.7a6e77f8699c from=translated src=- shape=9256036f vocab=e93aae51
-/
lemma contDiffOn_valueQuot
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' : EuclideanSpace ℝ (Fin n)) :
    ContDiffOn ℝ ∞ (valueQuot a y y') (valueTransition (n := n)) := by
  exact (contDiff_valueWeight.contDiffOn.inv
      (fun v hv => (valueWeight_pos hv).ne')).smul
    (contDiff_valueBase a y y').contDiffOn

/-- The perturbed value-slide map.-/
def valueCobFun
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' w : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  valueBase a y y' v - valueWeight v • w

/--
@isnad1 id=contdiff.0h6v.s11.d4669c24ee13 from=translated src=- shape=76d70d06 vocab=64737285
-/
lemma contDiff_valueCobFun
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' w : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (valueCobFun a y y' w) :=
  (contDiff_valueBase a y y').sub (contDiff_valueWeight.smul contDiff_const)

/--
@isnad1 id=eq.1h7v.s10.76c4a62c5f8a from=translated src=- shape=9984f144 vocab=06a032da
-/
lemma valueCobFun_eq_weight_smul
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' w : EuclideanSpace ℝ (Fin n))
    {v : EuclideanSpace ℝ (Fin (n + 1 + 1))} (hv : v ∈ valueTransition (n := n)) :
    valueCobFun a y y' w v = valueWeight v • (valueQuot a y y' v - w) := by
  simp [valueCobFun, valueQuot, smul_sub, smul_smul, (valueWeight_pos hv).ne']

/--
@isnad1 id=eq.1h8v.s10.1a432fb9c3b8 from=translated src=- shape=82e99b6e vocab=70fc718a
-/
lemma valueCobFun_collar_zero
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' w : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : t ≤ 1 / 4) :
    valueCobFun a y y' w (spaceTime x t) = bridgeHMapE a x - y := by
  rw [valueCobFun, valueBase, valueWeight, vertC_spaceTime, initCLM_spaceTime,
    timeProfile_of_le ht]
  simp

/--
@isnad1 id=eq.1h8v.s10.9211f1b6ea0a from=translated src=- shape=d02c6c6e vocab=70fc718a
-/
lemma valueCobFun_collar_one
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (y y' w : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 3 / 4 ≤ t) :
    valueCobFun a y y' w (spaceTime x t) = bridgeHMapE a x - y' := by
  rw [valueCobFun, valueBase, valueWeight, vertC_spaceTime, initCLM_spaceTime,
    timeProfile_of_ge ht]
  simp

/-- The moving target whose inverse image is the value-change cobordism.-/
def valueTarget (y y' w : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  (1 - timeProfile (vertC v)) • y + timeProfile (vertC v) • y' + valueWeight v • w

/--
@isnad1 id=lt.3h6v.s8.b2bd951e8d02 from=translated src=- shape=b3ff3762 vocab=2f87221e
-/
lemma valueTarget_axis_pos (i : Fin n) {y y' w : EuclideanSpace ℝ (Fin n)}
    (hy : 0 < y i) (hy' : 0 < y' i)
    (hw : ‖w‖ < min (y i) (y' i) / 2)
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : 0 < valueTarget y y' w v i := by
  have hs0 := Real.smoothTransition.nonneg (2 * vertC v - 1 / 2)
  have hs1 := Real.smoothTransition.le_one (2 * vertC v - 1 / 2)
  have hwiNorm := PiLp.norm_apply_le w i
  rw [Real.norm_eq_abs] at hwiNorm
  have hwlower : -‖w‖ ≤ w i := (neg_le_of_abs_le hwiNorm)
  have hbase : min (y i) (y' i) ≤
      (1 - timeProfile (vertC v)) * y i + timeProfile (vertC v) * y' i := by
    rw [timeProfile]
    rcases le_total (y i) (y' i) with hle | hle
    · rw [min_eq_left hle]
      nlinarith
    · rw [min_eq_right hle]
      nlinarith
  have hpert : -‖w‖ ≤ valueWeight v * w i := by
    by_cases hwi : 0 ≤ w i
    · exact (neg_nonpos.mpr (norm_nonneg w)).trans
        (mul_nonneg (valueWeight_nonneg v) hwi)
    · have hmul : w i ≤ valueWeight v * w i := by
        have := mul_le_mul_of_nonpos_right (valueWeight_le_one v) (le_of_not_ge hwi)
        simpa using this
      exact hwlower.trans hmul
  have hmin : 0 < min (y i) (y' i) := lt_min hy hy'
  show 0 < (1 - timeProfile (vertC v)) * y i + timeProfile (vertC v) * y' i +
    valueWeight v * w i
  nlinarith

/--
@isnad1 id=le.2h5v.s10.ce25e5529b70 from=translated src=- shape=451d4c89 vocab=452b945d
-/
lemma bridgeHMapE_norm_le_of_eq_ne_zero
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {z : EuclideanSpace ℝ (Fin n)}
    (hfx : bridgeHMapE a x = z) (hz : z ≠ 0) : ‖x‖ ≤ n + 1 := by
  have hnc : WithLp.ofLp x ∉ closedAmbientCollar (Fin (n + 1)) := by
    intro hc
    apply hz
    rw [← hfx]
    exact (bridgeHMap_of_mem_collar a hc).symm ▸ rfl
  have hcoord : ∀ i, |x i| ≤ 1 := by
    intro i
    have h1 : ¬(x i ≤ 1 / 5 ∨ 4 / 5 ≤ x i) := fun h => hnc ⟨i, h⟩
    rw [not_or, not_le, not_le] at h1
    exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have h1 : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := norm_sq_eq_sum x
  have h2 : (∑ i, x i ^ 2) ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have := hcoord i
    nlinarith [abs_nonneg (x i), sq_abs (x i)]
  have h3 : (∑ _i : Fin (n + 1), (1 : ℝ)) = n + 1 := by simp
  have h4 : ‖x‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc ‖x‖ ^ 2 = ∑ i, x i ^ 2 := h1
      _ ≤ n + 1 := h2.trans_eq h3
      _ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [norm_nonneg x, hn0]

/-- **Value change** (the analogue of Milnor, *Topology from the Differentiable
Viewpoint*, §7 Lemma B): two regular bridge values in a common open half-space
have cobordant level sets.

The proof uses the flat quotient trick.  If `s` is the collar profile and
`q=s(1-s)`, divide the unperturbed interpolation by `q` on the open transition
slab.  A relative Sard value `w` of that quotient gives
`G_w = q • (Φ-w)` on the slab, hence on its zero fiber
`DG_w = q • DΦ`.  Choosing `w` in a sufficiently small ball preserves the common
positive coordinate, so the spatial fiber remains inside the compact cube.
@isnad1 id=ex.7h6v.s11.5622935aa7b4 from=translated src=- shape=7f712979 vocab=860d88db
-/
theorem exists_valueChange_cobordism_spec (hn : 0 < n)
    {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
      (southPole n)} (a : Approximation p) (i : Fin n)
    {y y' : EuclideanSpace ℝ (Fin n)} (hypos : 0 < y i) (hy'pos : 0 < y' i)
    (hy0 : y ≠ 0) (hy'0 : y' ≠ 0)
    (h : IsRegularValue (bridgeHMapE a) y)
    (h' : IsRegularValue (bridgeHMapE a) y') :
    ∃ (C : FramedLevelCobordism n) (w : EuclideanSpace ℝ (Fin n)),
      C.X₀ = bridgeFLS a y hy0 h ∧ C.X₁ = bridgeFLS a y' hy'0 h' ∧
      ‖w‖ < min (y i) (y' i) / 2 ∧ C.G = valueCobFun a y y' w := by
  let r : ℝ := min (y i) (y' i) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min hypos hy'pos)
  obtain ⟨w, hwreg, hwball⟩ :=
    (sard_dense_regular_values_on (isOpen_valueTransition (n := n))
      (contDiffOn_valueQuot a y y')).exists_mem_open Metric.isOpen_ball
      (Metric.nonempty_ball.mpr hr : (Metric.ball
        (0 : EuclideanSpace ℝ (Fin n)) r).Nonempty)
  have hw : ‖w‖ < r := by
    rw [mem_ball, dist_zero_right] at hwball
    exact hwball
  refine ⟨{
    X₀ := bridgeFLS a y hy0 h
    X₁ := bridgeFLS a y' hy'0 h'
    G := valueCobFun a y y' w
    smooth := contDiff_valueCobFun a y y' w
    spatial_bounded := ?_
    regular := ?_
    collar_zero := valueCobFun_collar_zero a y y' w
    collar_one := valueCobFun_collar_one a y y' w
  }, w, rfl, rfl, hw, rfl⟩
  · refine ⟨n + 1, fun v hv => ?_⟩
    have hfx0 : bridgeHMapE a (initCLM (n + 1) v) - valueTarget y y' w v = 0 := by
      simpa [valueCobFun, valueBase, valueTarget, sub_sub] using hv
    have hfx : bridgeHMapE a (initCLM (n + 1) v) = valueTarget y y' w v :=
      sub_eq_zero.mp hfx0
    have htarget : valueTarget y y' w v ≠ 0 := by
      intro hz
      have hpos := valueTarget_axis_pos i hypos hy'pos (by simpa [r] using hw) v
      rw [hz] at hpos
      exact lt_irrefl 0 hpos
    exact bridgeHMapE_norm_le_of_eq_ne_zero a hfx htarget
  · intro v hv
    by_cases hleft : vertC v ≤ 1 / 4
    · have hv0 : (bridgeFLS a y hy0 h).g (initCLM (n + 1) v) = 0 := by
        show bridgeHMapE a (initCLM (n + 1) v) - y = 0
        have hc := valueCobFun_collar_zero a y y' w
          (initCLM (n + 1) v) hleft
        rw [spaceTime_init_vert] at hc
        rw [← hc]
        exact hv
      have hs := surjective_fderiv_of_time_collar
        (contDiff_valueCobFun a y y' w)
        (valueCobFun_collar_zero a y y' w) hleft
        ((bridgeFLS a y hy0 h).regular _ hv0)
      rwa [spaceTime_init_vert] at hs
    · by_cases hright : 3 / 4 ≤ vertC v
      · have hv1 : (bridgeFLS a y' hy'0 h').g (initCLM (n + 1) v) = 0 := by
          show bridgeHMapE a (initCLM (n + 1) v) - y' = 0
          have hc := valueCobFun_collar_one a y y' w
            (initCLM (n + 1) v) hright
          rw [spaceTime_init_vert] at hc
          rw [← hc]
          exact hv
        have hs := surjective_fderiv_of_time_collar_right
          (contDiff_valueCobFun a y y' w)
          (valueCobFun_collar_one a y y' w) hright
          ((bridgeFLS a y' hy'0 h').regular _ hv1)
        rwa [spaceTime_init_vert] at hs
      · have hvU : v ∈ valueTransition (n := n) :=
          ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
        have hweighted : valueWeight v • (valueQuot a y y' v - w) = 0 := by
          rw [← valueCobFun_eq_weight_smul a y y' w hvU]
          exact hv
        have hsub : valueQuot a y y' v - w = 0 := by
          exact (smul_eq_zero.mp hweighted).resolve_left (valueWeight_pos hvU).ne'
        have hPhi : valueQuot a y y' v = w := sub_eq_zero.mp hsub
        have hsurjWithin := hwreg v hvU hPhi
        have hsurj : Function.Surjective (fderiv ℝ (valueQuot a y y') v) := by
          rwa [fderivWithin_of_isOpen isOpen_valueTransition hvU] at hsurjWithin
        have hEv : valueCobFun a y y' w =ᶠ[𝓝 v]
            fun z => valueWeight z • (valueQuot a y y' z - w) :=
          Filter.eventuallyEq_of_mem (isOpen_valueTransition.mem_nhds hvU)
            fun _ hz => valueCobFun_eq_weight_smul a y y' w hz
        have hqdiff : DifferentiableAt ℝ (valueWeight (n := n)) v :=
          contDiff_valueWeight.differentiable infty_ne_zero |>.differentiableAt
        have hPhidiff : DifferentiableAt ℝ (valueQuot a y y') v :=
          ((contDiffOn_valueQuot a y y').contDiffAt
            (isOpen_valueTransition.mem_nhds hvU)).differentiableAt infty_ne_zero
        have hsubdiff : DifferentiableAt ℝ (fun z => valueQuot a y y' z - w) v :=
          hPhidiff.sub (differentiableAt_const (c := w))
        have hfd : fderiv ℝ (valueCobFun a y y' w) v =
            valueWeight v • fderiv ℝ (valueQuot a y y') v := by
          rw [hEv.fderiv_eq, fderiv_fun_smul hqdiff hsubdiff,
            fderiv_sub_const w, hPhi, sub_self]
          simp
        rw [hfd]
        intro z
        obtain ⟨u, hu⟩ := hsurj ((valueWeight v)⁻¹ • z)
        refine ⟨u, ?_⟩
        rw [smul_apply, hu, smul_smul,
          mul_inv_cancel₀ (valueWeight_pos hvU).ne', one_smul]

/-! ### The main theorem -/

end Submission
