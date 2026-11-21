import Tengoku.PshdLean.PshLines.FirstPass.GeometricForms
import Tengoku.PshdLean.PshLines.FirstPass.QuasiPshSingularities
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global quasi-PSH functions and local potentials of a given form

Functions take values in `EReal`, retaining their poles. Quasi-PSH means the
existing local PSH-plus-smooth decomposition in every holomorphic atlas chart.
The raw criterion allows the negative-infinite function; the potential predicate
separately requires the non-pole locus to meet every open neighborhood.

`smoothDDC` is the actual exterior derivative of `-du ∘ J / (4π)`.
The theta-PSH criterion requires local smooth potentials of the given form on
arbitrarily small chart neighborhoods, and PSH of the corrected function there.
It neither assumes that every form has potentials nor defines a surrogate order
on forms. Chart independence and change of local potential are separate theorems
proved elsewhere; no regularization module is imported here.
-/

open Set Filter
open scoped Topology ContDiff

namespace PshLines.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The coordinate representative is used only on the chart target.-/
def chartFunction (u : M → EReal) (e : ComplexChart n M) : ComplexModel n → EReal :=
  fun z => u (e.val.symm z)

/-- Raw global quasi-PSH regularity in the given holomorphic atlas.-/
def ManifoldQuasiPlurisubharmonic [IsComplexManifold n M] (u : M → EReal) : Prop :=
  ∀ e : ComplexChart n M, QuasiPlurisubharmonicOn (chartFunction u e) e.val.target

/-- No open neighborhood is entirely a pole set. For a quasi-PSH function,
which never takes the value `⊤`, this is density of the finite locus.-/
def LocallyNondegenerate (u : M → EReal) : Prop :=
  ∀ x : M, ∀ U : Set M, IsOpen U → x ∈ U → ∃ y ∈ U, u y ≠ ⊥

/-- A global quasi-PSH potential has explicit local nondegeneracy.-/
def IsGlobalQuasiPshPotential [IsComplexManifold n M] (u : M → EReal) : Prop :=
  ManifoldQuasiPlurisubharmonic (n := n) u ∧ LocallyNondegenerate u

/-- Smoothness of a real function in the actual holomorphic charts.-/
def ChartSmooth [IsComplexManifold n M] (h : M → ℝ) : Prop :=
  ∀ e : ComplexChart n M, ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) e.val.target

variable [IsComplexManifold n M]

/--
@isnad1 id=ne.1h4v.s6.a34e8c538ec4 from=translated src=- shape=83f3ebce vocab=55e040fa
-/
theorem ManifoldQuasiPlurisubharmonic.ne_top {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (x : M) : u x ≠ ⊤ := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h := (hu e (e.val x) (e.val.map_source hx)).ne_top
  simpa only [chartFunction, e.val.left_inv hx] using h

/--
@isnad1 id=manifold.0h3v.s6.ac06a394b07c from=translated src=- shape=7d7c1f85 vocab=f3165bd4
-/
theorem manifoldQuasiPlurisubharmonic_const (c : ℝ) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun _ : M => (c : EReal)) :=
  fun _ z _ => (plurisubharmonicAt_const c (EReal.coe_ne_top c) z).quasiPlurisubharmonicAt

/--
@isnad1 id=isglobal.0h3v.s6.92ec0b41c212 from=translated src=- shape=7d7c1f85 vocab=0ad39836
-/
theorem isGlobalQuasiPshPotential_const (c : ℝ) :
    IsGlobalQuasiPshPotential (n := n) (fun _ : M => (c : EReal)) :=
  ⟨manifoldQuasiPlurisubharmonic_const c,
    fun x _ _ hx => ⟨x, hx, EReal.coe_ne_bot c⟩⟩

/--
@isnad1 id=manifold.2h4v.s6.34249370099a from=translated src=- shape=9950938d vocab=fa687104
-/
theorem ManifoldQuasiPlurisubharmonic.add_smooth {u : M → EReal} {h : M → ℝ}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (hh : ChartSmooth (n := n) h) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun x => u x + (h x : EReal)) := by
  intro e z hz
  apply (hu e z hz).add_smooth
  exact eventually_of_mem (e.val.open_target.mem_nhds hz)
    (fun y hy => (hh e y hy).contDiffAt (e.val.open_target.mem_nhds hy))

/--
@isnad1 id=isglobal.2h4v.s6.6704c4109154 from=translated src=- shape=9950938d vocab=240f2a91
-/
theorem IsGlobalQuasiPshPotential.add_smooth {u : M → EReal} {h : M → ℝ}
    (hu : IsGlobalQuasiPshPotential (n := n) u) (hh : ChartSmooth (n := n) h) :
    IsGlobalQuasiPshPotential (n := n) (fun x => u x + (h x : EReal)) := by
  refine ⟨hu.1.add_smooth hh, ?_⟩
  intro x U hU hx
  obtain ⟨y, hy, hfin⟩ := hu.2 x U hU hx
  exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hfin, EReal.coe_ne_bot _⟩⟩

/-- Nondegeneracy yields an actual finite value on every open neighborhood.
@isnad1 id=ex.3h5v.s6.f8fbf90f6d17 from=translated src=- shape=4ae8c9ad vocab=309f17b3
-/
theorem IsGlobalQuasiPshPotential.exists_finite {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) (x : M) {U : Set M}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ y ∈ U, u y ≠ ⊥ ∧ u y ≠ ⊤ := by
  obtain ⟨y, hy, hfin⟩ := hu.2 x U hU hx
  exact ⟨y, hy, hfin, hu.1.ne_top y⟩

/-- On a nonempty manifold, the identically negative-infinite function is excluded.
@isnad1 id=not.0h2v.s6.9d63eadd447b from=translated src=- shape=5eef596f vocab=0304d7bc
-/
theorem not_isGlobalQuasiPshPotential_bot [Nonempty M] :
    ¬ IsGlobalQuasiPshPotential (n := n) (fun _ : M => (⊥ : EReal)) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨y, _, hy⟩ := h.2 x univ isOpen_univ (mem_univ x)
  exact hy rfl

/-- The genuine real-linear complex structure on the model tangent space.-/
def modelComplexStructure (n : ℕ) : ComplexModel n →L[ℝ] ComplexModel n :=
  (Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ

/--
@isnad1 id=eq.0h2v.s9.4c87acd74cc0 from=translated src=- shape=91c11267 vocab=a00a35e6
-/
@[simp] theorem modelComplexStructure_apply (v : ComplexModel n) :
    modelComplexStructure n v = Complex.I • v := rfl

/-- The normalized smooth one-form `dᶜh(v) = -Dh(Iv)/(4π)`.-/
def smoothDc (h : ComplexModel n → ℝ) (z : ComplexModel n) :
    (ComplexModel n) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1)
    ((-1 / (4 * Real.pi) : ℝ) • (fderiv ℝ h z).comp (modelComplexStructure n))

/--
@isnad1 id=eq.0h4v.s10.cbad6a480e41 from=translated src=- shape=4c1526e6 vocab=e6f51c64
-/
@[simp] theorem smoothDc_apply (h : ComplexModel n → ℝ) (z : ComplexModel n)
    (v : Fin 1 → ComplexModel n) :
    smoothDc h z v = (-1 / (4 * Real.pi)) * fderiv ℝ h z (Complex.I • v 0) := rfl

/-- The actual exterior derivative of the normalized one-form, with no
differentiability fallback used when it is asserted to be a smooth potential.-/
def smoothDDC (h : ComplexModel n → ℝ) :
    ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ := extDeriv (smoothDc h)

/-- The normalized operator depends only on the germ of the function.
@isnad1 id=eq.1h4v.s7.182f69d3e623 from=translated src=- shape=ccb9d60b vocab=e5e4c63f
-/
theorem smoothDDC_congr {h g : ComplexModel n → ℝ} {z : ComplexModel n}
    (heq : h =ᶠ[𝓝 z] g) : smoothDDC h z = smoothDDC g z := by
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
  simp only [smoothDc, hy]

/-- A local potential of a specified form on an open part of one chart.
The entire two-form must equal `ddᶜρ`, not only selected diagonal values.-/
def IsSmoothLocalPotential (θ : SmoothRealForm n M 2) (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) : Prop :=
  IsOpen W ∧ W ⊆ e.val.target ∧ ContDiffOn ℝ ∞ ρ W ∧
    EqOn (smoothDDC ρ) (θ.coeff e) W

/-- Having local potentials is a separate property of the form.-/
def HasSmoothLocalPotentials (θ : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target → ∃ W ρ, z ∈ W ∧ IsSmoothLocalPotential θ e W ρ

/--
@isnad1 id=issmooth.3h7v.s7.bde5512ad143 from=translated src=- shape=e0f55d6e vocab=89bcdb52
-/
theorem IsSmoothLocalPotential.mono {θ : SmoothRealForm n M 2} {e : ComplexChart n M}
    {W V : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (h : IsSmoothLocalPotential θ e W ρ) (hV : IsOpen V) (hVW : V ⊆ W) :
    IsSmoothLocalPotential θ e V ρ :=
  ⟨hV, hVW.trans h.2.1, h.2.2.1.mono hVW, h.2.2.2.mono hVW⟩

/--
@isnad1 id=iff.1h7v.s7.9fc36cd03ce2 from=translated src=- shape=1802e725 vocab=3ca762a2
-/
theorem SmoothRealForm.GeometricallyEq.localPotential_iff
    {θ η : SmoothRealForm n M 2} (hθη : θ.GeometricallyEq η)
    (e : ComplexChart n M) (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) :
    IsSmoothLocalPotential θ e W ρ ↔ IsSmoothLocalPotential η e W ρ := by
  constructor
  · rintro ⟨hW, hWe, hρ, heq⟩
    exact ⟨hW, hWe, hρ, fun z hz => (heq hz).trans (hθη e (hWe hz))⟩
  · rintro ⟨hW, hWe, hρ, heq⟩
    exact ⟨hW, hWe, hρ, fun z hz => (heq hz).trans (hθη e (hWe hz)).symm⟩

/-- The raw theta-PSH criterion: near every chart point, add an actual smooth
potential of `θ` and require the resulting extended-real germ to be PSH.-/
def ThetaPlurisubharmonic (θ : SmoothRealForm n M 2) (u : M → EReal) : Prop :=
  ∀ e z, z ∈ e.val.target → ∃ W ρ, z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
    PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) W

/-- Theta-PSH potentials additionally exclude an open set of poles.-/
def IsThetaPshPotential (θ : SmoothRealForm n M 2) (u : M → EReal) : Prop :=
  ThetaPlurisubharmonic θ u ∧ LocallyNondegenerate u

/--
@isnad1 id=hassmoot.1h4v.s6.d138cbed1f44 from=translated src=- shape=2718fd67 vocab=0aa09bfa
-/
theorem ThetaPlurisubharmonic.hasSmoothLocalPotentials {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) : HasSmoothLocalPotentials θ := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, _⟩ := hu e z hz
  exact ⟨W, ρ, hzW, hρ⟩

/-- The theta-PSH criterion really implies the local PSH-plus-smooth decomposition.
@isnad1 id=manifold.1h4v.s6.85b1f49cfcd2 from=translated src=- shape=f6256033 vocab=70267c94
-/
theorem ThetaPlurisubharmonic.quasiPlurisubharmonic {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) :
    ManifoldQuasiPlurisubharmonic (n := n) u := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
  refine ⟨fun y => chartFunction u e y + (ρ y : EReal), fun y => -ρ y,
    hp z hzW, ?_, ?_⟩
  · exact eventually_of_mem (hρ.1.mem_nhds hzW)
      (fun y hy => ((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).neg)
  · exact Eventually.of_forall fun y => by
      dsimp only
      rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/--
@isnad1 id=isglobal.1h4v.s6.5c106a2fed51 from=translated src=- shape=f6256033 vocab=a29ac792
-/
theorem IsThetaPshPotential.quasiPshPotential {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential θ u) :
    IsGlobalQuasiPshPotential (n := n) u := ⟨hu.1.quasiPlurisubharmonic, hu.2⟩

/--
@isnad1 id=iff.1h5v.s6.06007ccf3d7d from=translated src=- shape=462747bc vocab=288889c3
-/
theorem SmoothRealForm.GeometricallyEq.thetaPlurisubharmonic_iff
    {θ η : SmoothRealForm n M 2} (hθη : θ.GeometricallyEq η) (u : M → EReal) :
    ThetaPlurisubharmonic θ u ↔ ThetaPlurisubharmonic η u := by
  constructor
  · intro hu e z hz
    obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
    exact ⟨W, ρ, hzW, (hθη.localPotential_iff e W ρ).mp hρ, hp⟩
  · intro hu e z hz
    obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
    exact ⟨W, ρ, hzW, (hθη.localPotential_iff e W ρ).mpr hρ, hp⟩

/--
@isnad1 id=iff.1h5v.s6.e118aebc5118 from=translated src=- shape=462747bc vocab=ec47ac0f
-/
theorem SmoothRealForm.GeometricallyEq.thetaPshPotential_iff
    {θ η : SmoothRealForm n M 2} (hθη : θ.GeometricallyEq η) (u : M → EReal) :
    IsThetaPshPotential θ u ↔ IsThetaPshPotential η u :=
  and_congr (hθη.thetaPlurisubharmonic_iff u) Iff.rfl

end

end PshLines.FirstPass
