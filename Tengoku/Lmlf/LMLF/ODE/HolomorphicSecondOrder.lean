import Tengoku.Lmlf.LMLF.ODE.HolomorphicLinear
import Tengoku.Seed.Analysis.Calculus.Deriv.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar holomorphic second-order linear equations

The scalar equation is obtained from the Banach-valued first-order theorem by the state-vector
construction.  Solutions are counted after restriction to the domain.
-/

namespace LMLF.ODE

open Filter Metric Set
open scoped Topology

/-- A scalar second-order homogeneous linear equation with analytic coefficients on a simply
connected complex domain has a unique solution for each value and first derivative.-/
theorem exists_unique_holomorphicSecondOrderLinear
    {Z : Set ℂ} (hZ : IsOpen Z) (hZc : IsSimplyConnected Z)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Z) (hg : AnalyticOnNhd ℂ g Z)
    {x₀ : ℂ} (hx₀ : x₀ ∈ Z) (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, AnalyticOnNhd ℂ w Z ∧ w x₀ = w₀ ∧ HasDerivAt w w₁ x₀ ∧
      (∀ z ∈ Z, HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z) ∧
      ∀ v : ℂ → ℂ, AnalyticOnNhd ℂ v Z → v x₀ = w₀ → HasDerivAt v w₁ x₀ →
        (∀ z ∈ Z, HasDerivAt (deriv v) (-(f z * deriv v z + g z * v z)) z) →
        Set.EqOn w v Z := by
  let p₁ : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
  let p₂ : ℂ → (ℂ × ℂ →L[ℂ] ℂ) := fun z ↦
    -(g z • ContinuousLinearMap.fst ℂ ℂ ℂ +
      f z • ContinuousLinearMap.snd ℂ ℂ ℂ)
  let prodL :
      ((ℂ × ℂ →L[ℂ] ℂ) × (ℂ × ℂ →L[ℂ] ℂ)) →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ) :=
    (ContinuousLinearMap.prodL (𝕜 := ℂ) (E := ℂ × ℂ) (F := ℂ) (G := ℂ) ℂ).toContinuousLinearMap
  let A : ℂ → (ℂ × ℂ →L[ℂ] ℂ × ℂ) := fun z ↦
    prodL (p₁, p₂ z)
  have hp₁ : AnalyticOnNhd ℂ (fun _ : ℂ ↦ p₁) Z := analyticOnNhd_const
  have hp₂ : AnalyticOnNhd ℂ p₂ Z := by
    exact (hg.smul analyticOnNhd_const).add (hf.smul analyticOnNhd_const) |>.neg
  have hpair : AnalyticOnNhd ℂ (fun z ↦ (p₁, p₂ z)) Z := hp₁.prod hp₂
  have hprodL : AnalyticOnNhd ℂ (fun p ↦ prodL p) Set.univ :=
    fun z _ ↦ prodL.analyticAt z
  have hA : AnalyticOnNhd ℂ A Z :=
    hprodL.comp hpair (Set.mapsTo_univ _ _)
  obtain ⟨U, hU₀, hUAnalytic, hUOde, hUUnique⟩ :=
    exists_unique_holomorphicLinearIVP hZ hZc hA hx₀ (w₀, w₁)
  let fstCLM : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ
  let sndCLM : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
  let w : ℂ → ℂ := fun z ↦ (U z).1
  let v : ℂ → ℂ := fun z ↦ (U z).2
  have hwAnalytic : AnalyticOnNhd ℂ w Z := by
    have hfst : AnalyticOnNhd ℂ (fun x : ℂ × ℂ ↦ fstCLM x) Set.univ :=
      fun x _ ↦ fstCLM.analyticAt x
    exact hfst.comp hUAnalytic (Set.mapsTo_univ _ _)
  have hvAnalytic : AnalyticOnNhd ℂ v Z := by
    have hsnd : AnalyticOnNhd ℂ (fun x : ℂ × ℂ ↦ sndCLM x) Set.univ :=
      fun x _ ↦ sndCLM.analyticAt x
    exact hsnd.comp hUAnalytic (Set.mapsTo_univ _ _)
  have hwDeriv : ∀ z ∈ Z, HasDerivAt w (v z) z := by
    intro z hz
    have h := (fstCLM.hasFDerivAt.comp z (hUOde z hz).hasFDerivAt).hasDerivAt
    simpa [fstCLM, w, v, A, prodL, p₁, p₂, Function.comp_def] using h
  have hvDeriv : ∀ z ∈ Z, HasDerivAt v (-(g z * w z + f z * v z)) z := by
    intro z hz
    have h := (sndCLM.hasFDerivAt.comp z (hUOde z hz).hasFDerivAt).hasDerivAt
    simpa [sndCLM, w, v, A, prodL, p₁, p₂, Function.comp_def, add_comm] using h
  have hwSecond : ∀ z ∈ Z,
      HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z := by
    intro z hz
    have heq : deriv w =ᶠ[nhds z] v := by
      filter_upwards [hZ.mem_nhds hz] with y hy
      exact (hwDeriv y hy).deriv
    have h := (hvDeriv z hz).congr_of_eventuallyEq heq
    simpa only [heq.eq_of_nhds, add_comm] using h
  refine ⟨w, hwAnalytic, ?_, ?_, hwSecond, ?_⟩
  · exact congrArg Prod.fst hU₀
  · exact (hwDeriv x₀ hx₀).congr_deriv (congrArg Prod.snd hU₀)
  · intro q hqAnalytic hq₀ hqDeriv hqOde
    let Q : ℂ → ℂ × ℂ := fun z ↦ (q z, deriv q z)
    have hQAnalytic : AnalyticOnNhd ℂ Q Z := hqAnalytic.prod hqAnalytic.deriv
    have hQ₀ : Q x₀ = (w₀, w₁) := by
      rw [show Q x₀ = (q x₀, deriv q x₀) by rfl, hq₀, hqDeriv.deriv]
    have hQOde : ∀ z ∈ Z, HasDerivAt Q (A z (Q z)) z := by
      intro z hz
      have hqFirst := (hqAnalytic z hz).differentiableAt.hasDerivAt
      have h := hqFirst.prodMk (hqOde z hz)
      simpa [Q, A, prodL, p₁, p₂, add_comm] using h
    have hUQ := hUUnique Q hQ₀ hQAnalytic hQOde
    intro z hz
    exact congrArg Prod.fst (hUQ hz)

/-- There are infinitely many holomorphic solutions, counted as functions on the domain rather
than by arbitrary values of ambient extensions away from it.-/
theorem infinite_holomorphicSecondOrderLinearSolutions
    {Z : Set ℂ} (hZ : IsOpen Z) (hZc : IsSimplyConnected Z)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Z) (hg : AnalyticOnNhd ℂ g Z) :
    Set.Infinite {s : Z → ℂ | ∃ w : ℂ → ℂ, AnalyticOnNhd ℂ w Z ∧
      (∀ z ∈ Z, HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z) ∧
      s = fun z : Z ↦ w z} := by
  classical
  obtain ⟨x₀, hx₀⟩ := hZc.nonempty
  choose w hwAnalytic hw₀ hwDeriv hwOde hwUnique using
    fun a : ℂ ↦ exists_unique_holomorphicSecondOrderLinear hZ hZc hf hg hx₀ a 0
  let Φ : ℂ → (Z → ℂ) := fun a z ↦ w a z
  have hΦmem : ∀ a : ℂ, Φ a ∈ {s : Z → ℂ | ∃ w : ℂ → ℂ, AnalyticOnNhd ℂ w Z ∧
      (∀ z ∈ Z, HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z) ∧
      s = fun z : Z ↦ w z} := by
    intro a
    exact ⟨w a, hwAnalytic a, hwOde a, rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have := congrFun hab ⟨x₀, hx₀⟩
    simpa [Φ, hw₀] using this
  exact (Set.infinite_range_of_injective hΦinj).mono fun s hs ↦ by
    rcases hs with ⟨a, rfl⟩
    exact hΦmem a

end LMLF.ODE
