/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku.Seed.Topology.Algebra.Module.ModuleTopology
public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.LeanPool.LeanPool.LeanModularForms.Modularforms.ExpLems
import Tengoku.LeanPool.LeanPool.LeanModularForms.Modularforms.Iteratedderivs
import Tengoku.Seed.Analysis.Calculus.UniformLimitsDeriv
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Topology.ContinuousMap.Compact

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # TsumderivWithin -/

@[expose] public section

open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/-- The open upper half-plane as a subset of `ℂ`. -/
abbrev ℍ' := {z : ℂ | 0 < z.im}

lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by apply isOpen_lt (by fun_prop) (by fun_prop)

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply HasDerivWithinAt.derivWithin
  · apply HasDerivAt.hasDerivWithinAt
    have A :
      ∀ x : ℂ,
        x ∈ s →
          Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
            (𝓝 (∑' n : α, (fun z => f n z) x)) :=
          fun y hy ↦ Summable.hasSum <| hf y hy
    apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
    · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
    · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
      intro K hK1 hK2
      obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
      exact tendstoUniformlyOn_tsum hu1 (fun n x hx => hu2 n ⟨x, hx⟩)
    filter_upwards
    intro t r hr
    exact HasDerivAt.fun_sum (fun q _ => HasDerivWithinAt.hasDerivAt
      (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt (IsOpen.mem_nhds hs hr))
  exact IsOpen.uniqueDiffWithinAt hs hx

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r := by
  apply DifferentiableOn.differentiableAt
  · exact DifferentiableOn.congr (by fun_prop) (fun x hx => exp_iter_deriv_within k n hx)
  exact IsOpen.mem_nhds (isOpen_lt (by fun_prop) (by fun_prop)) r.2

theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ'
        ↑r := by
  apply symm
  apply DifferentiableAt.derivWithin
  · apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
      ℍ' ↑r =
      iteratedDerivWithin (k + 1)
        (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r := by
  rw [iteratedDerivWithin_succ]

/-- The continuous map `z ↦ exp (2π i z)` restricted to a subset `K` of `ℂ`. -/
noncomputable def ctsExpTwoPiN (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x := by
  have A : ∀ x : ℂ, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
        (𝓝 (∑' n : α, (fun z => f n z) x)) := fun y hy => (hf y hy).hasSum
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    exact tendstoUniformlyOn_tsum hu1 (fun n x hx => hu2 n ⟨x, hx⟩)
  filter_upwards
  intro t r hr
  exact HasDerivAt.fun_sum (fun q _ => HasDerivWithinAt.hasDerivAt
    (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt (IsOpen.mem_nhds hs hr))

theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt
