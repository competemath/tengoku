/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Util.Mathlib
import Tengoku.LeanTnorms.Tnorms.Util.DistFun
import Tengoku.LeanTnorms.Tnorms.Util.Seq

/-!
TODOs:
  * General proof cleanup
  * File docstring
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
variable {X : Type*} [MetricSpace X]

open unitInterval

lemma _root_.Tengoku.LeanTnorms.exists_match_fun_of_exists_accPt_unitInterval
    (h : ∃ x, AccPt x (⊤ : Filter X)) :
    ∃ x y : ℕ → X, (∀ U ∈ uniformity X, ∃ N : ℕ, ∀ n ≥ N, (x n, y n) ∈ U) ∧
    ∀ q : I, ∀ p : ℕ → I, Filter.Tendsto p Filter.atTop (nhds q) → ∃ f : X → I,
    UniformContinuous f ∧ (∀ n, f (x n) = p n) ∧ (∀ n, f (y n) = q) := by
  obtain ⟨y, hy⟩ := h
  rw [← Filter.principal_univ, accPt_principal_iff_clusterPt,
    ← mem_closure_iff_clusterPt, mem_closure_iff_seq_limit] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hx
  obtain ⟨φ, hφ, hda⟩ := refine_seq_uniformity x y hxy hx
  have hxy' : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds y) :=
    Filter.Tendsto.comp hxy <| StrictMono.tendsto_atTop hφ
  use x ∘ φ; use (fun n ↦ y)
  constructor
  · intro U hU
    simp [Filter.tendsto_iff_forall_eventually_mem] at hxy'
    obtain ⟨V, hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hU
    specialize hxy' (UniformSpace.ball y V) <| UniformSpace.ball_mem_nhds y hV
    obtain ⟨N, hN⟩ := hxy'
    use N
    intro n hn
    specialize hN n hn
    simp [UniformSpace.ball_eq_of_symmetry] at hN
    grind [refl_mem_uniformity, SetRel.mem_comp]
  · intro q p hpt
    use (dist_fun (x ∘ φ) y p q) ∘ (fun z ↦ dist z y)
    constructor
    · refine UniformContinuous.comp ?_ ?_
      · exact dist_fun_uniformContinuous hxy' hda hpt
      · exact UniformContinuous.dist uniformContinuous_id uniformContinuous_const
    constructor
    · intro n
      simp [dist_fun]
      split_ifs
      · rename_i hd
        specialize hx (φ n)
        simp at hd
        contradiction
      · rename_i hd hn'
        suffices n = Classical.choose hn' by
          simp [interpolate_n]
          conv => lhs; rhs; rw [this]
          conv => rhs; rw [this]
          rw [interpolate_right]
          exact hda (lt_add_one _)
        have hpn := Classical.choose_spec hn'
        obtain ⟨hcn, hnc⟩ := hpn
        refine le_antisymm ?_ ?_
        · refine Nat.le_of_lt_succ ?_
          contrapose! hcn
          exact (StrictAnti.antitone hda) hcn
        · contrapose! hnc
          exact hda hnc
      · have hn : ∃ m, dist (x (φ n)) y ∈ Set.Ioc (dist (x (φ (m + 1))) y) (dist (x (φ m)) y) := by
          use n
          simp
          exact hda (lt_add_one n)
        contradiction
    · simp [dist_fun]

variable {M : Type*} [UniformSpace M]

lemma _root_.Tengoku.LeanTnorms.exists_match_fun_of_match_fun_unitInterval (e : M ≃ᵤ I)
    (h : ∃ x y : ℕ → X, (∀ U ∈ uniformity X, ∃ N : ℕ, ∀ n ≥ N, (x n, y n) ∈ U) ∧
    ∀ q : I, ∀ p : ℕ → I, Filter.Tendsto p Filter.atTop (nhds q) → ∃ f : X → I,
    UniformContinuous f ∧ (∀ n, f (x n) = p n) ∧ (∀ n, f (y n) = q)) :
    ∃ x y : ℕ → X, (∀ U ∈ uniformity X, ∃ N : ℕ, ∀ n ≥ N, (x n, y n) ∈ U) ∧
    ∀ q : M, ∀ p : ℕ → M, Filter.Tendsto p Filter.atTop (nhds q) → ∃ f : X → M,
    UniformContinuous f ∧ (∀ n, f (x n) = p n) ∧ (∀ n, f (y n) = q) := by
  obtain ⟨x, y, hU, hf⟩ := h
  use x, y
  constructor
  · exact hU
  intro q p hpq
  specialize hf (e q) (e ∘ p) ?_
  · refine Filter.Tendsto.comp ?_ hpq
    exact Continuous.tendsto (UniformEquiv.continuous _) _
  obtain ⟨f', hf', hfx', hfy'⟩ := hf
  use e.symm ∘ f'
  constructor
  · exact UniformContinuous.comp (UniformEquiv.uniformContinuous_symm e) hf'
  constructor
  · simp only [Function.comp_apply] at hfx' ⊢
    intro n
    rw [← UniformEquiv.coe_symm_toEquiv, Equiv.symm_apply_eq, UniformEquiv.coe_toEquiv]
    exact hfx' n
  · simp only [Function.comp_apply] at hfy' ⊢
    intro n
    rw [← UniformEquiv.coe_symm_toEquiv, Equiv.symm_apply_eq, UniformEquiv.coe_toEquiv]
    exact hfy' n

lemma _root_.Tengoku.LeanTnorms.exists_match_fun_of_uniformEquiv_unitInterval (e : M ≃ᵤ I) (hX : ∃ x : X, AccPt x ⊤) :
    ∃ x y : ℕ → X, (∀ U ∈ uniformity X, ∃ N : ℕ, ∀ n ≥ N, (x n, y n) ∈ U) ∧
    ∀ q : M, ∀ p : ℕ → M, Filter.Tendsto p Filter.atTop (nhds q) → ∃ f : X → M,
    UniformContinuous f ∧ (∀ n, f (x n) = p n) ∧ (∀ n, f (y n) = q) := by
  refine exists_match_fun_of_match_fun_unitInterval e ?_
  exact exists_match_fun_of_exists_accPt_unitInterval hX
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
