/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Tactic.Abel
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.LocalizedModuleLadder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A localization five lemma

This file supplies the algebraic diagram chase needed to propagate affine localization/base
change through a cohomological long exact sequence.
-/

set_option autoImplicit false

universe u

namespace IsLocalizedModule

variable {R : Type u} [CommRing R] (S : Submonoid R)

variable {D A B C E D' A' B' C' E' : Type u}
  [AddCommGroup D] [Module R D] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]
  [AddCommGroup D'] [Module R D'] [AddCommGroup A'] [Module R A']
  [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
  [AddCommGroup E'] [Module R E']

/-- **Localization five lemma.**  In a commutative ladder of two five-term sequences which are
exact at the three inner positions, if the four outer vertical maps are localizations at `S`,
then the middle vertical map is a localization at `S`.-/
theorem middle_of_exact_five_ladder
    (d₀ : D →ₗ[R] A) (d₁ : A →ₗ[R] B) (d₂ : B →ₗ[R] C) (d₃ : C →ₗ[R] E)
    (d₀' : D' →ₗ[R] A') (d₁' : A' →ₗ[R] B') (d₂' : B' →ₗ[R] C')
    (d₃' : C' →ₗ[R] E')
    (vD : D →ₗ[R] D') (vA : A →ₗ[R] A') (vB : B →ₗ[R] B')
    (vC : C →ₗ[R] C') (vE : E →ₗ[R] E')
    (hexA : Function.Exact d₀ d₁) (hexB : Function.Exact d₁ d₂)
    (hexC : Function.Exact d₂ d₃)
    (hexA' : Function.Exact d₀' d₁') (hexB' : Function.Exact d₁' d₂')
    (hexC' : Function.Exact d₂' d₃')
    (hDA : ∀ x, d₀' (vD x) = vA (d₀ x))
    (hAB : ∀ x, d₁' (vA x) = vB (d₁ x))
    (hBC : ∀ x, d₂' (vB x) = vC (d₂ x))
    (hCE : ∀ x, d₃' (vC x) = vE (d₃ x))
    [IsLocalizedModule S vD] [IsLocalizedModule S vA]
    [IsLocalizedModule S vC] [IsLocalizedModule S vE] :
    IsLocalizedModule S vB := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    show Function.Bijective (fun x : B' => (s : R) • x)
    constructor
    · intro x y hxy
      change (s : R) • x = (s : R) • y at hxy
      have hsxy : (s : R) • (x - y) = 0 := by
        rw [smul_sub, hxy, sub_self]
      have hkerC : d₂' (x - y) = 0 := by
        apply injective_smul S vC s
        rw [smul_zero]
        simpa only [map_smul, map_zero] using congrArg d₂' hsxy
      obtain ⟨w, hw⟩ := (hexB' (x - y)).1 hkerC
      have hkerA : d₁' ((s : R) • w) = 0 := by
        rw [map_smul, hw, hsxy]
      obtain ⟨v, hv⟩ := (hexA' ((s : R) • w)).1 hkerA
      obtain ⟨w₀, hw₀⟩ := surjective_smul S vD s v
      have hw' : w = d₀' w₀ := by
        apply injective_smul S vA s
        calc
          (s : R) • w = d₀' v := hv.symm
          _ = d₀' ((s : R) • w₀) := congrArg d₀' hw₀.symm
          _ = (s : R) • d₀' w₀ := by rw [map_smul]
      apply sub_eq_zero.mp
      calc
        x - y = d₁' w := hw.symm
        _ = d₁' (d₀' w₀) := congrArg d₁' hw'
        _ = 0 := hexA'.apply_apply_eq_zero w₀
    · intro y
      obtain ⟨z, hz⟩ := surjective_smul S vC s (d₂' y)
      have hkerE : d₃' z = 0 := by
        apply injective_smul S vE s
        calc
          (s : R) • d₃' z = d₃' ((s : R) • z) := by rw [map_smul]
          _ = d₃' (d₂' y) := congrArg d₃' hz
          _ = 0 := hexC'.apply_apply_eq_zero y
          _ = (s : R) • 0 := by rw [smul_zero]
      obtain ⟨x, hx⟩ := (hexC' z).1 hkerE
      have hkerC : d₂' (y - (s : R) • x) = 0 := by
        rw [map_sub, map_smul, hx, hz, sub_self]
      obtain ⟨w, hw⟩ := (hexB' (y - (s : R) • x)).1 hkerC
      obtain ⟨w₀, hw₀⟩ := surjective_smul S vA s w
      refine ⟨x + d₁' w₀, ?_⟩
      change (s : R) • (x + d₁' w₀) = y
      rw [smul_add, ← map_smul, hw₀, hw]
      simp
  · intro y
    obtain ⟨⟨z, s⟩, hz⟩ := IsLocalizedModule.surj S vC (d₂' y)
    have hzR : (s : R) • d₂' y = vC z := by
      simpa only [Submonoid.smul_def] using hz
    have heq : vE (d₃ z) = vE 0 := by
      rw [← hCE, ← hzR, map_smul, hexC'.apply_apply_eq_zero, smul_zero, map_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := vE) heq
    have htR : (t : R) • d₃ z = 0 := by
      simpa only [Submonoid.smul_def, smul_zero] using ht
    have hkerE : d₃ ((t : R) • z) = 0 := by
      rw [map_smul, htR]
    obtain ⟨x, hx⟩ := (hexC ((t : R) • z)).1 hkerE
    have hkerC : d₂' (vB x - ((t * s : S) : R) • y) = 0 := by
      rw [map_sub, hBC, hx, map_smul, map_smul]
      change (t : R) • vC z - ((t : R) * (s : R)) • d₂' y = 0
      rw [← hzR, mul_smul, sub_self]
    obtain ⟨w, hw⟩ := (hexB' (vB x - ((t * s : S) : R) • y)).1 hkerC
    obtain ⟨⟨v, u⟩, hv⟩ := IsLocalizedModule.surj S vA w
    have hvR : (u : R) • w = vA v := by
      simpa only [Submonoid.smul_def] using hv
    refine ⟨⟨(u : R) • x - d₁ v, u * (t * s)⟩, ?_⟩
    change (((u * (t * s) : S) : R) • y) =
      vB ((u : R) • x - d₁ v)
    symm
    calc
      vB ((u : R) • x - d₁ v) =
          (u : R) • vB x - vB (d₁ v) := by rw [map_sub, map_smul]
      _ = (u : R) • vB x - d₁' (vA v) := by rw [hAB]
      _ = (u : R) • vB x - d₁' ((u : R) • w) := by rw [hvR]
      _ = (u : R) • (vB x - d₁' w) := by rw [map_smul, smul_sub]
      _ = (u : R) • (((t * s : S) : R) • y) := by
        rw [hw]
        abel_nf
      _ = (((u * (t * s) : S) : R) • y) := by
        simp only [Submonoid.coe_mul, mul_smul]
  · intro x₁ x₂ h
    let z := x₁ - x₂
    have hvz : vB z = 0 := by
      dsimp [z]
      rw [map_sub, h, sub_self]
    have heqC : vC (d₂ z) = vC 0 := by
      rw [← hBC, hvz, map_zero, map_zero]
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := vC) heqC
    have hsR : (s : R) • d₂ z = 0 := by
      simpa only [Submonoid.smul_def, smul_zero] using hs
    have hkerC : d₂ ((s : R) • z) = 0 := by
      rw [map_smul, hsR]
    obtain ⟨w, hw⟩ := (hexB ((s : R) • z)).1 hkerC
    have hkerA' : d₁' (vA w) = 0 := by
      rw [hAB, hw, map_smul, hvz, smul_zero]
    obtain ⟨v, hv⟩ := (hexA' (vA w)).1 hkerA'
    obtain ⟨⟨q, t⟩, ht⟩ := IsLocalizedModule.surj S vD v
    have htR : (t : R) • v = vD q := by
      simpa only [Submonoid.smul_def] using ht
    have hkerA : vA ((t : R) • w - d₀ q) = 0 := by
      calc
        vA ((t : R) • w - d₀ q) =
            (t : R) • vA w - vA (d₀ q) := by rw [map_sub, map_smul]
        _ = (t : R) • d₀' v - d₀' (vD q) := by rw [hv, hDA]
        _ = d₀' ((t : R) • v) - d₀' (vD q) := by rw [map_smul]
        _ = 0 := by rw [htR, sub_self]
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := vA)
      (show vA ((t : R) • w - d₀ q) = vA 0 by simpa using hkerA)
    refine ⟨u * (t * s), ?_⟩
    have hu' : (u : R) • ((t : R) • w - d₀ q) = 0 := by
      simpa only [Submonoid.smul_def, smul_zero] using hu
    have hmap := congrArg d₁ hu'
    simp only [map_smul, map_sub, hexA.apply_apply_eq_zero, map_zero, sub_zero] at hmap
    rw [hw] at hmap
    dsimp [z] at hmap
    apply sub_eq_zero.mp
    rw [← smul_sub]
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hmap

end IsLocalizedModule
