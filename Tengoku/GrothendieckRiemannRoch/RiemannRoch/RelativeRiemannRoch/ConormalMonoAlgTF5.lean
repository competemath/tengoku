/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Smooth.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.RingTheory.Smooth.StandardSmoothCotangent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# TF5 (algebra part): the rank count `r + d = m` for a smooth quotient of a smooth algebra

For `A ↠ B = A/I` with `A` and `B` formally smooth over `k`, the conormal sequence
`0 → I/I² → B ⊗_A Ω[A⁄k] → Ω[B⁄k] → 0` is (split) exact
(`kerCotangentToTensor_injective_of_formallySmooth`).  Hence ranks add
(`rank_conormal_add`): `rank (I/I²) + rank Ω[B⁄k] = rank (B ⊗_A Ω[A⁄k])`.
-/

set_option autoImplicit false
noncomputable section

open TensorProduct KaehlerDifferential

universe u v

namespace SchemeKTheory.TF5

/-- Ranks add in a short exact sequence with free sub and quotient.-/
theorem rank_add_of_exact {B : Type u} [CommRing B] [Nontrivial B] {N M Q : Type u}
    [AddCommGroup N] [Module B N] [AddCommGroup M] [Module B M] [AddCommGroup Q] [Module B Q]
    [Module.Free B N] [Module.Free B Q] (f : N →ₗ[B] M) (g : M →ₗ[B] Q) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.rank B M = Module.rank B N + Module.rank B Q := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hgs : ∀ q, g (s q) = q := fun q => LinearMap.congr_fun hs q
  let φ : N × Q →ₗ[B] M := f.coprod s
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨n, q⟩ h
      have h1 : f n + s q = 0 := h
      have h2 : g (f n) = 0 := (hex (f n)).mpr ⟨n, rfl⟩
      have hq : q = 0 := by
        have := congrArg g h1
        rw [map_add, h2, hgs, zero_add, map_zero] at this
        exact this
      subst hq
      simp only [map_zero, add_zero] at h1
      have : n = 0 := hf (by rw [h1, map_zero])
      simp [this]
    · intro x
      have : x - s (g x) ∈ LinearMap.range f := by
        rw [← hex.linearMap_ker_eq]
        simp [hgs]
      obtain ⟨n, hn⟩ := this
      exact ⟨(n, g x), by simp [φ, hn]⟩
  have := LinearEquiv.rank_eq (LinearEquiv.ofBijective φ hφ)
  rw [← this, rank_prod']

section Smooth

variable (k : Type u) (A B : Type u) [CommRing k] [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra A B] [IsScalarTower k A B]

end Smooth

end SchemeKTheory.TF5
