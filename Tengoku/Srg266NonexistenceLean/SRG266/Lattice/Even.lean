/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Overlattice
import Tengoku.Seed.Algebra.Ring.Int.Parity
import Tengoku.Seed.RingTheory.Int.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable (B : LinearMap.BilinForm ℚ W)

def IsEven (N : Submodule ℤ W) : Prop :=
  ∀ x ∈ N, ∃ n : ℤ, B x x = 2 * (n : ℚ)

theorem isEven_of_span (hsymm : B.IsSymm) {s : Set W}
    (hint : IsIntegral B (Submodule.span ℤ s))
    (hs : ∀ x ∈ s, ∃ n : ℤ, B x x = 2 * (n : ℚ)) :
    IsEven B (Submodule.span ℤ s) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hint hx y hy)
    have hk' : (k : ℚ) = B x y := by simpa using hk
    refine ⟨a + b + k, ?_⟩
    simp only [map_add, LinearMap.add_apply]
    rw [hsymm.eq y x, ha, hb, ← hk']
    push_cast
    ring
  | smul a x _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨a ^ 2 * k, ?_⟩
    simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, hk]
    push_cast
    ring

theorem IsEven.of_odd_smul {N P : Submodule ℤ W} (hN : IsEven B N)
    (hP : IsIntegral B P) {m : ℤ} (hm : Odd m)
    (hsmul : ∀ x ∈ P, m • x ∈ N) : IsEven B P := by
  intro x hx
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hP hx x hx)
  have hn' : (n : ℚ) = B x x := by simpa using hn
  obtain ⟨a, ha⟩ := hN _ (hsmul x hx)
  have heq : (m : ℚ) ^ 2 * (n : ℚ) = 2 * (a : ℚ) := by
    simpa only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, ← hn',
      pow_two, mul_assoc] using ha
  have hdiv : (2 : ℤ) ∣ m ^ 2 * n := ⟨a, by exact_mod_cast heq⟩
  have hdivn : (2 : ℤ) ∣ n :=
    (Int.isCoprime_two_left.mpr hm.pow).dvd_of_dvd_mul_left hdiv
  obtain ⟨k, hk⟩ := hdivn
  refine ⟨k, ?_⟩
  rw [← hn', hk]
  push_cast
  rfl

theorem exists_even_maximal_integral_overlattice_denominator
    (hnd : B.Nondegenerate) (hsymm : B.IsSymm)
    {N : Submodule ℤ W} (hN : IsLattice ℚ N) (hint : IsIntegral B N)
    (heven : IsEven B N) {k m : ℤ} {j : ℕ} (hkodd : Odd k)
    (hk : ∀ y ∈ B.dualSubmodule N, k • y ∈ N) (hdvd : k ∣ m ^ j) :
    ∃ P : Submodule ℤ W, N ≤ P ∧ IsLattice ℚ P ∧ IsMaximalIntegral B P ∧
      IsEven B P ∧ ∀ y ∈ B.dualSubmodule P, m • y ∈ P := by
  obtain ⟨P, hle, hlat, hmax, hden⟩ :=
    exists_maximal_integral_overlattice_denominator B hnd hsymm hN hint hk hdvd
  refine ⟨P, hle, hlat, hmax, ?_, hden⟩
  exact heven.of_odd_smul B hmax.integral hkodd
    (fun x hx => hk x (le_dual_of_le B hle hmax.integral hx))

end SRG266.Lattice
