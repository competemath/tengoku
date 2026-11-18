import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining

set_option autoImplicit false

namespace CohL2
namespace E1

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
variable {V : Type} [AddCommGroup V] [Module 𝒪 V]
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']

/--
@isnad1 id=mem.1h6v.s9.923da3d4e873 from=translated src=- shape=aa09673b vocab=08eb1f1d
-/
theorem smul_mem_ideal_smul_top (J : Ideal 𝒪) (t : B') {v' : V'}
    (h : v' ∈ (J • ⊤ : Submodule 𝒪 V')) : t • v' ∈ (J • ⊤ : Submodule 𝒪 V') := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro a ha v _
    rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro x y hx hy
    rw [smul_add]; exact Submodule.add_mem _ hx hy

/--
@isnad1 id=eq.1h9v.s10.181b05112f4f from=translated src=- shape=610ad506 vocab=9d775426
-/
theorem map_pow_apply (f : V →ₗ[𝒪] V') (g : V →ₗ[𝒪] V) (b' : B')
    (hfg : ∀ v : V, f (g v) = b' • f v) (n : ℕ) (v : V) : f ((g ^ n) v) = (b' ^ n) • f v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih (g v), hfg, smul_smul, ← pow_succ]

/--
@isnad1 id=eq.1h5v.s6.1bced86f9be0 from=translated src=- shape=1697fb31 vocab=99545b96
-/
theorem pow_mul_eq_of_mul_mul_eq {u b e : B'} (h : u * b * e = e) (n : ℕ) :
    u ^ n * b ^ n * e = e := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc u ^ (n + 1) * b ^ (n + 1) * e = u ^ n * b ^ n * (u * b * e) := by ring
      _ = e := by rw [h, ih]

end CohL2.E1

open CohL2.E1 IharaLemma in
/--
@isnad1 id=mem.3h10v.s10.aa6f45aaecea from=translated src=- shape=20e112b1 vocab=9bb063fd
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (W : Submodule 𝒪 V) (I : Ideal 𝒪)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ (I ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (hyp : ∀ j' : Fin S'.n, j' ≠ i' →
      ∃ (g : V →ₗ[𝒪] V) (b' : B'), b' ∉ S'.𝔪 j' ∧ (∀ v : V, f (g v) = b' • f v) ∧
        (∀ w ∈ W, g w ∈ W) ∧ (∀ k : ℕ, ∃ n : ℕ, ∀ w ∈ W, (g ^ n) w ∈ (I ^ k • ⊤ : Submodule 𝒪 V))) :
    ∀ w ∈ W, f w ∈ cornerSubmodule (M := V') (S'.e i') := by
  intro w hw

  have hzero : ∀ j' : Fin S'.n, j' ≠ i' → S'.e j' • f w = 0 := by
    intro j' hj'
    obtain ⟨g, b', hb', hfg, -, hnil⟩ := hyp j' hj'
    obtain ⟨u', hu'⟩ := exists_mul_mul_eq_of_notMem (S'.idem j') (S'.𝔪 j') (S'.mem_of_isMaximal_of_ne j') hb'
    apply hsep
    intro k
    obtain ⟨n, hn⟩ := hnil k
    have h1 : S'.e j' • f w = (u' ^ n * S'.e j') • ((b' ^ n) • f w) := by
      rw [smul_smul]
      congr 1
      calc S'.e j' = u' ^ n * b' ^ n * S'.e j' := (pow_mul_eq_of_mul_mul_eq hu' n).symm
        _ = u' ^ n * S'.e j' * b' ^ n := by ring
    rw [h1, ← map_pow_apply f g b' hfg n w]
    apply smul_mem_ideal_smul_top

    have hmap := Submodule.mem_map_of_mem (f := f) (hn w hw)
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono (le_refl (I ^ k)) le_top hmap

  have hsum : f w = ∑ j, S'.e j • f w := by
    rw [← Finset.sum_smul, S'.coi.complete, one_smul]
  rw [hsum, Finset.sum_eq_single i' (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i') h)]
  exact ⟨f w, rfl⟩
