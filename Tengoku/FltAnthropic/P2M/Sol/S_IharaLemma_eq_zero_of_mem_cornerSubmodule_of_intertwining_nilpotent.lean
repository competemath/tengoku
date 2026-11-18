import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent

set_option autoImplicit false

namespace CohL2
namespace E3

/--
@isnad1 id=eq.1h5v.s6.1bced86f9be0 from=translated src=- shape=1697fb31 vocab=99545b96
-/
theorem pow_mul_eq_of_mul_mul_eq {B' : Type} [CommRing B'] {u b e : B'} (h : u * b * e = e) (n : ℕ) :
    u ^ n * b ^ n * e = e := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc u ^ (n + 1) * b ^ (n + 1) * e = u ^ n * b ^ n * (u * b * e) := by ring
      _ = e := by rw [h, ih]

/--
@isnad1 id=eq.1h9v.s9.073b58a837fd from=translated src=- shape=a34e8bdd vocab=5f37b6c4
-/
theorem map_pow_smul {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V']
    (f : V' →ₗ[𝒪] V) (t' : B') (β : V →ₗ[𝒪] V) (hf : ∀ v' : V', f (t' • v') = β (f v'))
    (n : ℕ) (v' : V') : f ((t' ^ n) • v') = (β ^ n) (f v') := by
  induction n generalizing v' with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih, hf, pow_succ, Module.End.mul_apply]

end CohL2.E3

open CohL2.E3 IharaLemma in
/--
@isnad1 id=eq.5h11v.s10.6464938d6553 from=translated src=- shape=47f4b013 vocab=9bb063fd
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V' →ₗ[𝒪] V) (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (t' : B') (ht' : t' ∉ S'.𝔪 i') (β : V →ₗ[𝒪] V) (hf : ∀ v' : V', f (t' • v') = β (f v'))
    (I : Ideal 𝒪) (hβ : ∀ k : ℕ, ∃ n : ℕ, ∀ v : V, (β ^ n) v ∈ (I ^ k • ⊤ : Submodule 𝒪 V))
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) → v = 0) :
    ∀ v' ∈ cornerSubmodule (M := V') (S'.e i'), f v' = 0 := by
  intro v' hv'
  obtain ⟨u', hu'⟩ := exists_mul_mul_eq_of_notMem (S'.idem i') (S'.𝔪 i') (S'.mem_of_isMaximal_of_ne i') ht'
  have hev : S'.e i' • v' = v' := S'.e_smul_coe i' ⟨v', hv'⟩
  apply hsep
  intro k
  obtain ⟨n, hn⟩ := hβ k
  have h1 : v' = (t' ^ n) • ((u' ^ n * S'.e i') • v') := by
    rw [smul_smul]
    conv_lhs => rw [← hev, ← pow_mul_eq_of_mul_mul_eq hu' n]
    congr 1
    ring
  rw [h1, map_pow_smul f t' β hf n]
  exact hn _
