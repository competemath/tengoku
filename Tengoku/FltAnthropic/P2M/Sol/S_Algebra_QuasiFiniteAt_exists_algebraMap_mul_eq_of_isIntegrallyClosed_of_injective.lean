import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective

set_option autoImplicit false

/--
@isnad1 id=ex.1h5v.s8.0826e8daa6d9 from=translated src=- shape=a45088d3 vocab=57ec39d2
-/
theorem solution
    {R S K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsScalarTower R S K]
    (hSK : Function.Injective (algebraMap S K)) [Algebra.FiniteType R S]
    (𝔔 : Ideal S) [𝔔.IsPrime] [Algebra.QuasiFiniteAt R 𝔔] :
    ∀ s : S, ∃ a b : R, b ∉ 𝔔.comap (algebraMap R S) ∧ algebraMap R S b * s = algebraMap R S a := by
  classical
  intro s
  have hZ : Algebra.ZariskisMainProperty R 𝔔 := Algebra.ZariskisMainProperty.of_finiteType 𝔔
  obtain ⟨r, hr𝔔, hr⟩ := Algebra.zariskisMainProperty_iff'.mp hZ

  have hint : ∀ t : S, IsIntegral R t → ∃ y : R, algebraMap R S y = t := by
    intro t ht
    have ht' : IsIntegral R (algebraMap S K t) := ht.map (IsScalarTower.toAlgHom R S K)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral ht'
    refine ⟨y, hSK ?_⟩
    rw [← hy, ← IsScalarTower.algebraMap_apply]

  obtain ⟨m₁, hm₁⟩ := hr r
  have hrint : IsIntegral R r := by
    rw [← pow_succ] at hm₁
    exact (IsIntegral.pow_iff (Nat.succ_pos m₁)).mp hm₁
  obtain ⟨r₀, hr₀⟩ := hint r hrint
  obtain ⟨m, hm⟩ := hr s
  obtain ⟨y, hy⟩ := hint _ hm
  refine ⟨y, r₀ ^ m, ?_, ?_⟩
  · intro hmem
    rw [Ideal.mem_comap, map_pow, hr₀] at hmem
    exact hr𝔔 (Ideal.IsPrime.mem_of_pow_mem ‹_› m hmem)
  · rw [map_pow, hr₀, hy]
