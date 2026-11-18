import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul

set_option autoImplicit false

universe u v w

namespace K72WS

open PrimeSpectrum

variable {R : Type u} [CommRing R]

/--
@isnad1 id=ex.2h3v.s7.f0d5bdb896fc from=translated src=- shape=60cf991e vocab=2ba7ee06
-/
theorem exists_pow_le_annihilator_of_support_subset
    {K : Type v} [AddCommGroup K] [Module R K] [Module.Finite R K]
    {J : Ideal R} (hJ : J.FG) (h : Module.support R K ⊆ zeroLocus (J : Set R)) :
    ∃ n : ℕ, J ^ n ≤ Module.annihilator R K := by
  rw [Module.support_eq_zeroLocus, zeroLocus_subset_zeroLocus_iff] at h
  exact Ideal.exists_pow_le_of_le_radical_of_fg h hJ

/--
@isnad1 id=le.1h3v.s7.8d604df70138 from=translated src=- shape=4929cf3f vocab=17404e8e
-/
theorem support_subset_zeroLocus_of_forall_exists_pow_smul_eq_zero
    {K : Type v} [AddCommGroup K] [Module R K]
    {s : Set R} (h : ∀ a ∈ s, ∀ x : K, ∃ k : ℕ, a ^ k • x = 0) :
    Module.support R K ⊆ zeroLocus s := by
  intro p hp a ha
  have key : Module.support R K ⊆ zeroLocus {a} := by
    rw [← LocalizedModule.subsingleton_iff_support_subset, LocalizedModule.subsingleton_iff]
    intro m
    obtain ⟨k, hk⟩ := h a ha m
    exact ⟨a ^ k, ⟨k, rfl⟩, hk⟩
  exact key hp (Set.mem_singleton a)

/--
@isnad1 id=ex.3h4v.s8.accb0d293770 from=translated src=- shape=38abe71d vocab=f505d3a0
-/
theorem exists_pow_le_annihilator_of_forall_exists_pow_smul_eq_zero
    {K : Type v} [AddCommGroup K] [Module R K] [Module.Finite R K]
    {J : Ideal R} (hJ : J.FG) {s : Set R} (hs : Ideal.span s = J)
    (h : ∀ a ∈ s, ∀ x : K, ∃ k : ℕ, a ^ k • x = 0) :
    ∃ n : ℕ, J ^ n ≤ Module.annihilator R K := by
  apply exists_pow_le_annihilator_of_support_subset hJ
  rw [← hs, zeroLocus_span]
  exact support_subset_zeroLocus_of_forall_exists_pow_smul_eq_zero h

end K72WS

/--
@isnad1 id=ex.5h6v.s10.53a98a10e658 from=translated src=- shape=016199d5 vocab=25385ae1
-/
theorem solution
    {R : Type u} [CommRing R] (S : Finset R) (J : Ideal R) (hJ : Ideal.span (S : Set R) = J)
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (u : M →ₗ[R] N)
    (hker : (LinearMap.ker u).FG) (hcoker : Module.Finite R (N ⧸ LinearMap.range u))
    (hk : ∀ a ∈ S, ∀ x : M, u x = 0 → ∃ k : ℕ, a ^ k • x = 0)
    (hc : ∀ a ∈ S, ∀ y : N, ∃ (k : ℕ) (x : M), u x = a ^ k • y) :
    ∃ N₀ : ℕ,
      (∀ x : M, u x = 0 → ∀ a ∈ J ^ N₀, a • x = 0) ∧
      (∀ (y : N), ∀ a ∈ J ^ N₀, ∃ x : M, u x = a • y) := by
  have hJfg : J.FG := ⟨S, hJ⟩
  haveI : Module.Finite R (LinearMap.ker u) := Module.Finite.iff_fg.mpr hker
  haveI : Module.Finite R (N ⧸ LinearMap.range u) := hcoker
  obtain ⟨n₁, hn₁⟩ := K72WS.exists_pow_le_annihilator_of_forall_exists_pow_smul_eq_zero
    (K := LinearMap.ker u) hJfg hJ (fun a ha x => by
      obtain ⟨k, hk'⟩ := hk a (Finset.mem_coe.mp ha) x.1 x.2
      exact ⟨k, Subtype.ext (by simpa using hk')⟩)
  obtain ⟨n₂, hn₂⟩ := K72WS.exists_pow_le_annihilator_of_forall_exists_pow_smul_eq_zero
    (K := N ⧸ LinearMap.range u) hJfg hJ (fun a ha y => by
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨k, x, hx⟩ := hc a (Finset.mem_coe.mp ha) y
        refine ⟨k, ?_⟩
        rw [← Submodule.Quotient.mk_smul, ← hx, Submodule.Quotient.mk_eq_zero]
        exact LinearMap.mem_range_self u x)
  refine ⟨n₁ + n₂, ?_, ?_⟩
  · intro x hx a ha
    have ha' : a ∈ Module.annihilator R (LinearMap.ker u) :=
      hn₁ (Ideal.pow_le_pow_right (Nat.le_add_right n₁ n₂) ha)
    have := Module.mem_annihilator.mp ha' ⟨x, hx⟩
    simpa using congrArg Subtype.val this
  · intro y a ha
    have ha' : a ∈ Module.annihilator R (N ⧸ LinearMap.range u) :=
      hn₂ (Ideal.pow_le_pow_right (Nat.le_add_left n₂ n₁) ha)
    have := Module.mem_annihilator.mp ha' (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at this
    exact this
