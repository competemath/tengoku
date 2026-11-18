import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway

set_option autoImplicit false
open MvPolynomial

namespace P3LocalMem

attribute [local instance] MvPolynomial.algebraMvPolynomial

/--
@isnad1 id=ex.1h5v.s10.33c73aaac595 from=translated src=- shape=470979b6 vocab=81c09cb2
-/
theorem exists_pow_C_mul_mem {σ : Type} {A : Type} [CommRing A] (a : A)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A)
    (h : MvPolynomial.map (algebraMap A (Localization.Away a)) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away a))) I) :
    ∃ n : ℕ, (C a : MvPolynomial σ A) ^ n * f ∈ I := by
  set M : Submonoid (MvPolynomial σ A) := (Submonoid.powers a).map (C (σ := σ)) with hM
  haveI : IsLocalization M (MvPolynomial σ (Localization.Away a)) :=
    MvPolynomial.isLocalization (Submonoid.powers a) (Localization.Away a)
  rw [← MvPolynomial.algebraMap_def] at h
  obtain ⟨⟨⟨g, hg⟩, ⟨s, hs⟩⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff M _).mp h
  simp only at hgs
  rw [← map_mul] at hgs
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists M _).mp hgs
  simp only at hc'
  obtain ⟨_, ⟨m, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hs
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hc
  refine ⟨k + m, ?_⟩
  have : (C a : MvPolynomial σ A) ^ (k + m) * f = C (a ^ k) * (f * C (a ^ m)) := by
    rw [pow_add, map_pow, map_pow]; ring
  rw [this, hc']
  exact I.mul_mem_left _ hg

end P3LocalMem

/--
@isnad1 id=iff.1h6v.s10.9cd901d56edc from=translated src=- shape=08b0d304 vocab=326b26ff
-/
theorem solution
    {σ : Type} (A : Type) [CommRing A] {ι : Type} (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    f ∈ I ↔ ∀ i : ι,
      MvPolynomial.map (algebraMap A (Localization.Away (r i))) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away (r i)))) I := by
  constructor
  · intro hf i
    exact Ideal.mem_map_of_mem _ hf
  · intro H
    have hs : Ideal.span ((C : A →+* MvPolynomial σ A) '' Set.range r) = ⊤ := by
      rw [← Ideal.map_span, hr, Ideal.map_top]
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ hs f
    rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩⟩
    obtain ⟨n, hn⟩ := P3LocalMem.exists_pow_C_mul_mem (r i) I f (H i)
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
