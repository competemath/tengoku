import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span

set_option autoImplicit false

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K5ASOL

/--
@isnad1 id=eq.0h4v.s12.103688acf525 from=translated src=- shape=74025e42 vocab=296eca33
-/
theorem coe_decompose {σ A : Type} [CommRing A] (φ : MvPolynomial σ A) (i : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule σ A) φ) i : MvPolynomial σ A) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

/--
@isnad1 id=eq.1h6v.s9.f1b873f2fe2c from=translated src=- shape=cf54ee92 vocab=2140f051
-/
theorem homogeneousComponent_mul_of_mem_right {σ A : Type} [CommRing A] {e : ℕ} (a : MvPolynomial σ A)
    {g : MvPolynomial σ A} (hg : g ∈ homogeneousSubmodule σ A e) (d : ℕ) :
    homogeneousComponent d (a * g) = if e ≤ d then homogeneousComponent (d - e) a * g else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ A) (a := a) d hg
  simpa only [coe_decompose] using h

end K5ASOL

open K5ASOL in

/--
@isnad1 id=ex.3h5v.s9.a619ec4b02e6 from=translated src=- shape=c66e13f0 vocab=5021c9e3
-/
theorem solution
    {σ A : Type} [CommRing A] (J₀ : Set (MvPolynomial σ A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial σ A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial σ A)) (e : MvPolynomial σ A → ℕ) (c : MvPolynomial σ A → MvPolynomial σ A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G := by
  classical
  obtain ⟨a, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hFJ

  have hdeg : ∀ G : MvPolynomial σ A, ∃ e : ℕ, G ∈ J₀ → G.IsHomogeneous e := by
    intro G
    by_cases hG : G ∈ J₀
    · obtain ⟨e, he⟩ := hJ₀ G hG; exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => (hG h).elim⟩
  choose e he using hdeg
  refine ⟨t.filter (fun G => e G ≤ d), e, fun G => homogeneousComponent (d - e G) (a G), ?_, ?_, ?_⟩
  · intro G hG
    exact ht (Finset.mem_filter.mp hG).1
  · intro G hG
    obtain ⟨hGt, hGe⟩ := Finset.mem_filter.mp hG
    exact ⟨hGe, he G (ht hGt), homogeneousComponent_isHomogeneous _ _⟩
  ·
    have hFd : homogeneousComponent d F = F := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule d F).mpr hF), ite_eq_left rfl]
    rw [Finset.sum_filter, ← hFd, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun G hG => ?_
    rw [smul_eq_mul,
      homogeneousComponent_mul_of_mem_right (a G) ((mem_homogeneousSubmodule (e G) G).mpr (he G (ht hG))) d]
