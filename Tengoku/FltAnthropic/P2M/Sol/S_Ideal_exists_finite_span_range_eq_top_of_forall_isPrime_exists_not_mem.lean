import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem

set_option autoImplicit false

universe u

/--
@isnad1 id=ex.1h2v.s7.25c087380d10 from=translated src=- shape=b9367d8b vocab=b5995f50
-/
theorem solution
    {B : Type u} [CommRing B] (P : B → Prop)
    (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) := by
  classical

  have htop : Ideal.span {f : B | P f} = ⊤ := by
    by_contra h
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf𝔪, hPf⟩ := hloc 𝔪 h𝔪.isPrime
    exact hf𝔪 (hle (Ideal.subset_span hPf))

  have h1 : (1 : B) ∈ Ideal.span {f : B | P f} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨↥T, inferInstance, fun t => t.1, ?_, fun t => hTsub t.2⟩
  rw [Ideal.eq_top_iff_one]
  have : Set.range (fun t : ↥T => (t.1 : B)) = (T : Set B) := by
    ext b; simp
  rw [this]
  exact h1T
