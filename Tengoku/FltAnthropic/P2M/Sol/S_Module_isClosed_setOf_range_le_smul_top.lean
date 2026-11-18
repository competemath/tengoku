import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_isClosed_setOf_range_le_smul_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_isClosed_setOf_range_le_smul_top

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} := by
  classical
  let s : Set R := {r | ∃ (φ : Q →ₗ[R] R) (p : P), r = φ (f p)}
  suffices h : {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} = PrimeSpectrum.zeroLocus s by
    rw [h]; exact PrimeSpectrum.isClosed_zeroLocus s
  obtain ⟨sec, hsec⟩ := (inferInstance : Module.Projective R Q).out
  ext x
  simp only [Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hx
    rintro r ⟨φ, p, rfl⟩
    have hfp : f p ∈ x.asIdeal • (⊤ : Submodule R Q) := hx ⟨p, rfl⟩
    show φ (f p) ∈ x.asIdeal
    refine Submodule.smul_induction_on (p := fun q => φ q ∈ x.asIdeal) hfp ?_ ?_
    · intro a ha q _
      rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
    · intro u v hu hv
      rw [map_add]; exact Ideal.add_mem _ hu hv
  · intro hx
    rintro _ ⟨p, rfl⟩
    rw [← hsec (f p), Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact hx ⟨(Finsupp.lapply q).comp sec, p, rfl⟩
