import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchKFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

namespace Ws31
namespace KU

/--
@isnad1 id=righttra.1h4v.s10.2f07011003ab from=translated src=- shape=ce2bfca6 vocab=3e1de416
-/
theorem rightTranslatesSpanFinite_of_forall_mem {G : Type*} [Group G] (H : Subgroup G) (U : G → ℂ)
    (W : Submodule ℂ (↥H → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ g : G, (fun k : ↥H => U (g * (k : G))) ∈ W) :
    RightTranslatesSpanFinite H U := by
  classical
  let b := Module.finBasis ℂ W
  let v : G → W := fun g => ⟨fun k : ↥H => U (g * (k : G)), hW g⟩
  let c : Fin (Module.finrank ℂ W) → (G → ℂ) := fun i g => b.repr (v g) i
  refine ⟨Finset.univ.image c, fun k hk => ?_⟩
  have hpt : ∀ x : G, U (x * k) = ∑ i, c i x * ((b i : W) : ↥H → ℂ) ⟨k, hk⟩ := by
    intro x
    have h := b.sum_repr (v x)
    have h' := congrArg (fun w : W => ((w : ↥H → ℂ)) ⟨k, hk⟩) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h'
    exact h'.symm
  have hfun : (fun x => U (x * k)) = ∑ i, (((b i : W) : ↥H → ℂ) ⟨k, hk⟩) • c i := by
    funext x
    rw [hpt x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
  exact ⟨i, rfl⟩

end Ws31.KU

/--
@isnad1 id=isarchkf.1h2v.s14.b8fd2869f0ef from=translated src=- shape=59c26dbe vocab=1cd24d6e
-/
theorem solution
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => φ (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) :
    IsArchKFinite F φ := by
  intro w
  obtain ⟨W, hWfd, hW⟩ := _hKu w
  haveI := hWfd
  exact Ws31.KU.rightTranslatesSpanFinite_of_forall_mem _ _ W hW
