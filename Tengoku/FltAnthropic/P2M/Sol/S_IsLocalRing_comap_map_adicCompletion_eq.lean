import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_comap_map_adicCompletion_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_comap_map_adicCompletion_eq

set_option autoImplicit false

namespace C4sol
open IsLocalRing

/--
@isnad1 id=faithful.0h1v.s6.85028dee5ad7 from=translated src=- shape=d7071ce9 vocab=eca1334a
-/
theorem faithfullyFlat_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩

  have hm' : m = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hm)
  subst hm'
  intro htop

  have hle : (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := by
    have := AdicCompletion.pow_smul_top_le_ker_eval (I := maximalIdeal R) (M := R) 1
    simpa using this
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle

  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  rw [hle] at hsurj
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk 1)
  simp only [LinearMap.zero_apply] at hx
  have h1 : (1 : R) ∈ (maximalIdeal R) ^ 1 • (⊤ : Submodule R R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hx]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

end C4sol

open IsLocalRing in
/--
@isnad1 id=eq.0h2v.s9.0c2beee20e0e from=translated src=- shape=ee2cda4e vocab=03932625
-/
theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  haveI := C4sol.faithfullyFlat_adicCompletion R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I
