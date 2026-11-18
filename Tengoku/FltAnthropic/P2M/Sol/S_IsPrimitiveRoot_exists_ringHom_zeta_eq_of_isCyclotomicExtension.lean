import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension

set_option autoImplicit false

open IsLocalRing Polynomial

/--
@isnad1 id=ex.1h4v.s7.a932720d82d7 from=translated src=- shape=2137b7ba vocab=9e643f6c
-/
theorem solution
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  let E := hζ.embeddingsEquivPrimitiveRoots L hirr
  have hξmem : ξ ∈ primitiveRoots n L := (mem_primitiveRoots (NeZero.pos n)).mpr hξ
  let φ : K →ₐ[ℚ] L := E.symm ⟨ξ, hξmem⟩
  refine ⟨φ.toRingHom, ?_⟩
  have : (E φ : L) = φ (IsCyclotomicExtension.zeta n ℚ K) := hζ.embeddingsEquivPrimitiveRoots_apply_coe L hirr φ
  rw [show E φ = ⟨ξ, hξmem⟩ from E.apply_symm_apply _] at this
  exact this.symm
