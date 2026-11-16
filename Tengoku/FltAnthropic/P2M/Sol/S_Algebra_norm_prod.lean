import Tengoku.Seed.RingTheory.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_norm_prod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_norm_prod

/--
@isnad1 id=eq.0h4v.s8.fd25e5b09b23 from=translated src=- shape=c38807b1 vocab=4699c9ab
-/
theorem solution {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]
