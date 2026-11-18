import Tengoku.EgzFormalProof.EGZ.Expansion.Basic
import Tengoku.Seed.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Tengoku.Seed.Algebra.Module.ZMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-field characters as linear functionals

Restricting a character to scalar multiples of a vector and using the
one-dimensional character equivalence recovers its finite-field linear
functional.  This gives the exact normalization needed for geometric sums.
-/

namespace EGZ.Expansion

variable {p d : ℕ} [NeZero p]

noncomputable def scalarCharacter (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d) :
    AddChar (ZMod p) ℂ :=
  χ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod p) (FpCoord p d) a).toAddMonoidHom

/--
@isnad1 id=eq.0h5v.s7.c48213ec14be from=translated src=- shape=cdd782c3 vocab=1b13e471
-/
@[simp] theorem scalarCharacter_apply (χ : AddChar (FpCoord p d) ℂ)
    (a : FpCoord p d) (z : ZMod p) : scalarCharacter χ a z = χ (z • a) := rfl

noncomputable def characterLog (χ : AddChar (FpCoord p d) ℂ) :
    FpCoord p d →+ ZMod p where
  toFun a := AddChar.zmodAddEquiv.symm (scalarCharacter χ a)
  map_zero' := by
    apply AddChar.zmodAddEquiv.injective
    simp only [AddEquiv.apply_symm_apply, map_zero]
    ext z
    simp
  map_add' a b := by
    apply AddChar.zmodAddEquiv.injective
    simp only [map_add, AddEquiv.apply_symm_apply]
    ext z
    simp [smul_add, AddChar.map_add_eq_mul]

noncomputable def characterLinear (χ : AddChar (FpCoord p d) ℂ) :
    FpCoord p d →ₗ[ZMod p] ZMod p := (characterLog χ).toZModLinearMap p

/--
@isnad1 id=eq.0h4v.s9.4f16878c6f49 from=translated src=- shape=131cea22 vocab=9106dd27
-/
theorem characterLinear_spec (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d) :
    AddChar.zmodAddEquiv (characterLinear χ a) = scalarCharacter χ a :=
  AddEquiv.apply_symm_apply _ _

/--
@isnad1 id=eq.0h5v.s9.c065557730e2 from=translated src=- shape=890bf73b vocab=8e44a176
-/
theorem characterLinear_eval (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d)
    (n : ℕ) : (AddChar.zmodAddEquiv (characterLinear χ a)) (n : ZMod p) = χ (n • a) := by
  rw [characterLinear_spec, scalarCharacter_apply]
  congr 1
  ext i
  simp [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]

/--
@isnad1 id=ne.1h3v.s9.73c720b1bbf2 from=translated src=- shape=360345b3 vocab=7044f2fa
-/
theorem characterLinear_ne_zero {χ : AddChar (FpCoord p d) ℂ} (hχ : χ ≠ 0) :
    characterLinear χ ≠ 0 := by
  intro hz
  apply hχ
  ext a
  have hh := characterLinear_eval χ a 1
  rw [hz, LinearMap.zero_apply, map_zero] at hh
  simpa using hh.symm

end EGZ.Expansion
