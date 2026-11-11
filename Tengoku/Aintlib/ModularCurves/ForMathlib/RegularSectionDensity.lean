/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Subscheme
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Schematic density of the invertibility locus of a regular section ([KM-FMT-FLAT], engine)

The `[FMT-0]` reduction engine of the [KM-FMT-FLAT] gate (KM's step-(ii)→(iii)→(iv)
universal-case pipeline, KM 6.7.5 exemplar): a closed universal locus
(`Scheme.IdealSheafData`, the T-D15 interface shape) through which the basic open
`D(s) ↪ S` factors is all of `S`, provided `s` is a nonzerodivisor on the sections over
every affine open — *"`S[1/s]` is schematically dense when `S` has no `s`-torsion."*
ℤ-flatness (KM's "the moduli problem is flat over ℤ", First Main Theorem 5.1.1 / 6.6.1 /
6.8.1) enters ONLY through `isSMulRegular_natCast_of_flat`: torsion-free ⟹ every
`N ≠ 0` is regular. The flatness of the specific moduli spaces stays parametric
(tracked gates [FMT-1/2/3] — their spaces are still under construction by the
representability streams).

Consumers: STREAM-NISOG M3 wave (L9, L16, L19, L22, L24, L26) against
`ModularCurves.exists_factor_subschemeι_iff` (T-D14a′) and the T-D15 incidence loci.

Decomposition artifact: `.mathlib-quality/decomposition-fmt-flat.md` ([STREAM-FP], fable-FP).
-/

universe u

open CategoryTheory

/-- **[FMT-0a]** The kernel of localization away from a nonzerodivisor is zero — the
affine heart of "`D(f)` is schematically dense".
@isnad1 id=eq.1h2v.s8.c56f4001d8aa from=translated src=- shape=5939c4ac vocab=e022e014
-/
theorem Localization.Away.ker_algebraMap_eq_bot
    (R : Type*) [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) :
    RingHom.ker (algebraMap R (Localization.Away f)) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp <|
    IsLocalization.injective (M := Submonoid.powers f) (Localization.Away f)
      (Submonoid.powers_le.mpr hf)

/-- **[FMT-0c]** Over a ℤ-flat (equivalently torsion-free) ring, every nonzero integer is
a nonzerodivisor — the ONLY point where KM's "flat over ℤ" hypothesis is consumed.
@isnad1 id=mem.1h2v.s6.15b05b790576 from=translated src=- shape=b0d29427 vocab=70ae7dad
-/
theorem isSMulRegular_natCast_of_flat
    (R : Type*) [CommRing R] [Module.Flat ℤ R] {N : ℤ} (hN : N ≠ 0) :
    (N : R) ∈ nonZeroDivisors R := by
  have key : ∀ x : R, (N : R) * x = 0 → x = 0 := by
    intro x hx
    have hNx : N • x = 0 := by rwa [zsmul_eq_mul]
    have hmem : x ∈ Submodule.torsion ℤ R :=
      ⟨⟨N, mem_nonZeroDivisors_iff_ne_zero.mpr hN⟩, hNx⟩
    rwa [Module.Flat.torsion_eq_bot, Submodule.mem_bot] at hmem
  exact mem_nonZeroDivisors_iff.mpr
    ⟨key, fun x hx => key x (by rwa [mul_comm])⟩

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (s : Γ(S, ⊤))

end AlgebraicGeometry.Scheme
