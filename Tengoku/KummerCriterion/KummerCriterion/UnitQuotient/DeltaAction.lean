module

public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Basic
public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Galois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unit quotients: power quotients and `Δ`-components

This file is the power-quotient component layer. It defines the quotient `E / E^(p^N)`
`E = 𝒪_Kˣ`, records the exponent-killing lemma for the quotient map, and
packages the `Δ = (ZMod p)ˣ`-component size data used by reflection.

The component decomposition is kept data-driven: later files can instantiate
the supplied components with the intrinsic idempotent construction, while the
reflection layer can already consume stable character-tagged subgroups and
their computed cardinal exponents.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]

/-- The Galois character group `Δ = (ZMod p)ˣ` indexing unit-quotient
components.-/
abbrev CyclotomicUnitDelta : Type :=
  (ZMod p)ˣ

end KummerCriterion

/-!
# Unit quotients: the actual cyclotomic `Delta` action

The files `UnitQuotient.Components` and `UnitQuotient.Structure` allow a
declared action of `Delta = (ZMod p)ˣ` on `E/E^(p^N)`. This file supplies the
actual action when `K` is the `p`-th cyclotomic field.

The construction uses the standard cyclotomic Galois equivalence

```text
Gal(K / Q) ≃ (ZMod p)ˣ
```

and the induced action of field automorphisms on the ring of integers.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace KummerCriterion

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The standard cyclotomic Galois equivalence
`Gal(K / Q) ≃ (ZMod p)^*`.-/
noncomputable abbrev cyclotomicGalEquivZMod :
    Gal(K / ℚ) ≃* CyclotomicUnitDelta p :=
  IsCyclotomicExtension.Rat.galEquivZMod p K

/-- The Galois automorphism indexed by `a: (ZMod p)^*`.-/
noncomputable def cyclotomicSigmaOfUnit (a : CyclotomicUnitDelta p) :
    Gal(K / ℚ) :=
  (cyclotomicGalEquivZMod (p := p) K).symm a

/--
@isnad1 id=eq.0h3v.s9.ba47fb29d0c2 from=translated src=- shape=14039e96 vocab=f693c809
-/
@[simp]
theorem cyclotomicGalEquivZMod_sigmaOfUnit (a : CyclotomicUnitDelta p) :
    cyclotomicGalEquivZMod (p := p) K (cyclotomicSigmaOfUnit (p := p) K a) = a :=
  (cyclotomicGalEquivZMod (p := p) K).apply_symm_apply a

/--
@isnad1 id=eq.0h2v.s8.9252f7ca6541 from=translated src=- shape=0cb0aa07 vocab=c4698409
-/
@[simp]
theorem cyclotomicSigmaOfUnit_one :
    cyclotomicSigmaOfUnit (p := p) K 1 = 1 :=
  map_one (cyclotomicGalEquivZMod (p := p) K).symm

/--
@isnad1 id=eq.0h4v.s8.a9434dc7dcc3 from=translated src=- shape=1c2a1209 vocab=e5009f1e
-/
@[simp]
theorem cyclotomicSigmaOfUnit_mul (a b : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K (a * b) =
      cyclotomicSigmaOfUnit (p := p) K a * cyclotomicSigmaOfUnit (p := p) K b :=
  map_mul (cyclotomicGalEquivZMod (p := p) K).symm a b

/-- The distinguished primitive `p`-th root of unity in `O_K`.-/
noncomputable abbrev cyclotomicZetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/--
@isnad1 id=isprimit.0h2v.s5.f95b594888b1 from=translated src=- shape=ae028202 vocab=c51dd7c6
-/
theorem cyclotomicZetaInteger_isPrimitiveRoot :
    IsPrimitiveRoot (cyclotomicZetaInteger (p := p) K) p := by
  simpa [cyclotomicZetaInteger] using
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot

/--
@isnad1 id=eq.0h3v.s7.f6132a816264 from=translated src=- shape=6975579a vocab=a60c0bd0
-/
@[simp]
theorem cyclotomicSigmaOfUnit_apply_zeta (a : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K a (IsCyclotomicExtension.zeta p ℚ K) =
      (IsCyclotomicExtension.zeta p ℚ K) ^ (a : ZMod p).val := by
  let σ := cyclotomicSigmaOfUnit (p := p) K a
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (n := p) (K := K) (σ := σ)
      (x := IsCyclotomicExtension.zeta p ℚ K)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one)
  rwa [cyclotomicGalEquivZMod_sigmaOfUnit] at h

/--
@isnad1 id=eq.0h3v.s9.f734273d3f7d from=translated src=- shape=b0fce60a vocab=4189307c
-/
@[simp]
theorem cyclotomicSigmaOfUnit_smul_zetaInteger (a : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K a • cyclotomicZetaInteger (p := p) K =
      cyclotomicZetaInteger (p := p) K ^ (a : ZMod p).val := by
  let σ := cyclotomicSigmaOfUnit (p := p) K a
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
      (n := p) (K := K) (σ := σ)
      (x := cyclotomicZetaInteger (p := p) K)
      ((cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).pow_eq_one)
  rwa [cyclotomicGalEquivZMod_sigmaOfUnit] at h

/-- The ring-of-integers automorphism induced by the cyclotomic Galois
automorphism indexed by `a`.-/
noncomputable def cyclotomicRingOfIntegersEquiv (a : CyclotomicUnitDelta p) :
    𝓞 K ≃+* 𝓞 K :=
  MulSemiringAction.toRingEquiv (Gal(K / ℚ)) (𝓞 K)
    (cyclotomicSigmaOfUnit (p := p) K a)

/--
@isnad1 id=eq.0h3v.s8.28c0f73e80ba from=translated src=- shape=d018cd5b vocab=880700dc
-/
@[simp]
theorem cyclotomicRingOfIntegersEquiv_one_apply (x : 𝓞 K) :
    cyclotomicRingOfIntegersEquiv (p := p) K 1 x = x := by
  simp [cyclotomicRingOfIntegersEquiv]

/--
@isnad1 id=eq.0h5v.s9.58b666261fb4 from=translated src=- shape=060593a8 vocab=efd936c3
-/
theorem cyclotomicRingOfIntegersEquiv_mul_apply
    (a b : CyclotomicUnitDelta p) (x : 𝓞 K) :
    cyclotomicRingOfIntegersEquiv (p := p) K (a * b) x =
      cyclotomicRingOfIntegersEquiv (p := p) K a
        (cyclotomicRingOfIntegersEquiv (p := p) K b x) := by
  change cyclotomicSigmaOfUnit (p := p) K (a * b) • x =
    cyclotomicSigmaOfUnit (p := p) K a •
      cyclotomicSigmaOfUnit (p := p) K b • x
  simp [cyclotomicSigmaOfUnit_mul, smul_smul]

end KummerCriterion

end
