/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.BilinearForm.Hyperbolic
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.Lattice.Arithmetic.TorsionFree
import Tengoku.Seed.LinearAlgebra.BilinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Mukai extension of a symmetric bilinear lattice

Given an additive group `N` carrying a symmetric `ℤ`-bilinear form `b`, the
**Mukai extension** is `ℤ × N × ℤ` with

```
⟪(r, c, s), (r', c', s')⟫ = b c c' - r * s' - r' * s.
```

**This is not the Mukai lattice of a K3 surface.** It is the abstract lattice
that lattice is an instance of. Taking `N = NS(X)` with the intersection form
recovers the algebraic Mukai lattice `H⁰ ⊕ NS ⊕ H⁴`, but that identification
needs `D^b(Coh X)`, Chern characters and Hirzebruch–Riemann–Roch, none of which
exist in Mathlib at the pin. It is geometry, it lives in the assumption
frontier, and nothing here discharges it or depends on it.

This is the same discipline `LinearAlgebra/Lattice/Numerical.lean` applies to
`Fin 2 → ℤ`:
every theorem below is a theorem about **an arbitrary symmetric bilinear
`ℤ`-lattice**, and is true whether or not any surface exists.

## Naming

`expectedDim v = ⟪v, v⟫ + 2` is a **definition**, not the Mukai dimension
theorem. The statement that a moduli space of stable objects with primitive
Mukai vector `v` has dimension `⟪v, v⟫ + 2` is geometry and is not asserted.
The name records which numerical quantity is being tracked, nothing more.

## Main results

* `pairing_comm` — the extension is symmetric when `b` is.
* `even_selfPairing` — the extension of an even lattice is even.
* `pairing_rankUnit_corankUnit` — the rank/co-rank plane is a hyperbolic plane:
  two isotropic generators pairing to `-1`.
-/

namespace Mukai

/-- The underlying group of the Mukai extension of `N`: triples `(r, c, s)`.

The name is suggestive of the K3 case; the module docstring records that the
identification with any geometric lattice is **not** made here.-/
abbrev MukaiLattice (N : Type*) : Type _ := ℤ × N × ℤ

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-! ### Bilinearity

Proved directly from the definition rather than inherited, so that every
downstream rewrite has a named lemma to hit.

`linter.unusedSimpArgs` is disabled for this section, and the suppression is
load-bearing rather than cosmetic. It flags `LinearMap.add_apply` and its
siblings in the four *left*-hand lemmas as unused; removing them on that advice
makes all four fail. The reason is asymmetry in the definition: on the right,
`b u.2.1 (v.2.1 + w.2.1)` is closed by `map_add` on the applied form alone,
whereas on the left `b (u.2.1 + v.2.1) w.2.1` first becomes `(b u.2.1 + b v.2.1) w.2.1`
and needs `LinearMap.add_apply` to reach a goal `ring` can see. The linter
judges the `simp only` call in isolation and does not know a `ring` follows it.
Re-check this if the pin moves; do not delete the arguments on the warning
alone. -/

set_option linter.unusedSimpArgs false in
/--
@isnad1 id=eq.0h5v.s7.2e7294775f9e from=translated src=- shape=18d815e7 vocab=9ef14750
-/
theorem pairing_add_left (u v w : MukaiLattice N) :
    pairing b (u + v) w = pairing b u w + pairing b v w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

/--
@isnad1 id=eq.0h5v.s7.25db397a9eb9 from=translated src=- shape=f0377142 vocab=9ef14750
-/
theorem pairing_add_right (u v w : MukaiLattice N) :
    pairing b u (v + w) = pairing b u v + pairing b u w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add]
  ring

set_option linter.unusedSimpArgs false in
/--
@isnad1 id=eq.0h5v.s7.5ceccc6bf139 from=translated src=- shape=63088d8d vocab=6a35fe81
-/
theorem pairing_smul_left (a : ℤ) (v w : MukaiLattice N) :
    pairing b (a • v) w = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/--
@isnad1 id=eq.0h5v.s7.a45065abea5f from=translated src=- shape=9a4e7769 vocab=6a35fe81
-/
theorem pairing_smul_right (a : ℤ) (v w : MukaiLattice N) :
    pairing b v (a • w) = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
  ring

set_option linter.unusedSimpArgs false in
/--
@isnad1 id=eq.0h4v.s7.dae1bdd483cb from=translated src=- shape=526072ad vocab=c04c76cf
-/
theorem pairing_neg_left (v w : MukaiLattice N) :
    pairing b (-v) w = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg, LinearMap.neg_apply]
  ring

/--
@isnad1 id=eq.0h4v.s7.4d075bdb754c from=translated src=- shape=85b4f322 vocab=c04c76cf
-/
theorem pairing_neg_right (v w : MukaiLattice N) :
    pairing b v (-w) = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg]
  ring

set_option linter.unusedSimpArgs false in
/--
@isnad1 id=eq.0h5v.s7.42addac4e07e from=translated src=- shape=18d815e7 vocab=eed991db
-/
theorem pairing_sub_left (u v w : MukaiLattice N) :
    pairing b (u - v) w = pairing b u w - pairing b v w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub, LinearMap.sub_apply]
  ring

/--
@isnad1 id=eq.0h5v.s7.cff4858f09d7 from=translated src=- shape=f0377142 vocab=eed991db
-/
theorem pairing_sub_right (u v w : MukaiLattice N) :
    pairing b u (v - w) = pairing b u v - pairing b u w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

/--
@isnad1 id=eq.0h3v.s7.00e8de4a1561 from=translated src=- shape=18cbb6c1 vocab=263011d4
-/
@[simp]
theorem pairing_zero_left (w : MukaiLattice N) : pairing b 0 w = 0 := by
  simp [pairing]

/--
@isnad1 id=eq.0h3v.s7.2037cec6935f from=translated src=- shape=2dfa2168 vocab=263011d4
-/
@[simp]
theorem pairing_zero_right (v : MukaiLattice N) : pairing b v 0 = 0 := by
  simp [pairing]

/-! ### The quadratic refinement, over `ℤ`

`selfPairing` itself is generic and lives above; these are the `ℤ`-lattice
facts about it. -/

/--
@isnad1 id=eq.0h4v.s7.a2f740c192b6 from=translated src=- shape=7514dd74 vocab=6be33f89
-/
theorem selfPairing_smul (a : ℤ) (v : MukaiLattice N) :
    selfPairing b (a • v) = a ^ 2 * selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_smul_left, pairing_smul_right]
  ring

/--
@isnad1 id=eq.0h2v.s7.ec50b3335951 from=translated src=- shape=b6758c61 vocab=c332cfbd
-/
@[simp]
theorem selfPairing_zero : selfPairing b (0 : MukaiLattice N) = 0 := by
  simp [selfPairing_eq_pairing]

/--
@isnad1 id=eq.0h3v.s7.a71792b1c56a from=translated src=- shape=6d2ebc52 vocab=2fc1a758
-/
theorem selfPairing_neg (v : MukaiLattice N) :
    selfPairing b (-v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_neg_left, pairing_neg_right, neg_neg]

/-- The Mukai extension of an **even** lattice is even.

For a K3 surface the intersection form on `NS(X)` is even, and this is the
lattice-theoretic reason `⟪v, v⟫` is always even there. The hypothesis is
stated, never assumed from geometry.
@isnad1 id=even.1h3v.s8.d2f47ea0c63e from=translated src=- shape=14eb2954 vocab=6ac064cf
-/
theorem even_selfPairing (heven : ∀ x : N, Even (b x x)) (v : MukaiLattice N) :
    Even (selfPairing b v) := by
  obtain ⟨k, hk⟩ := heven v.2.1
  refine ⟨k - v.1 * v.2.2, ?_⟩
  simp only [selfPairing, pairing, hk]
  ring

/-! ### Distinguished classes

`IsSpherical` and `IsIsotropic` are the two numerical conditions the
wall-classification literature is organised around. Both are conditions on a
lattice vector alone. -/

/-- `⟪v, v⟫ = -2`. In the K3 case these are the classes of spherical objects;
here it is a numerical condition and nothing more.-/
def IsSpherical (v : MukaiLattice N) : Prop := selfPairing b v = -2

/-- `⟪v, v⟫ = 0`.-/
def IsIsotropic (v : MukaiLattice N) : Prop := selfPairing b v = 0

/--
@isnad1 id=iff.0h3v.s7.06b612006b1f from=translated src=- shape=e78adbfe vocab=62b40e9a
-/
theorem isSpherical_iff (v : MukaiLattice N) :
    IsSpherical b v ↔ selfPairing b v = -2 := Iff.rfl

/--
@isnad1 id=iff.0h3v.s7.edd77f0d0a7e from=translated src=- shape=630c56c7 vocab=ad307044
-/
theorem isIsotropic_iff (v : MukaiLattice N) :
    IsIsotropic b v ↔ selfPairing b v = 0 := Iff.rfl

/--
@isnad1 id=isspheri.1h3v.s7.64ddf030ec01 from=translated src=- shape=a55e9343 vocab=baa1b4d3
-/
theorem IsSpherical.neg {v : MukaiLattice N} (h : IsSpherical b v) :
    IsSpherical b (-v) := by
  rw [IsSpherical, selfPairing_neg]; exact h

/--
@isnad1 id=isisotro.1h3v.s7.2edaf2008b81 from=translated src=- shape=a55e9343 vocab=af01fcfa
-/
theorem IsIsotropic.neg {v : MukaiLattice N} (h : IsIsotropic b v) :
    IsIsotropic b (-v) := by
  rw [IsIsotropic, selfPairing_neg]; exact h

/--
@isnad1 id=not.0h3v.s6.bacf8f003d09 from=translated src=- shape=cb4b6b57 vocab=f42533dc
-/
theorem not_isSpherical_and_isIsotropic (v : MukaiLattice N) :
    ¬(IsSpherical b v ∧ IsIsotropic b v) := by
  rintro ⟨hs, hi⟩
  rw [IsSpherical, hi] at hs
  exact absurd hs (by decide)

/-- The numerical quantity `⟪v, v⟫ + 2`.

**A definition, not the Mukai dimension theorem.** See the module docstring.-/
def expectedDim (v : MukaiLattice N) : ℤ := selfPairing b v + 2

/--
@isnad1 id=iff.0h3v.s7.3e1b1679e982 from=translated src=- shape=2d69376f vocab=cfe41857
-/
theorem expectedDim_eq_zero_iff (v : MukaiLattice N) :
    expectedDim b v = 0 ↔ IsSpherical b v := by
  rw [expectedDim, IsSpherical]; omega

/--
@isnad1 id=iff.0h3v.s7.093d7e2b8f49 from=translated src=- shape=2d69376f vocab=119801a4
-/
theorem expectedDim_eq_two_iff (v : MukaiLattice N) :
    expectedDim b v = 2 ↔ IsIsotropic b v := by
  rw [expectedDim, IsIsotropic]; omega

/-! ### The hyperbolic plane in the rank / co-rank coordinates

The two outer summands span a copy of the hyperbolic plane `U`, independently
of `b`. This is the lattice-theoretic content of "the Mukai lattice contains
`H⁰ ⊕ H⁴`". -/

/-- `(1, 0, 0)`.-/
def rankUnit : MukaiLattice N := (1, 0, 0)

/-- `(0, 0, 1)`.-/
def corankUnit : MukaiLattice N := (0, 0, 1)

/-- Not `@[simp]`: `pairing_mk` together with `map_zero` already puts the
left-hand side in normal form, and marking this would fail `simpNF`. It is kept
as a readable statement of the outer-plane pairing.
@isnad1 id=eq.0h6v.s7.21e2cda6903b from=translated src=- shape=7a5a8635 vocab=4a9509c0
-/
theorem pairing_outer (r s r' s' : ℤ) :
    pairing b ((r, (0 : N), s)) ((r', (0 : N), s')) = -(r * s' + r' * s) := by
  simp [pairing]
  ring

/--
@isnad1 id=isisotro.0h2v.s6.a32343d51440 from=translated src=- shape=0f72ae94 vocab=1043cb0b
-/
theorem isIsotropic_rankUnit : IsIsotropic b (rankUnit : MukaiLattice N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, rankUnit]

/--
@isnad1 id=isisotro.0h2v.s6.de3be280c5b0 from=translated src=- shape=0f72ae94 vocab=88a03ed1
-/
theorem isIsotropic_corankUnit : IsIsotropic b (corankUnit : MukaiLattice N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, corankUnit]

/-- The two isotropic generators pair to `-1`: the outer plane is hyperbolic.
@isnad1 id=eq.0h2v.s7.89c40d1a441c from=translated src=- shape=22562996 vocab=c304e15e
-/
theorem pairing_rankUnit_corankUnit :
    pairing b (rankUnit : MukaiLattice N) corankUnit = -1 := by
  simp [rankUnit, corankUnit, pairing]

/-! ### Bundled form

The pairing packaged as a `ℤ`-bilinear map, for downstream use with Mathlib's
bilinear/quadratic-form API. -/

/-- The Mukai pairing as a bundled bilinear map.-/
def pairingBilin : MukaiLattice N →ₗ[ℤ] MukaiLattice N →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (pairing b)
    (pairing_add_left b)
    (fun a v w => by rw [pairing_smul_left]; simp)
    (pairing_add_right b)
    (fun a v w => by rw [pairing_smul_right]; simp)

/--
@isnad1 id=eq.0h4v.s9.e59556d8c6e4 from=translated src=- shape=ad1cddb4 vocab=9f6c443d
-/
@[simp]
theorem pairingBilin_apply (v w : MukaiLattice N) :
    pairingBilin b v w = pairing b v w :=
  rfl

end Mukai
