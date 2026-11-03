/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Slope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Slope stability is a stability function

Rank and degree data on an abelian category — what a polarised **curve** gives to
`Coh X`, with `degree` the usual degree — determine the charge

```
Z (E) = -degree E + i * rank E
```

and **that charge is a stability function**: it is additive on short exact
sequences because rank and degree are, and a nonzero object lands in the
semi-closed upper half-plane because rank is nonnegative and a nonzero object of
rank zero has positive degree.

So μ-slope stability is not a parallel theory: it is the repository's own
`StabilityFunction`, and the phase, semistability, and Harder–Narasimhan
machinery already built on that interface applies to it unchanged.

## The order bridge

`phase_le_iff_slope_le`: on objects of positive rank the phase order **is** the
slope order. The computation is one line through `phaseCross`,

```
phaseCross (Z E) (Z F) = rank E * degree F - degree E * rank F,
```

which is nonnegative exactly when `degree E / rank E ≤ degree F / rank F`. That
is what lets a torsion pair cut by a slope be read as one cut by a phase, which
is the form the tilting machinery consumes.

## What is data and what is proved

`rank_nonneg` and `degree_pos_of_rank_zero` are **fields**: they are the
geometric input, not provable here, since `A` is an arbitrary abelian category.

**They are the CURVE case, not the surface case, and an earlier version of this
docstring said surface.** On a curve a nonzero torsion sheaf has degree equal to
its length, which is positive. On a **surface** it is false: a dimension-zero
sheaf — a skyscraper — has `c₁ = 0`, hence `degree = c₁ · ω = 0`, so
`degree_pos_of_rank_zero` fails on exactly those objects.

The consequence is not cosmetic. μ-slope on a surface is a **weak** stability
function, not a stability function: a skyscraper has zero rank and zero degree, so
its charge is `0`, which `semiClosedUpperHalfPlane` excludes. That is why the weak
theory exists, and it is why a surface lane must not instantiate `SlopeData`.

The slope itself is `degree / rank`, which is junk at rank zero where the
classical slope is `+∞`; every statement about it carries a positive-rank
hypothesis, and the torsion sheaves are handled by the charge rather than by the
slope.

## The surface case is the weakening, not a parallel theory

`WeakSlopeData` (in `WeakSlope.lean`) replaces `degree_pos_of_rank_zero` by
`degree_nonneg_of_rank_zero`, and `toWeakSlopeData` below is the forgetful map
`0 < d → 0 ≤ d`. Everything in this file that carries a positive-rank hypothesis
— `phaseCross_charge`, `charge_ne_zero_of_rank_pos`, `arg_pos_of_rank_pos` and
the order bridge `phase_le_iff_slope_le` — is proved once on `WeakSlopeData` and
inherited here, so the surface lane gets the order bridge without a second copy
of its proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Rank and degree data on an abelian category: what a polarised **curve** gives
to its category of coherent sheaves. See the module docstring — on a surface
`degree_pos_of_rank_zero` is false for skyscrapers.-/
structure SlopeData (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The rank, as a hom out of the Grothendieck group.-/
  rankHom : K₀Ab A →+ ℤ
  /-- The degree, as a hom out of the Grothendieck group. Real-valued, as in
  `WeakSlopeData`, so that a real polarisation can supply it.-/
  degreeHom : K₀Ab A →+ ℝ
  /-- Rank is nonnegative — geometric input.-/
  rank_nonneg : ∀ E : A, 0 ≤ rankHom (K₀Ab.of E)
  /-- A nonzero object of rank zero has positive degree — geometric input, and
  what puts torsion sheaves on the negative real axis. **True on a curve; false
  on a surface**, where a skyscraper has `c₁ = 0` and so degree `0`. See the
  module docstring.-/
  degree_pos_of_rank_zero : ∀ E : A, ¬IsZero E → rankHom (K₀Ab.of E) = 0 →
    0 < degreeHom (K₀Ab.of E)

namespace SlopeData

variable (D : SlopeData A)

/-- The rank of an object.-/
abbrev rank (E : A) : ℤ := D.rankHom (K₀Ab.of E)

/-- The degree of an object.-/
abbrev degree (E : A) : ℝ := D.degreeHom (K₀Ab.of E)

/-! ### The six formal properties, now theorems

`rank_zero`, `rank_iso`, `rank_additive` and their degree counterparts were fields.
They are exactly `K₀Ab.of_isZero`, `of_iso` and `of_shortExact` composed with a hom,
so they are proved here and the names and argument shapes are unchanged. -/

/--
@isnad1 id=eq.1h3v.s5.91578c0f9f47 from=translated src=- shape=164fc834 vocab=41f07174
-/
theorem rank_zero (E : A) (hE : IsZero E) : D.rank E = 0 := by
  rw [rank, K₀Ab.of_isZero hE, map_zero]

/--
@isnad1 id=eq.1h3v.s5.3e182c24af0e from=translated src=- shape=164fc834 vocab=a1ace7f6
-/
theorem degree_zero (E : A) (hE : IsZero E) : D.degree E = 0 := by
  rw [degree, K₀Ab.of_isZero hE, map_zero]

/--
@isnad1 id=eq.0h5v.s5.e0309343be4a from=translated src=- shape=cc9e6acb vocab=b261adaf
-/
theorem rank_iso {E F : A} (e : E ≅ F) : D.rank E = D.rank F := by
  rw [rank, rank, K₀Ab.of_iso e]

/--
@isnad1 id=eq.0h5v.s5.57291fb55759 from=translated src=- shape=cc9e6acb vocab=ea9d0574
-/
theorem degree_iso {E F : A} (e : E ≅ F) : D.degree E = D.degree F := by
  rw [degree, degree, K₀Ab.of_iso e]

/--
@isnad1 id=eq.1h3v.s6.0b8c071c50ec from=translated src=- shape=4b040dc4 vocab=a18be293
-/
theorem rank_additive (S : ShortComplex A) (hS : S.ShortExact) :
    D.rank S.X₂ = D.rank S.X₁ + D.rank S.X₃ := by
  rw [rank, rank, rank, K₀Ab.of_shortExact S hS, map_add]

/--
@isnad1 id=eq.1h3v.s6.9fa01d76fb18 from=translated src=- shape=4b040dc4 vocab=6201dcc2
-/
theorem degree_additive (S : ShortComplex A) (hS : S.ShortExact) :
    D.degree S.X₂ = D.degree S.X₁ + D.degree S.X₃ := by
  rw [degree, degree, degree, K₀Ab.of_shortExact S hS, map_add]

/-! ### The curve case is an instance of the surface case

`degree_pos_of_rank_zero` implies `degree_nonneg_of_rank_zero`, so every
`SlopeData` is a `WeakSlopeData`.  Rank, degree, charge and slope are unchanged
by the map: it forgets a hypothesis and nothing else. -/

/-- **Forget `0 < degree` to `0 ≤ degree`.**  This is what makes `WeakSlopeData`
a genuine weakening of `SlopeData` rather than a second parallel structure.-/
def toWeakSlopeData : WeakSlopeData A where
  rankHom := D.rankHom
  degreeHom := D.degreeHom
  rank_nonneg := D.rank_nonneg
  degree_nonneg_of_rank_zero E hE hr := (D.degree_pos_of_rank_zero E hE hr).le

/--
@isnad1 id=eq.0h3v.s5.87fd3cebfd7c from=translated src=- shape=9a0dd4ec vocab=e8f2cdb3
-/
@[simp] theorem toWeakSlopeData_rank (E : A) : D.toWeakSlopeData.rank E = D.rank E := rfl

/--
@isnad1 id=eq.0h3v.s5.4c34ecc28e86 from=translated src=- shape=9a0dd4ec vocab=95c13166
-/
@[simp] theorem toWeakSlopeData_degree (E : A) : D.toWeakSlopeData.degree E = D.degree E := rfl

/-- The charge `-degree + i * rank`.-/
def charge (E : A) : ℂ := ⟨-(D.degree E : ℝ), (D.rank E : ℝ)⟩

/--
@isnad1 id=eq.0h3v.s5.36a15c2107cb from=translated src=- shape=ecb4440d vocab=62ceaff9
-/
@[simp] theorem charge_re (E : A) : (D.charge E).re = -(D.degree E : ℝ) := rfl

/--
@isnad1 id=eq.0h3v.s5.ae2f0eaf616c from=translated src=- shape=ecb4440d vocab=54454047
-/
@[simp] theorem charge_im (E : A) : (D.charge E).im = (D.rank E : ℝ) := rfl

/--
@isnad1 id=eq.0h3v.s5.ff287d9e0615 from=translated src=- shape=9a0dd4ec vocab=77f588f8
-/
@[simp] theorem toWeakSlopeData_charge (E : A) : D.toWeakSlopeData.charge E = D.charge E := rfl

/--
@isnad1 id=mem.1h3v.s5.b07929e0cf0c from=translated src=- shape=f0999199 vocab=7377176b
-/
theorem charge_mem_semiClosedUpperHalfPlane {E : A} (hE : ¬IsZero E) :
    D.charge E ∈ semiClosedUpperHalfPlane := by
  rcases lt_or_eq_of_le (D.rank_nonneg E) with hpos | hzero
  · left
    simpa using (by exact_mod_cast hpos : (0 : ℝ) < (D.rank E : ℝ))
  · right
    refine ⟨by simpa using (by exact_mod_cast hzero.symm : ((D.rank E : ℤ) : ℝ) = 0), ?_⟩
    have hdeg : 0 < D.degree E := D.degree_pos_of_rank_zero E hE hzero.symm
    have : (0 : ℝ) < (D.degree E : ℝ) := by exact_mod_cast hdeg
    simpa using this

/-- **Slope stability is a stability function.**

`map_zero` and `map_iso` are gone: they were consequences of additivity all
along, and `K₀Ab` proves them once.  Only the additivity of `charge` on short
exact sequences is supplied here, and it is the same two-line computation the
`additive` field used to carry.-/
noncomputable def toStabilityFunction : StabilityFunction A where
  Z := K₀Ab.liftOf D.charge (fun S hS ↦ by
    apply Complex.ext
    · simp only [charge_re, Complex.add_re, D.degree_additive S hS]
      ring
    · simp [D.rank_additive S hS])
  nonzero_mem E hE := by
    rw [abelianDatum_cl, K₀Ab.liftOf_of]
    exact D.charge_mem_semiClosedUpperHalfPlane hE

/--
@isnad1 id=eq.0h3v.s5.1350426cfeb5 from=translated src=- shape=9a0dd4ec vocab=bf9676cc
-/
@[simp]
theorem toStabilityFunction_charge (E : A) :
    D.toStabilityFunction.charge E = D.charge E := by
  simp [toStabilityFunction, StabilityFunction.charge, abelianDatum_cl]

/-- The **slope** `degree / rank`. It is junk at rank zero, where the classical
slope is `+∞`; every statement below asks for positive rank.-/
def slope (E : A) : ℝ := (D.degree E : ℝ) / (D.rank E : ℝ)

/--
@isnad1 id=eq.0h3v.s5.8687d6e83429 from=translated src=- shape=9a0dd4ec vocab=d773799a
-/
@[simp] theorem toWeakSlopeData_slope (E : A) : D.toWeakSlopeData.slope E = D.slope E := rfl

/-- The phase of `toStabilityFunction` **is** the weak phase of `toWeakSlopeData`:
both are `arg` of the same charge, normalised. This is the bridge along which the
positive-rank results below are inherited.
@isnad1 id=eq.0h3v.s5.619c63d9b6df from=translated src=- shape=0aa08258 vocab=8235e40e
-/
theorem toStabilityFunction_phase (E : A) :
    D.toStabilityFunction.phase E = D.toWeakSlopeData.phase E := by
  simp only [StabilityFunction.phase, toStabilityFunction_charge, WeakSlopeData.phase,
    toWeakSlopeData_charge]

/--
@isnad1 id=eq.0h4v.s6.0f1bb5f6d825 from=translated src=- shape=bee43e51 vocab=39586d96
-/
theorem phaseCross_charge (E F : A) :
    phaseCross (D.charge E) (D.charge F)
      = (D.rank E : ℝ) * (D.degree F : ℝ) - (D.degree E : ℝ) * (D.rank F : ℝ) :=
  D.toWeakSlopeData.phaseCross_charge E F

/--
@isnad1 id=ne.1h3v.s5.3b8f870ea8ad from=translated src=- shape=7a517e70 vocab=e42c0011
-/
theorem charge_ne_zero_of_rank_pos {E : A} (hE : 0 < D.rank E) : D.charge E ≠ 0 :=
  D.toWeakSlopeData.charge_ne_zero_of_rank_pos hE

/--
@isnad1 id=lt.1h3v.s5.9c1247e3332a from=translated src=- shape=7bf0bc54 vocab=2002d9b4
-/
theorem arg_pos_of_rank_pos {E : A} (hE : 0 < D.rank E) : 0 < arg (D.charge E) :=
  D.toWeakSlopeData.arg_pos_of_rank_pos hE

/-- **The phase order is the slope order** on objects of positive rank.

`phaseCross` turns the comparison of arguments into the sign of
`rank E * degree F - degree E * rank F`, which is the comparison of slopes once
both ranks are positive.

The proof is `WeakSlopeData.phase_le_iff_slope_le`, transported along
`toWeakSlopeData`: nothing in it uses `degree_pos_of_rank_zero`, because a
positive-rank charge is in the *open* upper half-plane.
@isnad1 id=iff.2h4v.s6.674348c67dc2 from=translated src=- shape=d6e18979 vocab=5cd94599
-/
theorem phase_le_iff_slope_le {E F : A} (hE : 0 < D.rank E) (hF : 0 < D.rank F) :
    D.toStabilityFunction.phase E ≤ D.toStabilityFunction.phase F ↔ D.slope E ≤ D.slope F := by
  rw [toStabilityFunction_phase, toStabilityFunction_phase]
  simpa using D.toWeakSlopeData.phase_le_iff_slope_le hE hF

end SlopeData

end CategoryTheory.Triangulated
