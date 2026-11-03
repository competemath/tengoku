/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.Algebra.Hom.Rat
import Tengoku.Seed.Algebra.Exact.Basic
import Tengoku.Seed.Algebra.GroupWithZero.Units.Fintype
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku
import Tengoku.Seed.RingTheory.ClassGroup.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Narrow Ideal Class Groups

Defines the narrow ideal class group and its natural map to the usual class
group. The two quotient definitions fit into

`1 → Prin_L⁺ → I_L → Cl_L⁺ → 1`

and

`1 → Prin_L → I_L → Cl_L → 1`.

Since `Prin_L⁺ ≤ Prin_L`, the comparison sequence has kernel
`Prin_L / Prin_L⁺`.

References: Keune, Number Fields, Chapter 6, Exercises 10-11, for the narrow
class group and its map to the ordinary class group. Emerton's genus theory
notes and Trifković, Sections 5.1 and 7.7, give the surrounding genus-theory and
quadratic-form viewpoints.

## TODO

For Keune Ch6 Ex. 11, finish the generic kernel statement for
`Cl⁺(K) → Cl(K)`.

* Identify the kernel with `P_K / P_K⁺`, then with the unit-sign quotient.
* Prove it has exponent two, using that squares are totally positive.

-/

open scoped BigOperators nonZeroDivisors

open FractionalIdeal

namespace Ideal

section NormalizedFactors

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- A Dedekind prime factor of a nonzero integral ideal, regarded as a nonzero
ideal. It is nonzero because the original ideal is contained in the factor.-/
def normalizedFactorNonzeroIdeal
    (I : (Ideal R)⁰)
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)}) :
    (Ideal R)⁰ :=
  ⟨P.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    have hI0 : (I : Ideal R) ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
    have hPdata := (Ideal.mem_normalizedFactors_iff hI0).mp P.2
    intro hPbot
    exact hI0 (le_bot_iff.mp (by simpa [hPbot] using hPdata.2)))⟩

end NormalizedFactors

end Ideal

/-! ### Quotient-group exactness helpers -/

namespace QuotientGroup

section SubgroupQuotient

variable {G : Type*} [CommGroup G]

/-- The natural map `M / N → G / N` induced by the inclusion `M ≤ G`.-/
def subgroupQuotientToQuotient (N M : Subgroup G) :
    M ⧸ N.subgroupOf M →* G ⧸ N :=
  QuotientGroup.map (N.subgroupOf M) N M.subtype (by
    intro x hx
    exact Subgroup.mem_subgroupOf.mp hx)

/--
@isnad1 id=eq.0h4v.s10.dbe9d2637627 from=translated src=- shape=5ad3eec5 vocab=d1544d7d
-/
@[simp]
theorem subgroupQuotientToQuotient_mk (N M : Subgroup G) (x : M) :
    subgroupQuotientToQuotient N M (x : M ⧸ N.subgroupOf M) =
      QuotientGroup.mk' N (x : G) :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- For `N ≤ M ≤ G`, the sequence `M / N → G / N → G / M` is exact at `G / N`.
@isnad1 id=mulexact.1h3v.s10.c22656940990 from=translated src=- shape=9e6122f5 vocab=1f9d4502
-/
theorem mulExact_subgroupQuotientToQuotient_mapOfLE (N M : Subgroup G) (hNM : N ≤ M) :
    Function.MulExact (subgroupQuotientToQuotient N M)
      (QuotientGroup.map N M (MonoidHom.id G) hNM) := by
  rw [MonoidHom.mulExact_iff]
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    change QuotientGroup.mk' M g = 1 at hq
    have hgM : g ∈ M := (QuotientGroup.eq_one_iff (N := M) g).mp hq
    exact ⟨QuotientGroup.mk' (N.subgroupOf M) ⟨g, hgM⟩,
      subgroupQuotientToQuotient_mk N M ⟨g, hgM⟩⟩
  · rintro ⟨qM, rfl⟩
    rw [MonoidHom.mem_ker]
    induction qM using QuotientGroup.induction_on with
    | _ x =>
        change QuotientGroup.map N M (MonoidHom.id G) hNM
            (subgroupQuotientToQuotient N M (x : M ⧸ N.subgroupOf M)) = 1
        rw [subgroupQuotientToQuotient_mk]
        change QuotientGroup.mk' M (x : G) = 1
        exact (QuotientGroup.eq_one_iff (N := M) (x : G)).mpr x.2

end SubgroupQuotient

end QuotientGroup

noncomputable section

namespace NarrowClassGroup

/-! ### Totally positive field elements -/

section TotallyPositive

variable {K : Type*} [Field K]

/-- An element of a field is totally positive if it is positive under every real
embedding. For fields with no real embeddings, this condition is vacuous.-/
def IsTotallyPositive (x : K) : Prop :=
  ∀ σ : K →+* ℝ, 0 < σ x

/-- Over a field with a `ℚ`-algebra structure, total positivity can be tested on
`ℚ`-algebra homomorphisms to `ℝ`.
@isnad1 id=iff.0h2v.s6.33bd5f6615f1 from=translated src=- shape=99aafb1e vocab=73b1edad
-/
theorem isTotallyPositive_iff_forall_ratAlgHom [Algebra ℚ K] (x : K) :
    IsTotallyPositive x ↔ ∀ σ : K →ₐ[ℚ] ℝ, 0 < σ x := by
  constructor
  · intro hx σ
    exact hx σ.toRingHom
  · intro hx σ
    simpa [RingHom.toRatAlgHom_apply] using hx σ.toRatAlgHom

/-- The subgroup of totally positive units of a field. That is K₊ˣ-/
def totallyPositiveUnits (K : Type*) [Field K] : Subgroup Kˣ where
  carrier := {x | IsTotallyPositive (x : K)}
  one_mem' := by
    intro σ
    simp
  mul_mem' := by
    intro x y hx hy σ
    simpa using mul_pos (hx σ) (hy σ)
  inv_mem' := by
    intro x hx σ
    simpa using inv_pos.mpr (hx σ)

/-- Membership in the subgroup of totally positive units.
@isnad1 id=iff.0h2v.s7.73b9bf7669a0 from=translated src=- shape=a8f4e913 vocab=590f96f4
-/
theorem mem_totallyPositiveUnits_iff (x : Kˣ) :
    x ∈ totallyPositiveUnits K ↔ IsTotallyPositive (x : K) :=
  Iff.rfl

/-- If a field has no real embeddings, every element is totally positive by
vacuity.
@isnad1 id=istotall.0h2v.s4.3a9b2d098b8b from=translated src=- shape=6bae7eb6 vocab=e7568149
-/
theorem isTotallyPositive_of_isEmpty [IsEmpty (K →+* ℝ)] (x : K) :
    IsTotallyPositive x := by
  intro σ
  exact isEmptyElim σ

/-- A nonzero square in a field is totally positive.
@isnad1 id=istotall.1h2v.s5.bfc5b2016b38 from=translated src=- shape=fba428df vocab=1b2335c6
-/
theorem isTotallyPositive_sq_of_ne_zero (x : K) (hx : x ≠ 0) :
    IsTotallyPositive (x ^ 2) := by
  intro σ
  have hσx : σ x ≠ 0 := (_root_.map_ne_zero σ).mpr hx
  simpa using sq_pos_of_ne_zero hσx

/-- Integer powers of a totally positive field unit are totally positive.
@isnad1 id=istotall.1h3v.s6.faaed517a4b6 from=translated src=- shape=8f75f0a1 vocab=d13a2b35
-/
theorem isTotallyPositive_zpow (u : Kˣ) (hu : IsTotallyPositive (u : K)) (n : ℤ) :
    IsTotallyPositive ((u ^ n : Kˣ) : K) := by
  intro σ
  simpa using zpow_pos (hu σ) n

/-- A totally positive element plus `1` is totally positive.
@isnad1 id=istotall.1h2v.s5.9bb38226244a from=translated src=- shape=69e55368 vocab=51ffebd2
-/
theorem isTotallyPositive_one_add {x : K} (hx : IsTotallyPositive x) :
    IsTotallyPositive (1 + x) := by
  intro σ
  simpa using add_pos (zero_lt_one : (0 : ℝ) < 1) (hx σ)

/-- If the field has a real embedding, `1 + x` is nonzero for a totally
positive `x`. This is the small positivity input in the concrete positive
Hilbert 90 proof.
@isnad1 id=ne.1h2v.s6.509dff970f08 from=translated src=- shape=3155b599 vocab=1cc3a58a
-/
theorem one_add_ne_zero_of_isTotallyPositive [Nonempty (K →+* ℝ)]
    {x : K} (hx : IsTotallyPositive x) :
    1 + x ≠ 0 := by
  rcases (inferInstance : Nonempty (K →+* ℝ)) with ⟨σ⟩
  intro hzero
  have hσzero : σ (1 + x) = 0 := by
    simpa using congrArg σ hzero
  have hpos : (0 : ℝ) < σ (1 + x) := isTotallyPositive_one_add hx σ
  linarith

/-- Concrete positive Hilbert 90 for an involution.

For the order-two Galois action in Emerton's strict class group item 10, this is
the statement that every totally positive norm-one cocycle `a` is the positive
coboundary of `b = 1 + a`. The real-embedding hypothesis is exactly what rules
out the degenerate imaginary/vacuous case `a = -1`.
@isnad1 id=ex.2h3v.s9.ca80279ef7f5 from=translated src=- shape=fd05245f vocab=424e9f1c
-/
theorem exists_positive_coboundary_of_mul_apply_eq_one
    [Nonempty (K →+* ℝ)] (τ : K ≃+* K) {a : Kˣ}
    (ha_pos : IsTotallyPositive (a : K))
    (ha_norm : (a : K) * τ (a : K) = 1) :
    ∃ b : Kˣ, IsTotallyPositive (b : K) ∧ (a : K) = (b : K) / τ (b : K) := by
  have hb_pos : IsTotallyPositive (1 + (a : K)) :=
    isTotallyPositive_one_add ha_pos
  have hb_ne : (1 + (a : K)) ≠ 0 :=
    one_add_ne_zero_of_isTotallyPositive ha_pos
  let b : Kˣ := Units.mk0 (1 + (a : K)) hb_ne
  refine ⟨b, hb_pos, ?_⟩
  have hτa : τ (a : K) = ((a : K)⁻¹) :=
    eq_inv_of_mul_eq_one_right ha_norm
  have hτb_ne : τ (1 + (a : K)) ≠ 0 :=
    (RingEquiv.map_ne_zero_iff τ).mpr hb_ne
  have hden : 1 + ((a : K)⁻¹) ≠ 0 := by
    simpa [hτa] using hτb_ne
  change (a : K) = (1 + (a : K)) / τ (1 + (a : K))
  rw [show τ (1 + (a : K)) = 1 + τ (a : K) by simp]
  rw [hτa]
  rw [eq_div_iff_mul_eq hden]
  field_simp [Units.ne_zero a]
  ring

end TotallyPositive

/-! ### Narrow principal ideals -/

section NarrowPrincipalIdeals

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The principal-ideal map restricted to totally positive field elements:
`K₊ˣ ↪ Kˣ → I_K`. Its image is `P_K⁺ ≤ P_K ≤ I_K`, the subgroup used in the
narrow quotient.-/
noncomputable def toNarrowPrincipalIdeal (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    totallyPositiveUnits K →* (FractionalIdeal R⁰ K)ˣ :=
  (toPrincipalIdeal R K).comp (totallyPositiveUnits K).subtype

/-- Principal fractional ideals with a totally positive generator, usually denoted `P_K⁺`.-/
noncomputable def narrowPrincipalIdeals (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup ((FractionalIdeal R⁰ K)ˣ) :=
  (toNarrowPrincipalIdeal R K).range

/-- Narrow principal ideals are ordinary principal ideals.
@isnad1 id=le.0h2v.s9.043699845b5f from=translated src=- shape=46effc36 vocab=6c4d98e7
-/
theorem narrowPrincipalIdeals_le_principalIdeals :
    narrowPrincipalIdeals R K ≤ (toPrincipalIdeal R K).range := by
  intro I hI
  rcases hI with ⟨x, rfl⟩
  exact ⟨x.1, rfl⟩

/-- If every field unit is totally positive, the narrow and usual principal
fractional ideals are the same subgroup.
@isnad1 id=eq.1h2v.s8.b79452645193 from=translated src=- shape=7f78a955 vocab=1fea6e7d
-/
theorem narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
    (hpos : ∀ x : Kˣ, IsTotallyPositive (x : K)) :
    narrowPrincipalIdeals R K = (toPrincipalIdeal R K).range := by
  apply le_antisymm
  · exact narrowPrincipalIdeals_le_principalIdeals
  · intro I hI
    rcases hI with ⟨x, rfl⟩
    exact ⟨⟨x, hpos x⟩, rfl⟩

/-- If there are no real embeddings, the positivity condition disappears, so
the narrow and usual principal fractional ideals coincide.
@isnad1 id=eq.0h2v.s8.b2c005bd8da6 from=translated src=- shape=cbcd66b4 vocab=92805b89
-/
theorem narrowPrincipalIdeals_eq_principalIdeals_of_isEmpty [IsEmpty (K →+* ℝ)] :
    narrowPrincipalIdeals R K = (toPrincipalIdeal R K).range :=
  narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
    (fun x => isTotallyPositive_of_isEmpty (x : K))

end NarrowPrincipalIdeals

/-! ### Positive-principal exact sequence -/

section PositivePrincipal

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

/-- The map from ring units to fraction-field units.-/
noncomputable abbrev ringUnitToFractionRing :
    Rˣ →* Kˣ :=
  Units.map (algebraMap R K).toMonoidHom

/-- The subgroup `O_Kˣ⁺` of ring units whose image in the fraction field is
totally positive.-/
def totallyPositiveRingUnits : Subgroup Rˣ where
  carrier := {u | IsTotallyPositive ((ringUnitToFractionRing R K u : Kˣ) : K)}
  one_mem' := by
    intro σ
    simp [ringUnitToFractionRing]
  mul_mem' := by
    intro u v hu hv σ
    simpa [ringUnitToFractionRing] using mul_pos (hu σ) (hv σ)
  inv_mem' := by
    intro u hu σ
    simpa [ringUnitToFractionRing] using inv_pos.mpr (hu σ)

/-- Membership in `O_Kˣ⁺`.
@isnad1 id=iff.0h3v.s8.e666b60c8540 from=translated src=- shape=32841d82 vocab=fb2497db
-/
theorem mem_totallyPositiveRingUnits_iff (u : Rˣ) :
    u ∈ totallyPositiveRingUnits R K ↔
      IsTotallyPositive ((ringUnitToFractionRing R K u : Kˣ) : K) :=
  Iff.rfl

/-- The inclusion `O_Kˣ⁺ → Kˣ⁺`.-/
noncomputable def totallyPositiveRingUnitsToField :
    totallyPositiveRingUnits R K →* totallyPositiveUnits K :=
  ((ringUnitToFractionRing R K).comp (totallyPositiveRingUnits R K).subtype).codRestrict
    (totallyPositiveUnits K) (by
      intro u
      exact u.2)

variable [IsFractionRing R K]

/-- The quotient map `Kˣ⁺ → P_K⁺`, with codomain restricted to its image.-/
noncomputable def toPositivePrincipalIdeals :
    totallyPositiveUnits K →* narrowPrincipalIdeals R K :=
  (toNarrowPrincipalIdeal R K).rangeRestrict

/-- The map `Kˣ⁺ → P_K⁺` is surjective by definition of `P_K⁺`.
@isnad1 id=surjecti.0h2v.s13.318c61036652 from=translated src=- shape=589e8c62 vocab=d57637ca
-/
theorem toPositivePrincipalIdeals_surjective :
    Function.Surjective (toPositivePrincipalIdeals R K) := by
  intro I
  rcases I.2 with ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- Concrete principal-layer consequence of positive Hilbert 90.

If a totally positive unit `a` is norm-one for an involution `τ`, then the
positive principal ideal `(a)` is the coboundary `(b) / (τ b)` for a totally
positive unit `b`. This is the multiplicative, concrete replacement for the
`H¹(G, P_K⁺) = 1` conclusion in Emerton's item 10.
@isnad1 id=ex.2h4v.s15.22e5dd9e1c98 from=translated src=- shape=48d52c85 vocab=f65629b8
-/
theorem toPositivePrincipalIdeals_coboundary_of_mul_apply_eq_one
    [Nonempty (K →+* ℝ)] (τ : K ≃+* K)
    (hτpos : ∀ x : K, IsTotallyPositive x → IsTotallyPositive (τ x))
    {a : totallyPositiveUnits K}
    (ha_norm : (a : Kˣ) * Units.map τ.toMonoidHom (a : Kˣ) = 1) :
    ∃ b : totallyPositiveUnits K,
      toPositivePrincipalIdeals R K a =
        toPositivePrincipalIdeals R K b /
          toPositivePrincipalIdeals R K ⟨Units.map τ.toMonoidHom (b : Kˣ),
            hτpos (((b : Kˣ) : K)) b.2⟩ := by
  have ha_norm_field : ((a : Kˣ) : K) * τ (((a : Kˣ) : K)) = 1 := by
    simpa using congrArg Units.val ha_norm
  obtain ⟨b, hb_pos, hb⟩ := exists_positive_coboundary_of_mul_apply_eq_one
    (τ := τ) (a := (a : Kˣ)) a.2 ha_norm_field
  let bpos : totallyPositiveUnits K := ⟨b, hb_pos⟩
  refine ⟨bpos, ?_⟩
  let τbpos : totallyPositiveUnits K :=
    ⟨Units.map τ.toMonoidHom b, hτpos (b : K) hb_pos⟩
  have ha_eq_units : (a : Kˣ) = (bpos : Kˣ) / (τbpos : Kˣ) := by
    apply Units.ext
    simpa [bpos, τbpos] using hb
  have ha_eq : a = bpos / τbpos := by
    apply Subtype.ext
    exact ha_eq_units
  have hτbpos :
      (⟨Units.map τ.toMonoidHom (bpos : Kˣ),
        hτpos (((bpos : Kˣ) : K)) bpos.2⟩ : totallyPositiveUnits K) = τbpos := by
    rfl
  rw [hτbpos, ha_eq]
  simp [map_div]

end PositivePrincipal

end NarrowClassGroup

/-! ### The narrow class group -/

/-- The narrow ideal class group of `R`.

It is the group of invertible fractional ideals modulo principal fractional
ideals generated by totally positive elements of the fraction field.
That is, `Cl⁺(R) = I(R) / P⁺(R)`, where `P⁺(R)` is generated by the totally
positive elements of `FractionRing R`.-/
def NarrowClassGroup (R : Type*) [CommRing R] [IsDomain R] :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸
    NarrowClassGroup.narrowPrincipalIdeals R (FractionRing R)
deriving CommGroup, Inhabited

namespace NarrowClassGroup

/-! ### Class number -/

/-- The number of narrow ideal classes of `R`.-/
noncomputable def narrowClassNumber (R : Type*) [CommRing R] [IsDomain R]
    [Fintype (NarrowClassGroup R)] : ℕ :=
  Fintype.card (NarrowClassGroup R)

/-! ### Quotient maps -/

section QuotientMaps

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Send an invertible fractional ideal to its narrow ideal class.-/
noncomputable def mk : (FractionalIdeal R⁰ K)ˣ →* NarrowClassGroup R :=
  (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R))).comp
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom)

/-- Unfolding lemma for the narrow ideal-class map.
@isnad1 id=eq.0h3v.s14.e766b42cfb8e from=translated src=- shape=eb046f68 vocab=a7323317
-/
theorem mk_def (I : (FractionalIdeal R⁰ K)ˣ) :
    mk I =
      (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)))
        (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom I) := rfl

/-- Send a nonzero field element to the narrow class of its principal fractional
ideal. This is the composite `Kˣ → I_K → Cl⁺(K)`.-/
noncomputable def principalToNarrow (R : Type*) [CommRing R] [IsDomain R] :
    (FractionRing R)ˣ →* NarrowClassGroup R :=
  mk.comp (toPrincipalIdeal R (FractionRing R))

/-- The natural map from the narrow ideal class group to the ordinary wide ideal
class group, induced by the inclusion of totally positive principal ideals into
all principal ideals. This is the map `Cl⁺(K) → Cl(K)` induced by `P_K⁺ ≤ P_K`.-/
noncomputable def toClassGroup (R : Type*) [CommRing R] [IsDomain R] :
    NarrowClassGroup R →* ClassGroup R :=
  QuotientGroup.map (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range (MonoidHom.id _) (by
      intro I hI
      exact narrowPrincipalIdeals_le_principalIdeals (R := R) (K := FractionRing R) hI)

/-- The natural map to the wide class group sends a narrow ideal class to the
corresponding ordinary ideal class.
@isnad1 id=eq.0h3v.s10.4f840d9cc5cd from=translated src=- shape=1455b3eb vocab=a2d852d8
-/
@[simp]
theorem toClassGroup_mk (I : (FractionalIdeal R⁰ K)ˣ) :
    toClassGroup R (mk I) = ClassGroup.mk K I := by
  rw [mk_def, ClassGroup.mk_def]
  exact QuotientGroup.map_mk' (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range (MonoidHom.id _)
    (by
      intro J hJ
      exact narrowPrincipalIdeals_le_principalIdeals (R := R) (K := FractionRing R) hJ)
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom I)

/-- Send a nonzero integral ideal to its narrow ideal class.

This is the narrow version of `ClassGroup.mk0`, used later for ambiguous ideals
and for the conjugation action on narrow classes.-/
noncomputable def mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* NarrowClassGroup R :=
  mk.comp (FractionalIdeal.mk0 (FractionRing R))

/-- The narrow ideal-class map on an integral ideal agrees with `mk0`.
@isnad1 id=eq.0h2v.s12.e6028e6d2526 from=translated src=- shape=8919a3ac vocab=260fe16e
-/
theorem mk_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    mk (FractionalIdeal.mk0 (FractionRing R) I) = mk0 I := by
  rfl

/-- The map to the wide class group sends the narrow class of an integral ideal
to its usual ideal class.
@isnad1 id=eq.0h2v.s11.0b0022dde0b6 from=translated src=- shape=3bf87e01 vocab=6eeda61b
-/
@[simp]
theorem toClassGroup_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    toClassGroup R (mk0 I) = ClassGroup.mk0 I := by
  rw [mk0, MonoidHom.comp_apply, toClassGroup_mk, ClassGroup.mk_mk0]

/-- Evaluate `toClassGroup` on a quotient representative: the narrow class of
`J` maps to the usual class of `J`.
@isnad1 id=eq.0h2v.s15.064f6bff3fcd from=translated src=- shape=7270b72b vocab=eedfa916
-/
theorem toClassGroup_mk' (R : Type*) [CommRing R] [IsDomain R]
    (J : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    toClassGroup R (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) J) =
      QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range J :=
  QuotientGroup.map_mk' _ _ _ _ J

/-- The natural map from the narrow ideal class group to the ordinary ideal
class group is surjective.
@isnad1 id=surjecti.0h1v.s7.103ffc426a7d from=translated src=- shape=e937283c vocab=0bd7ed3f
-/
theorem toClassGroup_surjective (R : Type*) [CommRing R] [IsDomain R] :
    Function.Surjective (toClassGroup R) := by
  intro C
  induction C using QuotientGroup.induction_on with
  | _ I =>
      refine ⟨QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) I, ?_⟩
      exact toClassGroup_mk' R I

end QuotientMaps

section NormalizedFactors

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

end NormalizedFactors

section FractionRing

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ### Quotient representatives -/

/-- Over the chosen fraction field, `mk` is just the quotient map.
@isnad1 id=eq.0h2v.s14.234f01a9e0f6 from=translated src=- shape=367ccecb vocab=608defa3
-/
theorem mk_eq_mk' (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    mk I = QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) I := by
  rw [mk_def, canonicalEquiv_self]
  rfl

/-! ### Narrow triviality of positive principal integral ideals -/

section PositivePrincipalIntegral

/-- Positive rational integers are totally positive in any fraction field.
@isnad1 id=istotall.1h2v.s7.63a76b7c8290 from=translated src=- shape=755b0923 vocab=09372ef8
-/
theorem isTotallyPositive_natCast_fractionRing (n : ℕ) (hn : 0 < n) :
    IsTotallyPositive (algebraMap R (FractionRing R) (n : R)) := by
  intro σ
  have hσ : σ (algebraMap R (FractionRing R) (n : R)) = (n : ℝ) := by
    exact map_natCast (σ.comp (algebraMap R (FractionRing R))) n
  rw [hσ]
  exact Nat.cast_pos.mpr hn

variable [IsDedekindDomain R]

/-- A principal integral ideal generated by a totally positive element is trivial
in the narrow class group.
@isnad1 id=eq.2h2v.s11.eae41528065b from=translated src=- shape=2b606aff vocab=c0729b6b
-/
theorem mk0_span_singleton_eq_one_of_isTotallyPositive
    {a : R} (ha : a ≠ 0)
    (hpos : IsTotallyPositive (algebraMap R (FractionRing R) a)) :
    mk0 (R := R)
      ⟨Ideal.span ({a} : Set R), by
        rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
          Ideal.span_singleton_eq_bot]
        exact ha⟩ = 1 := by
  let F := FractionRing R
  have haF : algebraMap R F a ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact ha
  let u : Fˣ := Units.mk0 (algebraMap R F a) haF
  have hu_pos : u ∈ totallyPositiveUnits F := hpos
  rw [← mk_mk0, mk_eq_mk']
  exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨u, hu_pos⟩, by
    apply Units.ext
    change (toPrincipalIdeal R F u : FractionalIdeal R⁰ F) =
      FractionalIdeal.mk0 F
        ⟨Ideal.span ({a} : Set R), by
          rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
            Ideal.span_singleton_eq_bot]
          exact ha⟩
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R F a) =
      (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ F)
    rw [FractionalIdeal.coeIdeal_span_singleton]⟩

end PositivePrincipalIntegral

/-! ### Exactness of the narrow-to-wide comparison -/

/-- The map `P_K / P_K⁺ → Cl⁺(K)` coming from the inclusion of principal
fractional ideals into all fractional ideals.-/
noncomputable def principalIdealsQuotientToNarrow (R : Type*) [CommRing R] [IsDomain R] :
    (toPrincipalIdeal R (FractionRing R)).range ⧸
      (narrowPrincipalIdeals R (FractionRing R)).subgroupOf
        (toPrincipalIdeal R (FractionRing R)).range →* NarrowClassGroup R :=
  QuotientGroup.subgroupQuotientToQuotient
    (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range

/-- The image of principal fractional ideals in the narrow class group is exactly
the kernel of the map `Cl⁺(K) → Cl(K)`.
@isnad1 id=mulexact.0h1v.s9.ffefd023c4d6 from=translated src=- shape=59c5e68d vocab=510e1fb0
-/
theorem mulExact_principalToNarrow_toClassGroup (R : Type*) [CommRing R] [IsDomain R] :
    Function.MulExact (principalToNarrow R) (toClassGroup R) := by
  rw [MonoidHom.mulExact_iff]
  ext C
  constructor
  · intro hC
    obtain ⟨I, rfl⟩ :=
      QuotientGroup.mk'_surjective (narrowPrincipalIdeals R (FractionRing R)) C
    rw [← mk_eq_mk'] at hC ⊢
    rw [MonoidHom.mem_ker, toClassGroup_mk, ← map_one (ClassGroup.mk (K := FractionRing R)),
      ClassGroup.mk_eq_mk] at hC
    obtain ⟨x, hx⟩ := hC
    refine ⟨x⁻¹, ?_⟩
    have hI : toPrincipalIdeal R (FractionRing R) x⁻¹ = I := by
      rw [map_inv]
      exact inv_eq_of_mul_eq_one_left hx
    change mk (toPrincipalIdeal R (FractionRing R) x⁻¹) = mk I
    rw [hI]
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, principalToNarrow, MonoidHom.comp_apply, toClassGroup_mk,
      ← map_one (ClassGroup.mk (K := FractionRing R)), ClassGroup.mk_eq_mk]
    exact ⟨x⁻¹, by rw [map_inv, mul_inv_cancel]⟩

/-- The kernel of `Cl⁺(K) → Cl(K)` is the image of principal ideals in the
narrow class group.
@isnad1 id=eq.0h1v.s7.7c5d3a33677c from=translated src=- shape=5d31e4b1 vocab=12e65766
-/
theorem toClassGroup_ker_eq_principalToNarrow_range
    (R : Type*) [CommRing R] [IsDomain R] :
    (toClassGroup R).ker = (principalToNarrow R).range :=
  Function.MulExact.monoidHom_ker_eq (mulExact_principalToNarrow_toClassGroup R)

/-! ### Equality and principal multipliers -/

set_option backward.isDefEq.respectTransparency false in
/-- Two invertible fractional ideals have the same narrow class exactly when
they differ by a totally positive principal fractional ideal.
@isnad1 id=iff.0h3v.s13.4953dc364503 from=translated src=- shape=74ffd14d vocab=2ed7ad38
-/
theorem mk_eq_mk {I J : (FractionalIdeal R⁰ (FractionRing R))ˣ} :
    mk I = mk J ↔
      ∃ x : totallyPositiveUnits (FractionRing R),
        I * toNarrowPrincipalIdeal R (FractionRing R) x = J := by
  rw [mk_eq_mk', mk_eq_mk']
  rw [QuotientGroup.mk'_eq_mk' (N := narrowPrincipalIdeals R (FractionRing R))]
  constructor
  · rintro ⟨P, hP, hIP⟩
    rcases hP with ⟨x, rfl⟩
    exact ⟨x, hIP⟩
  · rintro ⟨x, hIP⟩
    exact ⟨toNarrowPrincipalIdeal R (FractionRing R) x, ⟨x, rfl⟩, hIP⟩

/-- A principal nonzero integral ideal has a fraction-field generator whose
principal fractional ideal is its `mk0`.
@isnad1 id=ex.1h2v.s12.c9a702ea7657 from=translated src=- shape=2b6a20a2 vocab=8f77e1ea
-/
theorem exists_toPrincipalIdeal_eq_mk0_of_isPrincipal [IsDedekindDomain R]
    {I : (Ideal R)⁰} (hI : (I : Ideal R).IsPrincipal) :
    ∃ γ : (FractionRing R)ˣ,
      toPrincipalIdeal R (FractionRing R) γ = FractionalIdeal.mk0 (FractionRing R) I := by
  classical
  letI : (I : Ideal R).IsPrincipal := hI
  let a : R := Submodule.IsPrincipal.generator (I : Ideal R)
  have hIa : Ideal.span ({a} : Set R) = (I : Ideal R) := by
    simp [a]
  have hI0 : (I : Ideal R) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have ha0 : a ≠ 0 :=
    fun ha => hI0 (by rw [← hIa, ha, Ideal.span_singleton_eq_bot])
  let γ : (FractionRing R)ˣ := Units.mk0 (algebraMap R (FractionRing R) a) (by
    simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne ha0)
  refine ⟨γ, ?_⟩
  rw [toPrincipalIdeal_eq_iff]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a) =
    (FractionalIdeal.mk0 (FractionRing R) I : FractionalIdeal R⁰ (FractionRing R))
  rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) a, hIa]
  rfl

/-- Negating a fraction-field unit does not change its principal fractional ideal.
@isnad1 id=eq.0h2v.s12.26270449ffd7 from=translated src=- shape=a678ea14 vocab=879768f5
-/
theorem toPrincipalIdeal_neg (γ : (FractionRing R)ˣ) :
    toPrincipalIdeal R (FractionRing R) (-γ) = toPrincipalIdeal R (FractionRing R) γ := by
  rw [← Units.val_inj]
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨-1, by simp⟩

private theorem toPrincipalIdeal_algebraMap_unit_eq_one (u : Rˣ) :
    toPrincipalIdeal R (FractionRing R)
        (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 := by
  rw [← Units.val_inj]
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) (u : R)) =
    (1 : FractionalIdeal R⁰ (FractionRing R))
  rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) (u : R)]
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
  rfl

/-- Multiplying a fraction-field generator by an integral unit does not change
its principal fractional ideal.
@isnad1 id=eq.0h3v.s12.f0c91661088a from=translated src=- shape=df2efb42 vocab=5dc5963e
-/
-- Retain the Dedekind hypothesis to preserve the existing public theorem signature.
@[nolint unusedArguments]
theorem toPrincipalIdeal_mul_algebraMap_unit [IsDedekindDomain R]
    (γ : (FractionRing R)ˣ) (u : Rˣ) :
    toPrincipalIdeal R (FractionRing R)
        (γ * Units.map (algebraMap R (FractionRing R)).toMonoidHom u) =
      toPrincipalIdeal R (FractionRing R) γ := by
  rw [map_mul]
  rw [toPrincipalIdeal_algebraMap_unit_eq_one]
  simp

/-! ### Integral representatives -/

/-- An integral ideal representative for a narrow class.

Compared with the usual class-group numerator, this uses one extra denominator.
The change from the original fractional ideal is then generated by a square,
hence by a totally positive element.-/
def integralRep (I : FractionalIdeal R⁰ (FractionRing R)) : Ideal R :=
  Ideal.span ({(I.den : R)} : Set R) * I.num

/-- The narrow integral representative of a nonzero fractional ideal is nonzero.
@isnad1 id=mem.1h2v.s9.4b3a2c8c3fca from=translated src=- shape=d8faa2ea vocab=e58b4dbf
-/
theorem integralRep_mem_nonZeroDivisors
    {I : FractionalIdeal R⁰ (FractionRing R)} (hI : I ≠ 0) :
    integralRep I ∈ (Ideal R)⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero, integralRep]
  apply mul_ne_zero
  · rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.den.prop
  · rwa [ne_eq, FractionalIdeal.num_eq_zero_iff]

/-! ### Comparison with the usual class group -/

/-- If the narrow and usual principal fractional ideals are the same subgroup,
then the narrow and wide class groups are isomorphic.-/
noncomputable def mulEquivClassGroupOfEq (R : Type*) [CommRing R] [IsDomain R]
    (h : narrowPrincipalIdeals R (FractionRing R) =
      (toPrincipalIdeal R (FractionRing R)).range) :
    NarrowClassGroup R ≃* ClassGroup R :=
  QuotientGroup.quotientMulEquivOfEq h

/-- If the narrow and usual principal fractional ideals coincide, then
`toClassGroup` is bijective.
@isnad1 id=bijectiv.1h1v.s10.b7f743bb19cb from=translated src=- shape=9577355a vocab=76bffe4a
-/
theorem toClassGroup_bijective_of_eq (R : Type*) [CommRing R] [IsDomain R]
    (h : narrowPrincipalIdeals R (FractionRing R) =
      (toPrincipalIdeal R (FractionRing R)).range) :
    Function.Bijective (toClassGroup R) :=
  (mulEquivClassGroupOfEq R h).bijective

/-- If every unit of the fraction field is totally positive, then the narrow and
wide class groups are isomorphic.-/
noncomputable def mulEquivClassGroupOfForallIsTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    NarrowClassGroup R ≃* ClassGroup R :=
  mulEquivClassGroupOfEq R
    (narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
      (R := R) (K := FractionRing R) hpos)

/-- Nonempty form of `mulEquivClassGroupOfForallIsTotallyPositive`.
@isnad1 id=nonempty.1h1v.s7.789c8dcea9d7 from=translated src=- shape=b067127a vocab=78280cd3
-/
theorem nonempty_mulEquivClassGroup_of_forall_isTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    Nonempty (NarrowClassGroup R ≃* ClassGroup R) :=
  ⟨mulEquivClassGroupOfForallIsTotallyPositive R hpos⟩

/-- If every unit of the fraction field is totally positive, then
`toClassGroup` is bijective.
@isnad1 id=bijectiv.1h1v.s7.cc680c97786f from=translated src=- shape=290ce2f9 vocab=a9a0dfde
-/
theorem toClassGroup_bijective_of_forall_isTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    Function.Bijective (toClassGroup R) :=
  toClassGroup_bijective_of_eq R
    (narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
      (R := R) (K := FractionRing R) hpos)

/-- If the fraction field has no real embeddings, the narrow and wide class
groups are isomorphic.-/
noncomputable def mulEquivClassGroupOfIsEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    NarrowClassGroup R ≃* ClassGroup R :=
  mulEquivClassGroupOfForallIsTotallyPositive R
    (fun x => isTotallyPositive_of_isEmpty (x : FractionRing R))

/-- Nonempty form of `mulEquivClassGroupOfIsEmpty`.
@isnad1 id=nonempty.0h1v.s7.f33b28d6d446 from=translated src=- shape=b1b0e302 vocab=7a221bc5
-/
theorem nonempty_mulEquivClassGroup_of_isEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    Nonempty (NarrowClassGroup R ≃* ClassGroup R) :=
  ⟨mulEquivClassGroupOfIsEmpty R⟩

/-- If the fraction field has no real embeddings, then `toClassGroup` is
bijective.
@isnad1 id=bijectiv.0h1v.s7.e343ec54d623 from=translated src=- shape=b8987098 vocab=1e97e944
-/
theorem toClassGroup_bijective_of_isEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    Function.Bijective (toClassGroup R) :=
  toClassGroup_bijective_of_forall_isTotallyPositive R
    (fun x => isTotallyPositive_of_isEmpty (x : FractionRing R))

end FractionRing

/-! ### Finiteness of the narrow class group

The narrow class group is finite when the wide class group is finite and the
fraction field has finitely many real embeddings. For rings of integers in
number fields, both hypotheses hold. The kernel of `toClassGroup` is controlled
by signs of units at the real embeddings, so it embeds into a finite group of
sign vectors. -/

/-- The sign homomorphism on the units of `ℝ`, valued in the unit group of `SignType`.-/
def realSignUnitHom : ℝˣ →* SignTypeˣ :=
  Units.map (signHom : ℝ →*₀ SignType).toMonoidHom

/--
@isnad1 id=eq.0h1v.s7.3eaceae71545 from=translated src=- shape=27132441 vocab=9457447b
-/
theorem realSignUnitHom_apply (u : ℝˣ) :
    ((realSignUnitHom u : SignTypeˣ) : SignType) = SignType.sign (u : ℝ) :=
  rfl

/-- Send a unit of `K` to its signs at all real embeddings. The kernel is the
subgroup of totally positive units.-/
def signVectorHom (K : Type*) [Field K] : Kˣ →* ((K →+* ℝ) → SignTypeˣ) where
  toFun x σ := realSignUnitHom (Units.map (σ : K →+* ℝ).toMonoidHom x)
  map_one' := by funext σ; simp
  map_mul' a b := by funext σ; simp [map_mul]

/--
@isnad1 id=eq.0h3v.s9.5c9a66e471b5 from=translated src=- shape=b0655359 vocab=4c35adb1
-/
theorem signVectorHom_apply (K : Type*) [Field K] (x : Kˣ) (σ : K →+* ℝ) :
    signVectorHom K x σ = realSignUnitHom (Units.map (σ : K →+* ℝ).toMonoidHom x) :=
  rfl

/-- The subgroup of totally positive units is exactly the kernel of the sign-vector
homomorphism.
@isnad1 id=eq.0h1v.s7.5b049ca9260c from=translated src=- shape=60a2e948 vocab=fd6510d9
-/
theorem totallyPositiveUnits_eq_ker (K : Type*) [Field K] :
    totallyPositiveUnits K = (signVectorHom K).ker := by
  ext x
  simp only [mem_totallyPositiveUnits_iff, IsTotallyPositive, MonoidHom.mem_ker]
  constructor
  · intro hx
    funext σ
    ext
    change SignType.sign (σ (x : K)) = 1
    exact sign_eq_one_iff.mpr (hx σ)
  · intro hx σ
    have hxσ : signVectorHom K x σ = 1 := congrFun hx σ
    have hxσ_val : ((signVectorHom K x σ : SignTypeˣ) : SignType) = 1 := by
      simpa using congrArg Units.val hxσ
    change SignType.sign (σ (x : K)) = 1 at hxσ_val
    exact sign_eq_one_iff.mp hxσ_val

/-- If there are finitely many real embeddings, then units modulo totally
positive units form a finite group.
@isnad1 id=finite.0h1v.s6.7d2e04fdbce3 from=translated src=- shape=8b5c2150 vocab=78e58bcf
-/
instance instFiniteUnitsQuotientTotallyPositiveUnits (K : Type*) [Field K]
    [Finite (K →+* ℝ)] : Finite (Kˣ ⧸ totallyPositiveUnits K) := by
  rw [totallyPositiveUnits_eq_ker]
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective (signVectorHom K))

/-- The image of field units in the narrow class group is finite when the fraction field
has finitely many real embeddings.
@isnad1 id=finite.0h1v.s7.b3a1a5146c60 from=translated src=- shape=8898bf22 vocab=d6621c15
-/
theorem finite_range_principalToNarrow (R : Type*) [CommRing R] [IsDomain R]
    [Finite (FractionRing R →+* ℝ)] : Finite (principalToNarrow R).range := by
  let φ := principalToNarrow R
  have hker : totallyPositiveUnits (FractionRing R) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change mk (toPrincipalIdeal R (FractionRing R) x) = 1
    rw [mk_eq_mk']
    exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨x, hx⟩, rfl⟩
  let L := QuotientGroup.lift (totallyPositiveUnits (FractionRing R)) φ hker
  let ψ : (FractionRing R)ˣ ⧸ totallyPositiveUnits (FractionRing R) → φ.range :=
    fun q => ⟨L q, by
      induction q using QuotientGroup.induction_on with
      | _ x => exact ⟨x, (QuotientGroup.lift_mk' _ _ x).symm⟩⟩
  haveI : Finite φ.range := Finite.of_surjective ψ (by
    rintro ⟨_, x, rfl⟩
    exact ⟨QuotientGroup.mk' _ x, Subtype.ext (QuotientGroup.lift_mk' _ _ x)⟩)
  simpa [φ]

/-- The kernel of `Cl⁺(K) → Cl(K)` is finite when the fraction field has finitely
many real embeddings.
@isnad1 id=finite.0h1v.s7.136b60a8098c from=translated src=- shape=55b7fd2b vocab=a1f47dff
-/
theorem finite_ker_toClassGroup (R : Type*) [CommRing R] [IsDomain R]
    [Finite (FractionRing R →+* ℝ)] : Finite (toClassGroup R).ker := by
  rw [toClassGroup_ker_eq_principalToNarrow_range]
  exact finite_range_principalToNarrow R

/-- The narrow class group is finite if the wide class group is finite and the
fraction field has finitely many real embeddings.
@isnad1 id=finite.0h1v.s6.2378f449cf4d from=translated src=- shape=403a6b5c vocab=2e023238
-/
instance instFiniteNarrowClassGroup (R : Type*) [CommRing R] [IsDomain R]
    [Finite (ClassGroup R)] [Finite (FractionRing R →+* ℝ)] :
    Finite (NarrowClassGroup R) := by
  rw [(toClassGroup R).finite_iff_finite_ker_range]
  exact ⟨finite_ker_toClassGroup R, inferInstance⟩

end NarrowClassGroup
