/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.ZMod
import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.LinearAlgebra.Basis.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.RingTheory.Finiteness.Basic
import Tengoku.Seed.RingTheory.LaurentSeries
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.RingTheory.RingHom.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Coefficient-field descent for Laurent series

This file starts the remaining equal-characteristic descent in the local-field structure classification: a finite coefficient field `k` of characteristic `p` gives a canonical
coefficientwise map from `F_p((X))` to `k((X))`.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace FiniteCoefficientLaurent

open scoped LaurentSeries PowerSeries

section PowerSeriesFinite

variable {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]

/-- If the coefficient field extension `A/R` is finite-dimensional, then
`A⟦X⟧` is finitely generated over `R⟦X⟧`.  A finite `R`-basis of `A` gives
generators by embedding basis vectors as constant power series.
@isnad1 id=finite.0h2v.s6.26393eb6f752 from=translated src=- shape=f40ee9d6 vocab=da6599f3
-/
theorem powerSeries_moduleFinite_of_finiteDimensional
    [FiniteDimensional R A] :
    Module.Finite R⟦X⟧ A⟦X⟧ := by
  classical
  let b : Module.Basis (Fin (Module.finrank R A)) R A := Module.finBasis R A
  let gens : Finset A⟦X⟧ :=
    Finset.univ.image fun i : Fin (Module.finrank R A) =>
      PowerSeries.C (b i)
  refine ⟨gens, ?_⟩
  rw [eq_top_iff]
  intro f _hf
  let coord : Fin (Module.finrank R A) → R⟦X⟧ :=
    fun i => PowerSeries.mk fun n => b.repr (PowerSeries.coeff n f) i
  have hsum :
      (∑ i : Fin (Module.finrank R A),
          coord i • PowerSeries.C (b i)) = f := by
    apply PowerSeries.ext
    intro n
    calc
      PowerSeries.coeff n
          (∑ i : Fin (Module.finrank R A),
            coord i • PowerSeries.C (b i)) =
          ∑ i : Fin (Module.finrank R A),
            algebraMap R A (b.repr (PowerSeries.coeff n f) i) * b i := by
        simp [coord, Algebra.smul_def, PowerSeries.algebraMap_apply'',
          PowerSeries.coeff_map]
      _ = PowerSeries.coeff n f := by
        simpa [Algebra.smul_def] using
          (b.sum_repr (PowerSeries.coeff n f))
  rw [← hsum]
  exact
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (coord i) <|
        Submodule.subset_span (by
          simp [gens])

end PowerSeriesFinite

variable (p : ℕ) (k : Type u) [Fact p.Prime] [Field k] [CharP k p]

/-- A finite field of characteristic `p` is finite-dimensional over its prime
field `ZMod p`.
@isnad1 id=finitedi.0h2v.s6.f0c005ceb839 from=translated src=- shape=7d1419be vocab=0b35c26a
-/
theorem zmod_finiteDimensional_of_finite [Finite k] :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    FiniteDimensional (ZMod p) k := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : Fintype k := Fintype.ofFinite k
  exact Module.finite_def.2 <| by
    simpa using
    (Submodule.fg_span (R := ZMod p) (M := k)
      (s := Set.univ) (Set.finite_univ : (Set.univ : Set k).Finite))

/-- Finite generation of `k⟦X⟧` over `F_p⟦X⟧`, for a finite coefficient
field `k` of characteristic `p`.
@isnad1 id=finite.0h2v.s6.6b7c145ec60b from=translated src=- shape=a2a65413 vocab=b74dbc8e
-/
theorem zmodPowerSeries_moduleFinite [Finite k] :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    Module.Finite (ZMod p)⟦X⟧ k⟦X⟧ := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : FiniteDimensional (ZMod p) k :=
    zmod_finiteDimensional_of_finite p k
  exact powerSeries_moduleFinite_of_finiteDimensional (R := ZMod p) (A := k)

/-- Coefficientwise map on power series induced by the prime-field embedding
`ZMod p -> k`.-/
noncomputable def zmodPowerSeriesCoeffMap :
    (ZMod p)⟦X⟧ →+* k⟦X⟧ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  exact PowerSeries.map (algebraMap (ZMod p) k)

/--
Establishes the identity `zmodPowerSeriesCoeffMap p k (PowerSeries.C a) = PowerSeries.C
((ZMod.castHom (m := p) dvd_rfl k) a)`.
@isnad1 id=eq.0h3v.s8.6b03192cc995 from=translated src=- shape=8022fed6 vocab=b2afcdd0
-/
@[simp]
theorem zmodPowerSeriesCoeffMap_C (a : ZMod p) :
    zmodPowerSeriesCoeffMap p k (PowerSeries.C a) =
      PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  rw [zmodPowerSeriesCoeffMap, PowerSeries.map_C]
  change PowerSeries.C ((algebraMap (ZMod p) k) a) =
    PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a)
  rfl

/-- Establishes the identity `zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X`.
@isnad1 id=eq.0h2v.s7.38bf410c7de3 from=translated src=- shape=15564890 vocab=4a219a8e
-/
@[simp]
theorem zmodPowerSeriesCoeffMap_X :
    zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  simp [zmodPowerSeriesCoeffMap]

/-- The coefficientwise power-series map is finite when the coefficient field
extension `k / F_p` is finite.
@isnad1 id=finite.0h2v.s5.77c67912ffb8 from=translated src=- shape=ae968523 vocab=283b33c9
-/
theorem zmodPowerSeriesCoeffMap_finite [Finite k] :
    (zmodPowerSeriesCoeffMap p k).Finite := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change Module.Finite (ZMod p)⟦X⟧ k⟦X⟧
  exact zmodPowerSeries_moduleFinite p k

/-- Coefficientwise Laurent-series map induced from `ZMod p -> k`.-/
noncomputable def zmodLaurentCoeffMap :
    (ZMod p)⸨X⸩ →+* k⸨X⸩ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let φ : ZMod p →+* k := algebraMap (ZMod p) k
  exact
  { toFun := fun f => f.map φ
    map_zero' := by
      change HahnSeries.map (0 : (ZMod p)⸨X⸩) φ.toZeroHom = 0
      exact HahnSeries.map_zero (Γ := ℤ) (R := ZMod p) (S := k) φ.toZeroHom
    map_one' := by
      change HahnSeries.map (1 : (ZMod p)⸨X⸩) φ.toMonoidWithZeroHom = 1
      exact
        HahnSeries.map_one (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toMonoidWithZeroHom
    map_add' := by
      intro x y
      change
        HahnSeries.map (x + y) φ.toAddMonoidHom =
          HahnSeries.map x φ.toAddMonoidHom +
            HahnSeries.map y φ.toAddMonoidHom
      exact
        HahnSeries.map_add (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toAddMonoidHom
    map_mul' := by
      intro x y
      change
        HahnSeries.map (x * y) φ.toNonUnitalRingHom =
          HahnSeries.map x φ.toNonUnitalRingHom *
            HahnSeries.map y φ.toNonUnitalRingHom
      exact
        HahnSeries.map_mul (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toNonUnitalRingHom }

/--
Establishes the identity `(zmodLaurentCoeffMap p k f).coeff n = (ZMod.castHom (m := p) dvd_rfl k)
(f.coeff n)`.
@isnad1 id=eq.0h4v.s8.cf23feba344c from=translated src=- shape=50c51a4d vocab=55d2672d
-/
@[simp]
theorem zmodLaurentCoeffMap_coeff (f : (ZMod p)⸨X⸩) (n : ℤ) :
    (zmodLaurentCoeffMap p k f).coeff n =
      (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change (HahnSeries.map f (algebraMap (ZMod p) k)).coeff n =
    (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n)
  have hφ :
      algebraMap (ZMod p) k = ZMod.castHom (m := p) dvd_rfl k := rfl
  rw [hφ]
  rfl

/--
Establishes the identity `zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
(HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)`.
@isnad1 id=eq.0h3v.s9.5a190ee72e90 from=translated src=- shape=a1aca8b0 vocab=fc40c99d
-/
@[simp]
theorem zmodLaurentCoeffMap_C (a : ZMod p) :
    zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change
    HahnSeries.map (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩)
        (algebraMap (ZMod p) k) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩)
  rw [HahnSeries.map_C]
  change
    HahnSeries.C ((algebraMap (ZMod p) k) a) =
      (HahnSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)
  rfl

/--
Establishes the identity `(zmodLaurentCoeffMap p k).comp (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
(algebraMap k⟦X⟧ k⸨X⸩).comp (zmodPowerSeriesCoeffMap p k)`.
@isnad1 id=eq.0h2v.s8.cc47bee1577c from=translated src=- shape=16e1816a vocab=b521144d
-/
theorem zmodLaurentCoeffMap_comp_powerSeries :
    (zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
      (algebraMap k⟦X⟧ k⸨X⸩).comp
        (zmodPowerSeriesCoeffMap p k) := by
  ext f n
  cases n with
  | ofNat n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_map]
  | negSucc n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]

/--
Establishes the identity `zmodLaurentCoeffMap p k ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
(PowerSeries.X : (ZMod p)⟦X⟧)) = (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)`.
@isnad1 id=eq.0h2v.s9.6ad5fd6f9f18 from=translated src=- shape=00d75b56 vocab=c79525c0
-/
@[simp]
theorem zmodLaurentCoeffMap_powerSeries_X :
    zmodLaurentCoeffMap p k
        ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
          (PowerSeries.X : (ZMod p)⟦X⟧)) =
      (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧) := by
  change
    ((zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩))
      (PowerSeries.X : (ZMod p)⟦X⟧) =
    (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)
  rw [zmodLaurentCoeffMap_comp_powerSeries]
  simp

/-- The induced algebra structure of `k((X))` over `F_p((X))`.-/
@[reducible]
noncomputable def zmodLaurentCoeffAlgebra :
    Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
  RingHom.toAlgebra (zmodLaurentCoeffMap p k)

/-- The Laurent series whose coefficients are one coordinate of the coefficients
of `f` with respect to a fixed `ZMod p`-basis of `k`.-/
noncomputable def zmodLaurentCoeffCoord {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) :
    (ZMod p)⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun n : ℤ => b.repr (f.coeff n) i)
    (by
      refine ⟨f.order, ?_⟩
      intro n hn
      by_contra hlt
      have hzero : f.coeff n = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hlt)
      exact hn (by simp [hzero]))

omit [CharP k p] in
/--
Establishes the identity `(zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n = b.repr
(f.coeff n) i`.
@isnad1 id=eq.0h7v.s9.63adffde539f from=translated src=- shape=97b989e7 vocab=068f9f30
-/
@[simp]
theorem zmodLaurentCoeffCoord_coeff {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) (n : ℤ) :
    (zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n =
      b.repr (f.coeff n) i := by
  exact congrFun
    (HahnSeries.coeff_ofSuppBddBelow
      (f := fun m : ℤ => b.repr (f.coeff m) i))
    n

end FiniteCoefficientLaurent
end LocalFieldTheory.DiscreteValuationField
