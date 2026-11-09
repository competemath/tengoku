/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FiniteCoefficientLaurent
import Tengoku.Seed.FieldTheory.Finite.Extension
import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.LinearAlgebra.Basis.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The equal-characteristic completed-unramified construction: finite unramified coefficient extensions in equal characteristic

For a finite extension `l / k` of finite fields, coefficientwise extension
makes `l((T))` a finite extension of `k((T))` of the same degree.  Every
automorphism of `l / k` extends coefficientwise, and these extensions exhaust
the Galois group of `l((T)) / k((T))`.  In particular, arithmetic Frobenius
on `l` gives the genuine Frobenius automorphism of this finite Laurent-series
base change and fixes `T`.

This is the finite unramified source used to model the completed maximal
unramified field in the equal-characteristic completed-unramified construction.  The construction is coefficientwise and does not
postulate an abstract unramified extension.
-/

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} {l : Type v}

/-- The coefficientwise map `k((T)) -> l((T))` induced by a ring map
`k -> l`.-/
noncomputable def laurentSeriesCoefficientMap
    {k : Type u} {l : Type v} [Field k] [Field l]
    (f : k →+* l) : k⸨X⸩ →+* l⸨X⸩ where
  toFun x := HahnSeries.map x f
  map_zero' := by
    change HahnSeries.map (0 : k⸨X⸩) f.toZeroHom = 0
    exact HahnSeries.map_zero (Γ := ℤ) f.toZeroHom
  map_one' := by
    change HahnSeries.map (1 : k⸨X⸩) f.toMonoidWithZeroHom = 1
    exact HahnSeries.map_one (Γ := ℤ) f.toMonoidWithZeroHom
  map_add' x y := by
    change HahnSeries.map (x + y) f.toAddMonoidHom =
      HahnSeries.map x f.toAddMonoidHom + HahnSeries.map y f.toAddMonoidHom
    exact HahnSeries.map_add (Γ := ℤ) f.toAddMonoidHom
  map_mul' x y := by
    change HahnSeries.map (x * y) f.toNonUnitalRingHom =
      HahnSeries.map x f.toNonUnitalRingHom * HahnSeries.map y f.toNonUnitalRingHom
    exact HahnSeries.map_mul (Γ := ℤ) f.toNonUnitalRingHom

/-- Mapping Laurent-series coefficients applies the ring homomorphism coefficientwise.
@isnad1 id=eq.0h5v.s8.179d88c135ee from=translated src=- shape=91225d07 vocab=db4b36c3
-/
@[simp]
theorem laurentSeriesCoefficientMap_coeff
    [Field k] [Field l] (f : k →+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientMap f x).coeff m = f (x.coeff m) :=
  rfl

/-- The coefficient map sends a constant series to the mapped constant series.
@isnad1 id=eq.0h4v.s9.49507f4eb7f0 from=translated src=- shape=667b700b vocab=aa0d7d40
-/
@[simp]
theorem laurentSeriesCoefficientMap_C
    [Field k] [Field l] (f : k →+* l) (a : k) :
    laurentSeriesCoefficientMap f (HahnSeries.C (Γ := ℤ) a) =
      HahnSeries.C (Γ := ℤ) (f a) := by
  change HahnSeries.map (HahnSeries.C (Γ := ℤ) a) f = _
  exact HahnSeries.map_C a f

/-- The coefficient map fixes the Laurent uniformizer monomial.
@isnad1 id=eq.0h3v.s9.b55a6c020a5f from=translated src=- shape=fea8be53 vocab=62262e64
-/
@[simp]
theorem laurentSeriesCoefficientMap_single_one
    [Field k] [Field l] (f : k →+* l) :
    laurentSeriesCoefficientMap f (HahnSeries.single (1 : ℤ) 1) =
      (HahnSeries.single (1 : ℤ) 1 : l⸨X⸩) := by
  ext m
  by_cases h : m = 1
  · subst m
    simp
  · simp [HahnSeries.coeff_single_of_ne h]

/-- The induced `k((T))`-algebra structure on `l((T))`.-/
@[reducible]
noncomputable def laurentSeriesCoefficientAlgebra
    [Field k] [Field l] [Algebra k l] : Algebra k⸨X⸩ l⸨X⸩ :=
  RingHom.toAlgebra
    (laurentSeriesCoefficientMap (algebraMap k l))

attribute [local instance] laurentSeriesCoefficientAlgebra

/-- One coefficient coordinate of a Laurent series with respect to a basis
of the coefficient extension.-/
noncomputable def laurentSeriesCoefficientCoord
    [Field k] [Field l] [Algebra k l]
    {ι : Type*} (b : Module.Basis ι k l)
    (x : l⸨X⸩) (i : ι) : k⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦ b.repr (x.coeff m) i)
    (by
      refine ⟨x.order, ?_⟩
      intro m hm
      by_contra hnot
      have hxzero : x.coeff m = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hnot)
      exact hm (by simp [hxzero]))

/-- A Laurent coordinate series records the corresponding basis coordinate coefficientwise.
@isnad1 id=eq.0h7v.s9.bfb32063d720 from=translated src=- shape=88eaef9f vocab=5f71dad1
-/
@[simp]
theorem laurentSeriesCoefficientCoord_coeff
    [Field k] [Field l] [Algebra k l]
    {ι : Type*} (b : Module.Basis ι k l)
    (x : l⸨X⸩) (i : ι) (m : ℤ) :
    (laurentSeriesCoefficientCoord b x i).coeff m =
      b.repr (x.coeff m) i := by
  rfl

section FiniteBasis

variable [Field k] [Field l] [Algebra k l]
  {ι : Type*} [Fintype ι]

private theorem laurentSeriesCoefficientBasis_linearIndependent
    (b : Module.Basis ι k l) :
    LinearIndependent k⸨X⸩
      (fun i : ι ↦ (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)) := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  ext m
  have hcoeff := congrArg (fun x : l⸨X⸩ ↦ x.coeff m) hg
  have halgebraMap_coeff (x : k⸨X⸩) :
      (algebraMap k⸨X⸩ l⸨X⸩ x).coeff m =
        algebraMap k l (x.coeff m) := by
    change
      (laurentSeriesCoefficientMap (algebraMap k l) x).coeff m =
        algebraMap k l (x.coeff m)
    exact laurentSeriesCoefficientMap_coeff (algebraMap k l) x m
  have hsum :
      ∑ j : ι, algebraMap k l ((g j).coeff m) * b j = 0 := by
    simpa [Algebra.smul_def, laurentSeriesCoefficientAlgebra,
      laurentSeriesCoefficientMap, halgebraMap_coeff, mul_comm] using hcoeff
  have hrepr : ∀ j : ι, (g j).coeff m = 0 := by
    intro j
    have hb := Fintype.linearIndependent_iff.mp b.linearIndependent
      (fun t : ι ↦ (g t).coeff m) (by
        simpa [Algebra.smul_def] using hsum) j
    exact hb
  exact hrepr i

private theorem laurentSeriesCoefficientBasis_span
    (b : Module.Basis ι k l) :
    Submodule.span k⸨X⸩
        (Set.range (fun i : ι ↦
          (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩))) = ⊤ := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  classical
  rw [eq_top_iff]
  intro x _hx
  let coord : ι → k⸨X⸩ := fun i ↦ laurentSeriesCoefficientCoord b x i
  have hsum :
      (∑ i : ι, coord i •
        (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)) = x := by
    ext m
    rw [HahnSeries.coeff_sum]
    calc
      (∑ i : ι, (coord i •
          (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩) : l⸨X⸩).coeff m) =
          ∑ i : ι, algebraMap k l (b.repr (x.coeff m) i) * b i := by
        apply Finset.sum_congr rfl
        intro i _
        change
          ((HahnSeries.map (coord i) (algebraMap k l)) *
            (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)).coeff m = _
        rw [mul_comm]
        simp [coord, mul_comm]
      _ = x.coeff m := by
        simpa [Algebra.smul_def] using b.sum_repr (x.coeff m)
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ (coord i)
      (Submodule.subset_span ⟨i, rfl⟩)

/-- A finite coefficient basis extends coefficientwise to a Laurent-series
basis.-/
noncomputable def laurentSeriesCoefficientBasis
    (b : Module.Basis ι k l) : Module.Basis ι k⸨X⸩ l⸨X⸩ := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact Module.Basis.mk
    (laurentSeriesCoefficientBasis_linearIndependent b)
    (laurentSeriesCoefficientBasis_span b).ge

/-- The induced Laurent-series basis consists of constant images of the coefficient basis.
@isnad1 id=eq.0h5v.s9.58943db173f9 from=translated src=- shape=122aacc1 vocab=17211b92
-/
@[simp]
theorem laurentSeriesCoefficientBasis_apply
    (b : Module.Basis ι k l) (i : ι) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    laurentSeriesCoefficientBasis b i =
      (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩) := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact Module.Basis.mk_apply _ _ _

end FiniteBasis

/-- A coefficient-field ring equivalence extends coefficientwise to Laurent
series.-/
noncomputable def laurentSeriesCoefficientRingEquiv
    [Field k] [Field l] (e : k ≃+* l) : k⸨X⸩ ≃+* l⸨X⸩ where
  toFun := laurentSeriesCoefficientMap e.toRingHom
  invFun := laurentSeriesCoefficientMap e.symm.toRingHom
  left_inv x := by
    ext m
    simp
  right_inv x := by
    ext m
    simp
  map_add' := map_add (laurentSeriesCoefficientMap e.toRingHom)
  map_mul' := map_mul (laurentSeriesCoefficientMap e.toRingHom)

/-- A coefficientwise ring equivalence applies the base equivalence at every exponent.
@isnad1 id=eq.0h5v.s9.52d5cc38459e from=translated src=- shape=91225d07 vocab=0eac5d1b
-/
@[simp]
theorem laurentSeriesCoefficientRingEquiv_coeff
    [Field k] [Field l] (e : k ≃+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientRingEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- An automorphism of the coefficient extension acts coefficientwise as an
automorphism over the Laurent-series base.-/
noncomputable def laurentSeriesCoefficientAlgEquiv
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) : l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩ := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  refine
    { laurentSeriesCoefficientRingEquiv e.toRingEquiv with
      commutes' := ?_ }
  intro x
  change laurentSeriesCoefficientMap e.toRingHom
      (laurentSeriesCoefficientMap (algebraMap k l) x) =
    laurentSeriesCoefficientMap (algebraMap k l) x
  ext m
  change e (algebraMap k l (x.coeff m)) = algebraMap k l (x.coeff m)
  exact e.commutes (x.coeff m)

/-- A coefficientwise algebra equivalence applies the base automorphism at every exponent.
@isnad1 id=eq.0h5v.s8.c0d4260b81f0 from=translated src=- shape=c28a2133 vocab=a09760d4
-/
@[simp]
theorem laurentSeriesCoefficientAlgEquiv_coeff
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (laurentSeriesCoefficientAlgEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- Coefficientwise extension as a homomorphism between the two Galois
groups.-/
noncomputable def laurentSeriesCoefficientGalHom
    [Field k] [Field l] [Algebra k l] :
    (l ≃ₐ[k] l) →* (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact
    { toFun := laurentSeriesCoefficientAlgEquiv
      map_one' := by
        apply AlgEquiv.ext
        intro x
        ext m
        simp
      map_mul' := by
        intro e f
        apply AlgEquiv.ext
        intro x
        ext m
        simp }

/-- The Galois homomorphism sends an automorphism to its coefficientwise Laurent action.
@isnad1 id=eq.0h3v.s10.7d6b96db4f67 from=translated src=- shape=2e5e0b0b vocab=235e4d27
-/
@[simp]
theorem laurentSeriesCoefficientGalHom_apply
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    laurentSeriesCoefficientGalHom e = laurentSeriesCoefficientAlgEquiv e :=
  rfl

section FiniteFields

variable [Field k] [Finite k] [Field l] [Finite l] [Algebra k l]

/-- Arithmetic Frobenius on the coefficient field, extended to Laurent
series.-/
noncomputable def equalCharacteristicLaurentFrobenius :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩ := by
  letI : Fintype k := Fintype.ofFinite k
  exact laurentSeriesCoefficientAlgEquiv
    (k := k) (l := l)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k l)

/-- Laurent Frobenius raises each coefficient to the residue-field cardinality.
@isnad1 id=eq.0h4v.s8.e310707f2e3c from=translated src=- shape=5175705a vocab=9c24c1e9
-/
@[simp]
theorem equalCharacteristicLaurentFrobenius_coeff
    (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (equalCharacteristicLaurentFrobenius (k := k) (l := l) x).coeff m =
      (x.coeff m) ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  simp [equalCharacteristicLaurentFrobenius,
    Nat.card_eq_fintype_card]

/-- Laurent Frobenius fixes the Laurent uniformizer.
@isnad1 id=eq.0h2v.s9.a9fb7d1eb070 from=translated src=- shape=4524bf4d vocab=942574ba
-/
@[simp]
theorem equalCharacteristicLaurentFrobenius_single_one :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    equalCharacteristicLaurentFrobenius (k := k) (l := l)
        (HahnSeries.single (1 : ℤ) 1 : l⸨X⸩) =
      HahnSeries.single (1 : ℤ) 1 := by
  let : Fintype k := Fintype.ofFinite k
  ext m
  by_cases h : m = 1
  · subst m
    simp
  · simp [HahnSeries.coeff_single_of_ne h]

end FiniteFields

section ChosenFiniteExtension

variable (k : Type u) [Field k] [Finite k]
  (p n : ℕ) [Fact p.Prime] [CharP k p] [NeZero n]

/-- The finite unramified Laurent-series extension obtained from the chosen
degree-`n` extension of the residue field.-/
def equalCharacteristicFiniteUnramifiedExtension :=
  (FiniteField.Extension k p n)⸨X⸩

/-- The finite unramified Laurent-series extension is a field.-/
instance equalCharacteristicFiniteUnramifiedExtension_field :
    Field (equalCharacteristicFiniteUnramifiedExtension k p n) := by
  change Field ((FiniteField.Extension k p n)⸨X⸩)
  infer_instance

/-- The finite unramified extension is an algebra over the base Laurent field.-/
noncomputable instance equalCharacteristicFiniteUnramifiedAlgebra :
    Algebra k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n) :=
  laurentSeriesCoefficientAlgebra

section

local instance equalCharacteristicFiniteUnramifiedModule :
    @Module k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
      (inferInstance : DivisionRing k⸨X⸩).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicFiniteUnramifiedExtension k p n)).toAddCommMonoid :=
  @Algebra.toModule k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
    _ _ (equalCharacteristicFiniteUnramifiedAlgebra k p n)

end

/-- Comparison with the Laurent-series presentation over the chosen finite
coefficient extension.-/
def equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n ≃+*
      (FiniteField.Extension k p n)⸨X⸩ :=
  RingEquiv.refl _

/-- Algebra-linear comparison with the Laurent-series presentation.  This is
the degree-preserving bridge for the named finite unramified extension.-/
def equalCharacteristicFiniteUnramifiedExtensionAlgEquivLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n ≃ₐ[k⸨X⸩]
      (FiniteField.Extension k p n)⸨X⸩ := by
  change (FiniteField.Extension k p n)⸨X⸩ ≃ₐ[k⸨X⸩]
    (FiniteField.Extension k p n)⸨X⸩
  exact AlgEquiv.refl

/-- Construct a named finite unramified element from a Laurent series.-/
def equalCharacteristicFiniteUnramifiedExtensionOfLaurentSeries :
    (FiniteField.Extension k p n)⸨X⸩ →+*
      equalCharacteristicFiniteUnramifiedExtension k p n :=
  (equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries
    k p n).symm.toRingHom

/-- Read a named finite unramified element as a Laurent series.-/
def equalCharacteristicFiniteUnramifiedExtensionToLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n →+*
      (FiniteField.Extension k p n)⸨X⸩ :=
  (equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries
    k p n).toRingHom

/-- The coefficient of a named finite unramified Laurent element.-/
def equalCharacteristicFiniteUnramifiedExtensionCoeff
    (x : equalCharacteristicFiniteUnramifiedExtension k p n) (m : ℤ) :
    FiniteField.Extension k p n :=
  (equalCharacteristicFiniteUnramifiedExtensionToLaurentSeries
    k p n x).coeff m

/-- Its distinguished arithmetic Frobenius.-/
noncomputable def equalCharacteristicFiniteUnramifiedFrobenius :
    Gal(equalCharacteristicFiniteUnramifiedExtension k p n / k⸨X⸩) :=
  laurentSeriesCoefficientGalHom (FiniteField.Extension.frob k p n)

/-- Finite unramified Frobenius applies finite-field Frobenius coefficientwise.
@isnad1 id=eq.0h5v.s8.1643a0e2bcdb from=translated src=- shape=c1d41dbe vocab=6d588296
-/
@[simp]
theorem equalCharacteristicFiniteUnramifiedFrobenius_coeff
    (x : equalCharacteristicFiniteUnramifiedExtension k p n) (m : ℤ) :
    equalCharacteristicFiniteUnramifiedExtensionCoeff k p n
        (equalCharacteristicFiniteUnramifiedFrobenius k p n x) m =
      (equalCharacteristicFiniteUnramifiedExtensionCoeff k p n x m) ^
        Nat.card k :=
  by
    change ((FiniteField.Extension.frob k p n)
      (equalCharacteristicFiniteUnramifiedExtensionCoeff k p n x m)) = _
    exact FiniteField.Extension.frob_apply k p n

end ChosenFiniteExtension

end EqualCharacteristic
end LubinTate
