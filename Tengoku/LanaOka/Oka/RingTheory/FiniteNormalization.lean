/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.NoetherNormalization
import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.KrullDimension.NonZeroDivisors
import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Noetherian
import Tengoku.Seed.RingTheory.Localization.Finiteness
import Tengoku.Seed.RingTheory.Algebraic.Integral
import Tengoku.Seed.RingTheory.Polynomial.RationalRoot
import Tengoku.Seed.RingTheory.Polynomial.UniqueFactorization
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finiteness of normalisation

For a domain `D` of finite type over a field of characteristic zero, the integral closure of `D`
in its fraction field is finite over `D`: by Noether normalisation `D` is finite over a polynomial
ring `P`, which is noetherian and integrally closed, and `Frac D` is a finite separable extension
of `Frac P`.

For a reduced algebra `A` of finite type over such a field, the product over the minimal primes
`p` of the normalisations of `A ⧸ p` (`Normalization A`) is a finite injective `A`-algebra and a
finite product of integrally closed domains, and the conductor of `A` in it is contained in no
minimal prime of `A`. Hence `dim (A ⧸ 𝔠) < dim A` for the conductor `𝔠`.

## Main results

- `Algebra.FiniteType.finite_integralClosure`: finiteness of the normalisation of a domain.
- `ringKrullDim_le_of_isIntegral`: `dim S ≤ dim R` for an integral extension `R → S`.
- `ringKrullDim_quotient_add_one_le`: `dim (R ⧸ I) + 1 ≤ dim R` if `I` lies in no minimal prime.
- `exists_normalization`: the normalisation of a reduced algebra of finite type, with its
  conductor.
-/

open scoped nonZeroDivisors

universe u

section Domain

variable (k D : Type*) [Field k] [CharZero k] [CommRing D] [IsDomain D] [Algebra k D]
  [Algebra.FiniteType k D]

include k in
/-- **The normalisation of a domain of finite type over a field of characteristic zero is
finite.** -/
theorem Algebra.FiniteType.finite_integralClosure :
    Module.Finite D (integralClosure D (FractionRing D)) := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k D
  let P := MvPolynomial (Fin s) k
  letI : Algebra P D := g.toRingHom.toAlgebra
  haveI : Module.Finite P D := hgfin
  haveI : FaithfulSMul P D := (faithfulSMul_iff_algebraMap_injective P D).2 hginj
  let K := FractionRing D
  haveI : IsScalarTower P D K := inferInstance
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).2
    (by rw [IsScalarTower.algebraMap_eq P D K]; exact (IsFractionRing.injective D K).comp hginj)
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : Algebra.IsIntegral P D := inferInstance
  haveI : Module.Finite (FractionRing P) K :=
    Module.Finite.of_isLocalization P D P⁰ (Rₚ := FractionRing P) (Sₚ := K)
  haveI : Algebra.IsAlgebraic (FractionRing P) K := inferInstance
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : Module.Finite P (integralClosure P K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure P K)
  have hset : ((integralClosure D K).toSubmodule.restrictScalars P) =
      (integralClosure P K).toSubmodule := by
    ext x
    exact ⟨fun hx ↦ isIntegral_trans (R := P) (A := D) x hx, fun hx ↦ hx.tower_top⟩
  haveI : Module.Finite P ((integralClosure D K).toSubmodule.restrictScalars P) :=
    Module.Finite.equiv (LinearEquiv.ofEq _ _ hset).symm
  haveI : Module.Finite P (integralClosure D K) :=
    inferInstanceAs (Module.Finite P ((integralClosure D K).toSubmodule.restrictScalars P))
  exact Module.Finite.of_restrictScalars_finite P D _

end Domain

section Dimension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The Krull dimension does not increase along an integral extension. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun p q hpq ↦ ?_
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt (show p.asIdeal < q.asIdeal from hpq)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq.le ⟨hxq, hxp⟩
    (Algebra.IsIntegral.isIntegral x)

end Dimension

section Conductor

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The conductor of `R` in `S`: the elements `a ∈ R` with `a S ⊆ R`. -/
def conductorIdeal : Ideal R where
  carrier := {a | ∀ s : S, ∃ r, algebraMap R S r = algebraMap R S a * s}
  zero_mem' s := ⟨0, by simp⟩
  add_mem' {a b} ha hb s := by
    obtain ⟨r, hr⟩ := ha s
    obtain ⟨r', hr'⟩ := hb s
    exact ⟨r + r', by rw [map_add, map_add, hr, hr', add_mul]⟩
  smul_mem' c {a} ha s := by
    obtain ⟨r, hr⟩ := ha s
    exact ⟨c * r, by rw [smul_eq_mul, map_mul, map_mul, hr, mul_assoc]⟩

variable {R S}

lemma mem_conductorIdeal_iff {a : R} :
    a ∈ conductorIdeal R S ↔ ∀ s : S, ∃ r, algebraMap R S r = algebraMap R S a * s :=
  Iff.rfl

/-- The conductor is an ideal of `S`. -/
lemma exists_mem_conductorIdeal {i : R} (hi : i ∈ conductorIdeal R S) (s : S) :
    ∃ r ∈ conductorIdeal R S, algebraMap R S r = algebraMap R S i * s := by
  obtain ⟨r, hr⟩ := hi s
  refine ⟨r, fun s' ↦ ?_, hr⟩
  obtain ⟨r', hr'⟩ := hi (s * s')
  exact ⟨r', by rw [hr', hr, mul_assoc]⟩

end Conductor

section Normalization

/-- A ring **is a finite product of integrally closed domains**. For noetherian rings this is
normality. -/
def IsFiniteProductOfNormalDomains (R : Type u) [CommRing R] : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (D : ι → Type u) (_ : ∀ i, CommRing (D i))
    (_ : ∀ i, IsDomain (D i)) (_ : ∀ i, IsIntegrallyClosed (D i)), Nonempty (R ≃+* ∀ i, D i)

lemma IsFiniteProductOfNormalDomains.of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') (h : IsFiniteProductOfNormalDomains R') : IsFiniteProductOfNormalDomains R := by
  obtain ⟨ι, hι, D, h₁, h₂, h₃, ⟨e'⟩⟩ := h
  exact ⟨ι, hι, D, h₁, h₂, h₃, ⟨e.trans e'⟩⟩

variable (A : Type u) [CommRing A]

instance (p : minimalPrimes A) : p.1.IsPrime :=
  p.2.1.1

/-- **The normalisation** of a ring with finitely many minimal primes: the product, over the
minimal primes `p`, of the integral closures of `A ⧸ p` in their fraction fields. -/
abbrev Normalization : Type u :=
  (p : minimalPrimes A) → integralClosure (A ⧸ p.1) (FractionRing (A ⧸ p.1))

lemma normalization_apply_coe (a : A) (p : minimalPrimes A) :
    ((algebraMap A (Normalization A) a p : integralClosure (A ⧸ p.1) (FractionRing (A ⧸ p.1))) :
      FractionRing (A ⧸ p.1)) = algebraMap (A ⧸ p.1) (FractionRing (A ⧸ p.1))
        (Ideal.Quotient.mk p.1 a) :=
  rfl

lemma isFiniteProductOfNormalDomains_normalization [IsNoetherianRing A] :
    IsFiniteProductOfNormalDomains (Normalization A) :=
  ⟨minimalPrimes A, Set.finite_coe_iff.2 (minimalPrimes.finite_of_isNoetherianRing A), _,
    inferInstance, fun _ ↦ inferInstance,
    fun p ↦ integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (A ⧸ p.1)),
    ⟨RingEquiv.refl _⟩⟩

lemma injective_algebraMap_normalization [IsReduced A] :
    Function.Injective (algebraMap A (Normalization A)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ sInf (minimalPrimes A) := by
    refine Submodule.mem_sInf.2 fun (p : Ideal A) hp ↦ ?_
    have h := congrArg (fun x : Normalization A ↦
      ((x ⟨p, hp⟩ : integralClosure (A ⧸ p) (FractionRing (A ⧸ p))) :
        FractionRing (A ⧸ p))) ha
    haveI : p.IsPrime := hp.1.1
    change algebraMap (A ⧸ p) (FractionRing (A ⧸ p)) (Ideal.Quotient.mk p a) = 0 at h
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
  change a ∈ nilradical A at hmem
  rw [nilradical_eq_zero] at hmem
  exact hmem

variable (k : Type*) [Field k] [CharZero k] [Algebra k A] [Algebra.FiniteType k A]

include k in
lemma finite_normalization :
    Module.Finite A (Normalization A) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI := Set.finite_coe_iff.2 (minimalPrimes.finite_of_isNoetherianRing A)
  haveI (p : minimalPrimes A) :
      Module.Finite A (integralClosure (A ⧸ p.1) (FractionRing (A ⧸ p.1))) := by
    haveI : Algebra.FiniteType k (A ⧸ p.1) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p.1)
        Ideal.Quotient.mk_surjective
    haveI := Algebra.FiniteType.finite_integralClosure k (A ⧸ p.1)
    exact Module.Finite.trans (A ⧸ p.1) _
  exact Module.Finite.pi

include k in
/-- **The conductor of `A` in its normalisation is contained in no minimal prime.** -/
lemma not_conductorIdeal_le (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ¬ conductorIdeal A (Normalization A) ≤ p := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : p.IsPrime := hp.1.1
  let p' : minimalPrimes A := ⟨p, hp⟩
  let C := integralClosure (A ⧸ p) (FractionRing (A ⧸ p))
  -- a common denominator for the normalisation of `A ⧸ p`
  haveI : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      Ideal.Quotient.mk_surjective
  haveI := Algebra.FiniteType.finite_integralClosure k (A ⧸ p)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A ⧸ p) (M := C)
  obtain ⟨⟨b, hb⟩, hbT⟩ := IsLocalization.exist_integer_multiples_of_finset (A ⧸ p)⁰
    (T.image (fun t : C ↦ (t : FractionRing (A ⧸ p))))
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hint : ∀ x : C, ∃ d : A ⧸ p, algebraMap (A ⧸ p) C d = b • x := by
    intro x
    have hx : x ∈ Submodule.span (A ⧸ p) (T : Set C) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨d, hd⟩ := hbT _ (Finset.mem_image_of_mem _ ht)
      exact ⟨d, Subtype.ext hd⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd⟩ := hx
      obtain ⟨d', hd'⟩ := hy
      exact ⟨d + d', by rw [map_add, hd, hd', smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨d, hd⟩ := hx
      exact ⟨r * d, by rw [map_mul, hd, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
        mul_left_comm]⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- an element vanishing on the other minimal primes
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  let F := hfin.toFinset.erase p
  have hFp : ¬ F.prod id ≤ p := by
    rw [Ideal.IsPrime.prod_le ‹_›]
    rintro ⟨q, hq, hqp⟩
    have hq' := Finset.mem_of_mem_erase hq
    rw [Set.Finite.mem_toFinset] at hq'
    exact Finset.ne_of_mem_erase hq (le_antisymm hqp (hp.2 hq'.1 hqp))
  obtain ⟨a, haF, hap⟩ := Set.not_subset.1 hFp
  have haq : ∀ q ∈ F, a ∈ q := fun q hq ↦
    (Ideal.prod_le_inf.trans (Finset.inf_le hq)) haF
  refine fun h ↦ (‹p.IsPrime›.mul_notMem hap
    (fun hc ↦ hb0 (Ideal.Quotient.eq_zero_iff_mem.2 hc))) (h ?_)
  intro s
  obtain ⟨d, hd⟩ := hint (s p')
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨a * d, funext fun q ↦ Subtype.ext ?_⟩
  change algebraMap (A ⧸ q.1) (FractionRing (A ⧸ q.1)) (Ideal.Quotient.mk q.1 (a * d)) =
    algebraMap (A ⧸ q.1) (FractionRing (A ⧸ q.1)) (Ideal.Quotient.mk q.1 (a * c)) *
      (s q : FractionRing (A ⧸ q.1))
  by_cases hq : q = p'
  · subst hq
    have hd' := congrArg Subtype.val hd
    change algebraMap (A ⧸ p) (FractionRing (A ⧸ p)) (Ideal.Quotient.mk p d) =
      Ideal.Quotient.mk p c • (s p' : FractionRing (A ⧸ p)) at hd'
    rw [map_mul, map_mul, map_mul, map_mul, hd', Algebra.smul_def, mul_assoc]
  · have : a ∈ q.1 := haq q.1 (Finset.mem_erase.2 ⟨fun h ↦ hq (Subtype.ext h),
      (Set.Finite.mem_toFinset _).2 q.2⟩)
    simp only [map_mul, Ideal.Quotient.eq_zero_iff_mem.2 this, map_zero, zero_mul]

end Normalization
