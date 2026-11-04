/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveBundleFlatBaseChangeFieldTensorDimension
import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Generic components of arbitrary fibres after scalar extension

For arbitrary K-algebra A and genuine minimal q in L ⊗[K] A, let p be its actual
contraction along includeRight. The actual tensor quotient map to L ⊗[K] (A/p)
is proved surjective with kernel exactly the extended p. It transports the genuine
minimal prime and its actual quotient; the checked domain calculation then proves
trdeg_L((L ⊗[K] A)/q) = trdeg_K(A/p). No domain, reducedness, finite-generation or
desired transcendence-degree hypothesis is imposed on A.

The contracted prime is proved minimal using actual flatness, and the formula is
also proved for the actual residue fields. Their prime instances are derived from
q's minimality instead of additional inputs.

The projective lifted PureRelDim remains a geometric gate: actual scheme fibre
points and residue fields must be identified with these tensor components, then
the relative transcendence degree converted through the native height formula.
Existing flat-pullback coefficient/generic-support results can be reused. This
module does not assert general-flat all-rank Segre naturality or Chern naturality.
All proofs use default elaboration budgets.
-/

universe u
noncomputable section
open scoped TensorProduct

namespace AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension

/-- A surjective quotient map carries a generic component to a generic component
when its kernel is contained in that component.
@isnad1 id=mem.3h4v.s8.4b4c1e4ad8a3 from=translated src=- shape=cf54bde7 vocab=cbc9c46c
-/
theorem component_minimalPrime_map_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) {q : Ideal R} (hq : q ∈ minimalPrimes R)
    (hker : RingHom.ker f ≤ q) : q.map f ∈ minimalPrimes S := by
  have hq' : q ∈ (RingHom.ker f).minimalPrimes :=
    ⟨⟨hq.1.1, hker⟩, fun _ h hle ↦ hq.2 ⟨h.1, bot_le⟩ hle⟩
  have h := Ideal.minimalPrimes_map_of_surjective hf (⊥ : Ideal R)
  rw [Ideal.map_bot, sup_of_le_right bot_le] at h
  change q.map f ∈ (⊥ : Ideal S).minimalPrimes
  rw [h]
  exact ⟨q, hq', rfl⟩

/-- The quotient of a component is genuinely unchanged by a surjective map
whose kernel is contained in that component.
@isnad1 id=eq.2h5v.s8.cd03fbf50262 from=translated src=- shape=9d622c50 vocab=bdd1cc20
-/
theorem component_quotient_trdeg_of_surjective
    {K R S : Type u} [CommRing K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (f : R →ₐ[K] S)
    (hf : Function.Surjective f) (q : Ideal R) (hker : RingHom.ker f.toRingHom ≤ q) :
    Algebra.trdeg K (R ⧸ q) = Algebra.trdeg K (S ⧸ q.map f.toRingHom) := by
  have hc : (q.map f.toRingHom).comap f.toRingHom = q := by
    rw [Ideal.comap_map_of_surjective f.toRingHom hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  let ψ : R ⧸ q →ₐ[K] S ⧸ q.map f.toRingHom :=
    Ideal.quotientMapₐ (q.map f.toRingHom) f Ideal.le_comap_map
  have hi : Function.Injective ψ := Ideal.quotientMap_injective' (H := Ideal.le_comap_map) hc.le
  have hs : Function.Surjective ψ := Ideal.quotientMap_surjective (H := Ideal.le_comap_map) hf
  exact (AlgEquiv.ofBijective ψ ⟨hi, hs⟩).trdeg_eq

section TensorQuotient
variable {K L A : Type u} [CommRing K] [CommRing L] [CommRing A]
    [Algebra K L] [Algebra K A]

/-- The actual scalar-extended quotient map, defined by tensoring the quotient
map of A with the identity of L.-/
def tensorComponentQuotientMap (p : Ideal A) :
    L ⊗[K] A →ₐ[L] L ⊗[K] (A ⧸ p) :=
  Algebra.TensorProduct.map (AlgHom.id L L) (Ideal.Quotient.mkₐ K p)

/--
@isnad1 id=eq.0h6v.s10.769f9bee38da from=translated src=- shape=51febe1f vocab=4ec21f30
-/
@[simp]
theorem tensorComponentQuotientMap_tmul (p : Ideal A) (l : L) (a : A) :
    tensorComponentQuotientMap p (l ⊗ₜ[K] a) = l ⊗ₜ[K] Ideal.Quotient.mk p a := rfl

/-- The native tensor map is the checked tensor-quotient isomorphism after the
ordinary quotient by the extended ideal.
@isnad1 id=eq.0h4v.s12.54d9ce357ac0 from=translated src=- shape=3cf6a23e vocab=052fb67e
-/
theorem tensorComponentQuotientMap_factor (p : Ideal A) :
    tensorComponentQuotientMap (K := K) (L := L) p =
      (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm.toAlgHom.comp
        (Ideal.Quotient.mkₐ L (p.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))) := by
  ext a
  change (1 : L) ⊗ₜ[K] Ideal.Quotient.mk p a =
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm
      (Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] a))
  exact (Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul
    (R := K) L A L p 1 a).symm

/--
@isnad1 id=surjecti.0h4v.s9.0c0ad52586fa from=translated src=- shape=3253e362 vocab=eca6683f
-/
theorem tensorComponentQuotientMap_surjective (p : Ideal A) :
    Function.Surjective (tensorComponentQuotientMap (K := K) (L := L) p) := by
  rw [tensorComponentQuotientMap_factor]
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm.surjective.comp
    Ideal.Quotient.mk_surjective

/-- The native tensor quotient kernel is exactly the extended original ideal.
@isnad1 id=eq.0h4v.s10.ef028c590ceb from=translated src=- shape=dcda79bc vocab=75f701e1
-/
theorem tensorComponentQuotientMap_ker (p : Ideal A) :
    RingHom.ker (tensorComponentQuotientMap (K := K) (L := L) p).toRingHom =
      p.map (Algebra.TensorProduct.includeRight (R := K) (A := L)) := by
  rw [tensorComponentQuotientMap_factor]
  ext x
  change (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm
    (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [← map_zero (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm,
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L A L p).symm.injective.eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]

end TensorQuotient

/-- A generic component of scalar extension of an arbitrary K-algebra has the
transcendence degree of its contracted original component. The original algebra
may be nonreduced or have several components.
@isnad1 id=eq.1h4v.s11.f0ef72f6ce8a from=translated src=- shape=50dee294 vocab=72876af2
-/
theorem fibreFieldTensor_component_trdeg
    {K L A : Type u} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A]
    {q : Ideal (L ⊗[K] A)} (hq : q ∈ minimalPrimes (L ⊗[K] A)) :
    Algebra.trdeg L ((L ⊗[K] A) ⧸ q) =
      Algebra.trdeg K (A ⧸ q.comap
        (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom) := by
  let T := L ⊗[K] A
  let i : A →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let p : Ideal A := q.comap i
  letI : q.IsPrime := hq.1.1
  letI : p.IsPrime := Ideal.IsPrime.comap i
  let U := L ⊗[K] (A ⧸ p)
  letI : CommRing U := inferInstance
  let φ : T →ₐ[L] U := tensorComponentQuotientMap (K := K) (L := L) p
  have hs : Function.Surjective φ := tensorComponentQuotientMap_surjective p
  have hker : RingHom.ker φ.toRingHom ≤ q := by
    rw [tensorComponentQuotientMap_ker]
    exact Ideal.map_le_iff_le_comap.mpr le_rfl
  have hq' : q.map φ.toRingHom ∈ minimalPrimes U :=
    component_minimalPrime_map_of_surjective φ.toRingHom hs hq hker
  calc
    Algebra.trdeg L (T ⧸ q) = Algebra.trdeg L (U ⧸ q.map φ.toRingHom) :=
      component_quotient_trdeg_of_surjective φ hs q hker
    _ = Algebra.trdeg K (A ⧸ p) := domainFieldTensor_trdeg_quotient hq'

/-- The actual contracted component is generic in the original algebra.
@isnad1 id=mem.1h4v.s10.d77df109f066 from=translated src=- shape=af8005ff vocab=91128904
-/
theorem fibreFieldTensor_component_contraction_minimal
    {K L A : Type u} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A]
    {q : Ideal (L ⊗[K] A)} (hq : q ∈ minimalPrimes (L ⊗[K] A)) :
    q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom
      ∈ minimalPrimes A := by
  letI : Algebra A (L ⊗[K] A) := Algebra.TensorProduct.rightAlgebra
  letI : Module.Free K L := Module.Free.of_divisionRing K L
  letI : Module.Flat A (L ⊗[K] A) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight K A L).toLinearEquiv.symm
  exact minimalPrime_under_of_flat (R := A) hq

/-- The generic component formula for actual residue fields, with the prime
instances supplied by the checked minimality rather than as extra inputs.
@isnad1 id=other.1h4v.s11.9500d6540d30 from=translated src=- shape=cf2c39eb vocab=616229be
-/
theorem fibreFieldTensor_component_residueField_trdeg
    {K L A : Type u} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A]
    {q : Ideal (L ⊗[K] A)} (hq : q ∈ minimalPrimes (L ⊗[K] A)) :
    letI : q.IsPrime := hq.1.1
    let p := q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom
    letI : p.IsPrime := Ideal.IsPrime.comap _
    Algebra.trdeg L q.ResidueField = Algebra.trdeg K p.ResidueField := by
  letI : q.IsPrime := hq.1.1
  let p := q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom
  letI : p.IsPrime := Ideal.IsPrime.comap _
  haveI : Algebra.IsAlgebraic ((L ⊗[K] A) ⧸ q) q.ResidueField :=
    SchemeNormalCone.Algebra.isAlgebraic_of_isFractionRing' _ _
  haveI : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
    SchemeNormalCone.Algebra.isAlgebraic_of_isFractionRing' _ _
  calc
    Algebra.trdeg L q.ResidueField = Algebra.trdeg L ((L ⊗[K] A) ⧸ q) :=
      SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic L _ _
    _ = Algebra.trdeg K (A ⧸ p) := fibreFieldTensor_component_trdeg hq
    _ = Algebra.trdeg K p.ResidueField :=
      (SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic K _ _).symm

end AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension
