import Tengoku.Seed.NumberTheory.NumberField.InfinitePlace.Embeddings
import Tengoku.Seed.NumberTheory.NumberField.ClassNumber
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas
import Tengoku.Seed.RingTheory.ClassGroup
import Tengoku.Seed.LinearAlgebra.FreeModule.IdealQuotient
import Tengoku.Seed.GroupTheory.QuotientGroup.Finite
import Tengoku.Seed.Data.Fintype.Units

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Deep.NTSupply.coprimeToModulus` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.mem_coprimeToModulus_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.narrowRaySet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.narrowRaySubgroup` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.narrowRaySubgroup_le_coprimeToModulus` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.NarrowRayClassGroup` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.NarrowRayClassGroup.mk` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.one_mem_narrowRaySet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbol` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbol_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolHom` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolHom_prime` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolDescend` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolDescend_mk` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolDescend_primeClass` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.raySymbolIdealHom` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.primeUnit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.primeClass` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.movingLemma` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.finite` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.coprimeToModulus_top` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Deep.NTSupply.finite_closure_of_involutions` (it only prints; the queue checks the axioms of every declaration). -/

open NumberField nonZeroDivisors IsDedekindDomain

noncomputable section

namespace Deep.NTSupply

section Involutions

/--
@isnad1 id=finite.2h2v.s6.78f1532daa1f from=translated src=- shape=2e257570 vocab=df75c492
-/
theorem finite_closure_of_involutions {G : Type*} [CommGroup G] {S : Set G} (hS : S.Finite)
    (hsq : ∀ s ∈ S, s * s = 1) : ((Subgroup.closure S : Subgroup G) : Set G).Finite := by
  classical
  let F : Finset G := hS.toFinset
  let g : (F → Bool) → G := fun e => ∏ t ∈ F.attach, if e t then (t : G) else 1
  have hsqF : ∀ t : F, (t : G) * (t : G) = 1 := fun t => hsq t (hS.mem_toFinset.mp t.2)
  have key : ∀ (t : F) (b b' : Bool),
      (if b then (t : G) else 1) * (if b' then (t : G) else 1) = if (b != b') then (t : G) else 1 := by
    intro t b b'
    cases b <;> cases b' <;> simp [hsqF t]
  have hmul : ∀ e e' : F → Bool, g e * g e' = g (fun t => e t != e' t) := by
    intro e e'
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => key t (e t) (e' t)
  have hone : g (fun _ => false) = 1 := by simp [g]
  have hrange : (Set.range g).Finite := Set.finite_range g
  refine hrange.subset ?_
  intro x hx
  replace hx : x ∈ Subgroup.closure S := hx
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
      refine ⟨fun t => decide ((t : G) = s), ?_⟩
      have hsF : s ∈ F := hS.mem_toFinset.mpr hs
      show (∏ t ∈ F.attach, if decide ((t : G) = s) then (t : G) else 1) = s
      rw [Finset.prod_eq_single ⟨s, hsF⟩]
      · simp
      · intro t _ ht
        have : ((t : G) = s) = False := by
          have : (t : G) ≠ s := fun h => ht (Subtype.ext h)
          exact eq_false this
        simp [this]
      · intro h
        exact absurd (Finset.mem_attach F ⟨s, hsF⟩) h
  | one => exact ⟨fun _ => false, hone⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨e, rfl⟩ := iha
      obtain ⟨e', rfl⟩ := ihb
      exact ⟨fun t => e t != e' t, (hmul e e').symm⟩
  | inv a ha iha =>
      obtain ⟨e, rfl⟩ := iha
      have hself : g e * g e = 1 := by
        rw [hmul e e]
        have : (fun t : F => e t != e t) = fun _ => false := by
          funext t; simp
        rw [this, hone]
      exact ⟨e, (inv_eq_of_mul_eq_one_right hself).symm⟩

/--
@isnad1 id=finite.2h2v.s6.fff771c328ae from=translated src=- shape=d872ac77 vocab=127c71fa
-/
theorem finite_closure_of_involutions' {G : Type*} [CommGroup G] {S : Set G} (hS : S.Finite)
    (hsq : ∀ s ∈ S, s * s = 1) : Finite (Subgroup.closure S) :=
  (finite_closure_of_involutions hS hsq).to_subtype

end Involutions

section Carriers

variable (K : Type*) [Field K] [NumberField K]

def coprimeToModulus (𝔣 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
    FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = 0}
  mul_mem' := by
    intro I J hI hJ v hv
    have h : ((I * J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
        (I : FractionalIdeal ((𝓞 K)⁰) K) * (J : FractionalIdeal ((𝓞 K)⁰) K) := Units.val_mul I J
    rw [h, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  one_mem' := by
    intro v _
    rw [Units.val_one, FractionalIdeal.count_one]
  inv_mem' := by
    intro I hI v hv
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

/--
@isnad1 id=iff.0h3v.s10.8c518d9f8404 from=translated src=- shape=e6e15209 vocab=ee768a9b
-/
theorem mem_coprimeToModulus_iff {𝔣 : Ideal (𝓞 K)} {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ} :
    I ∈ coprimeToModulus K 𝔣 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = 0 :=
  Iff.rfl

def narrowRaySet (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
    (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) ∧
    (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)}

/--
@isnad1 id=iff.0h3v.s10.cd8c376bc656 from=translated src=- shape=d4cf8f89 vocab=1d9c8e4e
-/
theorem mem_narrowRaySet_iff {𝔣 : Ideal (𝓞 K)} {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ} :
    I ∈ narrowRaySet K 𝔣 ↔ ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) ∧
      (I : FractionalIdeal ((𝓞 K)⁰) K) =
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
  Iff.rfl

def narrowRaySubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  Subgroup.closure (narrowRaySet K 𝔣)

/--
@isnad1 id=eq.3h4v.s8.22beaaf11ef8 from=translated src=- shape=05509ea3 vocab=ddea5107
-/
theorem count_span_singleton_eq_zero_of_sub_one_mem {𝔣 : Ideal (𝓞 K)} {α : 𝓞 K} (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔣) :
    FractionalIdeal.count K v
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 0 := by
  classical
  have hJ0 : (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hα0
  have hndvd : ¬ v.asIdeal ∣ (Ideal.span {α} : Ideal (𝓞 K)) := by
    intro hdvd
    have hαv : α ∈ v.asIdeal := Ideal.dvd_span_singleton.mp hdvd
    have hα1v : α - 1 ∈ v.asIdeal := Ideal.le_of_dvd hv hα1
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem hαv hα1v
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rw [FractionalIdeal.count_coe K v hJ0]
  have hc : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {α} : Ideal (𝓞 K))).factors
      = 0 := by
    by_contra h
    exact hndvd ((Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mp h)
  rw [hc, Nat.cast_zero]

/--
@isnad1 id=le.0h2v.s10.abba6b66580c from=translated src=- shape=447566e1 vocab=0fa2e4ee
-/
theorem narrowRaySubgroup_le_coprimeToModulus (𝔣 : Ideal (𝓞 K)) :
    narrowRaySubgroup K 𝔣 ≤ coprimeToModulus K 𝔣 := by
  rw [narrowRaySubgroup, Subgroup.closure_le]
  rintro I ⟨α, hα0, hα1, -, hI⟩
  rw [SetLike.mem_coe, mem_coprimeToModulus_iff]
  intro v hv
  rw [hI]
  exact count_span_singleton_eq_zero_of_sub_one_mem K hα0 hα1 hv

abbrev NarrowRayClassGroup (𝔣 : Ideal (𝓞 K)) : Type _ :=
  ↥(coprimeToModulus K 𝔣) ⧸ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)

def NarrowRayClassGroup.mk (𝔣 : Ideal (𝓞 K)) :
    ↥(coprimeToModulus K 𝔣) →* NarrowRayClassGroup K 𝔣 :=
  QuotientGroup.mk' _

/--
@isnad1 id=mem.0h2v.s9.a4aa0f9ffe8e from=translated src=- shape=228df59d vocab=e6880397
-/
theorem one_mem_narrowRaySet (𝔣 : Ideal (𝓞 K)) :
    (1 : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySet K 𝔣 := by
  refine ⟨1, one_ne_zero, by simp, ?_, ?_⟩
  · intro τ
    rw [map_one, map_one]
    exact one_pos
  · rw [Units.val_one, Ideal.span_singleton_one, FractionalIdeal.coeIdeal_top]

end Carriers

section Symbol

variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]

def raySymbol (f : HeightOneSpectrum (𝓞 K) → M) (I : FractionalIdeal ((𝓞 K)⁰) K) : M :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v ^ FractionalIdeal.count K v I

/--
@isnad1 id=hasfinit.0h4v.s6.af1f26bfaf0f from=translated src=- shape=b554d086 vocab=7f617f5e
-/
theorem hasFiniteMulSupport_raySymbol_factors (f : HeightOneSpectrum (𝓞 K) → M)
    (I : FractionalIdeal ((𝓞 K)⁰) K) :
    Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => f v ^ FractionalIdeal.count K v I) := by
  show (Function.mulSupport _).Finite
  refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
  intro v hv
  simp only [Function.mem_mulSupport, ne_eq] at hv
  simp only [Set.mem_ofPred_eq]
  intro h
  exact hv (by rw [h, zpow_zero])

/--
@isnad1 id=eq.2h5v.s9.edd0bcd9e41f from=translated src=- shape=9638aa29 vocab=c2d5c9ef
-/
theorem raySymbol_mul (f : HeightOneSpectrum (𝓞 K) → M) {I J : FractionalIdeal ((𝓞 K)⁰) K}
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    raySymbol K f (I * J) = raySymbol K f I * raySymbol K f J := by
  unfold raySymbol
  rw [← finprod_mul_distrib (hasFiniteMulSupport_raySymbol_factors K f I)
    (hasFiniteMulSupport_raySymbol_factors K f J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul K v hI hJ, zpow_add]

def raySymbolUnitsHom (f : HeightOneSpectrum (𝓞 K) → M) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ →* M where
  toFun I := raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K)
  map_one' := by simp [raySymbol, FractionalIdeal.count_one]
  map_mul' I J := by
    simp only [Units.val_mul]
    exact raySymbol_mul K f I.ne_zero J.ne_zero

def raySymbolHom (𝔣 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → M) :
    ↥(coprimeToModulus K 𝔣) →* M :=
  (raySymbolUnitsHom K f).comp (coprimeToModulus K 𝔣).subtype

/--
@isnad1 id=eq.0h5v.s14.8142611280ae from=translated src=- shape=e04d1f8d vocab=88c94c96
-/
theorem raySymbolHom_apply (𝔣 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → M)
    (I : ↥(coprimeToModulus K 𝔣)) :
    raySymbolHom K 𝔣 f I =
      raySymbol K f ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) :=
  rfl

end Symbol

section Finiteness

variable (K : Type*) [Field K] [NumberField K]

def raySet (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
    (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)}

/--
@isnad1 id=le.0h2v.s8.c4d9d9ad0c1f from=translated src=- shape=447566e1 vocab=3bdf2550
-/
theorem narrowRaySet_subset_raySet (𝔣 : Ideal (𝓞 K)) : narrowRaySet K 𝔣 ⊆ raySet K 𝔣 := by
  rintro I ⟨α, hα0, hα1, -, hI⟩
  exact ⟨α, hα0, hα1, hI⟩

/--
@isnad1 id=le.0h2v.s10.c510c001bc8d from=translated src=- shape=dc780dc2 vocab=84813c6a
-/
theorem raySet_subset_coprimeToModulus (𝔣 : Ideal (𝓞 K)) :
    raySet K 𝔣 ⊆ (coprimeToModulus K 𝔣 : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
  rintro I ⟨α, hα0, hα1, hI⟩
  rw [SetLike.mem_coe, mem_coprimeToModulus_iff]
  intro v hv
  rw [hI]
  exact count_span_singleton_eq_zero_of_sub_one_mem K hα0 hα1 hv

def rayClasses (𝔣 : Ideal (𝓞 K)) : Set (NarrowRayClassGroup K 𝔣) :=
  (NarrowRayClassGroup.mk K 𝔣) ''
    {y : ↥(coprimeToModulus K 𝔣) | (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ raySet K 𝔣}

def rayClassSubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup (NarrowRayClassGroup K 𝔣) :=
  Subgroup.closure (rayClasses K 𝔣)

/--
@isnad1 id=normal.0h2v.s11.b8b7b4d60c6e from=translated src=- shape=4a052fd7 vocab=1b7a7618
-/
instance instNormalRayClassSubgroup (𝔣 : Ideal (𝓞 K)) : (rayClassSubgroup K 𝔣).Normal :=
  ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

/--
@isnad1 id=eq.1h3v.s14.4c301c4456ec from=translated src=- shape=23f1da1a vocab=2c54a030
-/
theorem NarrowRayClassGroup.mk_eq_one_of_mem {𝔣 : Ideal (𝓞 K)}
    {y : ↥(coprimeToModulus K 𝔣)}
    (hy : (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣) :
    NarrowRayClassGroup.mk K 𝔣 y = 1 := by
  rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact hy

/--
@isnad1 id=iff.0h4v.s15.ea7c11cba045 from=translated src=- shape=961cd12a vocab=f867b4e6
-/
theorem NarrowRayClassGroup.mk_eq_mk_iff {𝔣 : Ideal (𝓞 K)} {y y' : ↥(coprimeToModulus K 𝔣)} :
    NarrowRayClassGroup.mk K 𝔣 y = NarrowRayClassGroup.mk K 𝔣 y' ↔
      ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹ * (y' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
        narrowRaySubgroup K 𝔣 := by
  rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

/--
@isnad1 id=eq.1h3v.s12.167ddfcdeb75 from=translated src=- shape=07532119 vocab=34a4c400
-/
theorem rayClass_mul_self_eq_one {𝔣 : Ideal (𝓞 K)} {g : NarrowRayClassGroup K 𝔣}
    (hg : g ∈ rayClasses K 𝔣) : g * g = 1 := by
  obtain ⟨y, ⟨α, hα0, hα1, hy⟩, rfl⟩ := hg
  rw [← map_mul]
  apply NarrowRayClassGroup.mk_eq_one_of_mem
  apply Subgroup.subset_closure

  have hα' : (algebraMap (𝓞 K) K) α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hα0
  refine ⟨α * α, mul_ne_zero hα0 hα0, ?_, ?_, ?_⟩
  · have : α * α - 1 = (α + 1) * (α - 1) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hα1
  · intro τ
    rw [map_mul, map_mul]
    exact mul_self_pos.mpr ((map_ne_zero τ).mpr hα')
  · rw [Subgroup.coe_mul, Units.val_mul, hy, ← FractionalIdeal.coeIdeal_mul,
      Ideal.span_singleton_mul_span_singleton]

/--
@isnad1 id=mem.7h6v.s13.ecf042585908 from=translated src=- shape=2c1653a4 vocab=48798574
-/
theorem mul_mem_narrowRaySet_of_sameSign {𝔣 : Ideal (𝓞 K)}
    {y y' : ↥(coprimeToModulus K 𝔣)} {α α' : 𝓞 K}
    (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hy : ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hα0' : α' ≠ 0) (hα1' : α' - 1 ∈ 𝔣)
    (hy' : ((y' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α'} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hsgn : ∀ τ : K →+* ℝ,
      (0 < τ (algebraMap (𝓞 K) K α)) ↔ (0 < τ (algebraMap (𝓞 K) K α'))) :
    ((y * y' : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySet K 𝔣 := by
  have hα : (algebraMap (𝓞 K) K) α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hα0
  have hα'' : (algebraMap (𝓞 K) K) α' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hα0'
  refine ⟨α * α', mul_ne_zero hα0 hα0', ?_, ?_, ?_⟩
  · have : α * α' - 1 = α * (α' - 1) + (α - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hα1') hα1
  · intro τ
    rw [map_mul, map_mul]
    rcases lt_or_gt_of_ne ((map_ne_zero τ).mpr hα).symm with hpos | hneg
    · exact mul_pos hpos ((hsgn τ).mp hpos)
    · have hneg' : τ (algebraMap (𝓞 K) K α') < 0 := by
        rcases lt_or_gt_of_ne ((map_ne_zero τ).mpr hα'').symm with hpos' | hneg'
        · exact absurd ((hsgn τ).mpr hpos') (not_lt.mpr hneg.le)
        · exact hneg'
      exact mul_pos_of_neg_of_neg hneg hneg'
  · rw [Subgroup.coe_mul, Units.val_mul, hy, hy', ← FractionalIdeal.coeIdeal_mul,
      Ideal.span_singleton_mul_span_singleton]

/--
@isnad1 id=eq.7h6v.s15.438fb8c9d8f6 from=translated src=- shape=95db17d4 vocab=ac3a7cfe
-/
theorem NarrowRayClassGroup.mk_eq_of_sameSign {𝔣 : Ideal (𝓞 K)}
    {y y' : ↥(coprimeToModulus K 𝔣)} {α α' : 𝓞 K}
    (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hy : ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hα0' : α' ≠ 0) (hα1' : α' - 1 ∈ 𝔣)
    (hy' : ((y' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α'} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hsgn : ∀ τ : K →+* ℝ,
      (0 < τ (algebraMap (𝓞 K) K α)) ↔ (0 < τ (algebraMap (𝓞 K) K α'))) :
    NarrowRayClassGroup.mk K 𝔣 y = NarrowRayClassGroup.mk K 𝔣 y' := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  have h1 : ((y * y' : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hα0 hα1 hy hα0' hα1' hy' hsgn)
  have h2 : ((y * y : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hα0 hα1 hy hα0 hα1 hy
      (fun _ => Iff.rfl))
  rw [Subgroup.coe_mul] at h1 h2
  have e : ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹ * (y' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) =
      (((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) * (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹ *
        (((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) * (y' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) := by
    group
  rw [e]
  exact mul_mem (inv_mem h2) h1

/--
@isnad1 id=finite.0h2v.s5.c7353ec63de9 from=translated src=- shape=4a052fd7 vocab=8104c106
-/
theorem rayClasses_finite (𝔣 : Ideal (𝓞 K)) : (rayClasses K 𝔣).Finite := by
  classical

  refine (Set.finite_range (fun s : (K →+* ℝ) → Bool =>
    if h : ∃ (y : ↥(coprimeToModulus K 𝔣)) (α : 𝓞 K), α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
        ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
          ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ∧
        (fun τ : K →+* ℝ => decide (0 < τ (algebraMap (𝓞 K) K α))) = s
    then NarrowRayClassGroup.mk K 𝔣 (Classical.choose h) else 1)).subset ?_
  rintro _ ⟨y, ⟨α, hα0, hα1, hy⟩, rfl⟩
  refine ⟨fun τ : K →+* ℝ => decide (0 < τ (algebraMap (𝓞 K) K α)), ?_⟩
  have hex : ∃ (y : ↥(coprimeToModulus K 𝔣)) (α' : 𝓞 K), α' ≠ 0 ∧ α' - 1 ∈ 𝔣 ∧
      ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
        ((Ideal.span {α'} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ∧
      (fun τ : K →+* ℝ => decide (0 < τ (algebraMap (𝓞 K) K α'))) =
        (fun τ : K →+* ℝ => decide (0 < τ (algebraMap (𝓞 K) K α))) :=
    ⟨y, α, hα0, hα1, hy, rfl⟩
  simp only [dite_eq_left hex]
  obtain ⟨α₁, hα₁0, hα₁1, hy₁, hs₁⟩ := Classical.choose_spec hex
  apply NarrowRayClassGroup.mk_eq_of_sameSign K hα₁0 hα₁1 hy₁ hα0 hα1 hy
  intro τ
  have h : decide (0 < τ (algebraMap (𝓞 K) K α₁)) = decide (0 < τ (algebraMap (𝓞 K) K α)) :=
    congrFun hs₁ τ
  exact decide_eq_decide.mp h

/--
@isnad1 id=finite.0h2v.s12.9bb1a5375e5c from=translated src=- shape=22d4b0e4 vocab=b079e4f2
-/
theorem finite_rayClassSubgroup (𝔣 : Ideal (𝓞 K)) : Finite (rayClassSubgroup K 𝔣) :=
  finite_closure_of_involutions' (rayClasses_finite K 𝔣)
    (fun _ hg => rayClass_mul_self_eq_one K hg)

def principalUnit (a : 𝓞 K) (ha : a ≠ 0) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  FractionalIdeal.mk0 K ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha)⟩

/--
@isnad1 id=eq.1h2v.s8.111711aa9af9 from=translated src=- shape=d7716bce vocab=69024fa6
-/
theorem principalUnit_val (a : 𝓞 K) (ha : a ≠ 0) :
    ((principalUnit K a ha : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
  FractionalIdeal.coe_mk0 K _

def toClassGroup (𝔣 : Ideal (𝓞 K)) : ↥(coprimeToModulus K 𝔣) →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk (R := 𝓞 K) (K := K)).comp (coprimeToModulus K 𝔣).subtype

/--
@isnad1 id=eq.1h3v.s10.1082bf3c8a4e from=translated src=- shape=5d198e60 vocab=ed1f72df
-/
theorem classGroupMk_eq_one_of_principal {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ} {α : 𝓞 K}
    (hI : (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    ClassGroup.mk (R := 𝓞 K) (K := K) I = 1 := by
  rw [ClassGroup.mk_eq_one_iff, hI, FractionalIdeal.coeIdeal_span_singleton]
  exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨algebraMap (𝓞 K) K α, rfl⟩

/--
@isnad1 id=eq.1h4v.s14.cea2b4f50191 from=translated src=- shape=d51924e2 vocab=d035aec2
-/
theorem toClassGroup_eq_one_of_principal {𝔣 : Ideal (𝓞 K)} {y : ↥(coprimeToModulus K 𝔣)} {α : 𝓞 K}
    (hy : ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    toClassGroup K 𝔣 y = 1 := by
  rw [toClassGroup, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  exact classGroupMk_eq_one_of_principal K hy

/--
@isnad1 id=le.0h2v.s13.5c6327be52de from=translated src=- shape=551f1880 vocab=680be66a
-/
theorem narrowRaySubgroupOf_le_ker (𝔣 : Ideal (𝓞 K)) :
    (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ≤ (toClassGroup K 𝔣).ker := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  rw [MonoidHom.mem_ker]
  have hle : narrowRaySubgroup K 𝔣 ≤
      ((ClassGroup.mk (R := 𝓞 K) (K := K)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ →* ClassGroup (𝓞 K)).ker := by
    rw [narrowRaySubgroup, Subgroup.closure_le]
    rintro I ⟨α, hα0, hα1, -, hI⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact classGroupMk_eq_one_of_principal K hI
  exact MonoidHom.mem_ker.mp (hle hy)

def narrowRayClassGroupToClassGroup (𝔣 : Ideal (𝓞 K)) :
    NarrowRayClassGroup K 𝔣 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (toClassGroup K 𝔣) (narrowRaySubgroupOf_le_ker K 𝔣)

/--
@isnad1 id=eq.0h3v.s15.194b7148ef71 from=translated src=- shape=08cf7892 vocab=5c475783
-/
theorem narrowRayClassGroupToClassGroup_mk (𝔣 : Ideal (𝓞 K)) (y : ↥(coprimeToModulus K 𝔣)) :
    narrowRayClassGroupToClassGroup K 𝔣 (NarrowRayClassGroup.mk K 𝔣 y) = toClassGroup K 𝔣 y := by
  rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply]
  exact QuotientGroup.lift_mk' _ (narrowRaySubgroupOf_le_ker K 𝔣) y

/--
@isnad1 id=le.0h2v.s13.407e4420a008 from=translated src=- shape=e212c2c9 vocab=5f97e631
-/
theorem rayClassSubgroup_le_ker (𝔣 : Ideal (𝓞 K)) :
    rayClassSubgroup K 𝔣 ≤ (narrowRayClassGroupToClassGroup K 𝔣).ker := by
  rw [rayClassSubgroup, Subgroup.closure_le]
  rintro _ ⟨y, ⟨α, hα0, hα1, hy⟩, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, narrowRayClassGroupToClassGroup_mk]
  exact toClassGroup_eq_one_of_principal K hy

def rayClassGroupToClassGroup (𝔣 : Ideal (𝓞 K)) :
    NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (rayClassSubgroup K 𝔣) (narrowRayClassGroupToClassGroup K 𝔣)
    (rayClassSubgroup_le_ker K 𝔣)

/--
@isnad1 id=eq.0h3v.s16.40d55b578889 from=translated src=- shape=589c8802 vocab=0e04d17d
-/
theorem rayClassGroupToClassGroup_mk_mk (𝔣 : Ideal (𝓞 K)) (y : ↥(coprimeToModulus K 𝔣)) :
    rayClassGroupToClassGroup K 𝔣
      (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 y) :
        NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) = toClassGroup K 𝔣 y := by
  show (QuotientGroup.lift (rayClassSubgroup K 𝔣) (narrowRayClassGroupToClassGroup K 𝔣)
      (rayClassSubgroup_le_ker K 𝔣)) (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 y)) = _
  rw [QuotientGroup.lift_mk]
  exact narrowRayClassGroupToClassGroup_mk K 𝔣 y

def MovingLemma (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ x₀ : K, x₀ ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) = 0) →
    ∃ β : 𝓞 K, β ≠ 0 ∧ β - 1 ∈ 𝔣 ∧
      ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K β * x₀

/--
@isnad1 id=le.2h2v.s8.9e78b08542ab from=translated src=- shape=81545cf7 vocab=ebd4086e
-/
theorem le_one_of_forall_count_nonneg {I : FractionalIdeal ((𝓞 K)⁰) K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v I) : I ≤ 1 := by
  classical
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ FractionalIdeal.count K v I).Finite := by
    refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
    intro v hv
    simp only [Function.mem_mulSupport, ne_eq] at hv
    simp only [Set.mem_ofPred_eq]
    intro h0
    exact hv (by rw [h0, zpow_zero])
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset)
    (by rw [Set.Finite.coe_toFinset])]
  apply Finset.prod_induction _ (fun x => x ≤ 1)
  · intro a b ha hb
    calc a * b ≤ a * 1 := by gcongr
      _ = a := mul_one a
      _ ≤ 1 := ha
  · exact le_rfl
  · intro v _
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one

/--
@isnad1 id=movingle.1h2v.s6.46f5b99b503e from=translated src=- shape=7ddc84a8 vocab=4f3c2f34
-/
theorem movingLemma {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) : MovingLemma K 𝔣 := by
  classical
  intro x₀ hx₀ hcop
  by_cases htop : 𝔣 = ⊤
  ·
    obtain ⟨n, s, hs, hns⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x₀
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hs0' : (algebraMap (𝓞 K) K) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
    refine ⟨s, hs0, by rw [htop]; exact Submodule.mem_top, n, ?_⟩
    rw [← hns, mul_div_cancel₀ _ hs0']
  ·
    have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]

    obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ v, v ∈ T ↔ v.asIdeal ∣ 𝔣 :=
      ⟨(Ideal.finite_factors h𝔣0).toFinset, fun v => (Set.Finite.mem_toFinset _).trans Iff.rfl⟩

    have hWfin : {w : HeightOneSpectrum (𝓞 K) |
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) < 0}.Finite := by
      refine (Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀))).subset ?_
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      exact ne_of_lt hw
    obtain ⟨W, hW⟩ : ∃ W : Finset (HeightOneSpectrum (𝓞 K)),
        ∀ w, w ∈ W ↔ FractionalIdeal.count K w (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) < 0 :=
      ⟨hWfin.toFinset, fun w => (Set.Finite.mem_toFinset _).trans Iff.rfl⟩

    obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, ∀ v, e v =
        if v.asIdeal ∣ 𝔣 then (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors
        else (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀))).toNat :=
      ⟨_, fun v => rfl⟩

    obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
      (s := T ∪ W) (fun v => v.asIdeal) e
      (fun v _ => v.prime)
      (fun i _ j _ hij h => hij (by
        cases i; cases j; simpa using h))
      (fun v : ↥(T ∪ W) => if v.1 ∈ T then (1 : 𝓞 K) else 0)

    have hβT : ∀ v ∈ T, β - 1 ∈ v.asIdeal ^ e v := by
      intro v hvT
      have := hβ v (Finset.mem_union_left _ hvT)
      simpa [hvT] using this
    have hinf : (T.inf fun v => v.asIdeal ^ e v) = ∏ v ∈ T, v.asIdeal ^ e v :=
      IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod T e id (fun i _ j _ hij => hij)
    have hprod : ∏ v ∈ T, v.asIdeal ^ e v = 𝔣 := by
      rw [← Ideal.finprod_heightOneSpectrum_factorization h𝔣0,
        finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
      · refine Finset.prod_congr rfl fun v hv => ?_
        rw [he v, ite_eq_left ((hT v).mp hv)]
        rfl
      · intro v hv
        rw [Function.mem_mulSupport] at hv
        rw [Finset.mem_coe, hT]
        by_contra hndvd
        apply hv
        have hcnt : (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors = 0 := by
          by_contra hne
          exact hndvd ((Associates.count_ne_zero_iff_dvd h𝔣0 v.irreducible).mp hne)
        show v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors = 1
        rw [hcnt, pow_zero]
    have hβ1 : β - 1 ∈ 𝔣 := by
      have hle : Ideal.span {β - 1} ≤ T.inf fun v => v.asIdeal ^ e v :=
        Finset.le_inf fun v hv => (Ideal.span_singleton_le_iff_mem _).mpr (hβT v hv)
      have := hle (Ideal.mem_span_singleton_self _)
      rwa [hinf, hprod] at this

    obtain ⟨m, hm, hm𝔣⟩ := Ideal.exists_le_maximal 𝔣 htop
    have hmbot : m ≠ ⊥ := by
      rintro rfl
      exact h𝔣 (le_bot_iff.mp hm𝔣)
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : HeightOneSpectrum (𝓞 K), v₀.asIdeal = m :=
      ⟨⟨m, hm.isPrime, hmbot⟩, rfl⟩
    have hv₀T : v₀ ∈ T := (hT v₀).mpr (by rw [hv₀]; exact Ideal.dvd_iff_le.mpr hm𝔣)
    have hev₀ : e v₀ ≠ 0 := by
      rw [he v₀, ite_eq_left ((hT v₀).mp hv₀T)]
      exact (Associates.count_ne_zero_iff_dvd h𝔣0 v₀.irreducible).mpr ((hT v₀).mp hv₀T)
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have h1 := hβT v₀ hv₀T
      rw [zero_sub] at h1
      have h2 : (-1 : 𝓞 K) ∈ v₀.asIdeal := Ideal.pow_le_self hev₀ h1
      rw [hv₀] at h2
      exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using neg_mem_iff.mp h2))

    have hβ0' : (algebraMap (𝓞 K) K) β ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hβ0
    have hβspan : ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact hβ0
    have hβspan0 : (Ideal.span {β} : Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hβ0
    have hx0' : FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀ ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      exact hx₀
    have hI0 : FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K β * x₀) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      exact mul_ne_zero hβ0' hx₀
    have hsplit : FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K β * x₀) =
        ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) *
          FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀ := by
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    have hnonneg : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K β * x₀)) := by
      intro w
      rw [hsplit, FractionalIdeal.count_mul K w hβspan hx0']
      have hβw : 0 ≤ FractionalIdeal.count K w
          ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
        FractionalIdeal.count_coe_nonneg K w _
      by_cases hwW : w ∈ W
      ·
        have hwlt : FractionalIdeal.count K w (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) < 0 :=
          (hW w).mp hwW
        have hwT : w ∉ T := by
          intro hwT
          have h0 := hcop w ((hT w).mp hwT)
          rw [h0] at hwlt
          exact lt_irrefl _ hwlt
        have hndvd : ¬ w.asIdeal ∣ 𝔣 := by rwa [← hT]
        have hmem := hβ w (Finset.mem_union_right _ hwW)
        simp only [hwT, ite_false, sub_zero] at hmem

        have hew : (e w : ℤ) = -(FractionalIdeal.count K w
            (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀)) := by
          rw [he w, ite_eq_right hndvd, Int.toNat_of_nonneg (by omega)]
        have hdvd : w.asIdeal ^ e w ∣ (Ideal.span {β} : Ideal (𝓞 K)) :=
          (Ideal.dvd_span_singleton).mpr hmem
        have hle : e w ≤ (Associates.mk w.asIdeal).count
            (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors := by
          rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hβspan0)
            w.associates_irreducible, ← Associates.mk_pow]
          exact Associates.mk_dvd_mk.mpr hdvd
        have hcoe : FractionalIdeal.count K w
            ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
              ((Associates.mk w.asIdeal).count
                (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors : ℤ) :=
          FractionalIdeal.count_coe K w hβspan0
        have hle' : (e w : ℤ) ≤ FractionalIdeal.count K w
            ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
          rw [hcoe]
          exact_mod_cast hle
        omega
      ·
        have hwge : 0 ≤ FractionalIdeal.count K w
            (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) := by
          by_contra hlt
          exact hwW ((hW w).mpr (lt_of_not_ge hlt))
        exact add_nonneg hβw hwge

    have hle1 : FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K β * x₀) ≤ 1 :=
      le_one_of_forall_count_nonneg K hI0 hnonneg
    have hmem1 : algebraMap (𝓞 K) K β * x₀ ∈
        (1 : FractionalIdeal ((𝓞 K)⁰) K) :=
      hle1 (FractionalIdeal.mem_spanSingleton_self _ _)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hmem1
    exact ⟨β, hβ0, hβ1, a, ha⟩

/--
@isnad1 id=ex.3h3v.s9.1cce2e7c2c44 from=translated src=- shape=d31d3314 vocab=1efd5f92
-/
theorem exists_mul_sub_one_mem_of_counts_zero {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {a : 𝓞 K}
    (ha : a ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 0) :
    ∃ c : 𝓞 K, a * c - 1 ∈ 𝔣 := by
  classical

  have hsup : (Ideal.span {a} : Ideal (𝓞 K)) ⊔ 𝔣 = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm𝔣 : 𝔣 ≤ m := le_trans le_sup_right hle
    have hma : (Ideal.span {a} : Ideal (𝓞 K)) ≤ m := le_trans le_sup_left hle
    have hmbot : m ≠ ⊥ := by
      rintro rfl
      exact h𝔣 (le_bot_iff.mp hm𝔣)
    set v : HeightOneSpectrum (𝓞 K) := ⟨m, hm.isPrime, hmbot⟩
    have hvdvd : v.asIdeal ∣ 𝔣 := (Ideal.dvd_iff_le.mpr hm𝔣)
    have hva : v.asIdeal ∣ (Ideal.span {a} : Ideal (𝓞 K)) := (Ideal.dvd_iff_le.mpr hma)
    have hJ0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    have hcnt := hcop v hvdvd
    rw [FractionalIdeal.count_coe K v hJ0] at hcnt
    have hz : (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {a} : Ideal (𝓞 K))).factors = 0 := by
      exact_mod_cast hcnt
    exact ((Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mpr hva) hz

  have h1 : (1 : 𝓞 K) ∈ (Ideal.span {a} : Ideal (𝓞 K)) ⊔ 𝔣 := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨t, ht, f, hf, htf⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  refine ⟨c, ?_⟩
  have : a * c - 1 = -f := by rw [mul_comm]; linear_combination htf
  rw [this]
  exact neg_mem_iff.mpr hf

/--
@isnad1 id=mem.2h3v.s10.698628ed113f from=translated src=- shape=074380ac vocab=4bead932
-/
theorem principalUnit_mem_coprimeToModulus {𝔣 : Ideal (𝓞 K)} {β : 𝓞 K} (hβ0 : β ≠ 0)
    (hβ1 : β - 1 ∈ 𝔣) : principalUnit K β hβ0 ∈ coprimeToModulus K 𝔣 := by
  rw [mem_coprimeToModulus_iff]
  intro v hv
  rw [principalUnit_val]
  exact count_span_singleton_eq_zero_of_sub_one_mem K hβ0 hβ1 hv

/--
@isnad1 id=eq.1h3v.s15.66e2e1fbb2e7 from=translated src=- shape=196fcb64 vocab=95e7dca0
-/
theorem mk_mk_eq_one_of_raySet {𝔣 : Ideal (𝓞 K)} {z : ↥(coprimeToModulus K 𝔣)}
    (hz : (z : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ raySet K 𝔣) :
    (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 z) :
      NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.subset_closure ⟨z, hz, rfl⟩

private theorem exists_integral_ray_rep {𝔣 : Ideal (𝓞 K)} (hmove : MovingLemma K 𝔣)
    (y : ↥(coprimeToModulus K 𝔣)) (hprinc : toClassGroup K 𝔣 y = 1) :
    ∃ (a : 𝓞 K), a ≠ 0 ∧ ∃ (ya : ↥(coprimeToModulus K 𝔣)),
      ((ya : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
        ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ∧
      (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 ya) :
        NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) =
      QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 y) := by

  have hprinc' : ClassGroup.mk (R := 𝓞 K) (K := K)
      (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = 1 := hprinc
  rw [ClassGroup.mk_eq_one_iff] at hprinc'
  obtain ⟨x₀, hx₀⟩ := (FractionalIdeal.isPrincipal_iff _).mp hprinc'
  have hy0 : ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) ≠ 0 :=
    Units.ne_zero _
  have hx0 : x₀ ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.spanSingleton_zero] at hx₀
    exact hy0 hx₀

  have hcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) = 0 := by
    intro v hv
    rw [← hx₀]
    exact (mem_coprimeToModulus_iff K).mp y.2 v hv
  obtain ⟨β, hβ0, hβ1, a, ha⟩ := hmove x₀ hx0 hcop
  have hβ' : (algebraMap (𝓞 K) K) β ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hβ0
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact mul_ne_zero hβ' hx0 ha.symm

  refine ⟨a, ha0, ⟨principalUnit K β hβ0 * (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ),
    mul_mem (principalUnit_mem_coprimeToModulus K hβ0 hβ1) y.2⟩, ?_, ?_⟩
  · rw [Units.val_mul, principalUnit_val, hx₀, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, ha]
  · have hsplit : (⟨principalUnit K β hβ0 * (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ),
        mul_mem (principalUnit_mem_coprimeToModulus K hβ0 hβ1) y.2⟩ :
          ↥(coprimeToModulus K 𝔣)) =
        ⟨principalUnit K β hβ0, principalUnit_mem_coprimeToModulus K hβ0 hβ1⟩ * y := rfl
    rw [hsplit, map_mul, QuotientGroup.mk_mul,
      mk_mk_eq_one_of_raySet K ⟨β, hβ0, hβ1, principalUnit_val K β hβ0⟩, one_mul]

/--
@isnad1 id=eq.7h6v.s15.103a403eff75 from=translated src=- shape=73828371 vocab=50c6810d
-/
theorem mk_mk_eq_of_residue_eq {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (htop : 𝔣 ≠ ⊤)
    {a a' : 𝓞 K} (ha : a ≠ 0) (ha' : a' ≠ 0) (ya ya' : ↥(coprimeToModulus K 𝔣))
    (hya : ((ya : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hya' : ((ya' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {a'} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K))
    (hres : Ideal.Quotient.mk 𝔣 a = Ideal.Quotient.mk 𝔣 a') :
    (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 ya) :
      NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) =
      QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 ya') := by
  classical

  have hcopa : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v ((Ideal.span {a} : Ideal (𝓞 K)) :
        FractionalIdeal ((𝓞 K)⁰) K) = 0 := by
    intro v hv
    rw [← hya]
    exact (mem_coprimeToModulus_iff K).mp ya.2 v hv
  obtain ⟨c, hac⟩ := exists_mul_sub_one_mem_of_counts_zero K h𝔣 ha hcopa
  have ha'a : a' - a ∈ 𝔣 := by
    have := (Ideal.Quotient.eq (I := 𝔣)).mp hres
    have h' : a' - a = -(a - a') := by ring
    rw [h']
    exact neg_mem_iff.mpr this
  have ha'c : a' * c - 1 ∈ 𝔣 := by
    have : a' * c - 1 = (a' - a) * c + (a * c - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha'a) hac
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_sub] at hac
    exact htop ((Ideal.eq_top_iff_one _).mpr (by simpa using neg_mem_iff.mp hac))

  have hac0 : a * c ≠ 0 := mul_ne_zero ha hc0
  have hcopc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v ((Ideal.span {c} : Ideal (𝓞 K)) :
        FractionalIdeal ((𝓞 K)⁰) K) = 0 := by
    intro v hv
    have hprod : FractionalIdeal.count K v
        ((Ideal.span {a * c} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 0 :=
      count_span_singleton_eq_zero_of_sub_one_mem K hac0 hac hv
    have hA : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact ha
    have hC : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact hc0
    rw [← Ideal.span_singleton_mul_span_singleton, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K v hA hC, hcopa v hv, zero_add] at hprod
    exact hprod

  set yc : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K c hc0, (mem_coprimeToModulus_iff K).mpr (fun v hv => by
      rw [principalUnit_val]; exact hcopc v hv)⟩ with hyc
  have hvc : ((yc : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
    rw [hyc]; exact principalUnit_val K c hc0
  have h1 : (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 (ya * yc)) :
      NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) = 1 := by
    apply mk_mk_eq_one_of_raySet
    refine ⟨a * c, hac0, hac, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hya, hvc, ← FractionalIdeal.coeIdeal_mul,
      Ideal.span_singleton_mul_span_singleton]
  have h2 : (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 (ya' * yc)) :
      NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) = 1 := by
    apply mk_mk_eq_one_of_raySet
    refine ⟨a' * c, mul_ne_zero ha' hc0, ha'c, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hya', hvc, ← FractionalIdeal.coeIdeal_mul,
      Ideal.span_singleton_mul_span_singleton]
  rw [map_mul, QuotientGroup.mk_mul] at h1 h2
  exact mul_right_cancel (h1.trans h2.symm)

private theorem finite_ker_rayClassGroupToClassGroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmove : MovingLemma K 𝔣) : Finite ((rayClassGroupToClassGroup K 𝔣).ker) := by
  classical
  haveI : Finite (𝓞 K ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣

  apply Set.Finite.to_subtype
  refine ((Set.finite_range (fun q : 𝓞 K ⧸ 𝔣 =>
    if h : ∃ (a : 𝓞 K) (ya : ↥(coprimeToModulus K 𝔣)), a ≠ 0 ∧
        ((ya : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
          ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ∧
        Ideal.Quotient.mk 𝔣 a = q
    then (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 (Classical.choose (Classical.choose_spec h))) :
      NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣)
    else 1)).union (Set.finite_singleton 1)).subset ?_
  intro x hx
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x'
  replace hx : rayClassGroupToClassGroup K 𝔣
      (QuotientGroup.mk (NarrowRayClassGroup.mk K 𝔣 y)) = 1 := hx

  have hprinc : toClassGroup K 𝔣 y = 1 := by
    rw [← rayClassGroupToClassGroup_mk_mk]
    exact hx
  obtain ⟨a, ha, ya, hya, hcls⟩ := exists_integral_ray_rep K hmove y hprinc
  by_cases htop : 𝔣 = ⊤
  ·
    right
    rw [Set.mem_singleton_iff]
    exact hcls.symm.trans
      (mk_mk_eq_one_of_raySet K ⟨a, ha, by rw [htop]; exact Submodule.mem_top, hya⟩)
  · left
    refine ⟨Ideal.Quotient.mk 𝔣 a, ?_⟩
    have hdite : ∃ (a' : 𝓞 K) (ya' : ↥(coprimeToModulus K 𝔣)), a' ≠ 0 ∧
        ((ya' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
          ((Ideal.span {a'} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ∧
        Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a :=
      ⟨a, ya, ha, hya, rfl⟩
    simp only [dite_eq_left hdite]
    obtain ⟨ha₁, hya₁, hres₁⟩ := Classical.choose_spec (Classical.choose_spec hdite)
    exact (mk_mk_eq_of_residue_eq K h𝔣 htop ha₁ ha
      (Classical.choose (Classical.choose_spec hdite)) ya hya₁ hya hres₁).trans hcls

private theorem finite_rayClassQuotient_of_movingLemma {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmove : MovingLemma K 𝔣) :
    Finite (NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) := by
  have h1 : Finite ((rayClassGroupToClassGroup K 𝔣).ker) :=
    finite_ker_rayClassGroupToClassGroup K h𝔣 hmove
  have h2 : Finite ((NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣) ⧸
      (rayClassGroupToClassGroup K 𝔣).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (rayClassGroupToClassGroup K 𝔣)).symm.toEquiv
  exact (finite_iff_subgroup_quotient (rayClassGroupToClassGroup K 𝔣).ker).mpr ⟨h1, h2⟩

private theorem finite_of_movingLemma {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmove : MovingLemma K 𝔣) : Finite (NarrowRayClassGroup K 𝔣) :=
  (finite_iff_subgroup_quotient (rayClassSubgroup K 𝔣)).mpr
    ⟨finite_rayClassSubgroup K 𝔣, finite_rayClassQuotient_of_movingLemma K h𝔣 hmove⟩

/--
@isnad1 id=finite.1h2v.s6.10409446a31c from=translated src=- shape=8e54e7b8 vocab=78f22bc6
-/
theorem finite {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) : Finite (NarrowRayClassGroup K 𝔣) :=
  finite_of_movingLemma K h𝔣 (movingLemma K h𝔣)

end Finiteness

section Packaging

variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]

def primeUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero (by
    rw [Ne, Submodule.zero_eq_bot]
    exact v.ne_bot)⟩

/--
@isnad1 id=eq.0h2v.s7.9d5d14680d7f from=translated src=- shape=966e9573 vocab=1bc71264
-/
theorem primeUnit_val (v : HeightOneSpectrum (𝓞 K)) :
    ((primeUnit K v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) :=
  FractionalIdeal.coe_mk0 K _

/--
@isnad1 id=mem.1h3v.s10.7d833aa69563 from=translated src=- shape=8f934bc2 vocab=0500e473
-/
theorem primeUnit_mem_coprimeToModulus {𝔣 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔣) : primeUnit K v ∈ coprimeToModulus K 𝔣 := by
  rw [mem_coprimeToModulus_iff]
  intro w hw
  rw [primeUnit_val]
  exact FractionalIdeal.count_maximal_coprime K w (fun h => hv (h ▸ hw))

def primeClass (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    NarrowRayClassGroup K 𝔣 :=
  NarrowRayClassGroup.mk K 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩

/--
@isnad1 id=eq.0h4v.s7.580365c37638 from=translated src=- shape=7b1bca64 vocab=984fa9d8
-/
theorem raySymbol_primeUnit (f : HeightOneSpectrum (𝓞 K) → M) (v : HeightOneSpectrum (𝓞 K)) :
    raySymbol K f ((primeUnit K v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
      FractionalIdeal ((𝓞 K)⁰) K) = f v := by
  rw [primeUnit_val, raySymbol, finprod_eq_single _ v]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro w hw
    rw [FractionalIdeal.count_maximal_coprime K w (Ne.symm hw), zpow_zero]

/--
@isnad1 id=eq.1h5v.s14.0308f4549898 from=translated src=- shape=c0817f7b vocab=937862ef
-/
theorem raySymbolHom_prime (𝔣 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → M)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    raySymbolHom K 𝔣 f ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ = f v := by
  rw [raySymbolHom_apply]
  exact raySymbol_primeUnit K f v

/--
@isnad1 id=le.1h4v.s13.9de1d7c23ba2 from=translated src=- shape=2277c3af vocab=4666045f
-/
theorem narrowRaySubgroupOf_le_ker_raySymbolHom {𝔣 : Ideal (𝓞 K)}
    (f : HeightOneSpectrum (𝓞 K) → M)
    (hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K f ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1) :
    (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ≤ (raySymbolHom K 𝔣 f).ker := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  rw [MonoidHom.mem_ker, raySymbolHom_apply]
  have hle : narrowRaySubgroup K 𝔣 ≤ (raySymbolUnitsHom K f).ker := by
    rw [narrowRaySubgroup, Subgroup.closure_le]
    rintro I ⟨α, hα0, hα1, hpos, hI⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K) = 1
    rw [hI]
    exact hkill α hα0 hα1 hpos
  exact MonoidHom.mem_ker.mp (hle hy)

def raySymbolDescend {𝔣 : Ideal (𝓞 K)} (f : HeightOneSpectrum (𝓞 K) → M)
    (hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K f ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1) :
    NarrowRayClassGroup K 𝔣 →* M :=
  QuotientGroup.lift ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (raySymbolHom K 𝔣 f) (narrowRaySubgroupOf_le_ker_raySymbolHom K f hkill)

/--
@isnad1 id=eq.1h5v.s15.9c155a8f17dc from=translated src=- shape=87ce88fb vocab=aec0ef02
-/
theorem raySymbolDescend_mk {𝔣 : Ideal (𝓞 K)} (f : HeightOneSpectrum (𝓞 K) → M)
    (hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K f ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1)
    (y : ↥(coprimeToModulus K 𝔣)) :
    raySymbolDescend K f hkill (NarrowRayClassGroup.mk K 𝔣 y) = raySymbolHom K 𝔣 f y := by
  rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply]
  exact QuotientGroup.lift_mk' _ (narrowRaySubgroupOf_le_ker_raySymbolHom K f hkill) y

/--
@isnad1 id=eq.2h5v.s12.6ebe99f899b8 from=translated src=- shape=d450f902 vocab=95b60c9c
-/
theorem raySymbolDescend_primeClass {𝔣 : Ideal (𝓞 K)} (f : HeightOneSpectrum (𝓞 K) → M)
    (hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K f ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    raySymbolDescend K f hkill (primeClass K 𝔣 v hv) = f v := by
  rw [primeClass, raySymbolDescend_mk]
  exact raySymbolHom_prime K 𝔣 f hv

def raySymbolIdealHom (f : HeightOneSpectrum (𝓞 K) → M) : ↥(Ideal (𝓞 K))⁰ →* M :=
  (raySymbolUnitsHom K f).comp (FractionalIdeal.mk0 K)

/--
@isnad1 id=eq.0h4v.s12.cbddb8c394f2 from=translated src=- shape=0562bc3d vocab=8ed96a23
-/
theorem raySymbolIdealHom_apply (f : HeightOneSpectrum (𝓞 K) → M) (I : ↥(Ideal (𝓞 K))⁰) :
    raySymbolIdealHom K f I =
      raySymbol K f ((I : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  rw [raySymbolIdealHom, MonoidHom.comp_apply]
  show raySymbol K f ((FractionalIdeal.mk0 K I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
    FractionalIdeal ((𝓞 K)⁰) K) = _
  rw [FractionalIdeal.coe_mk0]

end Packaging

section Degenerate

variable (K : Type*) [Field K] [NumberField K]

/--
@isnad1 id=eq.0h1v.s9.013021eced52 from=translated src=- shape=db310d50 vocab=4566f5a8
-/
theorem coprimeToModulus_top : coprimeToModulus K (⊤ : Ideal (𝓞 K)) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [mem_coprimeToModulus_iff]
  intro v hv
  exact absurd (top_le_iff.mp (Ideal.dvd_iff_le.mp hv)) v.isPrime.ne_top

end Degenerate

end Deep.NTSupply
