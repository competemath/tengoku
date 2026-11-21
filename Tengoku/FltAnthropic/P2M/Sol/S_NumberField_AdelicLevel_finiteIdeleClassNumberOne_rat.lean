import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.RingTheory.DedekindDomain.SelmerGroup
import Tengoku.Seed.NumberTheory.NumberField.ClassNumber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms M4aP1R.GL2StrongApprox.finiteIdeleClassNumberOne_rat_impl` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat

set_option autoImplicit false

namespace M4aP1R

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open scoped nonZeroDivisors

namespace ClassFieldAxiom

section Carrier

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

abbrev IdeleGroup := (AdeleRing R K)ˣ

noncomputable def principalIdeles : Subgroup (IdeleGroup R K) :=
  (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K)).range

end Carrier

end ClassFieldAxiom

namespace ClassFieldAxiom

noncomputable section

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

section ComponentExponent

def adeleEvalAt (v : HeightOneSpectrum R) : AdeleRing R K →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

def ideleEvalAt (v : HeightOneSpectrum R) : IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  Units.map (adeleEvalAt R K v).toMonoidHom

/--
@isnad1 id=eq.0h4v.s9.57f81436a8d5 from=translated src=- shape=2efadfe2 vocab=a02f52f5
-/
@[scoped simp] lemma ideleEvalAt_val (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (ideleEvalAt R K v x : v.adicCompletion K) = (x : AdeleRing R K).2 v := rfl

/--
@isnad1 id=ne.0h4v.s9.2d0a0fb99a1f from=translated src=- shape=ff6f452d vocab=adf6df25
-/
lemma valued_ideleEvalAt_ne_zero (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (Valued.v ((ideleEvalAt R K v x : v.adicCompletion K))) ≠ 0 := by
  simp only [ne_eq, map_eq_zero]
  exact (ideleEvalAt R K v x).ne_zero

def ideleExponentAt (v : HeightOneSpectrum R) (x : IdeleGroup R K) : ℤ :=
  -log (Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)))

/--
@isnad1 id=eq.0h3v.s6.09893566f27b from=translated src=- shape=710d4b92 vocab=26baa381
-/
@[scoped simp] lemma ideleExponentAt_one (v : HeightOneSpectrum R) :
    ideleExponentAt R K v 1 = 0 := by
  simp [ideleExponentAt]

/--
@isnad1 id=eq.0h5v.s7.93e82d8e8878 from=translated src=- shape=2c6e19a9 vocab=388336a6
-/
lemma ideleExponentAt_mul (v : HeightOneSpectrum R) (x y : IdeleGroup R K) :
    ideleExponentAt R K v (x * y) = ideleExponentAt R K v x + ideleExponentAt R K v y := by
  simp only [ideleExponentAt, map_mul, Units.val_mul]
  rw [log_mul (valued_ideleEvalAt_ne_zero R K v x) (valued_ideleEvalAt_ne_zero R K v y)]
  ring

/--
@isnad1 id=eq.0h4v.s7.b6d677a45b27 from=translated src=- shape=7540b0e7 vocab=affe442c
-/
lemma ideleExponentAt_inv (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    ideleExponentAt R K v x⁻¹ = -ideleExponentAt R K v x := by
  have h := ideleExponentAt_mul R K v x x⁻¹
  rw [mul_inv_cancel, ideleExponentAt_one] at h
  omega

/--
@isnad1 id=iff.0h4v.s9.2be1a8f3b45b from=translated src=- shape=b7a634fa vocab=be596d44
-/
lemma ideleExponentAt_eq_zero_iff (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    ideleExponentAt R K v x = 0 ↔
      Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)) = 1 := by
  rw [ideleExponentAt, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (valued_ideleEvalAt_ne_zero R K v x)
    rw [← h2, h, exp_zero]
  · intro h
    rw [h, log_one]

end ComponentExponent

section FiniteSupport

private lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1)
    (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

/--
@isnad1 id=eq.2h4v.s9.49e3a29995fb from=translated src=- shape=381e9757 vocab=928f36c4
-/
theorem ideleExponentAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : IdeleGroup R K}
    (hx : Valued.v ((x : AdeleRing R K).2 v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 v) ≤ 1) :
    ideleExponentAt R K v x = 0 := by
  rw [ideleExponentAt_eq_zero_iff]
  have hmul : Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)) *
      Valued.v ((ideleEvalAt R K v x⁻¹ : v.adicCompletion K)) = 1 := by
    have h1 : ((ideleEvalAt R K v x : v.adicCompletion K)) *
        ((ideleEvalAt R K v x⁻¹ : v.adicCompletion K)) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h2 := congrArg Valued.v h1
    rwa [Valuation.map_mul, Valuation.map_one] at h2
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

/--
@isnad1 id=finite.0h3v.s6.34bc0f5044ad from=translated src=- shape=7554f6f8 vocab=96aff3a8
-/
theorem finite_mulSupport_ideleExponentAt (x : IdeleGroup R K) :
    {v : HeightOneSpectrum R | ideleExponentAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite,
      ((x : AdeleRing R K).2 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x : AdeleRing R K).2 : FiniteAdeleRing R K).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 : FiniteAdeleRing R K) v ∈
        v.adicCompletionIntegers K :=
    (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 : FiniteAdeleRing R K).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  intro hcon
  exact hv (ideleExponentAt_eq_zero_of_integral R K
    ((mem_adicCompletionIntegers R K v).mp hcon.1)
    ((mem_adicCompletionIntegers R K v).mp hcon.2))

end FiniteSupport

section AssociatedIdeal

omit [IsDedekindDomain R] in

/--
@isnad1 id=ne.0h3v.s7.91876d4f14b8 from=translated src=- shape=7a4f3ed4 vocab=1de97356
-/
lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) :
    (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

/--
@isnad1 id=ne.0h4v.s8.0c4dc98a5a29 from=translated src=- shape=15df2819 vocab=57deea1a
-/
lemma zpow_asIdeal_ne_zero (v : HeightOneSpectrum R) (n : ℤ) :
    (v.asIdeal : FractionalIdeal R⁰ K) ^ n ≠ 0 :=
  zpow_ne_zero n (coeIdeal_asIdeal_ne_zero R K v)

/--
@isnad1 id=le.0h3v.s8.7214921c568a from=translated src=- shape=78f4f7b3 vocab=c86bb5d9
-/
lemma mulSupport_zpow_subset (e : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ (e v)) ⊆
      {v | e v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  intro h0
  exact hv (by rw [h0, zpow_zero])

def associatedFractionalIdeal (x : IdeleGroup R K) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (ideleExponentAt R K v x)

/--
@isnad1 id=ne.0h3v.s7.8a9e3e5dbfeb from=translated src=- shape=3738b5ee vocab=c701f4d3
-/
lemma associatedFractionalIdeal_ne_zero (x : IdeleGroup R K) :
    associatedFractionalIdeal R K x ≠ 0 := by
  rw [associatedFractionalIdeal, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_mulSupport_ideleExponentAt R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_asIdeal_ne_zero R K v _

/--
@isnad1 id=eq.0h4v.s6.62b0cbe496b7 from=translated src=- shape=07fdd696 vocab=3d4c1bce
-/
theorem count_associatedFractionalIdeal (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    FractionalIdeal.count K v (associatedFractionalIdeal R K x) = ideleExponentAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_mulSupport_ideleExponentAt R K x))

/--
@isnad1 id=eq.0h4v.s8.cf66dcd73876 from=translated src=- shape=2f92da08 vocab=61e3d026
-/
theorem associatedFractionalIdeal_mul (x y : IdeleGroup R K) :
    associatedFractionalIdeal R K (x * y) =
      associatedFractionalIdeal R K x * associatedFractionalIdeal R K y := by
  unfold associatedFractionalIdeal
  rw [← finprod_mul_distrib
    ((finite_mulSupport_ideleExponentAt R K x).subset (mulSupport_zpow_subset R K _))
    ((finite_mulSupport_ideleExponentAt R K y).subset (mulSupport_zpow_subset R K _))]
  apply finprod_congr
  intro v
  rw [ideleExponentAt_mul, zpow_add₀ (coeIdeal_asIdeal_ne_zero R K v)]

end AssociatedIdeal

section ContentHom

def contentHom : IdeleGroup R K →* ClassGroup R where
  toFun x := ClassGroup.mk K (Units.mk0 (associatedFractionalIdeal R K x)
    (associatedFractionalIdeal_ne_zero R K x))
  map_one' := by
    have h1 : associatedFractionalIdeal R K (1 : IdeleGroup R K) = 1 := by
      unfold associatedFractionalIdeal
      rw [finprod_eq_one_of_forall_eq_one]
      intro v
      rw [ideleExponentAt_one, zpow_zero]
    rw [← map_one (ClassGroup.mk (R := R) K)]
    congr 1
    exact Units.ext (by simpa using h1)
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using associatedFractionalIdeal_mul R K x y)

/--
@isnad1 id=eq.0h3v.s9.2242a6928386 from=translated src=- shape=aa386e29 vocab=587f94e5
-/
@[scoped simp] lemma contentHom_apply (x : IdeleGroup R K) :
    contentHom R K x = ClassGroup.mk K (Units.mk0 (associatedFractionalIdeal R K x)
      (associatedFractionalIdeal_ne_zero R K x)) := rfl

/--
@isnad1 id=eq.0h4v.s7.7d80561d5ecc from=translated src=- shape=d18e8f6d vocab=ce6fbd6c
-/
theorem count_spanSingleton_eq_neg_log_valuation (v : HeightOneSpectrum R) (u : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (u : K)) =
      -log (v.valuation K (u : K)) := by
  classical

  rw [← valuationOfNeZeroToFun_eq v u]

  set n : R := (IsLocalization.sec R⁰ (u : K)).1 with hn
  set d : ↥R⁰ := (IsLocalization.sec R⁰ (u : K)).2 with hd
  have hsec : (u : K) * algebraMap R K (d : R) = algebraMap R K n :=
    IsLocalization.sec_spec R⁰ (u : K)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2

  have h_aJ : FractionalIdeal.spanSingleton R⁰ (u : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (d : R)))⁻¹ * ↑(Ideal.span {n}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp
    linear_combination hsec
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero) h_aJ]

  show _ = -log ((valuationOfNeZeroToFun v u : Multiplicative ℤ) : ℤᵐ⁰)
  rw [valuationOfNeZeroToFun]
  simp only [← hn, ← hd]
  rw [show ((Multiplicative.ofAdd _ : Multiplicative ℤ) : ℤᵐ⁰) = exp _ from rfl, log_exp]
  ring

/--
@isnad1 id=eq.0h4v.s9.0e4728560e46 from=translated src=- shape=3590b480 vocab=c887cf94
-/
theorem ideleExponentAt_principal (v : HeightOneSpectrum R) (u : Kˣ) :
    ideleExponentAt R K v
      (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u) =
      -log (v.valuation K (u : K)) := by
  unfold ideleExponentAt
  congr 1
  show log (Valued.v ((algebraMap K (AdeleRing R K) (u : K)).2 v)) = _
  rw [AdeleRing.algebraMap_snd_apply, valuedAdicCompletion_eq_valuation']

end ContentHom

section KernelClause

def unramifiedIdeles : Subgroup (IdeleGroup R K) where
  carrier := {x | ∀ v : HeightOneSpectrum R, ideleExponentAt R K v x = 0}
  one_mem' v := ideleExponentAt_one R K v
  mul_mem' hx hy v := by rw [ideleExponentAt_mul, hx v, hy v, add_zero]
  inv_mem' hx v := by rw [ideleExponentAt_inv, hx v, neg_zero]

/--
@isnad1 id=iff.0h3v.s8.0ad1ddd30dde from=translated src=- shape=bf0bee93 vocab=0d06687f
-/
@[scoped simp] lemma mem_unramifiedIdeles_iff (x : IdeleGroup R K) :
    x ∈ unramifiedIdeles R K ↔ ∀ v : HeightOneSpectrum R, ideleExponentAt R K v x = 0 :=
  Iff.rfl

def unramifiedIdelesOutside (T : Set (HeightOneSpectrum R)) : Subgroup (IdeleGroup R K) where
  carrier := {x | ∀ v : HeightOneSpectrum R, v ∉ T → ideleExponentAt R K v x = 0}
  one_mem' v _ := ideleExponentAt_one R K v
  mul_mem' hx hy v hv := by rw [ideleExponentAt_mul, hx v hv, hy v hv, add_zero]
  inv_mem' hx v hv := by rw [ideleExponentAt_inv, hx v hv, neg_zero]

/--
@isnad1 id=le.0h2v.s9.616979d3196a from=translated src=- shape=44ca00f9 vocab=df1f31b8
-/
theorem ker_le_unramifiedIdeles_sup_principal :
    MonoidHom.ker (contentHom R K) ≤ unramifiedIdeles R K ⊔ principalIdeles R K := by
  intro x hx
  rw [MonoidHom.mem_ker, contentHom_apply, ClassGroup.mk_eq_one_iff] at hx

  obtain ⟨a, ha⟩ := hx.principal
  have ha' : associatedFractionalIdeal R K x = FractionalIdeal.spanSingleton R⁰ a := by
    apply FractionalIdeal.coeToSubmodule_injective
    show (associatedFractionalIdeal R K x : Submodule R K) =
      (FractionalIdeal.spanSingleton R⁰ a : Submodule R K)
    rw [FractionalIdeal.coe_spanSingleton]
    simpa using ha
  have ha0 : a ≠ 0 := by
    intro h0
    apply associatedFractionalIdeal_ne_zero R K x
    rw [ha', h0, FractionalIdeal.spanSingleton_zero]
  set u : Kˣ := Units.mk0 a ha0 with hu
  set p : IdeleGroup R K :=
    Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u with hp

  have hquot : x * p⁻¹ ∈ unramifiedIdeles R K := by
    intro v
    rw [ideleExponentAt_mul, ideleExponentAt_inv]
    have h1 : ideleExponentAt R K v x =
        FractionalIdeal.count K v (associatedFractionalIdeal R K x) :=
      (count_associatedFractionalIdeal R K v x).symm
    have h2 : ideleExponentAt R K v p = FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
      rw [hp, ideleExponentAt_principal, count_spanSingleton_eq_neg_log_valuation]
    rw [h1, h2, ha']
    simp [hu]

  have hxp : x = (x * p⁻¹) * p := by group
  rw [hxp]
  exact Subgroup.mul_mem_sup hquot ⟨u, rfl⟩

end KernelClause

section SurjectivityClause

variable [DecidableEq (HeightOneSpectrum R)]

def finiteAdeleInr : FiniteAdeleRing R K →* AdeleRing R K where
  toFun b := ((1, b) : InfiniteAdeleRing K × FiniteAdeleRing R K)
  map_one' := rfl
  map_mul' b b' := by
    show ((1, b * b') : InfiniteAdeleRing K × FiniteAdeleRing R K) = (1 * 1, b * b')
    rw [one_mul]

end SurjectivityClause

end

end ClassFieldAxiom
open scoped _root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom

namespace GL2StrongApprox

open Matrix ClassFieldAxiom M4aP1R.ClassFieldAxiom

noncomputable section

/--
@isnad1 id=subsingl.0h0v.s3.7aab95c73678 from=translated src=- shape=ed5d6145 vocab=bc5855a6
-/
theorem subsingleton_classGroup_ringOfIntegers_rat : Subsingleton (ClassGroup (𝓞 ℚ)) :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)

/--
@isnad1 id=mem.1h2v.s9.397ca2823c8a from=translated src=- shape=1bb0fed4 vocab=cf8618ab
-/
theorem snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles
    {j : IdeleGroup (𝓞 ℚ) ℚ} (hj : j ∈ unramifiedIdeles (𝓞 ℚ) ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈ v.adicCompletionIntegers ℚ := by
  have h0 := (mem_unramifiedIdeles_iff (𝓞 ℚ) ℚ j).mp hj v
  have h1 := (ideleExponentAt_eq_zero_iff (𝓞 ℚ) ℚ v j).mp h0
  rw [ideleEvalAt_val] at h1
  exact (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr h1.le

/--
@isnad1 id=ex.0h1v.s10.bc17992b6ecf from=translated src=- shape=1c2401d2 vocab=d940ffac
-/
theorem exists_unramified_mul_principal_finiteIdele_rat
    (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ j ∈ unramifiedIdeles (𝓞 ℚ) ℚ, ∃ q : ℚˣ,
      (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
          = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ)
        ∧ ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
          = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by
  classical

  set x : IdeleGroup (𝓞 ℚ) ℚ := Units.map (finiteAdeleInr (𝓞 ℚ) ℚ) δ with hxdef

  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := subsingleton_classGroup_ringOfIntegers_rat
  have hker : x ∈ MonoidHom.ker (contentHom (𝓞 ℚ) ℚ) := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _

  have hsup : x ∈ unramifiedIdeles (𝓞 ℚ) ℚ ⊔ principalIdeles (𝓞 ℚ) ℚ :=
    ker_le_unramifiedIdeles_sup_principal (𝓞 ℚ) ℚ hker
  obtain ⟨j, hj, p, hp, hjp⟩ := Subgroup.mem_sup.mp hsup
  obtain ⟨q, hq⟩ := hp
  refine ⟨j, hj, q, ?_, ?_⟩
  ·
    have h1 : ((x : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = (δ : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hxdef]; rfl
    have h4 : ((p : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ) := by
      rw [← hq]; rfl
    calc (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((x : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := h1.symm
      _ = (((j * p : IdeleGroup (𝓞 ℚ) ℚ) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := by
          rw [hjp]
      _ = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * ((p : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := rfl
      _ = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ) := by rw [h4]
  ·
    have hjp' : j⁻¹ * p⁻¹ = x⁻¹ := by
      rw [← hjp, _root_.mul_inv_rev]
      exact mul_comm _ _
    have hq' : Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q⁻¹
        = p⁻¹ := by
      rw [map_inv, hq]
    have h1 : ((x⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hxdef]; rfl
    have h4 : ((p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by
      rw [← hq']; rfl
    calc ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((x⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := h1.symm
      _ = (((j⁻¹ * p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := by
          rw [hjp']
      _ = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * ((p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := rfl
      _ = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by rw [h4]

/--
@isnad1 id=ex.0h1v.s10.8db05822766b from=translated src=- shape=f2bf237b vocab=f3917d1f
-/
theorem finiteIdeleClassNumberOne_rat_impl (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ α : ℚˣ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((α⁻¹ : ℚˣ) : ℚ)
          * (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)) v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((α : ℚˣ) : ℚ)
          * ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) := by
  obtain ⟨j, hj, q, hdec, hdecinv⟩ := exists_unramified_mul_principal_finiteIdele_rat δ
  refine ⟨q, fun v => ?_, fun v => ?_⟩
  ·
    have hkey : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ)
        * (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hdec, mul_left_comm, ← map_mul, Units.inv_mul, map_one, mul_one]
    rw [hkey]
    exact snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles hj v
  ·
    have hkey : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ)
        * ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hdecinv, mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
    rw [hkey]
    exact snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles
      ((unramifiedIdeles (𝓞 ℚ) ℚ).inv_mem hj) v

end
open scoped _root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom

end GL2StrongApprox
open scoped _root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom

end M4aP1R
open scoped _root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom _root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R

/--
@isnad1 id=ex.0h1v.s10.8db05822766b from=translated src=- shape=f2bf237b vocab=f3917d1f
-/
theorem solution
    (δ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
    ∃ α : ℚˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α⁻¹ : ℚˣ) : ℚ)
            * (δ : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α : ℚˣ) : ℚ)
            * ((δ⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) := by
  exact M4aP1R.GL2StrongApprox.finiteIdeleClassNumberOne_rat_impl δ
