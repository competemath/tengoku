import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.MeasureTheory.Group.Measure
import Tengoku.Seed.LinearAlgebra.FreeModule.IdealQuotient
import Tengoku.Seed.RingTheory.Ideal.Norm.AbsNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

/--
@isnad1 id=eq.0h3v.s9.8a9adaea50fa from=translated src=- shape=b9226900 vocab=94a50a30
-/
theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

/--
@isnad1 id=eq.0h3v.s9.0d1b48394122 from=translated src=- shape=df00fba1 vocab=3a86ff45
-/
theorem valued_algebraMap_integer (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v) = v.intValuation a := by
  rw [algebraMap_integer_apply, show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)
        = ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

/--
@isnad1 id=eq.0h4v.s8.e8b51b37fa08 from=translated src=- shape=4ed4d2b4 vocab=7387c9d1
-/
theorem mul_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x * y) v = x v * y v := rfl

/--
@isnad1 id=eq.0h4v.s9.5688e4aefb6f from=translated src=- shape=4ed4d2b4 vocab=4ec63df4
-/
theorem sub_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x - y) v = x v - y v := rfl

/--
@isnad1 id=mem.0h2v.s8.b80b9d9fe371 from=translated src=- shape=ca189419 vocab=25980abb
-/
theorem algebraMap_integer_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a

/--
@isnad1 id=mem.1h3v.s9.80f39704fe2c from=translated src=- shape=dd8b2bc5 vocab=0a575a35
-/
theorem mul_integer_mem (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a) (hz v)

/--
@isnad1 id=mem.2h3v.s8.82ca31d3b7fd from=translated src=- shape=e4d16b89 vocab=1eecb234
-/
theorem add_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

/--
@isnad1 id=mem.2h3v.s8.052a193a4c55 from=translated src=- shape=e4d16b89 vocab=523a7a7c
-/
theorem sub_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z - w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  sub_mem (hz v) (hw v)

/--
@isnad1 id=mem.2h4v.s8.bed37472b70c from=translated src=- shape=4e4c91d8 vocab=0148c5b6
-/
theorem dBox_sub_mem {d : 𝓞 F} {y y' : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ dBox F d) (hy' : y' ∈ dBox F d) :
    y - y' ∈ dBox F d := by
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨w', hw', rfl⟩ := hy'
  exact ⟨w - w', sub_mem' F hw hw', by simp only [mul_sub]⟩

/--
@isnad1 id=iscompac.0h2v.s5.febad9f0d9b0 from=translated src=- shape=92e82c84 vocab=4e75cda7
-/
theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

variable {F}

/--
@isnad1 id=ex.2h3v.s9.f6376b1e04bd from=translated src=- shape=f83c10ba vocab=87f1605a
-/
theorem exists_sub_mem_dBox {d : 𝓞 F} (hd : d ≠ 0) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ a : 𝓞 F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ dBox F d := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F hz hd
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_apply', map_mul, sub_apply']
    have hdv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) ≠ 0 := by
      rw [valued_algebraMap_integer]; exact v.intValuation_ne_zero d hd
    have hinv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v)
        = (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹ := by
      rw [show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v
          = algebraMap F (v.adicCompletion F) (d : F)⁻¹ from rfl, map_inv₀, Valuation.map_inv]
      rfl
    have ha' : Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := ha v
    rw [hinv]
    calc (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := by gcongr
      _ = 1 := inv_mul_cancel₀ hdv
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))) = z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul]

/--
@isnad1 id=mem.2h4v.s9.47c6e16ef1f6 from=translated src=- shape=414d3c0f vocab=1dba3919
-/
theorem sub_mem_span_of_sub_mem_dBox {d a a' : 𝓞 F} (hd : d ≠ 0)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a' : F)
      ∈ dBox F d) : a - a' ∈ Ideal.span {d} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨w, hw, hw'⟩ := h
  set y : F := (d : F)⁻¹ * ((a : F) - (a' : F)) with hy
  have hwy : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
    have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - (a' : F)) := by rw [map_sub]; exact hw'
    calc w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * w := by
            rw [inv_mul_cancel₀ hd', map_one, one_mul]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) := by
            rw [map_mul, mul_assoc]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
  have hyint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
    have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
      rw [← hwy]; exact hw v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
  rw [Ideal.mem_span_singleton']
  refine ⟨b, RingOfIntegers.coe_injective ?_⟩
  have hb' : (b : F) = y := hb
  show ((b * d : 𝓞 F) : F) = ((a - a' : 𝓞 F) : F)
  have e1 : ((b * d : 𝓞 F) : F) = (b : F) * (d : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
  have e2 : ((a - a' : 𝓞 F) : F) = (a : F) - (a' : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
  rw [e1, e2, hb', hy, mul_comm, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

end LatIdx

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable {F : Type} [Field F] [NumberField F]

/--
@isnad1 id=eq.0h3v.s9.4eba62a8070d from=translated src=- shape=bce134cb vocab=71094b30
-/
theorem image_coset_eq (d : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) :
    (fun z : FiniteAdeleRing (𝓞 F) F ↦ x + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
        integralFiniteAdeles (𝓞 F) F
      = (fun y : FiniteAdeleRing (𝓞 F) F ↦ x + y) '' dBox F d := by
  rw [dBox, Set.image_image]

/--
@isnad1 id=eq.0h4v.s8.b2e28b3ca5af from=translated src=- shape=2928c5f6 vocab=76561227
-/
theorem measure_image_add_left [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (x : FiniteAdeleRing (𝓞 F) F) (s : Set (FiniteAdeleRing (𝓞 F) F)) :
    ν ((fun y ↦ x + y) '' s) = ν s := by
  rw [Set.image_add_left, measure_preimage_add]

/--
@isnad1 id=eq.1h4v.s10.5a56350175df from=translated src=- shape=f981bad9 vocab=d893246a
-/
theorem main [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) := by
  classical

  rw [image_coset_eq, measure_image_add_left]

  set I : Ideal (𝓞 F) := Ideal.span {d} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, ne_eq, Ideal.span_singleton_eq_bot]; exact hd
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set r : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective with hrdef
  have hr : ∀ q, Ideal.Quotient.mk I (r q) = q := Function.surjInv_eq Ideal.Quotient.mk_surjective
  set T : 𝓞 F ⧸ I → Set (FiniteAdeleRing (𝓞 F) F) :=
    fun q ↦ (fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) + y) '' dBox F d with hTdef
  have hcover : integralFiniteAdeles (𝓞 F) F = ⋃ q, T q := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := exists_sub_mem_dBox hd hz
      refine Set.mem_iUnion.mpr ⟨Ideal.Quotient.mk I a, ?_⟩
      have hra : r (Ideal.Quotient.mk I a) - a ∈ I := Ideal.Quotient.eq.mp (hr _)
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hra
      refine ⟨z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F), ?_,
        add_sub_cancel _ _⟩
      have : z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F)
          = (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))
            - algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) := by
        have e : ((r (Ideal.Quotient.mk I a) : 𝓞 F) : F) = (a : F) + (d : F) * (b : F) := by
          have hb2 : (r (Ideal.Quotient.mk I a) : 𝓞 F) = a + d * b := by rw [mul_comm, hb]; abel
          rw [hb2]; simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul]
        rw [e, map_add, map_mul]
        abel
      rw [this]
      exact dBox_sub_mem F ha ⟨_, algebraMap_integer_mem F b, rfl⟩
    · intro hz
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hq
      exact add_mem' F (algebraMap_integer_mem F _) (mul_integer_mem F d hw)
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨y', hy', hxy⟩
    dsimp only at hxy
    apply hqq'
    have hsub : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
        - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) ∈ dBox F d := by
      have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
          - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) = y - y' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm y, hxy]
      rw [this]
      exact dBox_sub_mem F hy hy'
    have hmem := sub_mem_span_of_sub_mem_dBox hd hsub
    rw [← hr q, ← hr q', Ideal.Quotient.eq]

    rw [← neg_sub]
    exact I.neg_mem hmem
  have hmeas : ∀ q, MeasurableSet (T q) := fun q =>
    ((isCompact_dBox F d).image (continuous_const.add continuous_id)).isClosed.measurableSet
  have hcard : (Ideal.absNorm I : ENNReal) = (Finset.univ : Finset (𝓞 F ⧸ I)).card := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, Finset.card_univ]
  calc (Ideal.absNorm I : ENNReal) * ν (dBox F d)
      = ∑ q : 𝓞 F ⧸ I, ν (dBox F d) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = ∑ q : 𝓞 F ⧸ I, ν (T q) := Finset.sum_congr rfl fun q _ => (measure_image_add_left ν _ _).symm
    _ = ∑' q : 𝓞 F ⧸ I, ν (T q) := (tsum_fintype _).symm
    _ = ν (⋃ q, T q) := (measure_iUnion hdisj hmeas).symm
    _ = ν (integralFiniteAdeles (𝓞 F) F) := by rw [← hcover]

end LatIdx

/--
@isnad1 id=eq.1h4v.s10.5a56350175df from=translated src=- shape=f981bad9 vocab=d893246a
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) :=
  LatIdx.main ν d hd k
