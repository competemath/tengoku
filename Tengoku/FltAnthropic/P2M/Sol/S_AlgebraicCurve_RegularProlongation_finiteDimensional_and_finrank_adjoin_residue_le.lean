import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularProlongation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le

set_option autoImplicit false

open _root_.AlgebraicCurve open _root_.IsLocalRing

namespace AlgebraicCurve
export _root_.AlgebraicCurve (RegularProlongation)
namespace RegularProlongation
export _root_.AlgebraicCurve.RegularProlongation (integers residue_algebraMap residue_surjective algebraMap_mem_iff ker_residue residue)
namespace FIneq
open _root_.AlgebraicCurve.RegularProlongation open _root_.AlgebraicCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h6v.s9.2a5eaed4daa0 from=translated src=- shape=cd801897 vocab=7ec6fc3a
-/
@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

/--
@isnad1 id=eq.0h6v.s10.c6a7c56ad787 from=translated src=- shape=bab91eb3 vocab=c07a5c52
-/
theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

/--
@isnad1 id=ex.2h6v.s8.1f955a229b0b from=translated src=- shape=a40a19db vocab=eff87759
-/
theorem exists_normalizer {ι : Type*} (t : Finset ι) (g : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

section resIndep

variable (R : RegularProlongation A F Fbar) {ι : Type*} (E : ι → R.integers)

/--
@isnad1 id=eq.0h9v.s10.42e4169d2b02 from=translated src=- shape=6c1f2780 vocab=9880c6f6
-/
theorem coe_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    ((∑ i ∈ t, constHom R (a i) * E i : R.integers) : F) = ∑ i ∈ t, (a i : L) • (E i : F) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_constHom, Algebra.smul_def]

/--
@isnad1 id=eq.0h9v.s11.607e6ec93c38 from=translated src=- shape=a563a8c0 vocab=c2d2c520
-/
theorem residue_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    R.residue (∑ i ∈ t, constHom R (a i) * E i) =
      ∑ i ∈ t, IsLocalRing.residue A (a i) • R.residue (E i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]

variable (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))
include hE

/--
@isnad1 id=eq.3h10v.s11.6a2c481d9319 from=translated src=- shape=6bb19fa1 vocab=e5186c69
-/
theorem residue_coeff_eq_zero (t : Finset ι) (a : ι → A)
    (h : R.residue (∑ i ∈ t, constHom R (a i) * E i) = 0) :
    ∀ i ∈ t, IsLocalRing.residue A (a i) = 0 := by
  rw [residue_sum_constHom_mul] at h
  exact linearIndependent_iff'.mp hE t (fun i => IsLocalRing.residue A (a i)) h

/--
@isnad1 id=mem.3h10v.s9.07e3dbdd3cc0 from=translated src=- shape=a08e7acf vocab=6235485c
-/
theorem mem_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) : ∀ i ∈ t, g i ∈ A := by
  classical
  by_contra hne
  obtain ⟨i₀, hi₀t, hgi₀⟩ := not_forall₂.mp hne
  have hg0 : g i₀ ≠ 0 := by
    rintro h0
    exact hgi₀ (h0 ▸ zero_mem A)
  obtain ⟨i₁, hi₁t, hg₁, hcA, hmax⟩ := exists_normalizer (A := A) t g hi₀t hg0
  set c : L := (g i₁)⁻¹ with hc

  have hv₀ : 1 < A.valuation (g i₀) := by
    rw [← not_le, A.valuation_le_one_iff]; exact hgi₀
  have hv₁ : 1 < A.valuation (g i₁) := lt_of_lt_of_le hv₀ (hmax i₀ hi₀t)
  have hcv : A.valuation c < 1 := by
    rw [hc, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hcv

  let a : ι → A := fun i => if hi : i ∈ t then ⟨c * g i, hcA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = c * g i := fun i hi => by simp [a, dite_eq_left hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = constHom R ⟨c, hcmem⟩ * ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    change _ = algebraMap L F c * ∑ i ∈ t, g i • (E i : F)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ha i hi, mul_smul, Algebra.smul_def]
  have hres : R.residue X = 0 := by
    rw [hXeq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero R E hE t a hres i₁ hi₁t
  have ha1 : a i₁ = 1 := Subtype.ext (by rw [ha i₁ hi₁t, hc, inv_mul_cancel₀ hg₁]; rfl)
  rw [ha1, map_one] at hall
  exact one_ne_zero hall

/--
@isnad1 id=lt.4h10v.s10.7a69f460f891 from=translated src=- shape=70ee528f vocab=9e5f708d
-/
theorem valuation_lt_one_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) (h0 : R.residue ⟨_, h⟩ = 0) :
    ∀ i ∈ t, A.valuation (g i) < 1 := by
  classical
  have hA := mem_of_sum_smul_mem R E hE t g h
  let a : ι → A := fun i => if hi : i ∈ t then ⟨g i, hA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = g i := fun i hi => by simp [a, dite_eq_left hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [ha i hi]
  have hres : R.residue X = 0 := by rw [hXeq]; exact h0
  intro i hi
  have hz := residue_coeff_eq_zero R E hE t a hres i hi
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hz
  rwa [ha i hi] at hz

/--
@isnad1 id=linearin.1h7v.s9.aabc12f78944 from=translated src=- shape=85f2e7c6 vocab=926e57fc
-/
theorem linearIndependent_coe : LinearIndependent L (fun i => (E i : F)) := by
  rw [linearIndependent_iff']
  intro t g hsum i hi
  have hmem : ∑ i ∈ t, g i • (E i : F) ∈ R.integers := by rw [hsum]; exact zero_mem _
  have h0 : R.residue ⟨_, hmem⟩ = 0 := by
    have : (⟨_, hmem⟩ : R.integers) = 0 := Subtype.ext hsum
    rw [this, map_zero]
  by_contra hgi

  have hsum' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) ∈ R.integers := by
    rw [hsum']; exact zero_mem _
  have h0' : R.residue ⟨_, hmem'⟩ = 0 := by
    have : (⟨_, hmem'⟩ : R.integers) = 0 := Subtype.ext hsum'
    rw [this, map_zero]
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE t (fun j => (g i)⁻¹ * g j) hmem' h0' i hi
  simp only [inv_mul_cancel₀ hgi, map_one, lt_self_iff_false] at hlt

end resIndep

/--
@isnad1 id=eq.0h4v.s8.dfeddfdb67c9 from=translated src=- shape=a9a04e0e vocab=7ca384c9
-/
theorem aeval_eq_linearCombination {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (x : B) (p : Polynomial K) :
    Polynomial.aeval x p = Finsupp.linearCombination K (fun j : ℕ => x ^ j) p.toFinsupp.coeff := by
  rcases p with ⟨q⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

/--
@isnad1 id=iff.0h3v.s6.685ea4a15f4c from=translated src=- shape=c1965ffc vocab=c7f13679
-/
theorem linearIndependent_pow_iff_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    (x : B) : LinearIndependent K (fun j : ℕ => x ^ j) ↔ Transcendental K x := by
  rw [linearIndependent_iff, transcendental_iff]
  constructor
  · intro h p hp
    have := h p.toFinsupp.coeff (by rw [← aeval_eq_linearCombination]; exact hp)
    exact Polynomial.toFinsupp_eq_zero.mp (AddMonoidAlgebra.coeff_eq_zero.mp this)
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rw [aeval_eq_linearCombination]; exact hl)
    exact congrArg AddMonoidAlgebra.coeff (Polynomial.ofFinsupp_eq_zero.mp this)

section frame

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

def frame (p : ℕ × Fin n) : R.integers := x ^ p.1 * y p.2

/--
@isnad1 id=eq.0h9v.s8.684af1fa9878 from=translated src=- shape=411be5b3 vocab=4a4280bc
-/
@[scoped simp] theorem coe_frame (p : ℕ × Fin n) :
    ((frame R x y p : R.integers) : F) = (x : F) ^ p.1 * (y p.2 : F) := by
  simp [frame]

include hx hy in

/--
@isnad1 id=linearin.2h8v.s12.17b4f4893528 from=translated src=- shape=3b652bdc vocab=a4ca2782
-/
theorem linearIndependent_residue_frame :
    LinearIndependent (ResidueField A) (fun p : ℕ × Fin n => R.residue (frame R x y p)) := by
  set k := ResidueField A
  set xb := R.residue x
  have hgen : LinearIndependent k
      (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) := by
    apply LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap)
    have : ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap : _ → Fbar) ∘
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) = fun j : ℕ => xb ^ j := by
      funext j
      simp
    rw [this]
    exact (linearIndependent_pow_iff_transcendental _).mpr hx
  have h := linearIndependent_smul hgen hy
  have hfun : (fun p : ℕ × Fin n => R.residue (frame R x y p)) =
      fun p : ℕ × Fin n => xb ^ p.1 * R.residue (y p.2) := by
    funext p
    simp [frame, map_mul, map_pow, xb]
  rw [hfun]
  convert h using 1
  rfl

include hx hy in

/--
@isnad1 id=linearin.2h8v.s12.6ae3b2478352 from=translated src=- shape=f7f75c11 vocab=f19ed1d0
-/
theorem linearIndependent_coe_frame :
    LinearIndependent L (fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F)) := by
  have h := linearIndependent_coe R (frame R x y) (linearIndependent_residue_frame R x hx y hy)
  have hfun : (fun p : ℕ × Fin n => ((frame R x y p : R.integers) : F)) =
      fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F) := by
    funext p; exact coe_frame R x y p
  rwa [hfun] at h

include hx hy in

/--
@isnad1 id=linearin.2h8v.s12.c22f2e797a37 from=translated src=- shape=d39b22be vocab=0a436c1d
-/
theorem linearIndependent_adjoin :
    LinearIndependent (Algebra.adjoin L ({(x : F)} : Set F)) (fun i : Fin n => (y i : F)) := by
  have h2 := linearIndependent_coe_frame R x hx y hy
  rw [linearIndependent_iff']
  intro t g hsum
  have hg : ∀ i, ∃ p : Polynomial L, Polynomial.aeval (x : F) p = (g i : F) := fun i => by
    have h : (g i : F) ∈ (Polynomial.aeval (R := L) (x : F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set N := t.sup (fun i => (p i).natDegree) + 1 with hN
  have hlt : ∀ i ∈ t, (p i).natDegree < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
    (fun q => (p q.2).coeff q.1) ?_
  · intro i hi
    have hpi : p i = 0 := by
      ext j
      by_cases hj : j < N
      · exact hzero (j, i) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hlt i hi) (not_lt.mp hj))
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  · rw [Finset.sum_product_right, ← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Subalgebra.smul_def, ← hp i, Polynomial.aeval_eq_sum_range' (hlt i hi),
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    exact (smul_mul_assoc _ _ _).symm

include hx hy in
open scoped IntermediateField.algebraAdjoinAdjoin in

/--
@isnad1 id=linearin.2h8v.s12.16395443f264 from=translated src=- shape=d704071f vocab=14b8d23a
-/
theorem linearIndependent_adjoinField :
    LinearIndependent (IntermediateField.adjoin L ({(x : F)} : Set F))
      (fun i : Fin n => (y i : F)) :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({(x : F)} : Set F))
    (IntermediateField.adjoin L ({(x : F)} : Set F))).mp (linearIndependent_adjoin R x hx y hy)

end frame

end AlgebraicCurve.RegularProlongation.FIneq
open scoped _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation.FIneq
open scoped _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation
open scoped _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le.AlgebraicCurve

open AlgebraicCurve.RegularProlongation.FIneq in
/--
@isnad1 id=and.1h6v.s12.120cd5803721 from=translated src=- shape=4692a646 vocab=8a5058c1
-/
theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : R.integers) (hf : Transcendental (IsLocalRing.ResidueField A) (R.residue f))
    [FiniteDimensional (IntermediateField.adjoin L ({(f : F)} : Set F)) F] :
    FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue f} : Set Fbar)) Fbar ∧
      Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue f} : Set Fbar)) Fbar ≤
        Module.finrank (IntermediateField.adjoin L ({(f : F)} : Set F)) F := by
  classical
  set k := IsLocalRing.ResidueField A
  set x : R.integers := f with hxdef
  set K := IntermediateField.adjoin k ({R.residue x} : Set Fbar) with hK
  set E := IntermediateField.adjoin L ({(f : F)} : Set F) with hE
  set n := Module.finrank E F with hn

  have hbound : ∀ s : Finset Fbar, LinearIndependent K (fun i : s => (i : Fbar)) → s.card ≤ n := by
    intro s hs
    have hlift : ∀ b : s, ∃ y : R.integers, R.residue y = (b : Fbar) := fun b => R.residue_surjective _
    choose y hy using hlift
    set e := s.equivFin with he
    let y' : Fin s.card → R.integers := fun i => y (e.symm i)
    have hy' : LinearIndependent K (fun i => R.residue (y' i)) := by
      have : (fun i => R.residue (y' i)) = (fun i : s => (i : Fbar)) ∘ e.symm := by
        funext i; simp [y', hy]
      rw [this]
      exact hs.comp _ e.symm.injective
    have hli := linearIndependent_adjoinField R x hf y' hy'
    have hcard := hli.fintype_card_le_finrank
    simpa using hcard
  have hrank : Module.rank K Fbar ≤ n := rank_le fun s hs => hbound s hs
  have hfin : Module.Finite K Fbar := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_⟩
  haveI := hfin
  exact Module.finrank_le_of_rank_le hrank
