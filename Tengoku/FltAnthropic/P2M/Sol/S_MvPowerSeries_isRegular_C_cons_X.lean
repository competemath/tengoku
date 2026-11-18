import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.Regular.RegularSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_isRegular_C_cons_X.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_isRegular_C_cons_X

set_option autoImplicit false

universe u

namespace M4cP4PSII

universe v

open MvPowerSeries

variable {σ : Type u} {R : Type v} [CommRing R]

def vanishIdeal (S : Set σ) (𝔞 : Ideal R) : Ideal (MvPowerSeries σ R) where
  carrier := {φ | ∀ m : σ →₀ ℕ, (∀ j ∈ S, m j = 0) → coeff m φ ∈ 𝔞}
  zero_mem' := fun m _ => by simp
  add_mem' := fun {φ ψ} hφ hψ m hm => by
    rw [map_add]; exact 𝔞.add_mem (hφ m hm) (hψ m hm)
  smul_mem' := fun ψ φ hφ m hm => by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine 𝔞.sum_mem fun p hp => 𝔞.mul_mem_left _ (hφ p.2 fun j hj => ?_)
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have : p.2 j ≤ m j := by rw [← h]; exact Nat.le_add_left _ _
    have hmj := hm j hj
    omega

/--
@isnad1 id=mem.1h5v.s6.ddc53d5c76d6 from=translated src=- shape=1d72c7c6 vocab=77bb10bf
-/
theorem X_mem_vanishIdeal {S : Set σ} (𝔞 : Ideal R) {j : σ} (hj : j ∈ S) :
    (X j : MvPowerSeries σ R) ∈ vanishIdeal S 𝔞 := by
  classical
  intro m hm
  rw [coeff_X, ite_eq_right]
  · exact 𝔞.zero_mem
  · rintro rfl
    have := hm j hj
    simp at this

/--
@isnad1 id=mem.1h5v.s7.ecb2edf06aef from=translated src=- shape=ef668da5 vocab=f19a35db
-/
theorem C_mem_vanishIdeal (S : Set σ) {𝔞 : Ideal R} {a : R} (ha : a ∈ 𝔞) :
    (C a : MvPowerSeries σ R) ∈ vanishIdeal S 𝔞 := by
  classical
  intro m _
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact 𝔞.zero_mem

/--
@isnad1 id=le.0h4v.s8.114db5232c80 from=translated src=- shape=1a7c8fad vocab=e392f88a
-/
theorem map_C_sup_span_le_vanishIdeal (S : Set σ) (𝔞 : Ideal R) :
    𝔞.map (C : R →+* MvPowerSeries σ R) ⊔ Ideal.span ((X : σ → MvPowerSeries σ R) '' S) ≤
      vanishIdeal S 𝔞 := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact C_mem_vanishIdeal S ha
  · rw [Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact X_mem_vanishIdeal 𝔞 hj

/--
@isnad1 id=le.0h4v.s8.7286bccd3afe from=translated src=- shape=06690947 vocab=1ec6212c
-/
theorem vanishIdeal_le_of_principal (S : Finset σ) (a : R) :
    vanishIdeal (↑S : Set σ) (Ideal.span {a}) ≤
      Ideal.span {(C a : MvPowerSeries σ R)} ⊔ Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ

    have hdiv : ∀ m : σ →₀ ℕ, ∃ b : R, coeff m φ = a * b := fun m => by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hφ m (by simp))
      exact ⟨b, by rw [← hb, mul_comm]⟩
    choose g hg using hdiv
    have hφeq : φ = C a * (show MvPowerSeries σ R from g) := by
      ext m
      rw [coeff_C_mul, hg m, coeff_apply]
    rw [hφeq]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  | insert j S hjS ih =>
    intro φ hφ

    let h : MvPowerSeries σ R := fun m => if m j = 0 then φ m else 0
    have hcoeff : ∀ m : σ →₀ ℕ, coeff m h = if m j = 0 then coeff m φ else 0 := fun m => rfl
    have hX : (X j : MvPowerSeries σ R) ∣ φ - h := by
      rw [X_dvd_iff]
      intro m hm
      rw [map_sub, hcoeff, ite_eq_left hm, sub_self]
    have hh : h ∈ vanishIdeal (↑S : Set σ) (Ideal.span {a}) := by
      intro m hm
      rw [hcoeff]
      split_ifs with hmj
      · exact hφ m (fun i hi => by
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp hi) with rfl | hi
          · exact hmj
          · exact hm i (Finset.mem_coe.mpr hi))
      · exact Ideal.zero_mem _
    have hsub : Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) ≤
        Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑(insert j S)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    have h1 : φ - h ∈ Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑(insert j S)) := by
      obtain ⟨q, hq⟩ := hX
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, by simp, rfl⟩)
    have h2 := (sup_le_sup_left hsub _) (ih hh)
    have : φ = (φ - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right h1) h2

/--
@isnad1 id=eq.0h4v.s7.ec0bd0d12de1 from=translated src=- shape=06690947 vocab=ffff4402
-/
theorem vanishIdeal_eq_of_principal (S : Finset σ) (a : R) :
    vanishIdeal (↑S : Set σ) (Ideal.span {a}) =
      Ideal.span {(C a : MvPowerSeries σ R)} ⊔ Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) := by
  refine le_antisymm (vanishIdeal_le_of_principal S a) ?_
  have := map_C_sup_span_le_vanishIdeal (↑S : Set σ) (Ideal.span {a} : Ideal R)
  rwa [Ideal.map_span, Set.image_singleton] at this

/--
@isnad1 id=eq.0h3v.s6.cb88f1062be3 from=translated src=- shape=30cfe010 vocab=77d044ef
-/
theorem vanishIdeal_bot_eq (S : Finset σ) :
    vanishIdeal (↑S : Set σ) (⊥ : Ideal R) = Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) := by
  have h := vanishIdeal_eq_of_principal S (0 : R)
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
  rw [h, map_zero, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

/--
@isnad1 id=mem.2h6v.s7.158e44ca3886 from=translated src=- shape=4be78a00 vocab=d6c6242b
-/
theorem mem_vanishIdeal_of_X_mul_mem {S : Set σ} {𝔞 : Ideal R} {i : σ} (hi : i ∉ S)
    {φ : MvPowerSeries σ R} (h : X i * φ ∈ vanishIdeal S 𝔞) : φ ∈ vanishIdeal S 𝔞 := by
  intro m hm
  have := h (Finsupp.single i 1 + m) fun j hj => by
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, hm j hj]
  rwa [X_def, coeff_add_monomial_mul, one_mul] at this

/--
@isnad1 id=mem.2h5v.s8.86fddd152d96 from=translated src=- shape=814cad29 vocab=5e4e537e
-/
theorem mem_vanishIdeal_of_C_mul_mem {S : Set σ} {a : R} (ha : a ∈ nonZeroDivisors R)
    {φ : MvPowerSeries σ R} (h : C a * φ ∈ vanishIdeal S (⊥ : Ideal R)) :
    φ ∈ vanishIdeal S (⊥ : Ideal R) := by
  intro m hm
  have := h m hm
  rw [coeff_C_mul, Ideal.mem_bot] at this
  exact Ideal.mem_bot.mpr ((mem_nonZeroDivisors_iff.mp ha).1 _ this)

/--
@isnad1 id=eq.0h4v.s5.2b756106c0ac from=translated src=- shape=0d3b52c9 vocab=c626c2e0
-/
theorem setOf_mem_take_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : ℕ) :
    {x | x ∈ (List.ofFn f).take i} = f '' {j : Fin n | (j : ℕ) < i} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hk
    exact ⟨⟨k, hk.2⟩, hk.1, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨j, by simp; omega, by simp⟩

/--
@isnad1 id=eq.0h3v.s7.0bf3425f6cc5 from=translated src=- shape=9f9b358b vocab=6d552dbd
-/
theorem ofList_take_ofFn_X {n : ℕ} (i : ℕ) :
    Ideal.ofList ((List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)).take i) =
      vanishIdeal (↑(Finset.univ.filter fun j : Fin n => (j : ℕ) < i) : Set (Fin n)) (⊥ : Ideal R) := by
  rw [vanishIdeal_bot_eq, Ideal.ofList, setOf_mem_take_ofFn, Finset.coe_filter]
  simp

/--
@isnad1 id=eq.0h2v.s6.94c03703fc99 from=translated src=- shape=64a4a719 vocab=02d285fd
-/
theorem ofList_ofFn_X {n : ℕ} :
    Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)) =
      vanishIdeal (Set.univ : Set (Fin n)) (⊥ : Ideal R) := by
  have h := ofList_take_ofFn_X (R := R) (n := n) n
  rw [List.take_of_length_le (by simp)] at h
  rw [h]
  congr 1
  ext j
  simp

/--
@isnad1 id=eq.0h2v.s7.3bf56679d5de from=translated src=- shape=d3b7573d vocab=a2638bb3
-/
theorem ideal_smul_top_eq {A : Type*} [CommRing A] (I : Ideal A) :
    (I • ⊤ : Submodule A A) = I := by
  rw [smul_eq_mul, Ideal.mul_top]

/--
@isnad1 id=isweakly.0h2v.s6.6918a3aec2bf from=translated src=- shape=20cf86e1 vocab=e7c39578
-/
theorem isWeaklyRegular_X (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)) := by
  refine ⟨fun i hi => ?_⟩
  rw [ofList_take_ofFn_X, ideal_smul_top_eq, isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro φ hφ
  rw [List.getElem_ofFn, smul_eq_mul] at hφ
  refine mem_vanishIdeal_of_X_mul_mem ?_ hφ
  simp

/--
@isnad1 id=isweakly.1h3v.s7.8f9161b5c975 from=translated src=- shape=54f295b1 vocab=c77087ab
-/
theorem isWeaklyRegular_X_append_C (n : ℕ) {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) := by
  rw [RingTheory.Sequence.isWeaklyRegular_append_iff]
  refine ⟨isWeaklyRegular_X n, ?_⟩
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff, ofList_ofFn_X, ideal_smul_top_eq,
    isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro φ hφ
  rw [smul_eq_mul] at hφ
  exact mem_vanishIdeal_of_C_mul_mem hϖ hφ

/--
@isnad1 id=eq.0h3v.s7.7d6048396f0a from=translated src=- shape=37d3e0ff vocab=a6985c4e
-/
theorem ofList_X_append_C (n : ℕ) (ϖ : R) :
    Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) =
      vanishIdeal (Set.univ : Set (Fin n)) (Ideal.span {ϖ}) := by
  rw [Ideal.ofList_append, Ideal.ofList_singleton, ofList_ofFn_X, ← Finset.coe_univ,
    vanishIdeal_bot_eq, vanishIdeal_eq_of_principal, sup_comm]

/--
@isnad1 id=isregula.2h3v.s7.977d268559ff from=translated src=- shape=69c819a3 vocab=32bc54d7
-/
theorem isRegular_X_append_C (n : ℕ) {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hu : ¬IsUnit ϖ) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) R)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) := by
  refine ⟨isWeaklyRegular_X_append_C n hϖ, ?_⟩
  rw [ofList_X_append_C, ideal_smul_top_eq]
  intro h
  have h1 : (1 : MvPowerSeries (Fin n) R) ∈ vanishIdeal (Set.univ : Set (Fin n)) (Ideal.span {ϖ}) := by
    rw [← h]; trivial
  have := h1 0 (by simp)
  rw [coeff_zero_one, Ideal.mem_span_singleton] at this
  exact hu (isUnit_of_dvd_one this)

/--
@isnad1 id=isregula.2h3v.s7.2075ce3ed1ff from=translated src=- shape=48d08a4f vocab=de81c432
-/
theorem isRegular_C_cons_X (n : ℕ) {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hu : ¬IsUnit ϖ) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) R)
      (C ϖ :: List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)) := by
  have hperm : Ideal.ofList (C ϖ :: List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)) =
      Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) := by
    rw [Ideal.ofList_cons, Ideal.ofList_append, Ideal.ofList_singleton, sup_comm]
  refine ⟨⟨fun i hi => ?_⟩, ?_⟩
  · rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro φ hφ
    cases i with
    | zero =>
      simp only [List.take_zero, Ideal.ofList_nil, Submodule.bot_smul, Submodule.mem_bot,
        List.getElem_cons_zero] at hφ ⊢
      rw [smul_eq_mul] at hφ

      ext m
      have := congrArg (coeff m) hφ
      rw [coeff_C_mul, map_zero] at this
      rw [map_zero]
      exact (mem_nonZeroDivisors_iff.mp hϖ).1 _ this
    | succ k =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.getElem_ofFn] at hφ ⊢
      rw [Ideal.ofList_cons, ofList_take_ofFn_X, vanishIdeal_bot_eq, ← vanishIdeal_eq_of_principal,
        ideal_smul_top_eq] at hφ ⊢
      rw [smul_eq_mul] at hφ
      refine mem_vanishIdeal_of_X_mul_mem ?_ hφ
      simp
  · rw [hperm]
    exact (isRegular_X_append_C n hϖ hu).top_ne_smul

end M4cP4PSII

/--
@isnad1 id=isregula.2h3v.s7.2075ce3ed1ff from=translated src=- shape=48d08a4f vocab=de81c432
-/
theorem solution {R : Type u} [CommRing R] (n : ℕ) {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hu : ¬IsUnit ϖ) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) R)
      (MvPowerSeries.C ϖ :: List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) :=
  M4cP4PSII.isRegular_C_cons_X n hϖ hu
