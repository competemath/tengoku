import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.Regular.RegularSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal

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
@isnad1 id=mem.1h5v.s6.b66c3afb4bad from=translated src=- shape=1d72c7c6 vocab=6a097b32
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
@isnad1 id=mem.1h5v.s7.05881e89eb0c from=translated src=- shape=ef668da5 vocab=5b4dd0bb
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
@isnad1 id=le.0h4v.s8.055f00591051 from=translated src=- shape=1a7c8fad vocab=988723b5
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
@isnad1 id=le.0h4v.s8.b032ee4835c4 from=translated src=- shape=06690947 vocab=524be55f
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
@isnad1 id=eq.0h4v.s7.c11e6de9e6f2 from=translated src=- shape=06690947 vocab=1ab06245
-/
theorem vanishIdeal_eq_of_principal (S : Finset σ) (a : R) :
    vanishIdeal (↑S : Set σ) (Ideal.span {a}) =
      Ideal.span {(C a : MvPowerSeries σ R)} ⊔ Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) := by
  refine le_antisymm (vanishIdeal_le_of_principal S a) ?_
  have := map_C_sup_span_le_vanishIdeal (↑S : Set σ) (Ideal.span {a} : Ideal R)
  rwa [Ideal.map_span, Set.image_singleton] at this

/--
@isnad1 id=eq.0h3v.s6.98cced79095c from=translated src=- shape=30cfe010 vocab=ccba3188
-/
theorem vanishIdeal_bot_eq (S : Finset σ) :
    vanishIdeal (↑S : Set σ) (⊥ : Ideal R) = Ideal.span ((X : σ → MvPowerSeries σ R) '' ↑S) := by
  have h := vanishIdeal_eq_of_principal S (0 : R)
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
  rw [h, map_zero, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

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
@isnad1 id=eq.0h3v.s7.784a05bf3a8a from=translated src=- shape=9f9b358b vocab=07ac584a
-/
theorem ofList_take_ofFn_X {n : ℕ} (i : ℕ) :
    Ideal.ofList ((List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)).take i) =
      vanishIdeal (↑(Finset.univ.filter fun j : Fin n => (j : ℕ) < i) : Set (Fin n)) (⊥ : Ideal R) := by
  rw [vanishIdeal_bot_eq, Ideal.ofList, setOf_mem_take_ofFn, Finset.coe_filter]
  simp

/--
@isnad1 id=eq.0h2v.s6.4b2134d57d9b from=translated src=- shape=64a4a719 vocab=6ed339c8
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
@isnad1 id=eq.0h3v.s7.51ca2f196989 from=translated src=- shape=37d3e0ff vocab=b8f8bf5f
-/
theorem ofList_X_append_C (n : ℕ) (ϖ : R) :
    Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) =
      vanishIdeal (Set.univ : Set (Fin n)) (Ideal.span {ϖ}) := by
  rw [Ideal.ofList_append, Ideal.ofList_singleton, ofList_ofFn_X, ← Finset.coe_univ,
    vanishIdeal_bot_eq, vanishIdeal_eq_of_principal, sup_comm]

/--
@isnad1 id=eq.1h3v.s7.f0e66cb8c8fe from=translated src=- shape=12d4935c vocab=dfafc3cf
-/
theorem ofList_X_append_C_eq_maximalIdeal [IsLocalRing R] (n : ℕ) {ϖ : R}
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) R) ++ [C ϖ]) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) := by
  apply le_antisymm
  · rw [Ideal.ofList, Ideal.span_le]
    intro x hx
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨j, rfl⟩ | rfl
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
        constantCoeff_X]
      exact not_isUnit_zero
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
        constantCoeff_C]
      have : ϖ ∈ IsLocalRing.maximalIdeal R := hϖ ▸ Ideal.mem_span_singleton_self ϖ
      exact this
  · intro φ hφ
    rw [ofList_X_append_C]
    intro m hm
    have hm0 : m = 0 := by ext j; exact hm j trivial
    subst hm0
    rw [← hϖ, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, coeff_zero_eq_constantCoeff]
    exact fun hc => hφ (isUnit_iff_constantCoeff.mpr hc)

/--
@isnad1 id=eq.1h3v.s7.6d30b7f38662 from=translated src=- shape=9b5c20d3 vocab=4636a98c
-/
theorem ofList_C_cons_X_eq_maximalIdeal [IsLocalRing R] (n : ℕ) {ϖ : R}
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    Ideal.ofList (C ϖ :: List.ofFn (X : Fin n → MvPowerSeries (Fin n) R)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) := by
  rw [Ideal.ofList_cons, ← ofList_X_append_C_eq_maximalIdeal n hϖ, Ideal.ofList_append,
    Ideal.ofList_singleton, sup_comm]

end M4cP4PSII

/--
@isnad1 id=eq.1h3v.s7.6d30b7f38662 from=translated src=- shape=9b5c20d3 vocab=4636a98c
-/
theorem solution {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) {ϖ : R} (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    Ideal.ofList (MvPowerSeries.C ϖ :: List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) :=
  M4cP4PSII.ofList_C_cons_X_eq_maximalIdeal n hϖ
