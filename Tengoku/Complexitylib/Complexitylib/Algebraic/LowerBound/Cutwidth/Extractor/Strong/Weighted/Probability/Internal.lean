/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Tengoku

/-!
# Finite mass identities and total variation bounds

Normalization is preserved by marginals and deterministic maps. Total
variation contracts under deterministic maps and bounds every finite test.
For equal total mass, the positive-difference test attains the distance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/--
@isnad1 id=ex.1h2v.s4.f552665170c1 from=translated src=- shape=ce542171 vocab=3de1133a
-/
theorem probabilityWeight_exists_pos {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) : ∃ x, 0 < p x := by
  have nonzero : ∑ x, p x ≠ 0 := by rw [hp.2]; norm_num
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact ⟨x, lt_of_le_of_ne (hp.1 x) (Ne.symm hx)⟩

/--
@isnad1 id=le.1h3v.s4.9c749f4267c7 from=translated src=- shape=9c0ab710 vocab=2314673e
-/
theorem probabilityWeight_le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) (x : α) : p x ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ x)

/--
@isnad1 id=isprobab.1h3v.s5.49ad5c5a58cd from=translated src=- shape=f9f93525 vocab=1c39d278
-/
theorem probabilityWeight_first {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : IsProbabilityWeight p) : IsProbabilityWeight (firstWeight p) := by
  refine ⟨fun a => Finset.sum_nonneg fun b _ => hp.1 (a, b), ?_⟩
  simpa only [firstWeight, ← Fintype.sum_prod_type] using hp.2

/--
@isnad1 id=isprobab.1h4v.s5.96dee1503e25 from=translated src=- shape=b373aadd vocab=18ec3ff6
-/
theorem probabilityWeight_map {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f : α → β) :
    IsProbabilityWeight (mapWeight f p) := by
  refine ⟨fun b => Finset.sum_nonneg fun a _ => ?_, ?_⟩
  · split_ifs <;> first | exact hp.1 a | rfl
  · simpa [mapWeight, Finset.sum_comm] using hp.2

/--
@isnad1 id=isprobab.0h1v.s3.2cd0db710f7e from=translated src=- shape=4c9b52a8 vocab=ab32b88b
-/
theorem probabilityWeight_uniform (α : Type*) [Fintype α] [Nonempty α] :
    IsProbabilityWeight (uniformWeight α) := by
  have positive : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  constructor
  · intro x
    exact inv_nonneg.mpr positive.le
  · simp [uniformWeight, ne_of_gt positive]

/--
@isnad1 id=eq.0h2v.s4.d639d81aa732 from=translated src=- shape=2f3ee489 vocab=a250473f
-/
theorem mapWeight_id {α : Type*} [Fintype α] (p : α → ℝ) : mapWeight id p = p := by
  funext x
  simp [mapWeight]

/--
@isnad1 id=eq.0h5v.s6.7981240f64b5 from=translated src=- shape=b9fa914f vocab=881edbd0
-/
theorem mapWeight_equiv_apply {α β : Type*} [Fintype α]
    (e : α ≃ β) (p : α → ℝ) (y : β) : mapWeight e p y = p (e.symm y) := by
  simp only [mapWeight, ← e.eq_symm_apply]
  simp

/--
@isnad1 id=eq.0h6v.s5.8ea47377c59d from=translated src=- shape=ef1fabd2 vocab=2f7befe1
-/
theorem mapWeight_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    mapWeight g (mapWeight f p) = mapWeight (fun x => g (f x)) p := by
  funext y
  simp only [mapWeight]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have swap (b : β) :
      (if g b = y then (if f x = b then p x else 0) else 0) =
        if f x = b then (if g b = y then p x else 0) else 0 := by
    by_cases h : f x = b <;> by_cases h' : g b = y <;> simp [h, h']
  simp_rw [swap]
  simp

/--
@isnad1 id=eq.0h3v.s5.10ca3ca726a2 from=translated src=- shape=649991af vocab=fc394cae
-/
theorem mapWeight_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) : mapWeight Prod.fst p = firstWeight p := by
  funext a
  rw [mapWeight, Fintype.sum_prod_type, Finset.sum_comm]
  simp [firstWeight]

/--
@isnad1 id=eq.0h4v.s5.24debb85b536 from=translated src=- shape=46090175 vocab=d96b02d9
-/
theorem mapWeight_snd_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) : mapWeight Prod.snd p b = ∑ a, p (a, b) := by
  simp [mapWeight, Fintype.sum_prod_type]

/--
@isnad1 id=le.2h3v.s4.5d68658c3354 from=translated src=- shape=9ec84121 vocab=aa8cd95b
-/
theorem cappedWeight_card_le {α : Type*} [Fintype α] {p : α → ℝ} {K : Nat}
    (hp : IsProbabilityWeight p) (cap : CappedWeight p K) : K ≤ Fintype.card α := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => cap x)
  rw [← Finset.mul_sum, hp.2, mul_one] at h
  simpa using h

/--
@isnad1 id=eq.2h2v.s4.0781d433f1f5 from=translated src=- shape=9051d84f vocab=9209c8d1
-/
theorem cappedWeight_eq_uniform {α : Type*} [Fintype α] {p : α → ℝ}
    (cap : CappedWeight p (Fintype.card α)) (hp : IsProbabilityWeight p) :
    p = uniformWeight α := by
  obtain ⟨x, _⟩ := probabilityWeight_exists_pos hp
  let : Nonempty α := ⟨x⟩
  have positive : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have upper (a : α) : p a ≤ uniformWeight α a := by
    change p a ≤ (Fintype.card α : ℝ)⁻¹
    rw [← one_div]
    apply (le_div_iff₀ positive).mpr
    simpa only [mul_comm] using cap a
  have mass : ∑ a, (uniformWeight α a - p a) = 0 := by
    rw [Finset.sum_sub_distrib, (probabilityWeight_uniform α).2, hp.2, sub_self]
  funext a
  have zero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b (_ : b ∈ (Finset.univ : Finset α)) => sub_nonneg.mpr (upper b))).mp mass a
      (Finset.mem_univ a)
  exact (sub_eq_zero.mp zero).symm

/--
@isnad1 id=le.0h3v.s4.1c68e6422e5c from=translated src=- shape=7325c23d vocab=385b4534
-/
theorem weightDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ weightDist p q := by
  unfold weightDist
  positivity

/--
@isnad1 id=eq.0h2v.s4.05305a4ef327 from=translated src=- shape=46428dbe vocab=0061b34f
-/
theorem weightDist_self {α : Type*} [Fintype α] (p : α → ℝ) : weightDist p p = 0 := by
  simp [weightDist]

/--
@isnad1 id=eq.0h3v.s4.d5b0dfae6a3c from=translated src=- shape=8cef85e8 vocab=0061b34f
-/
theorem weightDist_comm {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = weightDist q p := by
  simp only [weightDist, abs_sub_comm]

/--
@isnad1 id=le.0h4v.s5.a39861a1508a from=translated src=- shape=f79ff783 vocab=ecd8eb77
-/
theorem weightDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    weightDist p r ≤ weightDist p q + weightDist q r := by
  have bound := Finset.sum_le_sum
    (fun x (_ : x ∈ (Finset.univ : Finset α)) => abs_sub_le (p x) (q x) (r x))
  rw [Finset.sum_add_distrib] at bound
  unfold weightDist
  linarith

/--
@isnad1 id=iff.0h3v.s5.e5cba8f816c6 from=translated src=- shape=ef9397c1 vocab=0061b34f
-/
theorem weightDist_eq_zero_iff {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = 0 ↔ p = q := by
  constructor
  · intro zero
    have sumZero : ∑ x, |p x - q x| = 0 := by
      unfold weightDist at zero
      linarith
    funext x
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ (Finset.univ : Finset α)) => abs_nonneg (p y - q y))).mp sumZero x
        (Finset.mem_univ x)
    exact sub_eq_zero.mp (abs_eq_zero.mp this)
  · rintro rfl
    exact weightDist_self p

/--
@isnad1 id=le.2h3v.s5.947ffebd438b from=translated src=- shape=da694d26 vocab=b208f2d8
-/
theorem weightDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) : weightDist p q ≤ 1 := by
  have bound : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact (abs_sub (p x) (q x)).trans_eq (by rw [abs_of_nonneg (hp.1 x), abs_of_nonneg (hq.1 x)])
  rw [Finset.sum_add_distrib, hp.2, hq.2] at bound
  unfold weightDist
  linarith

/--
@isnad1 id=le.1h4v.s6.8040922728ed from=translated src=- shape=446606cc vocab=4f5e12f2
-/
theorem weightTestProb_sub_le_dist {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) (T : Finset α) :
    |weightTestProb p T - weightTestProb q T| ≤ weightDist p q := by
  have balance : (∑ x ∈ T, (p x - q x)) + (∑ x ∈ Tᶜ, (p x - q x)) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, mass, sub_self]
  have complement : |∑ x ∈ Tᶜ, (p x - q x)| = |∑ x ∈ T, (p x - q x)| := by
    have equality : (∑ x ∈ Tᶜ, (p x - q x)) = -(∑ x ∈ T, (p x - q x)) := by
      linarith
    rw [equality, abs_neg]
  have bound := add_le_add
    (Finset.abs_sum_le_sum_abs (fun x => p x - q x) T)
    (Finset.abs_sum_le_sum_abs (fun x => p x - q x) Tᶜ)
  rw [Finset.sum_add_sum_compl, complement] at bound
  unfold weightTestProb weightDist
  rw [← Finset.sum_sub_distrib]
  linarith

/--
@isnad1 id=iff.1h4v.s6.90f8463b3f68 from=translated src=- shape=233206be vocab=4f5e12f2
-/
theorem weightDist_le_iff_tests {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) {ε : ℝ} :
    weightDist p q ≤ ε ↔ ∀ T : Finset α,
      |weightTestProb p T - weightTestProb q T| ≤ ε := by
  constructor
  · exact fun bound T => (weightTestProb_sub_le_dist p q mass T).trans bound
  · intro tests
    let T := (Finset.univ : Finset α).filter fun x => q x ≤ p x
    have posSum : ∑ x ∈ T, |p x - q x| = ∑ x ∈ T, (p x - q x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
    have negSum : ∑ x ∈ Tᶜ, |p x - q x| = -(∑ x ∈ Tᶜ, (p x - q x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply abs_of_nonpos
      have h : ¬q x ≤ p x := by simpa only [T, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and] using hx
      exact sub_nonpos.mpr (le_of_lt (lt_of_not_ge h))
    have balance : (∑ x ∈ T, (p x - q x)) + (∑ x ∈ Tᶜ, (p x - q x)) = 0 := by
      rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, mass, sub_self]
    have attained : weightDist p q = weightTestProb p T - weightTestProb q T := by
      unfold weightDist weightTestProb
      rw [← Finset.sum_add_sum_compl T (fun x => |p x - q x|), posSum, negSum,
        ← Finset.sum_sub_distrib]
      linarith
    rw [attained]
    exact (le_abs_self _).trans (tests T)

/--
@isnad1 id=eq.0h5v.s6.b62e3c3b6f55 from=translated src=- shape=c009b578 vocab=991fd976
-/
theorem weightTestProb_map {α β : Type*} [Fintype α] (p : α → ℝ)
    (f : α → β) (T : Finset β) :
    weightTestProb (mapWeight f p) T = ∑ x, if f x ∈ T then p x else 0 := by
  unfold weightTestProb mapWeight
  rw [Finset.sum_comm]
  simp

/--
@isnad1 id=le.1h5v.s6.00d936ba8978 from=translated src=- shape=a512069b vocab=2a096b52
-/
theorem weightDist_map_map_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f g : α → β) :
    weightDist (mapWeight f p) (mapWeight g p) ≤ ∑ x with f x ≠ g x, p x := by
  apply (weightDist_le_iff_tests _ _
    ((probabilityWeight_map hp f).2.trans (probabilityWeight_map hp g).2.symm)).mpr
  intro T
  rw [weightTestProb_map, weightTestProb_map, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases same : f x = g x
  · simp [same]
  · by_cases hf : f x ∈ T <;> by_cases hg : g x ∈ T <;>
      simp [same, hf, hg, abs_of_nonneg (hp.1 x), hp.1 x]

end Algebraic.Cutwidth.Extractor.Internal
