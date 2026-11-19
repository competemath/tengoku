import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.RhoLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace OddCycleBound.DenseRegion

noncomputable def An (n : ℕ) (u : ℝ) : ℝ := u ^ n + (1 - u) ^ n

/--
@isnad1 id=eq.0h3v.s8.ce3f9983f854 from=translated src=- shape=08f9275a vocab=5926fcfe
-/
lemma rho_derivative (t r : ℕ) (u : ℝ) :
    (2 * (t : ℝ) + 1) * rho (2 * t + 1) (2 * t + 1 + 2 * r) u
      = 2 * (r : ℝ) * An (2 * t + 1) u
        - (1 - u) * ((2 * (t : ℝ) + 1) * (u ^ (2 * t) - (1 - u) ^ (2 * t))) := by
  have hn : (2 * (t : ℝ) + 1) ≠ 0 := by positivity
  unfold rho An
  rw [show 2 * t + 1 - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t), pow_succ (1 - u) (2 * t)]
  field_simp
  ring

noncomputable def aCoef (t j : ℕ) : ℝ :=
  2 * (Nat.choose (2 * t + 1) (2 * j) : ℝ) * (1 / 2 : ℝ) ^ (2 * t + 1 - 2 * j)

/--
@isnad1 id=lt.1h2v.s4.c30c335684dc from=translated src=- shape=430b0ef9 vocab=b11b9a54
-/
lemma aCoef_pos (t j : ℕ) (hj : j ≤ t) : 0 < aCoef t j := by
  have hc : 0 < (Nat.choose (2 * t + 1) (2 * j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 * j ≤ 2 * t + 1 from by omega)
  unfold aCoef; positivity

/--
@isnad1 id=eq.0h2v.s6.fff791496916 from=translated src=- shape=7b266970 vocab=37df85ec
-/
lemma An_half_expansion (t : ℕ) (v : ℝ) :
    An (2 * t + 1) (1 / 2 + v) = ∑ j ∈ Finset.range (t + 1), aCoef t j * v ^ (2 * j) := by
  classical
  set g : ℕ → ℝ := fun k =>
    (1 + (-1 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (2 * t + 1 - k) * (Nat.choose (2 * t + 1) k : ℝ)) * v ^ k
    with hg

  have hAn : An (2 * t + 1) (1 / 2 + v) = (v + 1 / 2) ^ (2 * t + 1) + (-v + 1 / 2) ^ (2 * t + 1) := by
    unfold An
    rw [show (1 : ℝ) / 2 + v = v + 1 / 2 from by ring,
        show (1 : ℝ) - (v + 1 / 2) = -v + 1 / 2 from by ring]
  have hexp : An (2 * t + 1) (1 / 2 + v) = ∑ k ∈ Finset.range (2 * t + 2), g k := by
    rw [hAn, add_pow, add_pow, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hnp : (-v) ^ k = (-1 : ℝ) ^ k * v ^ k := by rw [neg_pow]
    simp only [hg]; rw [hnp]; ring

  have hinj : ∀ a ∈ Finset.range (t + 1), ∀ b ∈ Finset.range (t + 1),
      (fun j => 2 * j) a = (fun j => 2 * j) b → a = b := by
    intro a _ b _ hab; dsimp only at hab; omega
  have himg : (Finset.range (t + 1)).image (fun j => 2 * j) ⊆ Finset.range (2 * t + 2) := by
    intro k hk; simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨j, hj, rfl⟩ := hk; omega
  have hz : ∀ k ∈ Finset.range (2 * t + 2),
      k ∉ (Finset.range (t + 1)).image (fun j => 2 * j) → g k = 0 := by
    intro k hkr hk
    simp only [Finset.mem_range] at hkr
    simp only [Finset.mem_image, Finset.mem_range] at hk
    have hodd : Odd k := by
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨j, rfl⟩ := he; exact absurd ⟨j, by omega, by ring⟩ hk
      · exact ho
    simp only [hg]; rw [hodd.neg_one_pow]; ring
  have hreindex : ∑ k ∈ Finset.range (2 * t + 2), g k = ∑ j ∈ Finset.range (t + 1), g (2 * j) := by
    rw [← Finset.sum_subset himg hz, Finset.sum_image hinj]

  have hterm : ∀ j ∈ Finset.range (t + 1), g (2 * j) = aCoef t j * v ^ (2 * j) := by
    intro j _
    simp only [hg, aCoef]
    rw [show (-1 : ℝ) ^ (2 * j) = 1 from by rw [pow_mul]; norm_num]
    ring
  rw [hexp, hreindex, Finset.sum_congr rfl hterm]

/--
@isnad1 id=eq.0h2v.s8.f33f34af7f11 from=translated src=- shape=27b5587d vocab=d529ca57
-/
lemma An_deriv_half_expansion (t : ℕ) (v : ℝ) :
    (2 * (t : ℝ) + 1) * ((1 / 2 + v) ^ (2 * t) - (1 / 2 - v) ^ (2 * t))
      = ∑ j ∈ Finset.range (t + 1), (2 * (j : ℝ)) * aCoef t j * v ^ (2 * j - 1) := by
  classical
  set g : ℕ → ℝ := fun k =>
    (2 * (t : ℝ) + 1) * (1 - (-1 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (2 * t - k) * (Nat.choose (2 * t) k : ℝ))
      * v ^ k with hg
  have hexp : (2 * (t : ℝ) + 1) * ((1 / 2 + v) ^ (2 * t) - (1 / 2 - v) ^ (2 * t))
      = ∑ k ∈ Finset.range (2 * t + 1), g k := by
    rw [show (1 : ℝ) / 2 + v = v + 1 / 2 from by ring, show (1 : ℝ) / 2 - v = -v + 1 / 2 from by ring,
        add_pow, add_pow, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hnp : (-v) ^ k = (-1 : ℝ) ^ k * v ^ k := by rw [neg_pow]
    simp only [hg]; rw [hnp]; ring

  have hinj : ∀ a ∈ Finset.range (t + 1), ∀ b ∈ Finset.range (t + 1),
      (fun j => 2 * j - 1) a = (fun j => 2 * j - 1) b → a = b := by
    intro a _ b _ hab; dsimp only at hab; omega
  have himg : (Finset.range (t + 1)).image (fun j => 2 * j - 1) ⊆ Finset.range (2 * t + 1) := by
    intro k hk; simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨j, hj, rfl⟩ := hk; omega
  have hz : ∀ k ∈ Finset.range (2 * t + 1),
      k ∉ (Finset.range (t + 1)).image (fun j => 2 * j - 1) → g k = 0 := by
    intro k hkr hk
    simp only [Finset.mem_range] at hkr
    simp only [Finset.mem_image, Finset.mem_range] at hk
    have heven : Even k := by
      rcases Nat.even_or_odd k with he | ho
      · exact he
      · obtain ⟨i, rfl⟩ := ho; exact absurd ⟨i + 1, by omega, by omega⟩ hk
    simp only [hg]; rw [heven.neg_one_pow]; ring
  have hreindex : ∑ k ∈ Finset.range (2 * t + 1), g k
      = ∑ j ∈ Finset.range (t + 1), g (2 * j - 1) := by
    rw [← Finset.sum_subset himg hz, Finset.sum_image hinj]
  have hterm : ∀ j ∈ Finset.range (t + 1),
      g (2 * j - 1) = (2 * (j : ℝ)) * aCoef t j * v ^ (2 * j - 1) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0; simp only [hg]; norm_num
    · have hodd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
      have hchoose : (2 * (t : ℝ) + 1) * (Nat.choose (2 * t) (2 * j - 1) : ℝ)
          = (2 * (j : ℝ)) * (Nat.choose (2 * t + 1) (2 * j) : ℝ) := by
        have h := Nat.add_one_mul_choose_eq (2 * t) (2 * j - 1)
        rw [show 2 * j - 1 + 1 = 2 * j from by omega] at h
        have hc := congrArg (Nat.cast (R := ℝ)) h
        push_cast at hc
        linear_combination hc
      simp only [hg, aCoef]
      rw [hodd.neg_one_pow, show 2 * t - (2 * j - 1) = 2 * t + 1 - 2 * j from by omega]
      linear_combination (2 * (1 / 2 : ℝ) ^ (2 * t + 1 - 2 * j) * v ^ (2 * j - 1)) * hchoose
  rw [hexp, hreindex, Finset.sum_congr rfl hterm]

/--
@isnad1 id=eq.0h3v.s8.95185e898086 from=translated src=- shape=31acda69 vocab=1e9c04b2
-/
lemma rho_centered (t r : ℕ) (v : ℝ) :
    (2 * (t : ℝ) + 1) * rho (2 * t + 1) (2 * t + 1 + 2 * r) (1 / 2 + v)
      = ∑ j ∈ Finset.range (t + 1),
          aCoef t j * (2 * ((r : ℝ) + (j : ℝ)) * v ^ (2 * j) - (j : ℝ) * v ^ (2 * j - 1)) := by
  rw [rho_derivative t r (1 / 2 + v), show (1 : ℝ) - (1 / 2 + v) = 1 / 2 - v from by ring,
      An_half_expansion, An_deriv_half_expansion, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0; simp; ring
  · have hpow : v ^ (2 * j) = v * v ^ (2 * j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]; ring
