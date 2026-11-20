import Tengoku.Hellingerrepolean4.Hellinger.FourierCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms high_walsh_eq_zero_of_noise_equality` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms signed_dictator_of_noise_equality` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Boolean Fourier rigidity with Parseval derived

The final theorem assumes Boolean-valuedness, balance, and an equality of
the actual noisy second moment. Fourier expansion and both Parseval identities
are derived from the actual function, not supplied as assumptions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Fourier

/--
@isnad1 id=eq.0h1v.s3.72d01ed2b02a from=translated src=- shape=a1232c14 vocab=9896a029
-/
theorem degree_zero : ∀ n, degree (fun _ : Fin n => false) = 0 := by
  intro n
  simp [degree, support]

/--
@isnad1 id=lt.1h2v.s4.7dec0c62418a from=translated src=- shape=84844805 vocab=6106af2f
-/
theorem degree_pos_of_ne_zero {n : ℕ} (s : Cube n) (hs : s ≠ (fun _ => false)) :
    0 < degree s := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ false := by
    by_contra! h
    exact hs (funext h)
  apply Finset.card_pos.mpr
  refine ⟨i, ?_⟩
  cases hsi : s i <;> simp_all [support]

/--
@isnad1 id=eq.0h2v.s4.76d83e142758 from=translated src=- shape=be902b59 vocab=b3bb0357
-/
theorem support_unit {n : ℕ} (i : Fin n) : support (unit i) = {i} := by
  ext j
  simp [support, unit]

/--
@isnad1 id=eq.0h2v.s4.0ed0a9bf9d5b from=translated src=- shape=5091f66c vocab=2a9052e1
-/
theorem degree_unit {n : ℕ} (i : Fin n) : degree (unit i) = 1 := by
  simp [degree, support_unit]

/--
@isnad1 id=injectiv.0h1v.s3.202496b3ef9f from=translated src=- shape=ca92e646 vocab=2529bfbf
-/
theorem unit_injective (n : ℕ) : Function.Injective (unit (n := n)) := by
  intro i j h
  have hs := congrArg support h
  simpa only [support_unit, Finset.singleton_inj] using hs

/--
@isnad1 id=iff.0h2v.s4.0c2519448e8b from=translated src=- shape=6bc0bd2d vocab=c3094ebf
-/
theorem degree_eq_one_iff {n : ℕ} (s : Cube n) :
    degree s = 1 ↔ ∃ i : Fin n, s = unit i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine ⟨i, ?_⟩
    apply (supportEquiv n).injective
    change support s = support (unit i)
    rw [hi, support_unit]
  · rintro ⟨i, rfl⟩
    exact degree_unit i

/--
@isnad1 id=eq.0h3v.s4.f62548029a0e from=translated src=- shape=6eda17d1 vocab=bbc627a2
-/
theorem phase_unit {n : ℕ} (i : Fin n) (x : Cube n) :
    phase (unit i) x = boolSign (x i) := by
  rw [phase_character, support_unit]
  simp [character]

/-- Higher Walsh coefficients vanish at equality of the actual noisy moment.
@isnad1 id=eq.7h4v.s7.6b59f588cf46 from=translated src=- shape=ea68d186 vocab=3d22c98c
-/
theorem high_walsh_eq_zero_of_noise_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) = ρ ^ 2)
    (s : Cube n) (hs : 1 < degree s) : walsh f s = 0 := by
  have hz : walsh f (fun _ => false) = 0 := by rw [walsh_zero, hm]
  have hnorm :
      (∑ t ∈ Finset.univ.erase (fun _ : Fin n => false), walsh f t ^ 2) = 1 := by
    rw [Finset.sum_erase _ (by rw [hz]; norm_num), boolean_parseval f hf]
  have hnoise :
      (∑ t ∈ Finset.univ.erase (fun _ : Fin n => false),
        ρ ^ (2 * degree t) * walsh f t ^ 2) = ρ ^ 2 := by
    rw [Finset.sum_erase _ (by rw [hz]; simp), ← noise_second_moment f ρ hρ, heq]
  apply Rigidity.coefficient_eq_zero_of_noise_parseval_equality degree (walsh f)
    ρ hρpos hρlt
    (fun t ht => degree_pos_of_ne_zero t (Finset.mem_erase.mp ht).1)
    hnorm hnoise
  · apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    subst s
    simp [degree_zero] at hs
  · exact hs

/--
@isnad1 id=eq.2h3v.s6.2d8793c0e85c from=translated src=- shape=f353edc1 vocab=45781d2c
-/
theorem linear_expansion_of_high_walsh_zero {n : ℕ} (f : Cube n → ℝ)
    (hm : mean f = 0) (hh : ∀ s, 1 < degree s → walsh f s = 0) (x : Cube n) :
    f x = ∑ i : Fin n, walsh f (unit i) * boolSign (x i) := by
  have hsub : Finset.univ.image (unit (n := n)) ⊆ (Finset.univ : Finset (Cube n)) :=
    Finset.subset_univ _
  have hvanish (s : Cube n) (hsmem : s ∈ Finset.univ)
      (hsnot : s ∉ Finset.univ.image (unit (n := n))) : walsh f s * phase s x = 0 := by
    have hneone : degree s ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := (degree_eq_one_iff s).mp h
      exact hsnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩)
    by_cases hs : s = (fun _ => false)
    · subst s
      rw [walsh_zero, hm, zero_mul]
    · have hpos := degree_pos_of_ne_zero s hs
      rw [hh s (by omega), zero_mul]
  calc
    f x = ∑ s, walsh f s * phase s x := inversion f x
    _ = ∑ s ∈ Finset.univ.image (unit (n := n)), walsh f s * phase s x :=
      (Finset.sum_subset hsub hvanish).symm
    _ = ∑ i : Fin n, walsh f (unit i) * boolSign (x i) := by
      rw [Finset.sum_image (fun i _ j _ h => unit_injective n h)]
      simp only [phase_unit]

/-- A balanced Boolean function attaining the dictator second moment is a
signed dictator. No Fourier coefficient identity is an input hypothesis.
@isnad1 id=ex.6h3v.s7.fb2966df9171 from=translated src=- shape=35ab0da2 vocab=d8cc46ec
-/
theorem signed_dictator_of_noise_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) = ρ ^ 2) :
    ∃ i : Fin n, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x, f x = a * boolSign (x i) := by
  have hlinear := linear_expansion_of_high_walsh_zero f hm
    (high_walsh_eq_zero_of_noise_equality f hf hm ρ hρ hρpos hρlt heq)
  have hbool : ∀ z : Fin n → ℝ, Rigidity.IsSignVector z →
      (∑ i, walsh f (unit i) * z i) ^ 2 = 1 := by
    intro z hz
    let x : Cube n := fun i => if z i = -1 then true else false
    have hx (i : Fin n) : boolSign (x i) = z i := by
      have hp : (z i - 1) * (z i + 1) = 0 := by nlinarith [hz i]
      rcases mul_eq_zero.mp hp with h | h
      · have hi : z i = 1 := by linarith
        norm_num [x, hi, boolSign]
      · have hi : z i = -1 := by linarith
        norm_num [x, hi, boolSign]
    have hxlinear := hlinear x
    simp only [hx] at hxlinear
    rw [← hxlinear]
    rcases hf x with h | h <;> simp [h]
  obtain ⟨i, hsign, hothers, hform⟩ :=
    Rigidity.boolean_linear_is_signed_coordinate (fun i => walsh f (unit i)) hbool
  refine ⟨i, walsh f (unit i), hsign, ?_⟩
  intro x
  rw [hlinear]
  exact hform (fun j => boolSign (x j))

end Hellinger.Fourier
