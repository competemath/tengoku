import Tengoku.Piirrationalitymeasure.Formalization.HataSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The least-index construction from (5.6)--(5.7).  These lemmas isolate the
discrete part of Hata's scale selection from the later approximation bounds.
-/

namespace PiIrrationality

open Filter
open scoped Topology

/--
@isnad1 id=ex.1h2v.s5.27b8d5d88013 from=translated src=- shape=892233a8 vocab=58c09719
-/
theorem exists_hata_scale (q : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ n : ℕ, (2 * q : ℝ) < Real.exp (a * (n : ℝ)) := by
  have hlin : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => Real.exp (a * (n : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  exact hexp.eventually_gt_atTop (2 * (q : ℝ)) |>.exists

noncomputable def hataScale (q : ℕ) (a : ℝ) (ha : 0 < a) : ℕ :=
  Nat.find (exists_hata_scale q ha)

/--
@isnad1 id=lt.1h2v.s5.85c6fec9ea57 from=translated src=- shape=5a397f76 vocab=6b2f5578
-/
theorem hataScale_spec (q : ℕ) {a : ℝ} (ha : 0 < a) :
    (2 * q : ℝ) < Real.exp (a * (hataScale q a ha : ℝ)) :=
  Nat.find_spec (exists_hata_scale q ha)

/--
@isnad1 id=lt.2h2v.s5.3d70fcecb72a from=translated src=- shape=802ec817 vocab=55f6ecb6
-/
theorem hataScale_pos (q : ℕ) {a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    0 < hataScale q a ha := by
  apply Nat.pos_of_ne_zero
  intro hN
  have hspec := hataScale_spec q ha
  simp [hN] at hspec
  have hq' : (1 : ℝ) ≤ q := by
    exact_mod_cast (show 1 ≤ q by omega)
  linarith

/--
@isnad1 id=and.2h2v.s6.3c0b7626e0bb from=translated src=- shape=186a3496 vocab=4b5faa96
-/
theorem hataScale_prev_spec (q : ℕ) {a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    Real.exp (a * ((hataScale q a ha - 1 : ℕ) : ℝ)) ≤ (2 * q : ℝ) ∧
      (2 * q : ℝ) < Real.exp (a * (hataScale q a ha : ℝ)) := by
  let N := hataScale q a ha
  have hN : 0 < N := hataScale_pos q hq ha
  have hupper : (2 * q : ℝ) < Real.exp (a * (N : ℝ)) := by
    exact hataScale_spec q ha
  have hmin : ¬ (2 * q : ℝ) < Real.exp (a * ((N - 1 : ℕ) : ℝ)) := by
    intro h
    have hle := Nat.find_min (exists_hata_scale q ha)
      (show N - 1 < Nat.find (exists_hata_scale q ha) by
        have hfind : 0 < Nat.find (exists_hata_scale q ha) := by
          simpa [hataScale] using hataScale_pos q hq ha
        change Nat.find (exists_hata_scale q ha) - 1 <
          Nat.find (exists_hata_scale q ha)
        exact Nat.sub_lt hfind (by decide))
    exact hle h
  constructor
  · exact le_of_not_gt hmin
  · exact hupper

/--
@isnad1 id=le.2h3v.s6.9b70722bdd56 from=translated src=- shape=4ad40581 vocab=4b5faa96
-/
theorem hataScale_ge_of_threshold (q n0 : ℕ) {a : ℝ} (ha : 0 < a)
    (hthreshold : Real.exp (a * ((n0 - 1 : ℕ) : ℝ)) ≤ (2 * q : ℝ)) :
    n0 ≤ hataScale q a ha := by
  let N := hataScale q a ha
  by_contra hN
  have hNlt : N < n0 := Nat.lt_of_not_ge hN
  have hmon : Monotone (fun n : ℕ => Real.exp (a * (n : ℝ))) := by
    intro m n hmn
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) ha.le
  have hle : Real.exp (a * (N : ℝ)) ≤
      Real.exp (a * ((n0 - 1 : ℕ) : ℝ)) := by
    apply hmon
    omega
  have hupper := hataScale_spec q ha
  linarith

/--
@isnad1 id=lt.2h3v.s6.d7540a2b4e95 from=translated src=- shape=5fd5880b vocab=f620e61c
-/
theorem hataScale_tail_small (q n : ℕ) {a : ℝ} (ha : 0 < a)
    (hNn : hataScale q a ha ≤ n) :
    (q : ℝ) * Real.exp (-a * (n : ℝ)) < (1 : ℝ) / 2 := by
  have hmono : Monotone (fun k : ℕ => Real.exp (a * (k : ℝ))) := by
    intro m k hmk
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmk) ha.le
  have hscale : (2 * q : ℝ) < Real.exp (a * (n : ℝ)) := by
    exact (hataScale_spec q ha).trans_le (hmono hNn)
  have hexppos : 0 < Real.exp (a * (n : ℝ)) := Real.exp_pos _
  have hdiv : (q : ℝ) / Real.exp (a * (n : ℝ)) < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ hexppos).2
    linarith
  have hexpneg : Real.exp (-a * (n : ℝ)) =
      (Real.exp (a * (n : ℝ)))⁻¹ := by
    rw [show -a * (n : ℝ) = -(a * (n : ℝ)) by ring, Real.exp_neg]
  calc
    (q : ℝ) * Real.exp (-a * (n : ℝ)) =
        (q : ℝ) / Real.exp (a * (n : ℝ)) := by
      rw [hexpneg, div_eq_mul_inv]
    _ < (1 : ℝ) / 2 := hdiv

/--
@isnad1 id=le.2h2v.s6.8b810fc4121c from=translated src=- shape=18002ad2 vocab=f9956d66
-/
theorem hataScale_exp_upper (q : ℕ) {a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    Real.exp (hataScale q a ha : ℝ) ≤
      Real.exp 1 * (2 * q : ℝ) ^ (1 / a) := by
  let N := hataScale q a ha
  have hNpos : 0 < N := hataScale_pos q hq ha
  have hprev := (hataScale_prev_spec q hq ha).1
  have hqpos : 0 < (2 * q : ℝ) := by positivity
  have hlog : a * ((N : ℝ) - 1) ≤ Real.log (2 * q : ℝ) := by
    apply (Real.le_log_iff_exp_le hqpos).2
    have hprev' : Real.exp (a * ((N - 1 : ℕ) : ℝ)) ≤ (2 * q : ℝ) := by
      simpa [N] using hprev
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hNpos.ne')]
      norm_num
    rw [hcast] at hprev'
    exact hprev'
  have hNle : (N : ℝ) ≤ 1 + Real.log (2 * q : ℝ) / a := by
    rw [show 1 + Real.log (2 * q : ℝ) / a =
        (a + Real.log (2 * q : ℝ)) / a by field_simp]
    apply (le_div_iff₀ ha).2
    nlinarith [hlog]
  have hexp := Real.exp_le_exp.mpr hNle
  calc
    Real.exp (N : ℝ) ≤ Real.exp (1 + Real.log (2 * q : ℝ) / a) := hexp
    _ = Real.exp 1 * (2 * q : ℝ) ^ (1 / a) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hqpos]
      congr 1
      ring

end PiIrrationality
