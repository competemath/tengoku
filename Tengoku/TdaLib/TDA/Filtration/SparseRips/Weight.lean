import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sparse Rips vertex weights

A vertex with finite deletion time `t` has weight zero until `(1 - 2 * η) * t`,
then increases with slope one half until `t`, and subsequently has weight `η * r`.
The first vertex is represented by deletion time `none` and always has weight zero.
-/

namespace TDA.Filtration.SparseRips

noncomputable section

/-- The three branches use the closed lower breakpoint and closed deletion breakpoint.-/
def finiteWeight (η t r : ℝ) : ℝ :=
  if r ≤ (1 - 2 * η) * t then 0
  else if r < t then (r - (1 - 2 * η) * t) / 2 else η * r

/--
@isnad1 id=eq.1h3v.s5.e9c29430c5ae from=translated src=- shape=0bfe7306 vocab=00162de9
-/
@[simp] theorem finiteWeight_of_le {η t r : ℝ} (h : r ≤ (1 - 2 * η) * t) :
    finiteWeight η t r = 0 := by simp [finiteWeight, h]

/--
@isnad1 id=eq.2h3v.s6.342dd3d2724f from=translated src=- shape=9c3cf52b vocab=1a4c68d2
-/
theorem finiteWeight_of_between {η t r : ℝ}
    (h₁ : (1 - 2 * η) * t < r) (h₂ : r < t) :
    finiteWeight η t r = (r - (1 - 2 * η) * t) / 2 := by
  simp [finiteWeight, not_le.mpr h₁, h₂]

/--
@isnad1 id=eq.3h3v.s5.5c46735e57eb from=translated src=- shape=bd0b3c64 vocab=d628a553
-/
theorem finiteWeight_of_time_le {η t r : ℝ} (hη : 0 ≤ η) (ht : 0 ≤ t) (h : t ≤ r) :
    finiteWeight η t r = η * r := by
  unfold finiteWeight
  split_ifs with hb
  · have hηt := mul_nonneg hη ht
    have htr : t = r := by nlinarith
    have hzero : η * r = 0 := by rw [← htr]; nlinarith
    exact hzero.symm
  · linarith
  · rfl

/--
@isnad1 id=le.2h3v.s5.34c410e8ad31 from=translated src=- shape=a1784887 vocab=f8db6d13
-/
theorem finiteWeight_nonneg {η t r : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r) :
    0 ≤ finiteWeight η t r := by
  unfold finiteWeight
  split_ifs <;> first | positivity | linarith

/--
@isnad1 id=le.3h3v.s6.caa514a32711 from=translated src=- shape=75ddec65 vocab=09fcd615
-/
theorem finiteWeight_le {η t r : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hr : 0 ≤ r) : finiteWeight η t r ≤ η * r := by
  unfold finiteWeight
  split_ifs with h₁ h₂
  · positivity
  · have hprod := mul_nonneg (show 0 ≤ 1 - 2 * η by linarith) (show 0 ≤ t - r by linarith)
    nlinarith
  · exact le_rfl

/-- The weight's forward change lies between zero and half the change in scale.
@isnad1 id=and.5h4v.s7.f00969c6e928 from=translated src=- shape=e3a74d63 vocab=811c2fa5
-/
theorem finiteWeight_increment {η t r s : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    0 ≤ finiteWeight η t s - finiteWeight η t r ∧
      finiteWeight η t s - finiteWeight η t r ≤ (s - r) / 2 := by
  have hp := mul_nonneg hη (show 0 ≤ s - r by linarith)
  have hq := mul_nonneg (show 0 ≤ 1 / 2 - η by linarith) (show 0 ≤ s - r by linarith)
  have hηt := mul_nonneg hη ht
  unfold finiteWeight
  split_ifs <;> constructor <;> nlinarith

/-- `none` records the immortal vertex without coercing infinity to a real number.-/
def weight (η : ℝ) (time : Option ℝ) (r : ℝ) : ℝ :=
  time.elim 0 (fun t => finiteWeight η t r)

/--
@isnad1 id=eq.0h2v.s4.d2e790ff2827 from=translated src=- shape=c9b1a7ff vocab=4f5e9cdb
-/
@[simp] theorem weight_none (η r : ℝ) : weight η none r = 0 := rfl

/--
@isnad1 id=eq.0h3v.s4.8ea0d4bc8b77 from=translated src=- shape=8a9272f6 vocab=1d64e341
-/
@[simp] theorem weight_some (η t r : ℝ) : weight η (some t) r = finiteWeight η t r := rfl

/--
@isnad1 id=le.2h3v.s5.eae3e38689b6 from=translated src=- shape=dcaf25b0 vocab=99267db2
-/
theorem weight_nonneg {η r : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r) (time : Option ℝ) :
    0 ≤ weight η time r := by
  cases time with
  | none => simp
  | some t => exact finiteWeight_nonneg hη hr

/--
@isnad1 id=le.3h3v.s6.5f82d9a80535 from=translated src=- shape=3b3befe7 vocab=b390bb7d
-/
theorem weight_le {η r : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (hr : 0 ≤ r)
    (time : Option ℝ) : weight η time r ≤ η * r := by
  cases time with
  | none => simpa using mul_nonneg hη hr
  | some t => exact finiteWeight_le hη hη' hr

/--
@isnad1 id=and.5h4v.s7.c9d31e1b5592 from=translated src=- shape=b0594847 vocab=778d7206
-/
theorem weight_increment {η r s : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (time : Option ℝ) (ht : ∀ t ∈ time, 0 ≤ t) (hr : 0 ≤ r) (hrs : r ≤ s) :
    0 ≤ weight η time s - weight η time r ∧
      weight η time s - weight η time r ≤ (s - r) / 2 := by
  cases time with
  | none => simp only [weight_none, sub_self, le_refl, true_and]; linarith
  | some t => exact finiteWeight_increment hη hη' (ht t (by simp)) hr hrs

end

end TDA.Filtration.SparseRips
