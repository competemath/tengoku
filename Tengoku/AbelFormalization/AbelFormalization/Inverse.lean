import Tengoku.AbelFormalization.AbelFormalization.Basic
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The inverse of an Abel function

The inverse and its recurrence are derived from the paper's hypotheses.
No surjectivity or inverse-function hypotheses are added.
-/

noncomputable section

namespace AbelFormalization

open Set Function

/-- The inverse dynamical map on the positive half-line.-/
def L (x : ℝ) : ℝ := Real.log (1 + x)

/--
@isnad1 id=lt.1h1v.s4.b45d48917b37 from=translated src=- shape=35bd48ee vocab=4ba4ebe5
-/
theorem L_pos {x : ℝ} (hx : 0 < x) : 0 < L x := by
  exact Real.log_pos (by linarith)

/--
@isnad1 id=eq.1h1v.s4.c15ef4017021 from=translated src=- shape=cc7bc718 vocab=4d408cc2
-/
theorem E_L {x : ℝ} (hx : 0 < x) : E (L x) = x := by
  unfold E L
  rw [Real.exp_log (by linarith : 0 < 1 + x)]
  ring

/--
@isnad1 id=lt.1h2v.s4.d8b06f9e62f3 from=translated src=- shape=adab10c0 vocab=6b460cf8
-/
theorem L_iterate_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < L^[n] x := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using L_pos ih

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/--
@isnad1 id=eq.2h2v.s5.f8c4095ea988 from=translated src=- shape=73dbd7fb vocab=2ea8dd90
-/
theorem abel_L {x : ℝ} (hx : 0 < x) : A (L x) = A x - 1 := by
  have h := hA.abel (L x) (L_pos hx)
  rw [E_L hx] at h
  linarith

/--
@isnad1 id=eq.2h3v.s5.2958c8465a7d from=translated src=- shape=df9e845a vocab=27d19806
-/
theorem abel_L_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    A (L^[n] x) = A x - n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hA.abel_L (L_iterate_pos hx n), ih]
      push_cast
      ring

/-- Every real number is attained at a positive argument.
@isnad1 id=surjon.1h1v.s4.b4ed8c9a9a97 from=translated src=- shape=fa253e92 vocab=2fdb6b9b
-/
theorem surjOn : Set.SurjOn A (Set.Ioi 0) Set.univ := by
  intro y _
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  have hlo : A (L^[n] 1) = -(n : ℝ) := by
    rw [hA.abel_L_iterate (by norm_num : (0 : ℝ) < 1), hA.normalized]
    ring
  have hhi : A (E^[n] 1) = (n : ℝ) := by
    rw [hA.abel_iterate (by norm_num : (0 : ℝ) < 1), hA.normalized]
    ring
  apply hA.analytic.continuousOn.surjOn_Icc
    (L_iterate_pos (by norm_num : (0 : ℝ) < 1) n)
    (E_iterate_pos (by norm_num : (0 : ℝ) < 1) n)
  constructor
  · rw [hlo]
    have := neg_abs_le y
    linarith
  · rw [hhi]
    exact (le_abs_self y).trans hn.le

/--
@isnad1 id=bijon.1h1v.s4.e5f3c7b2112b from=translated src=- shape=fa253e92 vocab=a216ba34
-/
theorem bijOn : Set.BijOn A (Set.Ioi 0) Set.univ :=
  ⟨fun _ _ => Set.mem_univ _, hA.injectiveOn, hA.surjOn⟩

end IsAbel

/-- The inverse of `A` on its positive domain.-/
def inverse (A : ℝ → ℝ) : ℝ → ℝ := Function.invFunOn A (Set.Ioi 0)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/--
@isnad1 id=lt.1h2v.s4.b7b9297b74a2 from=translated src=- shape=c3193f73 vocab=a1c0723f
-/
theorem inverse_pos (s : ℝ) : 0 < inverse A s :=
  Function.invFunOn_mem (hA.surjOn (Set.mem_univ s))

/--
@isnad1 id=eq.1h2v.s4.3f1ce06921d7 from=translated src=- shape=a0abe01b vocab=4add97a2
-/
theorem apply_inverse (s : ℝ) : A (inverse A s) = s :=
  Function.invFunOn_eq (hA.surjOn (Set.mem_univ s))

/--
@isnad1 id=eq.2h2v.s4.672a57e36da8 from=translated src=- shape=07d6dae6 vocab=a1c0723f
-/
theorem inverse_apply {x : ℝ} (hx : 0 < x) : inverse A (A x) = x :=
  hA.injectiveOn.leftInvOn_invFunOn hx

/--
@isnad1 id=strictmo.1h1v.s3.8461f446945c from=translated src=- shape=1e8957a6 vocab=d32c04a1
-/
theorem inverse_strictMono : StrictMono (inverse A) := by
  intro a b hab
  by_contra h
  have hle := le_of_not_gt h
  have he := hA.strictMonoOn.monotoneOn (hA.inverse_pos b) (hA.inverse_pos a) hle
  rw [hA.apply_inverse, hA.apply_inverse] at he
  exact (not_le_of_gt hab) he

/--
@isnad1 id=eq.1h1v.s4.0857c4ccea6e from=translated src=- shape=f70a2079 vocab=4add97a2
-/
theorem inverse_zero : inverse A 0 = 1 := by
  rw [← hA.normalized]
  exact hA.inverse_apply (by norm_num)

/--
@isnad1 id=eq.1h2v.s5.8363b33f9ac5 from=translated src=- shape=4159b952 vocab=a2ccdcf0
-/
theorem inverse_add_one (s : ℝ) : inverse A (s + 1) = Real.exp (inverse A s) - 1 := by
  apply hA.injectiveOn (hA.inverse_pos (s + 1)) (E_pos (hA.inverse_pos s))
  rw [hA.apply_inverse, hA.abel _ (hA.inverse_pos s), hA.apply_inverse]

/--
@isnad1 id=lt.2h2v.s5.e0fc1686c005 from=translated src=- shape=604cafe9 vocab=a1c0723f
-/
theorem one_lt_inverse {s : ℝ} (hs : 0 < s) : 1 < inverse A s := by
  simpa only [hA.inverse_zero] using hA.inverse_strictMono hs

/--
@isnad1 id=iff.1h3v.s5.2d8f9d7c85d4 from=translated src=- shape=101a1380 vocab=a1c0723f
-/
theorem inverse_eq_iff {s x : ℝ} :
    inverse A s = x ↔ 0 < x ∧ A x = s := by
  constructor
  · rintro rfl
    exact ⟨hA.inverse_pos s, hA.apply_inverse s⟩
  · rintro ⟨hx, he⟩
    rw [← he]
    exact hA.inverse_apply hx

/--
@isnad1 id=iff.2h3v.s5.e6256592db19 from=translated src=- shape=75173c04 vocab=a1c0723f
-/
theorem inverse_eq_iff_of_pos {s x : ℝ} (hs : 0 < s) :
    inverse A s = x ↔ 1 < x ∧ A x = s := by
  constructor
  · rintro rfl
    exact ⟨hA.one_lt_inverse hs, hA.apply_inverse s⟩
  · rintro ⟨hx, he⟩
    exact hA.inverse_eq_iff.mpr ⟨lt_trans (by norm_num) hx, he⟩

end IsAbel

end AbelFormalization
