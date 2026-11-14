import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Laurent-coefficient interface for the pole at `t = -5`.

The regularized function is holomorphic at the pole; its normalized
derivatives are the Laurent coefficients used in Section 2.2.  The valuation
inequalities are proved in later files, after the finite binomial expansion is
introduced.
-/

namespace PiIrrationality

noncomputable def regularizedRat (n : ℕ) (t : ℚ) : ℚ :=
  5 * t ^ (2 * 1857 * n) * (t^4 + 6 * t^2 + 25) ^ (3714 * n) /
    (5 - t) ^ (5570 * n + 1)

/--
@isnad1 id=eq.2h2v.s6.1fa2783b8ee6 from=translated src=- shape=f666a64b vocab=51bad51d
-/
theorem regularizedRat_eq_mul (n : ℕ) (t : ℚ)
    (ht : t ≠ 5) (ht' : t ≠ -5) :
    regularizedRat n t = (t + 5) ^ (5570 * n + 1) * rationalFunction n t := by
  unfold regularizedRat rationalFunction
  have hfactor : 25 - t^2 = (t + 5) * (5 - t) := by ring
  rw [hfactor, mul_pow]
  have h₁ : t + 5 ≠ 0 := by
    intro h
    apply ht'
    linarith
  have h₂ : 5 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  field_simp [h₁, h₂]

noncomputable def regularized (n : ℕ) (t : ℝ) : ℝ :=
  5 * t ^ (2 * 1857 * n) * (t^4 + 6 * t^2 + 25) ^ (3714 * n) /
    (5 - t) ^ (5570 * n + 1)

noncomputable def regularizedZpowCore (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * 1857 * n) * (((t + 1)^2 + 4) ^ (3714 * n)) *
    (((t - 1)^2 + 4) ^ (3714 * n)) *
    (5 - t) ^ (-(5570 * n + 1) : ℤ)

/--
@isnad1 id=eq.0h1v.s5.eb7ddfa3de6d from=translated src=- shape=9c089c9c vocab=f52f69ae
-/
theorem regularizedZpowCore_at_pole_eq (n : ℕ) :
    5 * regularizedZpowCore n (-5) = regularized n (-5) := by
  unfold regularizedZpowCore regularized
  rw [zpow_neg]
  norm_num [zpow_natCast]
  field_simp
  have hexp : (5570 * (↑n : ℤ) + 1 : ℤ) = ((n * 5570 + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast, pow_add]
  rw [← mul_pow]
  rw [pow_add]
  ring

/--
@isnad1 id=eventual.0h1v.s5.9dccb4e4fb5b from=translated src=- shape=72a7a10f vocab=6a0aeaf7
-/
theorem regularized_eventuallyEq_ZpowCore (n : ℕ) :
    (regularized n) =ᶠ[nhds (-5 : ℝ)]
      (fun t => 5 * regularizedZpowCore n t) := by
  filter_upwards [eventually_ne_nhds (show (-5 : ℝ) ≠ 5 by norm_num)] with t ht
  unfold regularized regularizedZpowCore
  rw [zpow_neg]
  have hexp : (5570 * (n : ℤ) + 1 : ℤ) = ((5570 * n + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast]
  have hquartic : t^4 + 6 * t^2 + 25 =
      (((t + 1)^2 + 4) * ((t - 1)^2 + 4)) := by ring
  rw [hquartic]
  have hden : 5 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  field_simp [hden]
  rw [mul_pow]
  ring

/--
@isnad1 id=eq.0h2v.s7.49b3e2d9622b from=translated src=- shape=ebf2eefd vocab=c4f93383
-/
theorem regularized_quartic_factorization (n : ℕ) (t : ℝ) :
    regularized n t =
      5 * t ^ (2 * 1857 * n) *
        (((t + 1)^2 + 4) * ((t - 1)^2 + 4)) ^ (3714 * n) /
        (5 - t) ^ (5570 * n + 1) := by
  unfold regularized
  congr 2
  ring

/--
@isnad1 id=eq.0h2v.s8.2d390f58423f from=translated src=- shape=e42d9b3d vocab=c4f93383
-/
theorem regularized_six_factor_shape (n : ℕ) (t : ℝ) :
    regularized n t =
      5 * t ^ (2 * 1857 * n) *
        ((t + 1)^2 + 4) ^ (3714 * n) *
        ((t - 1)^2 + 4) ^ (3714 * n) /
        (5 - t) ^ (5570 * n + 1) := by
  rw [regularized_quartic_factorization, mul_pow]
  ring

noncomputable def normalizedDeriv (k : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  iteratedDeriv k f x / k.factorial

/--
@isnad1 id=eq.0h2v.s5.14f9535ec9d9 from=translated src=- shape=c8ea2b31 vocab=50d96531
-/
theorem normalizedDeriv_regularized_eq_ZpowCore (n k : ℕ) :
    normalizedDeriv k (regularized n) (-5) =
      5 * normalizedDeriv k (regularizedZpowCore n) (-5) := by
  unfold normalizedDeriv
  have hder := (regularized_eventuallyEq_ZpowCore n).iteratedDeriv_eq k
  rw [hder]
  rw [iteratedDeriv_const_mul_field]
  ring

/--
@isnad1 id=eq.0h3v.s7.8e1495502bab from=translated src=- shape=ec7d8cee vocab=23a3c86c
-/
theorem normalized_inv_linear_deriv (M k : ℕ) (x : ℝ) :
    normalizedDeriv k (fun t : ℝ => (5 - t) ^ (-M : ℤ)) x =
      ((-1 : ℝ) ^ k *
        (∏ i ∈ Finset.range k, ((-(M : ℝ)) - i)) *
        (5 - x) ^ (-(M : ℤ) - k)) / (k.factorial : ℝ) := by
  unfold normalizedDeriv
  have hcomp := iteratedDeriv_comp_const_sub k
    (fun z : ℝ => z ^ (-M : ℤ)) 5
  rw [congrFun hcomp x]
  simp only [smul_eq_mul]
  have hz : iteratedDeriv k (fun z : ℝ => z ^ (-M : ℤ)) (5 - x) =
      (∏ i ∈ Finset.range k, ((-(M : ℝ)) - i)) *
        (5 - x) ^ (-(M : ℤ) - k) := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
    norm_num
  rw [hz]
  ring

noncomputable def laurentCoeff (n : ℕ) (j : ℤ) : ℝ :=
  if j ≤ 5570 * n then
    normalizedDeriv (5570 * (n : ℤ) - j).toNat (regularized n) (-5)
  else 0

/--
@isnad1 id=ne.0h1v.s6.db69da089046 from=translated src=- shape=e27252e4 vocab=7d7e4cc9
-/
theorem regularized_denominator_at_pole (n : ℕ) :
    (5 - (-5 : ℝ)) ^ (5570 * n + 1) ≠ 0 := by
  norm_num

/--
@isnad1 id=contdiff.0h1v.s5.205f643f176a from=translated src=- shape=09cecdbf vocab=652cd26d
-/
theorem regularized_contDiffAt (n : ℕ) :
    ContDiffAt ℝ ⊤ (regularized n) (-5) := by
  unfold regularized
  have hden : (5 - (-5 : ℝ)) ^ (5570 * n + 1) ≠ 0 := by
    norm_num
  fun_prop (disch := aesop)

/--
@isnad1 id=ex.0h2v.s3.280ac09dbff6 from=translated src=- shape=6e13a134 vocab=efa781d9
-/
theorem laurentCoeff_is_real (n : ℕ) (j : ℤ) :
    ∃ x : ℝ, laurentCoeff n j = x := by
  exact ⟨laurentCoeff n j, rfl⟩

/--
@isnad1 id=eq.1h2v.s6.7ab2793388d0 from=translated src=- shape=b6f08299 vocab=7f642c73
-/
theorem laurentCoeff_eq_iteratedDeriv (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ 5570 * n) :
    laurentCoeff n j =
      iteratedDeriv (5570 * n - j.toNat) (regularized n) (-5) /
        (5570 * n - j.toNat).factorial := by
  have horder : (5570 * (n : ℤ) - j).toNat = 5570 * n - j.toNat := by omega
  simp only [laurentCoeff, ite_eq_left hj.2, normalizedDeriv, horder]

/--
@isnad1 id=eq.1h2v.s6.08c67c18f7e2 from=translated src=- shape=c5e77a1c vocab=518821fc
-/
theorem laurentCoeff_eq_normalizedDeriv (n : ℕ) (j : ℤ)
    (hj : j ≤ 5570 * (n : ℤ)) :
    laurentCoeff n j =
      normalizedDeriv (5570 * (n : ℤ) - j).toNat (regularized n) (-5) := by
  simp only [laurentCoeff, ite_eq_left hj]

/--
@isnad1 id=eq.0h2v.s5.03ca17cd1632 from=translated src=- shape=fadd9bcd vocab=a95bd338
-/
theorem laurentCoeff_neg_eq_normalizedDeriv (n k : ℕ) :
    laurentCoeff n (-(k : ℤ)) =
      normalizedDeriv (5570 * n + k) (regularized n) (-5) := by
  have hj : -(k : ℤ) ≤ 5570 * (n : ℤ) := by omega
  have horder : (5570 * (n : ℤ) - -(k : ℤ)).toNat = 5570 * n + k := by omega
  rw [laurentCoeff_eq_normalizedDeriv n _ hj, horder]

/--
@isnad1 id=eq.1h2v.s6.ff1d3f0bded7 from=translated src=- shape=95090882 vocab=d4997dff
-/
theorem laurentCoeff_eq_normalizedZpowCore (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ 5570 * n) :
    laurentCoeff n j =
      5 * normalizedDeriv (5570 * n - j.toNat)
        (regularizedZpowCore n) (-5) := by
  rw [laurentCoeff_eq_iteratedDeriv n j hj]
  change normalizedDeriv (5570 * n - j.toNat) (regularized n) (-5) = _
  rw [normalizedDeriv_regularized_eq_ZpowCore]

/--
@isnad1 id=eq.1h2v.s5.54797ace2577 from=translated src=- shape=1254084d vocab=91bca46f
-/
theorem laurentCoeff_zero_of_outside (n : ℕ) (j : ℤ)
    (h : 5570 * (n : ℤ) < j) : laurentCoeff n j = 0 := by
  simp only [laurentCoeff, ite_eq_right (not_le.mpr h)]

/--
@isnad1 id=eq.0h0v.s5.9029f041ab1d from=translated src=- shape=ed69ff62 vocab=f76351c6
-/
theorem laurentCoeff_zero_zero : laurentCoeff 0 0 = (1 : ℝ) / 2 := by
  simp [laurentCoeff, normalizedDeriv, regularized]
  norm_num

/--
@isnad1 id=eq.0h0v.s5.a797d3b75cbd from=translated src=- shape=61d8315b vocab=05c2ec17
-/
theorem laurentCoeff_zero_neg_one : laurentCoeff 0 (-1) = (1 : ℝ) / 20 := by
  have hreg : regularized 0 = (fun t : ℝ => 5 / (5 - t)) := by
    funext t
    simp [regularized]
  have hd : HasDerivAt (fun t : ℝ => 5 / (5 - t)) ((1 : ℝ) / 20) (-5) := by
    convert! (hasDerivAt_const (-5 : ℝ) (5 : ℝ)).div
      ((hasDerivAt_const (-5 : ℝ) (5 : ℝ)).sub (hasDerivAt_id (-5)))
      (by norm_num) using 1 <;> norm_num [Pi.div_apply, Pi.sub_apply, id_eq]
  change laurentCoeff 0 (-(1 : ℕ) : ℤ) = _
  rw [laurentCoeff_neg_eq_normalizedDeriv, hreg]
  norm_num [normalizedDeriv, iteratedDeriv_one, hd.deriv]

/--
@isnad1 id=eq.0h1v.s5.d3044c382180 from=translated src=- shape=df1643fc vocab=e7a461cb
-/
theorem laurentCoeff_top (n : ℕ) :
    laurentCoeff n (5570 * n : ℤ) = regularized n (-5) := by
  simp [laurentCoeff, normalizedDeriv]

/--
@isnad1 id=eq.0h1v.s7.8faa44c4dcd7 from=translated src=- shape=b0e149cc vocab=243f3d33
-/
theorem regularized_at_pole_eq (n : ℕ) :
    regularized n (-5) =
      5 * (5 : ℝ) ^ (2 * 1857 * n) * (800 : ℝ) ^ (3714 * n) /
        (10 : ℝ) ^ (5570 * n + 1) := by
  unfold regularized
  norm_num

/--
@isnad1 id=lt.0h1v.s4.66fc5aa71e90 from=translated src=- shape=07da37f9 vocab=749337d9
-/
theorem regularized_at_pole_pos (n : ℕ) : 0 < regularized n (-5) := by
  rw [regularized_at_pole_eq]
  have hfive : 0 < (5 : ℝ) ^ (2 * 1857 * n) := by positivity
  have height : 0 < (800 : ℝ) ^ (3714 * n) := by positivity
  have hten : 0 < (10 : ℝ) ^ (5570 * n + 1) := by positivity
  positivity

/--
@isnad1 id=lt.0h1v.s4.de55719e250e from=translated src=- shape=d23c8ed4 vocab=91bca46f
-/
theorem laurentCoeff_top_pos (n : ℕ) :
    0 < laurentCoeff n (5570 * n : ℤ) := by
  rw [laurentCoeff_top]
  exact regularized_at_pole_pos n

end PiIrrationality
