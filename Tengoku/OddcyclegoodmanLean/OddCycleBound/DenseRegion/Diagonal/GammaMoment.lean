import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set Real
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/--
@isnad1 id=eq.0h1v.s6.2a94ce286193 from=translated src=- shape=5c0d35c2 vocab=db1a0472
-/
lemma intPowExp (k : ℕ) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ k * Real.exp (-y) = (Nat.factorial k : ℝ) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 1) (by positivity) one_pos
  rw [one_div, inv_one, Real.one_rpow, one_mul, show (k : ℝ) + 1 - 1 = (k : ℝ) from by ring,
      Real.Gamma_nat_eq_factorial] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  rw [Real.rpow_natCast, one_mul]

/--
@isnad1 id=eq.2h2v.s7.3570fa3ebd68 from=translated src=- shape=27da401c vocab=ab14d9c8
-/
lemma intPowExpMul (m : ℕ) (hm : 1 ≤ m) (w : ℝ) (hw : 0 < w) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (m - 1) * Real.exp (-(w * t))
      = (Nat.factorial (m - 1) : ℝ) / w ^ m := by
  have hΓ : Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) := by
    rw [show (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 from by rw [Nat.cast_sub hm]; ring,
      Real.Gamma_nat_eq_factorial]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ)) (r := w) (by positivity) hw
  have hRHS : (1 / w) ^ (m : ℝ) * Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) / w ^ m := by
    rw [hΓ, Real.rpow_natCast, div_pow, one_pow]; ring
  rw [hRHS] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [show (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) from by rw [Nat.cast_sub hm, Nat.cast_one],
    Real.rpow_natCast]

noncomputable def gExp (r : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * f y

/--
@isnad1 id=integrab.0h2v.s6.ca0e5beeb3b2 from=translated src=- shape=23be5c71 vocab=cb1f8ebf
-/
lemma gExp_integrableOn (r i : ℕ) :
    IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * y ^ i) (Set.Ioi (0 : ℝ)) := by
  have hconv := Real.GammaIntegral_convergent (s := ((r - 1 + i : ℕ) : ℝ) + 1) (by positivity)
  refine hconv.congr_fun (fun y hy => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hy
  have he : ((r - 1 + i : ℕ) : ℝ) + 1 - 1 = ((r - 1 + i : ℕ) : ℝ) := by ring
  simp only [he, Real.rpow_natCast, pow_add]
  ring

/--
@isnad1 id=eq.0h2v.s5.614792c0917a from=translated src=- shape=74fa98ed vocab=ffb37f81
-/
lemma gExp_monomial (r i : ℕ) :
    gExp r (fun y => y ^ i) = (Nat.factorial (r - 1 + i) : ℝ) := by
  unfold gExp
  rw [show (∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * y ^ i)
        = ∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1 + i) * Real.exp (-y) from ?_, intPowExp]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [pow_add]; ring

/--
@isnad1 id=le.1h2v.s5.86e6a338e75b from=translated src=- shape=4734c104 vocab=b142c3be
-/
lemma gExp_nonneg (r : ℕ) (f : ℝ → ℝ) (hf : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ f y) :
    0 ≤ gExp r f := by
  refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  exact mul_nonneg (mul_nonneg (pow_nonneg hy.le _) (Real.exp_pos _).le) (hf y (Set.mem_Ioi.mpr hy))

/--
@isnad1 id=eq.0h3v.s5.3452cf514f8c from=translated src=- shape=6c70e6bd vocab=a89a4eb4
-/
lemma gExp_const_mul (r : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    gExp r (fun y => c * f y) = c * gExp r f := by
  unfold gExp
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/--
@isnad1 id=integrab.0h4v.s6.8814ec814567 from=translated src=- shape=5b5ec15f vocab=d9533f7d
-/
lemma gExp_affinePow_integrableOn (r k : ℕ) (a b : ℝ) :
    IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * (a * y + b) ^ k) (Set.Ioi (0 : ℝ)) := by
  have hrw : (fun y => y ^ (r - 1) * Real.exp (-y) * (a * y + b) ^ k)
      = fun y => ∑ i ∈ Finset.range (k + 1),
          ((Nat.choose k i : ℝ) * a ^ i * b ^ (k - i)) * (y ^ (r - 1) * Real.exp (-y) * y ^ i) := by
    funext y
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow]; ring
  rw [hrw]
  exact integrable_finsetSum _ (fun i _ => (gExp_integrableOn r i).const_mul _)

/--
@isnad1 id=eq.2h3v.s7.fdf38d9ada20 from=translated src=- shape=f2553183 vocab=1235fbba
-/
lemma gExp_add (r : ℕ) (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * f y) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * g y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => f y + g y) = gExp r f + gExp r g := by
  unfold gExp
  rw [← MeasureTheory.integral_add hf hg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/--
@isnad1 id=eq.2h3v.s7.c67fa11fb46f from=translated src=- shape=6cd297d2 vocab=4d60281b
-/
lemma gExp_sub (r : ℕ) (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * f y) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * g y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => f y - g y) = gExp r f - gExp r g := by
  unfold gExp
  rw [← MeasureTheory.integral_sub hf hg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/--
@isnad1 id=eq.1h4v.s7.83ab69dae377 from=translated src=- shape=f49d1c75 vocab=d9a0f17e
-/
lemma gExp_finset_sum {ι : Type*} (r : ℕ) (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * F i y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, gExp r (F i) := by
  unfold gExp
  rw [← MeasureTheory.integral_finsetSum s hF]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [Finset.mul_sum]

end OddCycleBound.DenseRegion
