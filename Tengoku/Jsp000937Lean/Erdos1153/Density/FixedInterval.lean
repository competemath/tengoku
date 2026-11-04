import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.Analysis.Complex.Exponential
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Nat.Factorial.BigOperators
import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.Topology.Algebra.Polynomial
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial growth from a fixed subinterval

This file proves the fixed-interval exponential growth estimate needed by the
damping argument.  The proof is elementary Lagrange interpolation at equally
spaced points; in particular it does not assume a Remez theorem.
-/

namespace Erdos1153.Density

open Polynomial Finset Set

noncomputable section

/-- The `i`th of `d+1` equally spaced nodes in `[u,v]`.  This definition is
used only with `0 < d` and `i ≤ d`.-/
def equiNode (u v : ℝ) (d i : ℕ) : ℝ :=
  u + (v - u) * ((i : ℝ) / (d : ℝ))

/--
@isnad1 id=eq.1h5v.s6.f3b7f5ab85a7 from=translated src=- shape=aee15aa8 vocab=b7debaea
-/
lemma equiNode_sub_equiNode {u v : ℝ} {d i j : ℕ} (hd : 0 < d) :
    equiNode u v d i - equiNode u v d j =
      ((v - u) / d) * ((i : ℝ) - j) := by
  simp only [equiNode]
  field_simp
  ring

/--
@isnad1 id=injon.2h3v.s5.74e78c39934d from=translated src=- shape=284b243c vocab=cef61fbe
-/
lemma equiNode_injOn {u v : ℝ} {d : ℕ} (hd : 0 < d) (huv : u < v) :
    Set.InjOn (equiNode u v d) (Finset.range (d + 1)) := by
  intro i _ j _ hij
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale : (v - u) / (d : ℝ) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr huv.ne') hdR.ne'
  have hdiff : ((v - u) / d) * ((i : ℝ) - j) = 0 := by
    rw [← equiNode_sub_equiNode hd, hij, sub_self]
  have hcast : (i : ℝ) - j = 0 := by
    rcases mul_eq_zero.mp hdiff with hs | hij'
    · exact (hscale hs).elim
    · exact hij'
  have : (i : ℝ) = j := sub_eq_zero.mp hcast
  exact_mod_cast this

/--
@isnad1 id=mem.3h4v.s5.2eda31d54f72 from=translated src=- shape=49028240 vocab=deca7872
-/
lemma equiNode_mem_Icc {u v : ℝ} {d i : ℕ} (hd : 0 < d)
    (huv : u ≤ v) (hi : i ≤ d) : equiNode u v d i ∈ Set.Icc u v := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hiR : (0 : ℝ) ≤ (i : ℝ) / d := div_nonneg (by positivity) hdR.le
  have hiOne : (i : ℝ) / d ≤ 1 := (div_le_one hdR).2 (by exact_mod_cast hi)
  constructor <;> simp only [equiNode]
  · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr huv) hiR)
  · nlinarith [mul_le_mul_of_nonneg_left hiOne (sub_nonneg.mpr huv)]

/-- The exact product of the integer spacings from the `i`th point of a
`d+1` point grid.  This is the factorial cancellation that keeps the
Lagrange estimate exponential rather than superexponential.
@isnad1 id=eq.1h2v.s6.3c976f1dc0e9 from=translated src=- shape=b5f39dbd vocab=b6bf7af4
-/
lemma prod_abs_cast_sub_eq_factorials {d i : ℕ} (hi : i ≤ d) :
    (∏ j ∈ (Finset.range (d + 1)).erase i, |(i : ℝ) - (j : ℝ)|) =
      (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by
  have hunion : (Finset.range (d + 1)).erase i =
      Finset.range i ∪ Finset.Ioc i d := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.range i) (Finset.Ioc i d) := by
    exact Finset.disjoint_left.mpr fun j hjr hji =>
      (Nat.not_lt_of_ge (Finset.mem_Ioc.mp hji).1.le) (Finset.mem_range.mp hjr)
  have hleft : (∏ j ∈ Finset.range i, |(i : ℝ) - (j : ℝ)|) =
      (i.factorial : ℝ) := by
    calc
      (∏ j ∈ Finset.range i, |(i : ℝ) - (j : ℝ)|) =
          ∏ j ∈ Finset.range i, ((i - j : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≤ i := (Finset.mem_range.mp hj).le
            rw [abs_of_nonneg]
            · exact (Nat.cast_sub hji).symm
            · exact sub_nonneg.mpr (by exact_mod_cast hji)
      _ = ((∏ j ∈ Finset.range i, (i - j : ℕ)) : ℝ) := by
            exact_mod_cast rfl
      _ = (i.factorial : ℝ) := by
            norm_cast
            exact (Nat.descFactorial_eq_prod_range i i).symm.trans
              (Nat.descFactorial_self i)
  have hright : (∏ j ∈ Finset.Ioc i d, |(i : ℝ) - (j : ℝ)|) =
      ((d - i).factorial : ℝ) := by
    calc
      (∏ j ∈ Finset.Ioc i d, |(i : ℝ) - (j : ℝ)|) =
          ∏ j ∈ Finset.Ioc i d, ((j - i : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hij : i ≤ j := (Finset.mem_Ioc.mp hj).1.le
            rw [abs_of_nonpos]
            · rw [Nat.cast_sub hij]
              ring
            · exact sub_nonpos.mpr (by exact_mod_cast hij)
      _ = ((∏ j ∈ Finset.Ioc i d, (j - i : ℕ)) : ℝ) := by
            exact_mod_cast rfl
      _ = ((d - i).factorial : ℝ) := by
            norm_cast
            rw [← Finset.Ico_add_one_add_one_eq_Ioc]
            rw [Finset.prod_Ico_eq_prod_range]
            have hcard : d + 1 - (i + 1) = d - i := by omega
            rw [hcard]
            calc
              (∏ k ∈ Finset.range (d - i), (i + 1 + k - i)) =
                  ∏ k ∈ Finset.range (d - i), (k + 1) := by
                    apply Finset.prod_congr rfl
                    intro k _
                    omega
              _ = (d - i).factorial := Finset.prod_range_add_one_eq_factorial _
  rw [hunion, Finset.prod_union hdisj, hleft, hright]

/-- The compact maximum of `|p|` on the closed interval `[u,v]`.-/
def polyMaxIcc (p : ℝ[X]) (u v : ℝ) : ℝ :=
  sSup ((fun x => |p.eval x|) '' Set.Icc u v)

/-- On a nonempty closed interval, `polyMaxIcc` is attained and dominates
every other value of `|p|` on that interval.
@isnad1 id=ex.1h3v.s6.32f7575ae89b from=translated src=- shape=1c4f4f0c vocab=6094bcfe
-/
lemma exists_polyMaxIcc_eq_and_ge (p : ℝ[X]) {u v : ℝ} (huv : u ≤ v) :
    ∃ x ∈ Set.Icc u v,
      polyMaxIcc p u v = |p.eval x| ∧
        ∀ y ∈ Set.Icc u v, |p.eval y| ≤ |p.eval x| := by
  simpa only [polyMaxIcc] using
    (isCompact_Icc.exists_sSup_image_eq_and_ge (Set.nonempty_Icc.mpr huv)
      p.continuous.abs.continuousOn)

/--
@isnad1 id=le.2h4v.s5.7de56c532a8d from=translated src=- shape=59931976 vocab=6094bcfe
-/
lemma abs_eval_le_polyMaxIcc (p : ℝ[X]) {u v x : ℝ} (huv : u ≤ v)
    (hx : x ∈ Set.Icc u v) : |p.eval x| ≤ polyMaxIcc p u v := by
  obtain ⟨z, hz, hmax, hge⟩ := exists_polyMaxIcc_eq_and_ge p huv
  rw [hmax]
  exact hge x hx

/--
@isnad1 id=le.1h3v.s4.6b3bfa23fcbc from=translated src=- shape=4ab32028 vocab=3c594228
-/
lemma polyMaxIcc_nonneg (p : ℝ[X]) {u v : ℝ} (huv : u ≤ v) :
    0 ≤ polyMaxIcc p u v := by
  obtain ⟨x, hx, hmax, _⟩ := exists_polyMaxIcc_eq_and_ge p huv
  rw [hmax]
  positivity

/-- Evaluation of the `i`th Lagrange basis on the equispaced grid.  We keep
the source-transparent quotient product visible rather than hiding it behind
the polynomial API.-/
def equiBasisValue (u v : ℝ) (d i : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ (Finset.range (d + 1)).erase i,
    (t - equiNode u v d j) / (equiNode u v d i - equiNode u v d j)

/--
@isnad1 id=eq.0h5v.s5.c1fad7a83afc from=translated src=- shape=b536b7d2 vocab=1d34490b
-/
lemma equiBasisValue_eq_eval_basis (u v : ℝ) (d i : ℕ) (t : ℝ) :
    equiBasisValue u v d i t =
      (Lagrange.basis (Finset.range (d + 1)) (equiNode u v d) i).eval t := by
  classical
  simp only [equiBasisValue, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro j _
  ring

/-- Lagrange interpolation of a degree-at-most-`d` polynomial on the
`d+1` equispaced points of `[u,v]`.
@isnad1 id=eq.3h5v.s6.ad408d17bb97 from=translated src=- shape=2305c710 vocab=a338a5f3
-/
lemma eval_eq_sum_equiBasisValue {p : ℝ[X]} {u v t : ℝ} {d : ℕ}
    (hd : 0 < d) (huv : u < v) (hdeg : p.natDegree ≤ d) :
    p.eval t = ∑ i ∈ Finset.range (d + 1),
      p.eval (equiNode u v d i) * equiBasisValue u v d i t := by
  classical
  have hdegree : p.degree < (Finset.range (d + 1)).card := by
    rw [Finset.card_range]
    calc
      p.degree ≤ (p.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (d : WithBot ℕ) := by exact_mod_cast hdeg
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hp := Lagrange.eq_interpolate
    (s := Finset.range (d + 1)) (v := equiNode u v d) (f := p)
    (equiNode_injOn hd huv) hdegree
  have hpeval := congrArg (Polynomial.eval t) hp
  rw [hpeval]
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i _
  rw [equiBasisValue_eq_eval_basis]

/--
@isnad1 id=le.2h2v.s6.4d0158c9cdc9 from=translated src=- shape=c837677f vocab=4d91b127
-/
lemma abs_sub_le_two_of_mem_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |x - y| ≤ 2 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Exact denominator size for the equispaced Lagrange basis.
@isnad1 id=eq.3h4v.s7.b90e88fc8f71 from=translated src=- shape=8f13a4d4 vocab=0946a718
-/
lemma prod_abs_equiNode_sub_eq {u v : ℝ} {d i : ℕ} (hd : 0 < d)
    (huv : u < v) (hi : i ≤ d) :
    (∏ j ∈ (Finset.range (d + 1)).erase i,
      |equiNode u v d i - equiNode u v d j|) =
      ((v - u) / (d : ℝ)) ^ d *
        ((i.factorial : ℝ) * ((d - i).factorial : ℝ)) := by
  have himem : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale : 0 < (v - u) / (d : ℝ) := div_pos (sub_pos.mpr huv) hdR
  calc
    (∏ j ∈ (Finset.range (d + 1)).erase i,
        |equiNode u v d i - equiNode u v d j|) =
        ∏ j ∈ (Finset.range (d + 1)).erase i,
          ((v - u) / (d : ℝ)) * |(i : ℝ) - (j : ℝ)| := by
            apply Finset.prod_congr rfl
            intro j _
            rw [equiNode_sub_equiNode hd, abs_mul, abs_of_pos hscale]
    _ = (∏ _j ∈ (Finset.range (d + 1)).erase i,
          ((v - u) / (d : ℝ))) *
        ∏ j ∈ (Finset.range (d + 1)).erase i, |(i : ℝ) - (j : ℝ)| := by
          rw [Finset.prod_mul_distrib]
    _ = ((v - u) / (d : ℝ)) ^ d *
        ((i.factorial : ℝ) * ((d - i).factorial : ℝ)) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem himem,
            Finset.card_range, prod_abs_cast_sub_eq_factorials hi]
          simp

/--
@isnad1 id=eq.3h5v.s7.7a9921af79f0 from=translated src=- shape=26b88af5 vocab=f8040850
-/
lemma abs_equiBasisValue_eq {u v t : ℝ} {d i : ℕ} (hd : 0 < d)
    (huv : u < v) (hi : i ≤ d) :
    |equiBasisValue u v d i t| =
      (∏ j ∈ (Finset.range (d + 1)).erase i,
        |t - equiNode u v d j|) /
      (((v - u) / (d : ℝ)) ^ d *
        ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) := by
  simp only [equiBasisValue, abs_prod, abs_div, Finset.prod_div_distrib]
  rw [prod_abs_equiNode_sub_eq hd huv hi]

/--
@isnad1 id=le.6h5v.s7.ba85dad7a612 from=translated src=- shape=99db9120 vocab=6f081249
-/
lemma prod_abs_sub_equiNode_le_two_pow {u v t : ℝ} {d i : ℕ}
    (hd : 0 < d) (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hi : i ≤ d) :
    (∏ j ∈ (Finset.range (d + 1)).erase i,
      |t - equiNode u v d j|) ≤ (2 : ℝ) ^ d := by
  have himem : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  calc
    (∏ j ∈ (Finset.range (d + 1)).erase i,
        |t - equiNode u v d j|) ≤
        ∏ _j ∈ (Finset.range (d + 1)).erase i, (2 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j _
            positivity
          · intro j hj
            have hjle : j ≤ d := Nat.le_of_lt_succ
              (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
            have hjJ := equiNode_mem_Icc hd huv.le hjle
            exact abs_sub_le_two_of_mem_Icc ht ⟨hu.trans hjJ.1, hjJ.2.trans hv⟩
    _ = (2 : ℝ) ^ d := by
      rw [Finset.prod_const, Finset.card_erase_of_mem himem, Finset.card_range]
      simp

/--
@isnad1 id=le.6h5v.s7.24a51096ec21 from=translated src=- shape=1746d71c vocab=87d47f15
-/
lemma abs_equiBasisValue_le_factorial {u v t : ℝ} {d i : ℕ}
    (hd : 0 < d) (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hi : i ≤ d) :
    |equiBasisValue u v d i t| ≤
      (2 : ℝ) ^ d /
        (((v - u) / (d : ℝ)) ^ d *
          ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) := by
  rw [abs_equiBasisValue_eq hd huv hi]
  apply div_le_div_of_nonneg_right
  · exact prod_abs_sub_equiNode_le_two_pow hd hu huv hv ht hi
  · have hscale : 0 < (v - u) / (d : ℝ) := by
      exact div_pos (sub_pos.mpr huv) (by exact_mod_cast hd)
    exact (mul_pos (pow_pos hscale d) (mul_pos (by positivity) (by positivity))).le

private lemma div_pow_factorial_cancel (q : ℝ) (hq : q ≠ 0) (d i : ℕ) :
    (2 : ℝ) ^ d /
        (q ^ d * ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) =
      (((2 : ℝ) / q) ^ d / (d.factorial : ℝ)) *
        ((d.factorial : ℝ) /
          ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) := by
  have hfi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hfdi : ((d - i).factorial : ℝ) ≠ 0 := by positivity
  have hfd : (d.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

/-- Each grid-basis value is controlled by its binomial coefficient.
@isnad1 id=le.6h5v.s7.e9eff456f787 from=translated src=- shape=62ce0220 vocab=b77fb00a
-/
lemma abs_equiBasisValue_le_choose {u v t : ℝ} {d i : ℕ}
    (hd : 0 < d) (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hi : i ≤ d) :
    |equiBasisValue u v d i t| ≤
      (((2 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)) *
        (d.choose i : ℝ) := by
  calc
    |equiBasisValue u v d i t| ≤
        (2 : ℝ) ^ d /
          (((v - u) / (d : ℝ)) ^ d *
            ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) :=
      abs_equiBasisValue_le_factorial hd hu huv hv ht hi
    _ = (((2 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)) *
        (d.choose i : ℝ) := by
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have huv0 : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
      have hfi : (i.factorial : ℝ) ≠ 0 := by positivity
      have hfdi : ((d - i).factorial : ℝ) ≠ 0 := by positivity
      have hfd : (d.factorial : ℝ) ≠ 0 := by positivity
      let s : ℝ := (v - u) / (d : ℝ)
      have hs : s ≠ 0 := div_ne_zero huv0 hd0
      have hbase : (2 : ℝ) * d / (v - u) = 2 / s := by
        dsimp only [s]
        field_simp
      change (2 : ℝ) ^ d / (s ^ d * ((i.factorial : ℝ) *
          ((d - i).factorial : ℝ))) = _
      rw [hbase, Nat.cast_choose ℝ hi]
      exact div_pow_factorial_cancel s hs d i

/-- The explicit exponential base delivered by equispaced interpolation.-/
def fixedIntervalGrowthBase (u v : ℝ) : ℝ :=
  4 * Real.exp 1 / (v - u)

/--
@isnad1 id=le.0h1v.s5.a4a9ebb31ad9 from=translated src=- shape=3a8826a3 vocab=38f987ca
-/
lemma pow_nat_div_factorial_le_exp (d : ℕ) :
    (d : ℝ) ^ d / (d.factorial : ℝ) ≤ Real.exp (d : ℝ) := by
  simpa using Real.pow_div_factorial_le_exp (x := (d : ℝ)) (by positivity) d

/--
@isnad1 id=le.1h3v.s6.ebc8060355ff from=translated src=- shape=62cbdd5a vocab=4d1f291b
-/
lemma scaled_pow_div_factorial_le_growthBase {u v : ℝ} (huv : u < v) (d : ℕ) :
    (((4 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)) ≤
      fixedIntervalGrowthBase u v ^ d := by
  have huv0 : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hfd : (d.factorial : ℝ) ≠ 0 := by positivity
  have hL : 0 < v - u := sub_pos.mpr huv
  have hnonneg : 0 ≤ ((4 : ℝ) / (v - u)) ^ d := by positivity
  calc
    (((4 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)) =
        ((4 : ℝ) / (v - u)) ^ d *
          ((d : ℝ) ^ d / (d.factorial : ℝ)) := by
            field_simp
            ring
    _ ≤ ((4 : ℝ) / (v - u)) ^ d * Real.exp (d : ℝ) :=
      mul_le_mul_of_nonneg_left (pow_nat_div_factorial_le_exp d) hnonneg
    _ = fixedIntervalGrowthBase u v ^ d := by
      have hexp : Real.exp (d : ℝ) = Real.exp 1 ^ d := by
        simpa using (Real.exp_nat_mul (1 : ℝ) d)
      rw [hexp, ← mul_pow]
      congr 1
      simp only [fixedIntervalGrowthBase]
      field_simp

/--
@isnad1 id=le.5h4v.s6.12109af32b2e from=translated src=- shape=3f61b6c0 vocab=d1763a89
-/
lemma sum_abs_equiBasisValue_le_growthBase {u v t : ℝ} {d : ℕ}
    (hd : 0 < d) (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (∑ i ∈ Finset.range (d + 1), |equiBasisValue u v d i t|) ≤
      fixedIntervalGrowthBase u v ^ d := by
  let A : ℝ := ((2 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)
  calc
    (∑ i ∈ Finset.range (d + 1), |equiBasisValue u v d i t|) ≤
        ∑ i ∈ Finset.range (d + 1), A * (d.choose i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact abs_equiBasisValue_le_choose hd hu huv hv ht
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = A * (2 : ℝ) ^ d := by
      rw [← Finset.mul_sum]
      congr 1
      norm_cast
      exact Nat.sum_range_choose d
    _ = (((4 : ℝ) * d / (v - u)) ^ d / (d.factorial : ℝ)) := by
      dsimp only [A]
      rw [div_mul_eq_mul_div, ← mul_pow]
      congr 2
      ring
    _ ≤ fixedIntervalGrowthBase u v ^ d :=
      scaled_pow_div_factorial_le_growthBase huv d

/-- Pointwise fixed-interval growth for a positive-degree polynomial.  The
right side uses the attained compact maximum on `[u,v]`.
@isnad1 id=le.5h4v.s6.54dbc2c7ac6a from=translated src=- shape=7b04410d vocab=77f816b6
-/
lemma abs_eval_le_growthBase_pow_mul_polyMaxIcc_of_pos_natDegree
    {p : ℝ[X]} {u v t : ℝ} (hd : 0 < p.natDegree)
    (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |p.eval t| ≤ fixedIntervalGrowthBase u v ^ p.natDegree *
      polyMaxIcc p u v := by
  rw [eval_eq_sum_equiBasisValue hd huv le_rfl]
  calc
    |∑ i ∈ Finset.range (p.natDegree + 1),
        p.eval (equiNode u v p.natDegree i) *
          equiBasisValue u v p.natDegree i t| ≤
        ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.eval (equiNode u v p.natDegree i) *
            equiBasisValue u v p.natDegree i t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
        |p.eval (equiNode u v p.natDegree i)| *
          |equiBasisValue u v p.natDegree i t| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        polyMaxIcc p u v * |equiBasisValue u v p.natDegree i t| := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right
          · apply abs_eval_le_polyMaxIcc p huv.le
            exact equiNode_mem_Icc hd huv.le
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          · positivity
    _ = polyMaxIcc p u v *
        ∑ i ∈ Finset.range (p.natDegree + 1),
          |equiBasisValue u v p.natDegree i t| := by
            rw [Finset.mul_sum]
    _ ≤ polyMaxIcc p u v * fixedIntervalGrowthBase u v ^ p.natDegree :=
      mul_le_mul_of_nonneg_left
        (sum_abs_equiBasisValue_le_growthBase hd hu huv hv ht)
        (polyMaxIcc_nonneg p huv.le)
    _ = fixedIntervalGrowthBase u v ^ p.natDegree * polyMaxIcc p u v :=
      mul_comm _ _

/-- Pointwise fixed-subinterval growth, including constant polynomials.
@isnad1 id=le.4h4v.s6.b0a3984fb232 from=translated src=- shape=0dd37e90 vocab=77f816b6
-/
theorem abs_eval_le_growthBase_pow_mul_polyMaxIcc
    (p : ℝ[X]) {u v t : ℝ}
    (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |p.eval t| ≤ fixedIntervalGrowthBase u v ^ p.natDegree *
      polyMaxIcc p u v := by
  by_cases hd : p.natDegree = 0
  · have hlocal := abs_eval_le_polyMaxIcc p huv.le
      (x := u) (show u ∈ Set.Icc u v from ⟨le_rfl, huv.le⟩)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd] at hlocal ⊢
    simpa [hd] using hlocal
  · exact abs_eval_le_growthBase_pow_mul_polyMaxIcc_of_pos_natDegree
      (Nat.pos_of_ne_zero hd) hu huv hv ht

/-- The fixed-interval growth base is genuinely larger than one whenever
`[u,v]` is a nondegenerate subinterval of `[-1,1]`.
@isnad1 id=lt.3h2v.s5.9423bf160711 from=translated src=- shape=957443cb vocab=e8c97c1b
-/
lemma one_lt_fixedIntervalGrowthBase {u v : ℝ}
    (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    1 < fixedIntervalGrowthBase u v := by
  have hL : 0 < v - u := sub_pos.mpr huv
  have hLle : v - u ≤ 2 := by linarith
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  rw [fixedIntervalGrowthBase, lt_div_iff₀ hL]
  nlinarith

/-- Source-transparent Phase 6.1 estimate: the compact maximum on `[-1,1]`
is at most an explicit fixed base to the polynomial degree times the compact
maximum on the fixed nondegenerate subinterval `[u,v]`.
@isnad1 id=le.3h3v.s6.2de6cebe5c4d from=translated src=- shape=15bcf9d8 vocab=eb6d1e57
-/
theorem polyMaxIcc_neg_one_one_le_growthBase_pow_mul
    (p : ℝ[X]) {u v : ℝ}
    (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    polyMaxIcc p (-1) 1 ≤ fixedIntervalGrowthBase u v ^ p.natDegree *
      polyMaxIcc p u v := by
  obtain ⟨t, ht, hmax, _⟩ :=
    exists_polyMaxIcc_eq_and_ge p (show (-1 : ℝ) ≤ 1 by norm_num)
  rw [hmax]
  exact abs_eval_le_growthBase_pow_mul_polyMaxIcc p hu huv hv ht

/-- Existential form matching the Phase 6.1 planning contract.  The witness
is explicitly `4 * exp 1 / (v-u)` and is independent of the polynomial.
@isnad1 id=ex.3h2v.s6.23ebd1c19035 from=translated src=- shape=fef077cf vocab=0cafe40e
-/
theorem exists_fixedInterval_growthBase {u v : ℝ}
    (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ C : ℝ, 1 < C ∧ ∀ p : ℝ[X],
      polyMaxIcc p (-1) 1 ≤ C ^ p.natDegree * polyMaxIcc p u v := by
  exact ⟨fixedIntervalGrowthBase u v,
    one_lt_fixedIntervalGrowthBase hu huv hv,
    fun p => polyMaxIcc_neg_one_one_le_growthBase_pow_mul p hu huv hv⟩

end

end Erdos1153.Density
