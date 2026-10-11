module
public import Tengoku.Causalean.Causalean.Stat.OrderStatistic.WeightedConcomitant.ConcomitantTagged

/-!
# Bernstein expectation of rank-weighted concomitants

This module turns the tagged conditional-mean identity into the Bernstein-kernel
expectation formula for a complete finite marked sample.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic
open scoped BigOperators

noncomputable section

/-- For a [bounded marked iid law](hyp:μ,hmark), [continuous coordinate CDF](hyp:hcont),
 [cell weights](hyp:a), and a [conditional mean function and version](hyp:m,hm), [conditioning replaces each sorted mark
 by that mean in the expected rank concomitant](goal). -/
theorem integral_rankConcomitant_eq_conditionalMean {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    (∫ x, rankConcomitant a x ∂Measure.pi (fun _ : Fin N => μ)) =
      ∫ x, (∑ j : Fin N,
        a j * m (ProbabilityTheory.cdf (μ.map Prod.fst)
          (x (Tuple.sort (fun i => (x i).1) j)).1))
        ∂Measure.pi (fun _ : Fin N => μ) := by
  -- Expand the finite sum, condition each tagged mark on its CDF coordinate,
  -- and use `sort_cdf_eq_ae` to make the rank event coordinate-measurable.
  classical
  let ν : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ => μ)
  let F : ℝ × ℝ → ℝ := fun p => ProbabilityTheory.cdf (μ.map Prod.fst) p.1
  have hF : Measurable F := hcont.measurable.comp measurable_fst
  have hinj : ∀ᵐ x ∂ν, Function.Injective (fun k => F (x k)) := by
    have hu := iid_uniform_coordinates_injective_ae (N := N)
    rw [← cdf_transport_iid μ hcont] at hu
    exact ae_of_ae_map
      (by
        apply Measurable.aemeasurable
        apply measurable_pi_iff.mpr
        intro k
        exact hF.comp (measurable_pi_apply k)
        : AEMeasurable (fun x : Fin N → ℝ × ℝ => fun k => F (x k)) ν) hu
  have hC (i j : Fin N) : MeasurableSet
      {x : Fin N → ℝ × ℝ |
        (((Finset.univ : Finset (Fin N)).erase i).filter
          (fun k => F (x k) < F (x i))).card = j.val} := by
    apply measurableSet_eq_fun
    · simp_rw [Finset.card_filter]
      apply Finset.measurable_sum
      intro k _
      apply Measurable.ite
      · exact measurableSet_lt (hF.comp (measurable_pi_apply k))
          (hF.comp (measurable_pi_apply i))
      · exact measurable_const
      · exact measurable_const
    · exact measurable_const
  have hrank (i j : Fin N) : ∀ᵐ x ∂ν,
      (((Tuple.sort (fun k => (x k).1)).symm i = j) ↔
        (((Finset.univ : Finset (Fin N)).erase i).filter
          (fun k => F (x k) < F (x i))).card = j.val) := by
    filter_upwards [sort_cdf_eq_ae μ hcont, hinj] with x hs hx
    rw [hs, ← uniform_tagged_rank_eq_count (fun k => F (x k)) i hx]
    exact Fin.ext_iff
  obtain ⟨g, hg, hmg⟩ := conditionalMean_exists_measurable_version μ m hm
  have hgbound : ∀ᵐ p ∂μ, |g (F p)| ≤ 1 := by
    filter_upwards [conditionalMean_comp_mem_Icc_ae μ hmark m hm, hmg] with p hp he
    rw [he] at hp
    exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
  have hmarkBound (i : Fin N) : ∀ᵐ x ∂ν, |(x i).2| ≤ 1 := by
    have hbμ : ∀ᵐ p ∂μ, |p.2| ≤ 1 := hmark.mono fun p hp =>
      abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
    exact ae_of_ae_map (μ := ν) (f := fun x : Fin N → ℝ × ℝ => x i)
      (p := fun p => |p.2| ≤ 1) (measurable_pi_apply i).aemeasurable
      (by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
          exact hbμ)
  have hgBound (i : Fin N) : ∀ᵐ x ∂ν, |g (F (x i))| ≤ 1 := by
    exact ae_of_ae_map (μ := ν) (f := fun x : Fin N → ℝ × ℝ => x i)
      (p := fun p => |g (F p)| ≤ 1) (measurable_pi_apply i).aemeasurable
      (by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
          exact hgbound)
  have hmgCoord (i : Fin N) : ∀ᵐ x ∂ν, m (F (x i)) = g (F (x i)) := by
    exact ae_of_ae_map (μ := ν) (f := fun x : Fin N → ℝ × ℝ => x i)
      (p := fun p => m (F p) = g (F p)) (measurable_pi_apply i).aemeasurable
      (by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
          exact hmg)
  have htagInt (i j : Fin N) (b : ℝ) : Integrable
      (fun x : Fin N → ℝ × ℝ =>
        if (Tuple.sort (fun k => (x k).1)).symm i = j then b * (x i).2 else 0) ν := by
    let C : Set (Fin N → ℝ × ℝ) :=
      {x | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => F (x k) < F (x i))).card = j.val}
    have hL : Integrable (fun x : Fin N → ℝ × ℝ =>
        if x ∈ C then b * (x i).2 else 0) ν := by
      apply Integrable.of_bound
        ((measurable_const.mul (measurable_snd.comp (measurable_pi_apply i))).ite
          (hC i j) measurable_const).aestronglyMeasurable |b|
      filter_upwards [hmarkBound i] with x hx
      change ‖(if x ∈ C then b * (x i).2 else 0 : ℝ)‖ ≤ |b|
      by_cases hc : x ∈ C
      · simpa [hc, Real.norm_eq_abs, abs_mul] using
          (mul_le_mul_of_nonneg_left hx (abs_nonneg b))
      · simp [hc]
    apply hL.congr
    filter_upwards [hrank i j] with x hx
    simp only [C, Set.mem_ofPred_eq, if_congr hx rfl rfl]
  have hmeanInt (i j : Fin N) (b : ℝ) : Integrable
      (fun x : Fin N → ℝ × ℝ =>
        if (Tuple.sort (fun k => (x k).1)).symm i = j then b * m (F (x i)) else 0) ν := by
    let C : Set (Fin N → ℝ × ℝ) :=
      {x | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => F (x k) < F (x i))).card = j.val}
    have hL : Integrable (fun x : Fin N → ℝ × ℝ =>
        if x ∈ C then b * g (F (x i)) else 0) ν := by
      apply Integrable.of_bound
        ((measurable_const.mul (hg.comp (hF.comp (measurable_pi_apply i)))).ite
          (hC i j) measurable_const).aestronglyMeasurable |b|
      filter_upwards [hgBound i] with x hx
      change ‖(if x ∈ C then b * g (F (x i)) else 0 : ℝ)‖ ≤ |b|
      by_cases hc : x ∈ C
      · simpa [hc, Real.norm_eq_abs, abs_mul] using
          (mul_le_mul_of_nonneg_left hx (abs_nonneg b))
      · simp [hc]
    apply hL.congr
    filter_upwards [hrank i j, hmgCoord i] with x hx hm'
    simp only [C, Set.mem_ofPred_eq, if_congr hx rfl rfl, hm']
  have hpoint (x : Fin N → ℝ × ℝ) (z : Fin N → ℝ) :
      (∑ j : Fin N, a j * z ((Tuple.sort (fun k => (x k).1)) j)) =
        ∑ i : Fin N, ∑ j : Fin N,
          if (Tuple.sort (fun k => (x k).1)).symm i = j then a j * z i else 0 := by
    let σ := Tuple.sort (fun k => (x k).1)
    have h := Equiv.sum_comp σ (fun i : Fin N =>
      ∑ j : Fin N, if σ.symm i = j then a j * z i else 0)
    simpa only [σ, Equiv.symm_apply_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] using h
  have hterm (i j : Fin N) :
      (∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
          a j * (x i).2 else 0) ∂ν) =
        ∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
          a j * m (F (x i)) else 0) ∂ν := by
    calc
      _ = a j * ∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
          (x i).2 else 0) ∂ν := by
        rw [← integral_const_mul]
        congr 1
        funext x
        split_ifs <;> simp [*]
      _ = a j * ∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
          m (F (x i)) else 0) ∂ν := by
        exact congrArg (a j * ·)
          (integral_tagged_rank_mark_eq_conditionalMean μ hcont hmark i j m hm)
      _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext x
        split_ifs <;> simp [*]
  calc
    (∫ x, rankConcomitant a x ∂ν) =
        ∫ x, ∑ i : Fin N, ∑ j : Fin N,
          (if (Tuple.sort (fun k => (x k).1)).symm i = j then
            a j * (x i).2 else 0) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [rankConcomitant] using hpoint x (fun i => (x i).2))
    _ = ∑ i : Fin N, ∑ j : Fin N,
          ∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
            a j * (x i).2 else 0) ∂ν := by
      rw [integral_finsetSum (s := Finset.univ) (fun i _ =>
        integrable_finsetSum _ (fun j _ => htagInt i j (a j)))]
      congr 1
      funext i
      rw [integral_finsetSum (s := Finset.univ) (fun j _ => htagInt i j (a j))]
    _ = ∑ i : Fin N, ∑ j : Fin N,
          ∫ x, (if (Tuple.sort (fun k => (x k).1)).symm i = j then
            a j * m (F (x i)) else 0) ∂ν := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = ∫ x, ∑ i : Fin N, ∑ j : Fin N,
          (if (Tuple.sort (fun k => (x k).1)).symm i = j then
            a j * m (F (x i)) else 0) ∂ν := by
      rw [integral_finsetSum (s := Finset.univ) (fun i _ =>
        integrable_finsetSum _ (fun j _ => hmeanInt i j (a j)))]
      congr 1
      funext i
      rw [integral_finsetSum (s := Finset.univ) (fun j _ => hmeanInt i j (a j))]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [F] using (hpoint x (fun i => m (F (x i)))).symm)

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
