import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Finite

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRecomputed (N : ℕ) (x : FInput N) : FInput N :=
  finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))) x

/--
@isnad1 id=eq.0h1v.s5.398878dd21e6 from=translated src=- shape=5d442560 vocab=296d2cdb
-/
@[simp] theorem finiteRecomputed_zero (N : ℕ) : finiteRecomputed N 0=0 := map_zero _

/--
@isnad1 id=le.2h5v.s12.f6965b2294f8 from=translated src=- shape=0250f039 vocab=3ef175d7
-/
theorem finiteFrozen_weight_error {W V : FrozenWeights} {x : FInput N} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V (finiteEmbed N x) q) :
    ‖finiteFrozen N W x-finiteFrozen N V x‖≤6*q := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hq)).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x-finiteRow V (i,Fin.last N) x|≤_
    rw [finiteRow_eq,finiteRow_eq]
    exact (rowScalar_weight_error W V _ _ (h.row _)).trans (by linarith)
  · change |finiteFrozenFunction W x (.inr γ)-finiteFrozenFunction V x (.inr γ)|≤_
    rw [finiteFrozen_block,finiteFrozen_block]
    exact (cfun_norm_apply_le (frozenShift W (finiteEmbed N x)-frozenShift V (finiteEmbed N x)) (fLabel γ)).trans
      (shift_weight_error hq h)

/--
@isnad1 id=le.0h3v.s13.2025d46a97fd from=translated src=- shape=738e5469 vocab=583377ed
-/
theorem finiteRecomputed_mixed_left (x y : FInput N) :
    ‖finiteRecomputed N x-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) x‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_left (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

/--
@isnad1 id=le.0h3v.s13.7d542397c870 from=translated src=- shape=43a1e4f5 vocab=583377ed
-/
theorem finiteRecomputed_mixed_right (x y : FInput N) :
    ‖finiteRecomputed N y-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) y‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_right (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

/--
@isnad1 id=le.0h3v.s13.6bbbbf7ab6fe from=translated src=- shape=1e48fae2 vocab=583377ed
-/
theorem finiteRecomputed_mixed_approx (x y : FInput N) :
    ‖finiteRecomputed N x-finiteRecomputed N y-
      finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  have he : finiteRecomputed N x-finiteRecomputed N y-finiteFrozen N W (x-y)=
      (finiteRecomputed N x-finiteFrozen N W x)-(finiteRecomputed N y-finiteFrozen N W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [finiteRecomputed_mixed_left x y,finiteRecomputed_mixed_right x y])

/--
@isnad1 id=and.3h5v.s7.0a2d8ba15211 from=translated src=- shape=e7b7c6f4 vocab=896c3840
-/
theorem fiveBounds_of_error {E : Type*} [NormedAddCommGroup E] {a b : E} {d e : ℝ}
    (he : ‖a-b‖≤e*d) (hU : ‖b‖≤5*d) (hL : d≤5*‖b‖) :
    (1/5-e)*d≤‖a‖ ∧ ‖a‖≤(5+e)*d := by
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  constructor <;> nlinarith

/--
@isnad1 id=and.0h3v.s12.e557eeb53545 from=translated src=- shape=8dd15f36 vocab=0fd19062
-/
theorem finiteRecomputed_global_bounds (x y : FInput N) :
    (1/5-24*eta)*dist x y≤dist (finiteRecomputed N x) (finiteRecomputed N y) ∧
    dist (finiteRecomputed N x) (finiteRecomputed N y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  let a := finiteRecomputed N x-finiteRecomputed N y
  let b := finiteFrozen N W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := finiteRecomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by
    change ‖finiteFrozenFunction W (x-y)‖≤5*dist x y
    rw [dist_eq_norm]
    exact finiteFrozen_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using finiteFrozen_lower W (x-y)
  rw [dist_eq_norm (finiteRecomputed N x) (finiteRecomputed N y)]
  exact fiveBounds_of_error he hU hL

/--
@isnad1 id=lipschit.0h1v.s11.45c6da3051c6 from=translated src=- shape=defbb0cc vocab=fd2564e8
-/
theorem finiteRecomputed_lipschitz (N : ℕ) : LipschitzWith (628/125) (finiteRecomputed N) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (finiteRecomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

/--
@isnad1 id=antilips.0h1v.s11.abf988e113c4 from=translated src=- shape=defbb0cc vocab=11f402ee
-/
theorem finiteRecomputed_antilipschitz (N : ℕ) : AntilipschitzWith (125/22) (finiteRecomputed N) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (finiteRecomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
@isnad1 id=le.0h3v.s8.3e8f9aa47564 from=translated src=- shape=cb11bb8b vocab=859648e2
-/
theorem finite_operator_norm_le_columns (T : (A → ℝ) →L[ℝ] E) :
    ‖T‖≤∑ a,‖T (Pi.single a 1)‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  intro x
  have he : (∑ a, x a • Pi.single a (1 : ℝ))=x := by
    ext b
    simp [Pi.single_apply]
  have hEq : T x=∑ a,x a • T (Pi.single a 1) := by
    simpa only [map_sum,map_smul] using congrArg T he.symm
  rw [hEq]
  calc
    _ ≤ ∑ a, ‖x a • T (Pi.single a 1)‖ := norm_sum_le _ _
    _ = ∑ a, ‖T (Pi.single a 1)‖*‖x a‖ := by simp only [norm_smul,mul_comm]
    _ ≤ ∑ a, ‖T (Pi.single a 1)‖*‖x‖ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x a) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

/--
@isnad1 id=tendsto.1h6v.s9.5989c9161537 from=translated src=- shape=2339a710 vocab=49642d69
-/
theorem tendsto_finiteOperator_of_columns {X : Type*} {l : Filter X}
    (T : X → (A → ℝ) →L[ℝ] E) (S : (A → ℝ) →L[ℝ] E)
    (h : ∀ a, Tendsto (fun z => T z (Pi.single a 1)) l (nhds (S (Pi.single a 1)))) :
    Tendsto T l (nhds S) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun z => norm_nonneg _) (fun z => finite_operator_norm_le_columns (T z-S))
  have hh : Tendsto (fun z => ∑ a, ‖T z (Pi.single a 1)-S (Pi.single a 1)‖) l (nhds (∑ a : A, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun a _ => tendsto_iff_norm_sub_tendsto_zero.mp (h a))
  simpa only [sub_apply,Finset.sum_const_zero] using hh

end FiniteOperators

/--
@isnad1 id=ex.3h8v.s7.e5138eada842 from=translated src=- shape=fc2fa87a vocab=21c37ffd
-/
theorem diagonal_neighborhood {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup G] (q : X → Y) {x : X} (hq : ContinuousAt q x)
    (A : Y × Y → G) (g : G) (hA : Tendsto A (nhds (q x,q x)) (nhds g))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Set X, s∈nhds x ∧ ∀ y∈s, ∀ z∈s, ‖A (q y,q z)-g‖<ε := by
  have hp : Tendsto (fun p : X × X => (q p.1,q p.2)) (nhds (x,x)) (nhds (q x,q x)) :=
    (hq.comp continuous_fst.continuousAt).prodMk (hq.comp continuous_snd.continuousAt)
  have ht := hA.comp hp
  have he : {p : X × X | ‖A (q p.1,q p.2)-g‖<ε}∈nhds (x,x) := by
    have hh := Metric.tendsto_nhds.mp ht ε hε
    change ∀ᶠ p : X × X in nhds (x,x), ‖A (q p.1,q p.2)-g‖<ε
    filter_upwards [hh] with p h
    simpa only [Function.comp_def,dist_eq_norm] using h
  rw [nhds_prod_eq] at he
  obtain ⟨s,hs,t,ht,hst⟩ := Filter.mem_prod_iff.mp he
  exact ⟨s∩t,inter_mem hs ht,fun y hy z hz => @hst (y,z) ⟨hy.1,hz.2⟩⟩

end
end C0Absorption

end OAI
