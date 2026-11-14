import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletTail
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Analytic.Uniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered primitive Dirichlet sums on the positive half-plane

The quantitative finite tail bound gives locally uniform ordered convergence.
Its holomorphic limit agrees with `LFunction` by the identity theorem, extending
the same truncation bound to `0 < s.re`. No unconditional summability is asserted
in the strip `0 < s.re ≤ 1`.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- The ordered limit, defined independently of convergence proofs.-/
def characterDirichletLimit {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  limUnder atTop (characterDirichletPartialSum χ s)

/--
@isnad1 id=tendsto.3h3v.s6.2106874f4ffd from=translated src=- shape=7e081d0e vocab=04d5c5ce
-/
theorem tendsto_characterDirichletPartialSum_limit {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (characterDirichletPartialSum χ s) atTop (𝓝 (characterDirichletLimit χ s)) :=
  (cauchySeq_characterDirichletPartialSum hq χ hχ s hs).tendsto_limUnder

/--
@isnad1 id=le.4h4v.s7.bc4e93b6f9b6 from=translated src=- shape=7da6db51 vocab=5e3fdd15
-/
theorem norm_characterDirichletLimit_sub_partialSum_le {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : 0 < s.re) :
    ‖characterDirichletLimit χ s - characterDirichletPartialSum χ s M‖ ≤
      (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-s.re) *
        (1 + ‖s‖ / s.re) := by
  have hL := tendsto_characterDirichletPartialSum_limit hq χ hχ s hs
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [characterDirichletPartialSum_sub χ s hMN]
  exact norm_sum_primitive_character_dirichlet_Ioc_le hq χ hχ M N hM hMN s hs

/-- A common quantitative tail budget on every bounded set separated from
the boundary of the positive half-plane.
@isnad1 id=le.6h6v.s7.f0353e9e611b from=translated src=- shape=e11f225f vocab=5e3fdd15
-/
theorem norm_characterDirichletLimit_sub_partialSum_le_uniform {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (M : ℕ) (hM : 1 ≤ M) (δ H : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hσ : δ ≤ s.re) (hH : ‖s‖ ≤ H) :
    ‖characterDirichletLimit χ s - characterDirichletPartialSum χ s M‖ ≤
      (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-δ) * (1 + H / δ) := by
  have hs := hδ.trans_le hσ
  have hC : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log q) := by
    have := Real.log_natCast_nonneg q
    positivity
  apply (norm_characterDirichletLimit_sub_partialSum_le hq χ hχ M hM s hs).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (neg_le_neg hσ)
  · exact add_le_add le_rfl (div_le_div₀ ((norm_nonneg _).trans hH) hH hδ hσ)
  · positivity
  · positivity

/-- Uniform convergence on bounded closed portions of `0 < s.re`.
@isnad1 id=tendstou.3h4v.s6.0defa2396ec8 from=translated src=- shape=6604df2b vocab=71731792
-/
theorem tendstoUniformlyOn_characterDirichletPartialSum_limit {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (δ H : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun N s => characterDirichletPartialSum χ s N)
      (characterDirichletLimit χ) atTop {s : ℂ | δ ≤ s.re ∧ ‖s‖ ≤ H} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ =>
      (Real.sqrt q * (1 + Real.log q)) * (N : ℝ) ^ (-δ) * (1 + H / δ))
      atTop (𝓝 0) := by
    simpa using (hp.const_mul (Real.sqrt q * (1 + Real.log q))).mul_const (1 + H / δ)
  filter_upwards [eventually_ge_atTop 1, hb.eventually (gt_mem_nhds hε)] with N hN hbN
  intro s hs
  rw [dist_eq_norm]
  exact (norm_characterDirichletLimit_sub_partialSum_le_uniform hq χ hχ N hN
    δ H hδ s hs.1 hs.2).trans_lt hbN

/-- The uniform bounded-region estimates give locally uniform convergence
on the whole positive half-plane.
@isnad1 id=tendstol.2h2v.s6.3891c9454a9e from=translated src=- shape=8cab25ac vocab=e756d977
-/
theorem tendstoLocallyUniformlyOn_characterDirichletPartialSum_limit {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    TendstoLocallyUniformlyOn (fun N s => characterDirichletPartialSum χ s N)
      (characterDirichletLimit χ) atTop {s : ℂ | 0 < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0 < z.re at hz
  let δ : ℝ := z.re / 2
  let H : ℝ := ‖z‖ + 1
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos hz
  have hlo : {s : ℂ | δ < s.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [δ]; linarith)
  have hhi : {s : ℂ | ‖s‖ < H} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp [H]; linarith)
  refine ⟨{s : ℂ | δ ≤ s.re ∧ ‖s‖ ≤ H}, mem_nhdsWithin_of_mem_nhds ?_,
    tendstoUniformlyOn_characterDirichletPartialSum_limit hq χ hχ δ H hδ⟩
  exact mem_of_superset (inter_mem hlo hhi) (fun s hs => ⟨hs.1.le, hs.2.le⟩)

/-- Every ordered partial sum is an entire function of the complex exponent.
@isnad1 id=differen.0h3v.s6.47d1139cfa8c from=translated src=- shape=5e8f902f vocab=c5630200
-/
theorem differentiable_characterDirichletPartialSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Differentiable ℂ (fun s => characterDirichletPartialSum χ s N) := by
  unfold characterDirichletPartialSum
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Ioc.mp hn).1)
  exact (differentiable_id.neg.const_cpow (Or.inl hn0)).mul_const (χ (n : ZMod q))

/-- The ordered limit is holomorphic on the positive half-plane.
@isnad1 id=differen.2h2v.s6.77d192bef2cf from=translated src=- shape=35b9f965 vocab=c1108759
-/
theorem differentiableOn_characterDirichletLimit {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (characterDirichletLimit χ) {s : ℂ | 0 < s.re} :=
  (tendstoLocallyUniformlyOn_characterDirichletPartialSum_limit hq χ hχ).differentiableOn
    (Eventually.of_forall (fun N => (differentiable_characterDirichletPartialSum χ N).differentiableOn))
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The identity theorem identifies the ordered limit with the existing
analytic continuation on the connected positive half-plane.
@isnad1 id=eqon.2h2v.s6.df4fdc26efc1 from=translated src=- shape=80b442c4 vocab=03eb0b74
-/
theorem characterDirichletLimit_eqOn_LFunction {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    Set.EqOn (characterDirichletLimit χ) (DirichletCharacter.LFunction χ)
      {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hf := (differentiableOn_characterDirichletLimit hq χ hχ).analyticOnNhd hopen
  have hg := (DirichletCharacter.differentiable_LFunction
    (primitive_character_ne_one hq χ hχ)).differentiableOn.analyticOnNhd hopen
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2 : ℂ)) (by norm_num)
  have htwo : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [htwo] with s hs
  exact tendsto_nhds_unique
    (tendsto_characterDirichletPartialSum_limit hq χ hχ s (lt_trans zero_lt_one hs))
    (tendsto_characterDirichletPartialSum_LFunction χ s hs)

/-- Locally uniform ordered convergence to the actual L-function.
@isnad1 id=tendstol.2h2v.s6.08cfbc2a9fcb from=translated src=- shape=404c0323 vocab=c651d52e
-/
theorem tendstoLocallyUniformlyOn_characterDirichletPartialSum_LFunction {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    TendstoLocallyUniformlyOn (fun N s => characterDirichletPartialSum χ s N)
      (DirichletCharacter.LFunction χ) atTop {s : ℂ | 0 < s.re} :=
  (tendstoLocallyUniformlyOn_characterDirichletPartialSum_limit hq χ hχ).congr_right
    (characterDirichletLimit_eqOn_LFunction hq χ hχ)

/-- Ordered convergence to `LFunction` throughout `0 < s.re`.
@isnad1 id=tendsto.3h3v.s6.03e4c482b298 from=translated src=- shape=875de4bf vocab=94770584
-/
theorem tendsto_characterDirichletPartialSum_LFunction_of_re_pos {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (characterDirichletPartialSum χ s) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
  rw [← characterDirichletLimit_eqOn_LFunction hq χ hχ hs]
  exact tendsto_characterDirichletPartialSum_limit hq χ hχ s hs

/-- The original Pólya--Vinogradov truncation budget now applies to the
actual L-function on the full positive half-plane.
@isnad1 id=le.4h4v.s7.2bc1a8819490 from=translated src=- shape=869f3f7d vocab=edad62a4
-/
theorem norm_LFunction_sub_characterDirichletPartialSum_le_of_re_pos {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s - characterDirichletPartialSum χ s M‖ ≤
      (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-s.re) *
        (1 + ‖s‖ / s.re) := by
  rw [← characterDirichletLimit_eqOn_LFunction hq χ hχ hs]
  exact norm_characterDirichletLimit_sub_partialSum_le hq χ hχ M hM s hs

end TwinPrime.Analytic
