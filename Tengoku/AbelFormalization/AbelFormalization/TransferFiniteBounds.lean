import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Analysis.Asymptotics.SuperpolynomialDecay

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative bounds for finite generating families

The quantitative-reduction argument changes finite generating lists twice.
This file packages the elementary estimate used in both changes: a lower
bound for a finite family of linear combinations, together with polynomial
bounds for the coefficients, gives an inverse-power lower bound for the
original finite family.
-/

noncomputable section

namespace AbelFormalization

open Filter Finset
open scoped Topology

variable {X ι κ : Type*}

/-- The maximum absolute value in a nonempty finite family.-/
def finiteFamilyMaxAbs [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (x : X) : ℝ :=
  (Finset.univ.image fun i => |f i x|).max' (by simp)

/--
@isnad1 id=le.0h5v.s5.8a1e47d4a8d0 from=translated src=- shape=465c0ef0 vocab=5ae3364c
-/
theorem abs_le_finiteFamilyMaxAbs [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (x : X) (i : ι) :
    |f i x| ≤ finiteFamilyMaxAbs f x := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/--
@isnad1 id=ex.0h4v.s5.d377ff1d82da from=translated src=- shape=4c96fe69 vocab=bcafbe36
-/
theorem exists_abs_eq_finiteFamilyMaxAbs [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (x : X) :
    ∃ i, |f i x| = finiteFamilyMaxAbs f x := by
  have hm := Finset.max'_mem (Finset.univ.image fun i => |f i x|) (by simp)
  obtain ⟨i, _hi, himax⟩ := Finset.mem_image.mp hm
  exact ⟨i, himax⟩

/--
@isnad1 id=le.0h4v.s5.0622a001660e from=translated src=- shape=c9fb8897 vocab=25cbb5d9
-/
theorem finiteFamilyMaxAbs_nonneg [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (x : X) : 0 ≤ finiteFamilyMaxAbs f x := by
  obtain ⟨i, hi⟩ := exists_abs_eq_finiteFamilyMaxAbs f x
  rw [← hi]
  exact abs_nonneg _

/-- Pointwise triangle estimate for one finite linear combination.
@isnad1 id=le.2h4v.s6.6eb079ec0f50 from=translated src=- shape=f5dbcc02 vocab=0c1ed8f9
-/
theorem abs_linearCombination_le [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (a : ι → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ H) :
    |∑ i, a i * f i| ≤
      (Fintype.card ι : ℝ) * H *
        finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () := by
  let F : ℝ := finiteFamilyMaxAbs (fun i (_ : Unit) => f i) ()
  have hF : 0 ≤ F := finiteFamilyMaxAbs_nonneg _ _
  calc
    |∑ i, a i * f i| ≤ ∑ i, |a i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, H * F := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i)
        (abs_le_finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () i)
        (abs_nonneg _) hH
    _ = (Fintype.card ι : ℝ) * H * F := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Pointwise maximum estimate for a finite family of linear combinations.
@isnad1 id=le.3h6v.s7.5d47ee4c8ba2 from=translated src=- shape=0e05d9a3 vocab=0c1ed8f9
-/
theorem finiteFamilyMaxAbs_linearCombination_le
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (f : ι → ℝ) (g : κ → ℝ) (a : κ → ι → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (ha : ∀ b i, |a b i| ≤ H)
    (hg : ∀ b, g b = ∑ i, a b i * f i) :
    finiteFamilyMaxAbs (fun b (_ : Unit) => g b) () ≤
      (Fintype.card ι : ℝ) * H *
        finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () := by
  obtain ⟨b, hb⟩ := exists_abs_eq_finiteFamilyMaxAbs
    (fun b (_ : Unit) => g b) ()
  rw [← hb, hg b]
  exact abs_linearCombination_le f (a b) H hH (ha b)

/-- A nonempty finite family has an inverse-power lower bound along `l` at
scale `R` if its maximum absolute value is eventually at least `c / R^M`
for some positive constant `c` and natural exponent `M`.-/
def HasInversePowerLowerBound (l : Filter X) (R : X → ℝ)
    [Fintype ι] [Nonempty ι] (f : ι → X → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ,
    ∀ᶠ x in l, c / (R x) ^ M ≤ finiteFamilyMaxAbs f x

/-- Uniform polynomial upper bounds for a finite matrix of coefficient
functions.-/
def HasUniformPolynomialUpperBound (l : Filter X) (R : X → ℝ)
    (a : κ → ι → X → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
    ∀ᶠ x in l, ∀ b i, |a b i x| ≤ C * (R x) ^ P

/-- The pointwise arithmetic underlying transfer between two generating
lists.
@isnad1 id=le.6h10v.s7.62ca50bb03be from=translated src=- shape=2e4e2716 vocab=e8c78137
-/
theorem inversePowerLowerBound_pointwise
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (R c C : ℝ) (M P : ℕ) (f : ι → ℝ) (g : κ → ℝ)
    (a : κ → ι → ℝ)
    (hR : 1 ≤ R) (_hc : 0 < c) (hC : 0 < C)
    (ha : ∀ b i, |a b i| ≤ C * R ^ P)
    (hg : ∀ b, g b = ∑ i, a b i * f i)
    (hlower : c / R ^ M ≤ finiteFamilyMaxAbs (fun b (_ : Unit) => g b) ()) :
    (c / ((Fintype.card ι : ℝ) * C)) / R ^ (M + P) ≤
      finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hK : 0 < (Fintype.card ι : ℝ) * C := mul_pos hcard hC
  have hmax := finiteFamilyMaxAbs_linearCombination_le f g a (C * R ^ P)
    (mul_nonneg hC.le (pow_nonneg hRpos.le _)) ha hg
  have hraw : c / R ^ M ≤
      (Fintype.card ι : ℝ) * (C * R ^ P) *
        finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () := hlower.trans hmax
  apply (div_le_iff₀ (pow_pos hRpos (M + P))).2
  apply (div_le_iff₀ hK).2
  have hcraw : c ≤
      ((Fintype.card ι : ℝ) * (C * R ^ P) *
        finiteFamilyMaxAbs (fun i (_ : Unit) => f i) ()) * R ^ M :=
    (div_le_iff₀ (pow_pos hRpos M)).1 hraw
  calc
    c ≤ ((Fintype.card ι : ℝ) * (C * R ^ P) *
        finiteFamilyMaxAbs (fun i (_ : Unit) => f i) ()) * R ^ M := hcraw
    _ = finiteFamilyMaxAbs (fun i (_ : Unit) => f i) () * R ^ (M + P) *
        ((Fintype.card ι : ℝ) * C) := by rw [pow_add]; ring

/-- Quantitative propagation through finitely many polynomially bounded
linear-combination identities.  This is the generator-list step used twice
in the manuscript's quantitative-reduction proof.
@isnad1 id=hasinver.4h8v.s6.96ec93946b96 from=translated src=- shape=b307892b vocab=9358a8cc
-/
theorem hasInversePowerLowerBound_of_linearCombinations
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {R : X → ℝ}
    (f : ι → X → ℝ) (g : κ → X → ℝ)
    (a : κ → ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hg : ∀ᶠ x in l, ∀ b, g b x = ∑ i, a b i x * f i x)
    (ha : HasUniformPolynomialUpperBound l R a)
    (hglower : HasInversePowerLowerBound l R g) :
    HasInversePowerLowerBound l R f := by
  obtain ⟨C, hC, P, ha⟩ := ha
  obtain ⟨c, hc, M, hglower⟩ := hglower
  refine ⟨c / ((Fintype.card ι : ℝ) * C), ?_, M + P, ?_⟩
  · have hcard : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    positivity
  · filter_upwards [hR, hg, ha, hglower] with x hxR hxg hxa hxlower
    exact inversePowerLowerBound_pointwise (R x) c C M P (fun i => f i x)
      (fun b => g b x) (fun b i => a b i x) hxR hc hC hxa hxg hxlower

/-- Superpolynomial decay is preserved after multiplication by any function
with an eventual fixed polynomial bound in the same scale.
@isnad1 id=superpol.4h7v.s7.4a46e96a0981 from=translated src=- shape=ad6e1a3a vocab=846cc25b
-/
theorem Asymptotics.SuperpolynomialDecay.mul_of_polynomialBound
    {l : Filter X} {R e f : X → ℝ} {C : ℝ} {P : ℕ}
    (he : Asymptotics.SuperpolynomialDecay l R e)
    (hR : ∀ᶠ x in l, 0 ≤ R x) (hC : 0 ≤ C)
    (hf : ∀ᶠ x in l, |f x| ≤ C * (R x) ^ P) :
    Asymptotics.SuperpolynomialDecay l R (fun x => e x * f x) := by
  have hdom := (he.param_pow_mul P).const_mul C
  apply hdom.trans_eventually_abs_le
  filter_upwards [hR, hf] with x hxR hxf
  dsimp only [Function.comp_apply, Pi.mul_apply]
  simp only [abs_mul, Pi.pow_apply, abs_pow, abs_of_nonneg hxR,
    abs_of_nonneg hC]
  nlinarith [abs_nonneg (e x)]

/-- A finite sum of superpolynomially decaying functions still has
superpolynomial decay.
@isnad1 id=superpol.1h6v.s6.293a090c5be1 from=translated src=- shape=4b249554 vocab=c1418f3f
-/
theorem superpolynomialDecay_finset_sum {l : Filter X} {R : X → ℝ}
    {J : Type*} (s : Finset J) (f : J → X → ℝ)
    (hf : ∀ j ∈ s, Asymptotics.SuperpolynomialDecay l R (f j)) :
    Asymptotics.SuperpolynomialDecay l R (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (Asymptotics.superpolynomialDecay_zero l R).congr (by simp)
  | @insert j s hjs ih =>
      have hj := hf j (Finset.mem_insert_self j s)
      have hs := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      exact (hj.add hs).congr (by intro x; simp [Finset.sum_insert hjs])

/-- A rapidly decaying perturbation cannot destroy an inverse-power lower
bound for a nonempty finite family.
@isnad1 id=hasinver.4h7v.s6.6917de019587 from=translated src=- shape=68297758 vocab=425bb150
-/
theorem hasInversePowerLowerBound_of_superpolynomialPerturbation
    [Fintype ι] [Nonempty ι]
    {l : Filter X} {R : X → ℝ}
    (f g e : ι → X → ℝ)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hge : ∀ᶠ x in l, ∀ i, g i x = f i x + e i x)
    (he : ∀ i, Asymptotics.SuperpolynomialDecay l R (e i))
    (hg : HasInversePowerLowerBound l R g) :
    HasInversePowerLowerBound l R f := by
  obtain ⟨c, hc, M, hg⟩ := hg
  have herr : ∀ᶠ x in l, ∀ i, |e i x| ≤ (c / 2) / (R x) ^ M := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (he i M)
    have hibound := hi.eventually (Metric.ball_mem_nhds 0 (half_pos hc))
    filter_upwards [hibound, hR] with x hx hxR
    rw [Real.dist_eq, sub_zero, abs_mul, abs_pow,
      abs_of_nonneg (zero_le_one.trans hxR)] at hx
    have hpow : 0 < (R x) ^ M := pow_pos (zero_lt_one.trans_le hxR) M
    apply (le_div_iff₀ hpow).2
    simpa only [mul_comm] using hx.le
  refine ⟨c / 2, half_pos hc, M, ?_⟩
  filter_upwards [hR, hge, hg, herr] with x hxR hxge hxg hxerr
  obtain ⟨j, hj⟩ := exists_abs_eq_finiteFamilyMaxAbs g x
  have hgj : c / (R x) ^ M ≤ |g j x| := by simpa only [hj] using hxg
  have htriangle : |g j x| ≤ |f j x| + |e j x| := by
    rw [hxge j]
    exact abs_add_le _ _
  have hfj : |f j x| ≤ finiteFamilyMaxAbs f x := abs_le_finiteFamilyMaxAbs f x j
  have hsplit : c / (R x) ^ M =
      (c / 2) / (R x) ^ M + (c / 2) / (R x) ^ M := by ring
  rw [hsplit] at hgj
  linarith [hxerr j]

end AbelFormalization
