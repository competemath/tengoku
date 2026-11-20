import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.FiniteObstruction
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.BernsteinOperations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set

namespace Erdos1133

/-- The finite analytic obstruction restricted to distinct nodes.-/
def InjectiveBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t → ∀ (a : ℝ),
    (∀ i, t i ∈ Icc a (a + (k : ℝ) + 1)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

/--
@isnad1 id=finitebe.1h2v.s3.8a636379c4ab from=translated src=- shape=6ef4b4a0 vocab=a854aaac
-/
theorem finiteObstruction_of_injective {H : ℝ} {k : ℕ}
    (h : InjectiveBernsteinObstruction H k) : FiniteBernsteinObstruction H k := by
  classical
  intro t a ht
  by_cases hi : Function.Injective t
  · exact h t hi a ht
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hij, hne⟩ := hi
    let y : Fin k → Icc (-1 : ℝ) 1 := fun l =>
      if l = i then ⟨0, by constructor <;> norm_num⟩
      else ⟨1, by constructor <;> norm_num⟩
    refine ⟨y, ?_⟩
    intro f _
    by_contra hfit
    push Not at hfit
    have hzero : f (t i) = 0 := by simpa [y] using hfit i
    have hone : f (t j) = 1 := by simpa [y, Ne.symm hne] using hfit j
    have : (0 : ℂ) = 1 := hzero.symm.trans ((congrArg (fun x : ℝ => f x) hij).trans hone)
    exact zero_ne_one this

/-- Centered distinct-node form, with the slightly enlarged bandwidth needed
to compress an interval of length `k + 1` into one of length `k`.-/
def CenteredBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t →
    (∀ i, t i ∈ Icc (-(k : ℝ) / 2) ((k : ℝ) / 2)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction (Real.pi * (1 + 1 / (k : ℝ))) H f →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

/-- The core need only obstruct functions that are real on the real axis.-/
def CenteredRealBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t →
    (∀ i, t i ∈ Icc (-(k : ℝ) / 2) ((k : ℝ) / 2)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction (Real.pi * (1 + 1 / (k : ℝ))) H f →
        (∀ x : ℝ, (f x).im = 0) →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

/--
@isnad1 id=centered.1h2v.s3.2e8f9b3d797a from=translated src=- shape=6ef4b4a0 vocab=dc328649
-/
theorem centeredObstruction_of_real {H : ℝ} {k : ℕ}
    (h : CenteredRealBernsteinObstruction H k) : CenteredBernsteinObstruction H k := by
  classical
  intro t ht hloc
  obtain ⟨y, hy⟩ := h t ht hloc
  refine ⟨y, ?_⟩
  intro f hf
  obtain ⟨i, hi⟩ := hy (bernsteinRealification f) hf.realification
    (bernsteinRealification_im f)
  exact ⟨i, fun heq => hi (bernsteinRealification_real_value heq)⟩

/--
@isnad1 id=injectiv.2h2v.s4.160a849759d1 from=translated src=- shape=b06c76f5 vocab=fbd3dd79
-/
theorem injectiveObstruction_of_centered {H : ℝ} {k : ℕ} (hk : 0 < k)
    (h : CenteredBernsteinObstruction H k) : InjectiveBernsteinObstruction H k := by
  classical
  intro t hinj a ht
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let c : ℝ := 1 + 1 / (k : ℝ)
  let b : ℝ := a + ((k : ℝ) + 1) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hck : c * (k : ℝ) = (k : ℝ) + 1 := by
    dsimp [c]
    field_simp
  let s : Fin k → ℝ := fun i => (t i - b) / c
  have hs : Function.Injective s := by
    intro i j hij
    apply hinj
    have heq : t i - b = t j - b := (div_left_inj' hc.ne').mp hij
    linarith
  have hloc : ∀ i, s i ∈ Icc (-(k : ℝ) / 2) ((k : ℝ) / 2) := by
    intro i
    obtain ⟨hil, hir⟩ := ht i
    constructor
    · apply (le_div_iff₀ hc).mpr
      dsimp [b]
      nlinarith
    · apply (div_le_iff₀ hc).mpr
      dsimp [b]
      nlinarith
  obtain ⟨y, hy⟩ := h s hs hloc
  refine ⟨y, ?_⟩
  intro f hf
  have hfa : IsBernsteinFunction (Real.pi * (1 + 1 / (k : ℝ))) H
      (bernsteinAffine f c b) := by
    simpa only [abs_of_pos hc] using hf.affine c b
  obtain ⟨i, hi⟩ := hy (bernsteinAffine f c b) hfa
  refine ⟨i, ?_⟩
  have harg : bernsteinAffine f c b (s i) = f (t i) := by
    unfold bernsteinAffine
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    congr 1
    congr 1
    dsimp [s]
    field_simp
    ring
  simpa only [harg] using hi

/--
@isnad1 id=finitebe.2h2v.s4.11c9131b3630 from=translated src=- shape=b06c76f5 vocab=082c100d
-/
theorem finiteObstruction_of_centered_real {H : ℝ} {k : ℕ} (hk : 0 < k)
    (h : CenteredRealBernsteinObstruction H k) : FiniteBernsteinObstruction H k :=
  finiteObstruction_of_injective
    (injectiveObstruction_of_centered hk (centeredObstruction_of_real h))

/-- A freely chosen shorter centered interval leaves a gap at the period ends.
The bandwidth exactly compensates for the affine compression.-/
def CenteredIntervalRealBernsteinObstruction (H : ℝ) (k : ℕ) (L : ℝ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t →
    (∀ i, t i ∈ Icc (-L / 2) (L / 2)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction (Real.pi * (((k : ℝ) + 1) / L)) H f →
        (∀ x : ℝ, (f x).im = 0) →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

/--
@isnad1 id=finitebe.2h3v.s4.44228d767dc5 from=translated src=- shape=bffad1d8 vocab=f5c6b2b9
-/
theorem finiteObstruction_of_centered_interval_real {H L : ℝ} {k : ℕ}
    (hL : 0 < L) (h : CenteredIntervalRealBernsteinObstruction H k L) :
    FiniteBernsteinObstruction H k := by
  classical
  apply finiteObstruction_of_injective
  intro t hinj a ht
  let c : ℝ := ((k : ℝ) + 1) / L
  let b : ℝ := a + ((k : ℝ) + 1) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcL : c * L = (k : ℝ) + 1 := by
    dsimp [c]
    field_simp
  let s : Fin k → ℝ := fun i => (t i - b) / c
  have hs : Function.Injective s := by
    intro i j hij
    apply hinj
    have heq : t i - b = t j - b := (div_left_inj' hc.ne').mp hij
    linarith
  have hloc : ∀ i, s i ∈ Icc (-L / 2) (L / 2) := by
    intro i
    obtain ⟨hil, hir⟩ := ht i
    constructor
    · apply (le_div_iff₀ hc).mpr
      dsimp [b]
      nlinarith
    · apply (div_le_iff₀ hc).mpr
      dsimp [b]
      nlinarith
  obtain ⟨y, hy⟩ := h s hs hloc
  refine ⟨y, ?_⟩
  intro f hf
  have hfa : IsBernsteinFunction (Real.pi * (((k : ℝ) + 1) / L)) H
      (bernsteinAffine f c b) := by
    simpa only [abs_of_pos hc] using hf.affine c b
  obtain ⟨i, hi⟩ := hy (bernsteinRealification (bernsteinAffine f c b))
    hfa.realification (bernsteinRealification_im _)
  refine ⟨i, ?_⟩
  intro heq
  apply hi
  apply bernsteinRealification_real_value
  convert heq using 1
  unfold bernsteinAffine
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  congr 1
  dsimp [s]
  field_simp
  ring

end Erdos1133
