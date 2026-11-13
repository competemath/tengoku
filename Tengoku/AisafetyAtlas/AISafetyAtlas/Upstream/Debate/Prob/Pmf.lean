/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Tengoku.Seed.MeasureTheory.Integral.IntegrableOn
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Basic
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Monad
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.Debate.Misc.Finset
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.Debate.Prob.Basics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Upstream/Debate/Prob/Pmf.lean`: removed 7 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

@[expose] public section
namespace Tengoku.AisafetyAtlas end Tengoku.AisafetyAtlas open Tengoku.AisafetyAtlas 
-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

/-!
`Prob` injects into `PMF`
-/

open Classical
open Set
open scoped Real Topology
noncomputable section

variable {α β γ : Type}

/-- Turn a `Prob` into a `PMF`-/
def Tengoku.AisafetyAtlas.Prob.toPmf (f : Prob α) : PMF α where
  val x := .ofReal (f.prob x)
  property := by
    have e : f.supp.sum (fun x => ENNReal.ofReal (f.prob x)) = 1 := by
      have t := f.total; simp only [Finsupp.sum] at t
      simp only [Finset.sum_ofReal (fun _ ↦ prob_nonneg _), supp, t, ENNReal.ofReal_one]
    rw [←e]; apply Finset.hasSum_sum;
    intro x m; simp only [mem_iff, not_not] at m; simp only [m, ENNReal.ofReal_zero]

/-- Turn a finitely supported `PMF` into a `Prob`-/
def PMF.toProb (f : PMF α) (finite : f.support.Finite) : Prob α where
  prob := by
    apply Finsupp.ofSupportFinite (fun x ↦ ENNReal.toReal (f x))
    rcases finite.exists_finset with ⟨s,h⟩
    apply Set.Finite.ofFinset s
    intro x
    simp only [h, PMF.mem_support_iff, ne_eq, Function.mem_support, ENNReal.toReal_eq_zero_iff,
      PMF.apply_ne_top, or_false]
  prob_nonneg := by intro x; simp only [Finsupp.ofSupportFinite_coe]; apply ENNReal.toReal_nonneg
  total := by
    rcases finite.exists_finset with ⟨s,h⟩
    apply eq_of_forall_dist_le; intro e ep
    set e' : ENNReal := .ofReal e
    have e0' : e' ≠ 0 := (ENNReal.ofReal_pos.mpr ep).ne'
    have m : 1 ∈ Ioo (1-e' : ENNReal) (1+e') := by
      simp only [ge_iff_le, gt_iff_lt, not_lt, mem_Ioo]; constructor
      · apply ENNReal.sub_lt_self; norm_num; norm_num; exact e0'
      · apply ENNReal.lt_add_right; norm_num; exact e0'
    rcases tendsto_atTop_nhds.mp f.property (Ioo (1-e') (1+e')) m isOpen_Ioo with ⟨t,total⟩
    · specialize total (s ∪ t) (Finset.subset_union_right)
      rw [←Finset.sum_subset (Finset.subset_union_left)] at total
      · simp only [Finsupp.sum, Finsupp.ofSupportFinite_coe]
        rw [@Finset.sum_subset _ _ _ s]
        · simp only [ge_iff_le, gt_iff_lt, not_lt, mem_Ioo] at total
          simp only [Finset.sum_toReal (λ _ ↦ PMF.apply_ne_top _ _), Real.dist_eq, abs_le,
            le_sub_iff_add_le, sub_le_iff_le_add, add_comm _ (1:ℝ)]
          constructor
          · rw [←ENNReal.ofReal_le_iff_le_toReal]
            · rw [←sub_eq_add_neg, ENNReal.ofReal_sub, ENNReal.ofReal_one]; exact le_of_lt total.1
              exact le_of_lt ep
            · apply Finset.sum_ne_top; intro x; apply PMF.apply_ne_top
          · apply ENNReal.toReal_le_of_le_ofReal
            · exact add_nonneg (by norm_num) (le_of_lt ep)
            · rw [ENNReal.ofReal_add, ENNReal.ofReal_one]; exact le_of_lt total.2
              · norm_num
              · exact le_of_lt ep
        · intro x
          simp only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, h,
            ENNReal.toReal_ne_zero, PMF.mem_support_iff]
          apply And.left
        · intro x _ m
          simpa only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq, not_not] using m
      · intro x _ m; exact (PMF.apply_eq_zero_iff f x).mpr (fun c ↦ m ((h x).mpr c))

/-- `Prob.toPmf` has the expected coe
@isnad1 id=eq.0h3v.s5.effd1a8720ab from=translated src=- shape=3848d58c vocab=5854fb67
-/
@[simp] lemma Tengoku.AisafetyAtlas.Prob.toPmf_coe (f : Prob α) (x : α) : f.toPmf x = ENNReal.ofReal (f.prob x) := rfl

/-- `PMF.toProb` has the expected prob
@isnad1 id=eq.1h3v.s5.c654ca1ee882 from=translated src=- shape=cceffa12 vocab=c12da4d3
-/
@[simp] lemma PMF.prob_toProb (f : PMF α) (h : f.support.Finite) (x : α) :
    (f.toProb h).prob x = ENNReal.toReal (f x) := rfl

/-- `Prob.toPmf` has finite support
@isnad1 id=finite.0h2v.s3.18f9a59d1279 from=translated src=- shape=3d086f6a vocab=eb007187
-/
lemma Tengoku.AisafetyAtlas.Prob.toPmf_support_finite (f : Prob α) : f.toPmf.support.Finite := by
  apply Set.Finite.ofFinset f.supp; intro x
  simp only [mem_iff, ne_eq, PMF.mem_support_iff, toPmf_coe, ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro h; exact Ne.lt_of_le (Ne.symm h) (prob_nonneg _)
  · intro h; exact h.ne'

/-- `Prob → PMF → Prob` is the identity
@isnad1 id=eq.0h2v.s3.f17d5bc3e8c7 from=translated src=- shape=e6906362 vocab=4a49e486
-/
theorem Tengoku.AisafetyAtlas.Prob.toProb_toPmf (f : Prob α) : f.toPmf.toProb f.toPmf_support_finite = f := by
  ext; simp only [PMF.prob_toProb, toPmf_coe, ENNReal.toReal_ofReal_eq_iff]; apply prob_nonneg

/-- `PMF → Prob → PMF` is the identity on finitely-supported `PMF`s.
@isnad1 id=eq.1h2v.s4.2c1a06e28273 from=translated src=- shape=9c9c22c4 vocab=f9e24530
-/
theorem PMF.toPmf_toProb (f : PMF α) (hf : f.support.Finite) : (f.toProb hf).toPmf = f := by
  ext
  simp [ne_eq, ENNReal.ofReal_toReal_eq_iff, apply_ne_top]

/-- `PMF.pure_apply` with `Pure.pure` rather than `PMF.pure`
@isnad1 id=eq.0h3v.s5.b933d8fdae7c from=translated src=- shape=c8d042a9 vocab=80ef304c
-/
lemma PMF.pure_apply' (x y : α) : (Pure.pure x : PMF α) y = if y = x then 1 else 0 := rfl

/-- `PMF.bind_apply` with `Bind.bind` rather than `PMF.bind`
@isnad1 id=eq.0h5v.s6.5e0ee35f405e from=translated src=- shape=b4d91b35 vocab=044249a9
-/
lemma PMF.bind_apply' (p : PMF α) (f : α → PMF β) (y : β) :
    (Bind.bind p f) y = ∑' x : α, p x * f x y := rfl

/-- `Prob.toPmf` commutes with pure
@isnad1 id=eq.0h2v.s4.89b8bae937ae from=translated src=- shape=64469822 vocab=897a2a98
-/
lemma Tengoku.AisafetyAtlas.Prob.pure_toPmf (x : α) : (pure x : Prob α).toPmf = pure x := by
  ext y; simp only [toPmf_coe, prob_pure, PMF.pure_apply']
  split_ifs; simp only [ENNReal.ofReal_one]; simp only [ENNReal.ofReal_zero]

/-- `Prob.toPmf` commutes with bind
@isnad1 id=eq.0h4v.s5.760511f459aa from=translated src=- shape=90fedbae vocab=96374cf2
-/
lemma Tengoku.AisafetyAtlas.Prob.bind_toPmf (f : Prob α) (g : α → Prob β) :
    (f >>= g).toPmf = f.toPmf >>= (fun x ↦ (g x).toPmf) := by
  ext y
  simp only [Prob.toPmf_coe, PMF.bind_apply', Prob.prob_bind, Prob.exp, Finsupp.sum,
    ←Finset.sum_ofReal fun _ ↦ mul_nonneg (prob_nonneg _) (prob_nonneg _),
    ←ENNReal.ofReal_mul (prob_nonneg _)]
  refine (HasSum.tsum_eq ?_).symm
  apply Finset.hasSum_sum
  intro _ m
  simp only [Finsupp.mem_support_iff, not_not] at m
  simp only [m, zero_mul, ENNReal.ofReal_zero]

/-- `Prob.exp` is tsum over `toPmf`
@isnad1 id=eq.0h3v.s5.e33caeb92ebd from=translated src=- shape=7f7248e9 vocab=8bbe9cf4
-/
lemma Tengoku.AisafetyAtlas.Prob.tsum_toPmf_eq_exp (f : Prob α) (u : α → ℝ) :
    ∑' x, (f.toPmf x).toReal * u x = f.exp u := by
  apply HasSum.tsum_eq; simp only [Prob.toPmf_coe, ENNReal.toReal_ofReal (prob_nonneg _)]
  apply Finset.hasSum_sum; intro _ m
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m; simp only [m, zero_mul]

/-- Everything is integrable over `PMF`s with finite support
@isnad1 id=integrab.1h3v.s5.5b995a9bfe89 from=translated src=- shape=b05f44d5 vocab=7eefeedc
-/
lemma PMF.integrable_of_support_finite (f : PMF α) (u : α → ℝ) (hf : f.support.Finite)
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasureTheory.Integrable u f.toMeasure := by
  rw [←PMF.restrict_toMeasure_support, ←MeasureTheory.IntegrableOn]
  have e : f.support = ⋃ (x : α) (_ : x ∈ hf.toFinset), {x} := by
    ext x
    simp only [mem_support_iff, ne_eq, Finite.mem_toFinset, mem_iUnion, mem_singleton_iff,
      exists_prop, exists_eq_right']
  rw [e, MeasureTheory.integrableOn_finset_iUnion]
  intro _ _
  rw [MeasureTheory.integrableOn_singleton_iff,  PMF.toMeasure_apply_singleton]
  · right; apply f.apply_lt_top
  · apply MeasurableSet.singleton

/-- Everything is integrable over `toPmf`, since it has finite support
@isnad1 id=integrab.0h3v.s5.e3044e669fdd from=translated src=- shape=dcdd4233 vocab=be5c5f7b
-/
lemma Tengoku.AisafetyAtlas.Prob.integrable_toPmf (f : Prob α) (u : α → ℝ) [MeasurableSpace α]
    [MeasurableSingletonClass α] : MeasureTheory.Integrable u f.toPmf.toMeasure :=
  PMF.integrable_of_support_finite _ _ f.toPmf_support_finite

/-- `Prob.exp` is integration over `toPmf`, if `α` is nice
@isnad1 id=eq.0h3v.s5.38f1c47005bf from=translated src=- shape=ff49ff94 vocab=da45163b
-/
lemma Tengoku.AisafetyAtlas.Prob.integral_toPmf_eq_exp (f : Prob α) (u : α → ℝ) [MeasurableSpace α]
    [MeasurableSingletonClass α] : ∫ x, u x ∂(f.toPmf.toMeasure) = f.exp u := by
  simp_rw [←Prob.tsum_toPmf_eq_exp, ←smul_eq_mul]
  exact PMF.integral_eq_tsum _ _ (f.integrable_toPmf _)
-- Tengoku: root names of this library moved to Tengoku.AisafetyAtlas so they do not collide with other libraries (generated)
