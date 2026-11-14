import Tengoku.Seed.Probability.ProbabilityMassFunction.Constructions
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite independent sampling and probability couplings

The tuple law samples with replacement. Couplings have exact probability
marginals: no mass is deleted or supplied by a reservoir. All costs in this
module are costs between probability laws on a ground type.
-/

noncomputable section

universe u v w z

namespace TDA.Probability

open scoped ENNReal

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}

/-- Expectation of a nonnegative extended-real cost.-/
def expectation (μ : PMF X) (f : X → ℝ≥0∞) : ℝ≥0∞ := ∑' x, μ x * f x

/--
@isnad1 id=eq.0h3v.s4.f87988010cbc from=translated src=- shape=e9783546 vocab=0d0e4ecd
-/
@[simp] theorem expectation_const (μ : PMF X) (c : ℝ≥0∞) :
    expectation μ (fun _ => c) = c := by
  simp [expectation, ENNReal.tsum_mul_right, μ.tsum_coe]

/--
@isnad1 id=eq.0h3v.s4.0064350cb9f3 from=translated src=- shape=81243ce1 vocab=f142ec2b
-/
@[simp] theorem expectation_pure (x : X) (f : X → ℝ≥0∞) :
    expectation (PMF.pure x) f = f x := by
  classical
  simp [expectation, PMF.pure_apply]

/-- The pushforward identity holds without a measurable-space choice on the ground type.
@isnad1 id=eq.0h5v.s5.5d232674713b from=translated src=- shape=34d13af5 vocab=6c0e0816
-/
theorem expectation_map (μ : PMF X) (g : X → Y) (f : Y → ℝ≥0∞) :
    expectation (μ.map g) f = expectation μ (fun x => f (g x)) := by
  classical
  simp only [expectation, PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  funext x
  simp

/-- Iterated independent sampling obeys the usual iterated expectation identity.
@isnad1 id=eq.0h5v.s5.e30a6ba96a98 from=translated src=- shape=969ab4aa vocab=34f70fdd
-/
theorem expectation_bind (μ : PMF X) (ν : X → PMF Y) (f : Y → ℝ≥0∞) :
    expectation (μ.bind ν) f = expectation μ (fun x => expectation (ν x) f) := by
  simp only [expectation, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc, ENNReal.tsum_mul_left]

/--
@isnad1 id=le.1h4v.s5.27829c1a2e97 from=translated src=- shape=a1ebe783 vocab=02d29569
-/
theorem expectation_mono (μ : PMF X) {f g : X → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    expectation μ f ≤ expectation μ g :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul_right (h x) _

/-- A probability coupling; the joint law may split mass arbitrarily.-/
structure Coupling (μ : PMF X) (ν : PMF Y) where
  joint : PMF (X × Y)
  fst_map : joint.map Prod.fst = μ
  snd_map : joint.map Prod.snd = ν

namespace Coupling

variable {μ : PMF X} {ν : PMF Y}

/-- Independent coupling, showing feasibility without a transport minimizer.-/
def independent (μ : PMF X) (ν : PMF Y) : Coupling μ ν where
  joint := μ.bind fun x => ν.map fun y => (x, y)
  fst_map := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (μ.bind fun x => ν.map (Function.const Y x)) = μ
    simp [PMF.map_const, PMF.bind_pure]
  snd_map := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (μ.bind fun _ => ν.map id) = ν
    rw [PMF.map_id, PMF.bind_const]

instance : Nonempty (Coupling μ ν) := ⟨independent μ ν⟩

/-- Push forward both marginals of a coupling.-/
def map (π : Coupling μ ν) (f : X → Z) (g : Y → W) :
    Coupling (μ.map f) (ν.map g) where
  joint := π.joint.map fun xy => (f xy.1, g xy.2)
  fst_map := by
    rw [PMF.map_comp]
    change π.joint.map (f ∘ Prod.fst) = _
    rw [← PMF.map_comp, π.fst_map]
  snd_map := by
    rw [PMF.map_comp]
    change π.joint.map (g ∘ Prod.snd) = _
    rw [← PMF.map_comp, π.snd_map]

/-- On finite input types, the joint law is a nonnegative matrix with the
prescribed row sums.
@isnad1 id=eq.0h6v.s6.a1198ac6b617 from=translated src=- shape=2baebabc vocab=54dd57cf
-/
theorem row_sum [Fintype X] [Fintype Y] (π : Coupling μ ν) (x : X) :
    ∑ y, π.joint (x, y) = μ x := by
  classical
  have h := congrArg (fun p : PMF X => p x) π.fst_map
  simpa [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm] using h

/-- Every column also preserves its full prescribed probability mass.
@isnad1 id=eq.0h6v.s6.160f7f6eb614 from=translated src=- shape=56caf3cd vocab=54dd57cf
-/
theorem col_sum [Fintype X] [Fintype Y] (π : Coupling μ ν) (y : Y) :
    ∑ x, π.joint (x, y) = ν y := by
  classical
  have h := congrArg (fun p : PMF Y => p y) π.snd_map
  simpa [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type] using h

/-- Cost is integrated against the entire probability joint law.-/
def cost (π : Coupling μ ν) (c : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  expectation π.joint (fun xy => c xy.1 xy.2)

/--
@isnad1 id=eq.0h10v.s6.98b2b8c3780e from=translated src=- shape=e7d240a0 vocab=97ade764
-/
@[simp] theorem cost_map (π : Coupling μ ν) (f : X → Z) (g : Y → W)
    (c : Z → W → ℝ≥0∞) :
    (π.map f g).cost c = π.cost (fun x y => c (f x) (g y)) :=
  expectation_map _ _ _

end Coupling

/-- Iid sampling on an ordered tuple of draws, including repeated values.-/
def iid (μ : PMF X) : (n : ℕ) → PMF (Fin n → X)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => μ.bind fun x => (iid μ n).map (Fin.cons x)

/--
@isnad1 id=eq.0h2v.s5.c72fc4c98cc6 from=translated src=- shape=f1b12abb vocab=43d98b7c
-/
@[simp] theorem iid_zero (μ : PMF X) : iid μ 0 = PMF.pure Fin.elim0 := rfl

/--
@isnad1 id=eq.0h3v.s6.d13cb3f934f1 from=translated src=- shape=c710bf8e vocab=b9fcf3f6
-/
@[simp] theorem iid_succ (μ : PMF X) (n : ℕ) :
    iid μ (n + 1) = μ.bind (fun x => (iid μ n).map (Fin.cons x)) := rfl

/-- Independent sampling commutes with a deterministic map of each draw.
@isnad1 id=eq.0h5v.s5.526927a970e8 from=translated src=- shape=c9f043b2 vocab=98f03d97
-/
theorem iid_map (μ : PMF X) (f : X → Y) (n : ℕ) :
    (iid μ n).map (fun t i => f (t i)) = iid (μ.map f) n := by
  induction n with
  | zero =>
    rw [iid_zero, PMF.pure_map, iid_zero]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [iid_succ, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    congr 1
    funext x
    rw [← ih]
    change (iid μ n).map _ = ((iid μ n).map _).map _
    rw [PMF.map_comp]
    congr 1
    funext t
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Couple iid tuples by drawing iid pairs from the original coupling.-/
def Coupling.tuples {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) (n : ℕ) :
    Coupling (iid μ n) (iid ν n) where
  joint := (iid π.joint n).map (fun t => (fun i => (t i).1, fun i => (t i).2))
  fst_map := by
    rw [PMF.map_comp]
    change (iid π.joint n).map (fun t i => Prod.fst (t i)) = _
    rw [iid_map, π.fst_map]
  snd_map := by
    rw [PMF.map_comp]
    change (iid π.joint n).map (fun t i => Prod.snd (t i)) = _
    rw [iid_map, π.snd_map]

/-- Any statistic of iid samples inherits a coupling by pushforward.-/
def Coupling.sampleLaw {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) (n : ℕ)
    (f : (Fin n → X) → Z) (g : (Fin n → Y) → W) :
    Coupling ((iid μ n).map f) ((iid ν n).map g) :=
  (π.tuples n).map f g

/-- Ordinary optimal probability transport with a supplied ground cost.-/
def transportCost (c : X → Y → ℝ≥0∞) (μ : PMF X) (ν : PMF Y) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, π.cost c

/--
@isnad1 id=le.0h6v.s5.c6e4a85d7e2b from=translated src=- shape=470d39fb vocab=63f52c20
-/
theorem transportCost_le_coupling (c : X → Y → ℝ≥0∞) (μ : PMF X) (ν : PMF Y)
    (π : Coupling μ ν) : transportCost c μ ν ≤ π.cost c := iInf_le _ π

/-- The rooted p-cost of ordinary probability transport on a ground type.-/
def wasserstein (p : ℝ) (c : X → Y → ℝ≥0∞) (μ : PMF X) (ν : PMF Y) : ℝ≥0∞ :=
  transportCost (fun x y => c x y ^ p) μ ν ^ p⁻¹

/-- Taking the root after the infimum equals the infimum of the rooted costs,
so the atomic definition agrees with the usual optimal-transport convention.
@isnad1 id=eq.1h6v.s6.93177cd1ee8b from=translated src=- shape=135cd806 vocab=e3e1a949
-/
theorem wasserstein_eq_iInf {p : ℝ} (hp : 0 < p) (c : X → Y → ℝ≥0∞)
    (μ : PMF X) (ν : PMF Y) :
    wasserstein p c μ ν = ⨅ π : Coupling μ ν, π.cost (fun x y => c x y ^ p) ^ p⁻¹ := by
  exact (ENNReal.orderIsoRpow p⁻¹ (inv_pos.mpr hp)).map_iInf _

/-- Essential supremum for an atomic probability law: ignore all zero-mass points.-/
def essentialSup (μ : PMF X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ x ∈ μ.support, f x

/--
@isnad1 id=eq.0h5v.s5.c8537c57deed from=translated src=- shape=34d13af5 vocab=1527d029
-/
theorem essentialSup_map (μ : PMF X) (g : X → Y) (f : Y → ℝ≥0∞) :
    essentialSup (μ.map g) f = essentialSup μ (fun x => f (g x)) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_iSup_of_le (g x)
    apply le_iSup_of_le ((PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩)
    exact le_rfl

/-- Infinity transport cost uses the essential, rather than pointwise, supremum.-/
def wassersteinInfinity (c : X → Y → ℝ≥0∞) (μ : PMF X) (ν : PMF Y) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, essentialSup π.joint (fun xy => c xy.1 xy.2)

end TDA.Probability
