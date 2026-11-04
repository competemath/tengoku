module

public import Tengoku.AtPalomar.Paper.Targets
public import Tengoku.Seed.MeasureTheory.Integral.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Finite Sherrington--Kirkpatrick model integrability

The concrete product Gaussian coupling law has probability mass one.
Every Hamiltonian, every exponential weight, the partition function, and
its logarithm are genuinely integrable, including the harmless size-zero
case. Thus the finite free-energy expectations do not use Bochner's junk
value for a nonintegrable function.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper

/--
@isnad1 id=isprobab.0h1v.s4.be2de4ee1561 from=translated src=- shape=627ed832 vocab=dfd35237
-/
instance skCouplingLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (skCouplingLaw n) := by
  unfold skCouplingLaw
  infer_instance

/-- A Gaussian coupling coordinate is integrable under the independent product law.
@isnad1 id=integrab.0h2v.s5.03517d52f890 from=translated src=- shape=3a3cb25a vocab=a4399f73
-/
theorem integrable_skCoupling_coordinate {n : ℕ} (ij : SKEdge n) :
    Integrable (fun g : SKCouplings n => g ij) (skCouplingLaw n) := by
  apply integrable_eval
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl

/-- The actual finite SK Hamiltonian is an integrable affine Gaussian function.
@isnad1 id=integrab.0h4v.s5.4fa26790bc5f from=translated src=- shape=2e723710 vocab=863efe0d
-/
theorem integrable_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Integrable (fun g => skHamiltonian β h g σ) (skCouplingLaw n) := by
  unfold skHamiltonian
  apply Integrable.add
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro ij hij
    exact ((integrable_skCoupling_coordinate ij).mul_const
      (spinSign (σ ij.val.1))).mul_const (spinSign (σ ij.val.2))
  · exact integrable_const _

/-- An exponential Hamiltonian factors into independent Gaussian exponential moments.
@isnad1 id=integrab.0h4v.s5.bd3016572641 from=translated src=- shape=a26e7fb9 vocab=201b45ea
-/
theorem integrable_exp_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Integrable (fun g => Real.exp (skHamiltonian β h g σ)) (skCouplingLaw n) := by
  let a : SKEdge n → ℝ := fun ij =>
    β / Real.sqrt (n : ℝ) * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)
  let b : ℝ := h * ∑ i : Fin n, spinSign (σ i)
  have hprod : Integrable (fun g : SKCouplings n => ∏ ij, Real.exp (a ij * g ij))
      (skCouplingLaw n) := by
    exact Integrable.fintype_prod (fun ij =>
      integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a ij))
  have heq : (fun g : SKCouplings n => Real.exp (skHamiltonian β h g σ)) =
      fun g => Real.exp b * ∏ ij, Real.exp (a ij * g ij) := by
    funext g
    have hH : skHamiltonian β h g σ = b + ∑ ij, a ij * g ij := by
      unfold skHamiltonian a b
      rw [Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    rw [hH, Real.exp_add, Real.exp_sum]
  rw [heq]
  exact hprod.const_mul _

/--
@isnad1 id=continuo.0h4v.s5.c775b5e958bb from=translated src=- shape=04eb3f89 vocab=6cb9a032
-/
theorem continuous_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Continuous (fun g => skHamiltonian β h g σ) := by
  unfold skHamiltonian
  fun_prop

/-- The finite partition function is positive because every exponential weight is positive.
@isnad1 id=lt.0h4v.s4.f8b3771b4760 from=translated src=- shape=fbeefb1c vocab=b437af06
-/
theorem skPartitionFunction_pos {n : ℕ} (β h : ℝ) (g : SKCouplings n) :
    0 < skPartitionFunction β h g := by
  unfold skPartitionFunction
  exact Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Each single exponential weight is bounded by the full partition function.
@isnad1 id=le.0h5v.s4.8b759dafebcb from=translated src=- shape=5750e3ce vocab=275b5dd6
-/
theorem exp_skHamiltonian_le_partition {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : Real.exp (skHamiltonian β h g σ) ≤ skPartitionFunction β h g := by
  exact Finset.single_le_sum (fun τ _ => (Real.exp_pos _).le) (Finset.mem_univ σ)

/-- The logarithm of the partition function dominates each Hamiltonian.
@isnad1 id=le.0h5v.s4.6d5f6ec2afff from=translated src=- shape=efadb99e vocab=5e7b5e98
-/
theorem skHamiltonian_le_log_partition {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : skHamiltonian β h g σ ≤ Real.log (skPartitionFunction β h g) := by
  have hh := Real.log_le_log (Real.exp_pos (skHamiltonian β h g σ))
    (exp_skHamiltonian_le_partition β h g σ)
  simpa only [Real.log_exp] using hh

/-- A finite sum of integrable exponential Hamiltonians is integrable.
@isnad1 id=integrab.0h3v.s5.3d20a7ebebe4 from=translated src=- shape=c455d333 vocab=91a51f49
-/
theorem integrable_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Integrable (fun g : SKCouplings n => skPartitionFunction β h g) (skCouplingLaw n) := by
  unfold skPartitionFunction
  apply integrable_finsetSum
  intro σ hσ
  exact integrable_exp_skHamiltonian β h σ

/--
@isnad1 id=continuo.0h3v.s5.8d37c2727e60 from=translated src=- shape=f21ed3f3 vocab=474e01dc
-/
theorem continuous_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Continuous (fun g : SKCouplings n => skPartitionFunction β h g) := by
  unfold skPartitionFunction
  apply continuous_finsetSum
  intro σ hσ
  exact Real.continuous_exp.comp (continuous_skHamiltonian β h σ)

/-- A simple domination sufficient for logarithmic integrability. Any fixed
configuration can be used in the lower bound.
@isnad1 id=le.0h5v.s5.9abfbe3e1841 from=translated src=- shape=61894883 vocab=6066a41d
-/
theorem abs_log_skPartitionFunction_le {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) :
    |Real.log (skPartitionFunction β h g)| ≤ skPartitionFunction β h g + |skHamiltonian β h g σ| := by
  have hZ := skPartitionFunction_pos β h g
  have hupper := Real.log_le_sub_one_of_pos hZ
  have hlower := skHamiltonian_le_log_partition β h g σ
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (skHamiltonian β h g σ)]
  · linarith [abs_nonneg (skHamiltonian β h g σ)]

/-- The concrete finite free-energy integrand is genuinely integrable for all parameters.
@isnad1 id=integrab.0h3v.s5.e045c60c347d from=translated src=- shape=80e00293 vocab=52238b34
-/
theorem integrable_log_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Integrable (fun g : SKCouplings n => Real.log (skPartitionFunction β h g))
      (skCouplingLaw n) := by
  let σ : SKConfiguration n := fun _ => true
  have hdom := (integrable_skPartitionFunction (n := n) β h).add
    (integrable_skHamiltonian β h σ).abs
  apply hdom.mono'
  · exact ((continuous_skPartitionFunction β h).log
      (fun g => ne_of_gt (skPartitionFunction_pos β h g))).aestronglyMeasurable
  · filter_upwards [] with g
    rw [Real.norm_eq_abs]
    exact abs_log_skPartitionFunction_le β h g σ

/-- At size zero, the Hamiltonian vanishes under the totalized real normalization.
@isnad1 id=eq.0h4v.s5.f4b3380b80ab from=translated src=- shape=7fd6fd1a vocab=b21bc7f7
-/
@[simp] theorem skHamiltonian_zero (β h : ℝ) (g : SKCouplings 0) (σ : SKConfiguration 0) :
    skHamiltonian β h g σ = 0 := by
  simp [skHamiltonian]

/-- There is one configuration at size zero, and its exponential weight is one.
@isnad1 id=eq.0h3v.s4.b4424e3c5b51 from=translated src=- shape=fa7b8a09 vocab=3d743250
-/
@[simp] theorem skPartitionFunction_zero (β h : ℝ) (g : SKCouplings 0) :
    skPartitionFunction β h g = 1 := by
  simp [skPartitionFunction]

/-- The finite free energy has its explicitly stipulated harmless zero-size value.
@isnad1 id=eq.0h2v.s4.a70c480b4285 from=translated src=- shape=4f096759 vocab=36e8de58
-/
@[simp] theorem finiteSKFreeEnergy_zero (β h : ℝ) : finiteSKFreeEnergy β h 0 = 0 := by
  simp [finiteSKFreeEnergy]

end Paper
