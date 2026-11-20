import Tengoku.Hellingerrepolean4.Hellinger.ChannelSections
import Tengoku.Hellingerrepolean4.Hellinger.TranslationNoise
import Tengoku.Seed.LinearAlgebra.Pi
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact identification of the Boolean BSC with additive noise over F₂.
All coordinate changes below retain their transformed noise law. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.F2Model

abbrev F2 := ZMod 2
abbrev Cube (n : ℕ) := Fin n → F2

set_option backward.isDefEq.respectTransparency false in
def bitEquiv : Bool ≃ F2 where
  toFun := PaperSpecs.bit
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> norm_num [PaperSpecs.bit]
  right_inv z := by fin_cases z <;> norm_num [PaperSpecs.bit]

/--
@isnad1 id=eq.0h0v.s5.5c90e3009d46 from=translated src=- shape=39b6f50c vocab=0ef6ed4d
-/
@[simp] theorem bitEquiv_false : bitEquiv false = 0 := rfl
/--
@isnad1 id=eq.0h0v.s5.98a8a1cbd356 from=translated src=- shape=39b6f50c vocab=e638fadb
-/
@[simp] theorem bitEquiv_true : bitEquiv true = 1 := rfl

def bitsEquiv (ι : Type*) : (ι → Bool) ≃ (ι → F2) :=
  Equiv.arrowCongr (Equiv.refl ι) bitEquiv

/--
@isnad1 id=eq.0h3v.s6.3424d9825891 from=translated src=- shape=869c44e2 vocab=a3d91d6f
-/
@[simp] theorem bitsEquiv_apply {ι : Type*} (x : ι → Bool) (i : ι) :
    bitsEquiv ι x i = bitEquiv (x i) := rfl

/--
@isnad1 id=eq.0h3v.s6.49d4e1df2a0a from=translated src=- shape=6fb99bb0 vocab=6f0ef1ba
-/
@[simp] theorem bitsEquiv_symm_apply {ι : Type*} (x : ι → F2) (i : ι) :
    (bitsEquiv ι).symm x i = bitEquiv.symm (x i) := rfl

def sign (z : F2) : ℝ := if z = 0 then 1 else -1

/--
@isnad1 id=eq.0h1v.s4.591d9ba921f1 from=translated src=- shape=ddd41dd1 vocab=daeeb841
-/
@[simp] theorem sign_bit (b : Bool) : sign (bitEquiv b) = boolSign b := by
  cases b <;> norm_num [sign, boolSign]

/--
@isnad1 id=eq.0h2v.s5.fbf5e39694c6 from=translated src=- shape=0438c7a3 vocab=acdb543a
-/
theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  obtain ⟨a, rfl⟩ := bitEquiv.surjective a
  obtain ⟨b, rfl⟩ := bitEquiv.surjective b
  cases a <;> cases b <;> norm_num [sign, show (1 : F2) + 1 = 0 from rfl]

def transportedChannel {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (K : UniformChannel Ω) : UniformChannel Λ where
  weight x y := K.weight (e.symm x) (e.symm y)
  nonneg x y := K.nonneg _ _
  row_sum x := by rw [e.symm.sum_comp]; exact K.row_sum _
  column_sum y := by
    rw [e.symm.sum_comp (fun x => K.weight x (e.symm y))]
    exact K.column_sum _

/--
@isnad1 id=eq.0h6v.s6.176d5e139595 from=translated src=- shape=b28dfbc7 vocab=7f180fec
-/
theorem transportedChannel_apply {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (K : UniformChannel Ω) (f : Λ → ℝ) (x : Ω) :
    (transportedChannel e K).apply f (e x) = K.apply (f ∘ e) x := by
  simp only [UniformChannel.apply, transportedChannel, Equiv.symm_apply_apply,
    Function.comp_apply]
  rw [← e.sum_comp (fun y => K.weight x (e.symm y) * f y)]
  simp only [Equiv.symm_apply_apply]

def oneStep (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel F2 :=
  transportedChannel bitEquiv (bsc ρ hρ)

/--
@isnad1 id=eq.1h3v.s6.29a0563ff1ff from=translated src=- shape=13d8c035 vocab=4f04639d
-/
theorem oneStep_weight (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : F2) :
    (oneStep ρ hρ).weight x y = if x = y then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  simp [oneStep, transportedChannel, bsc]

def noise (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel (ι → F2) :=
  UniformChannel.product (fun _ : ι => oneStep ρ hρ)

/--
@isnad1 id=eq.1h4v.s7.1e166ab71d73 from=translated src=- shape=191cdeb4 vocab=ea6bc60c
-/
theorem noise_weight_bits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : ι → Bool) :
    (noise ι ρ hρ).weight (bitsEquiv ι x) (bitsEquiv ι y) =
      (ChannelSections.indexedBSC ι ρ hρ).weight x y := by
  simp [noise, UniformChannel.product, oneStep, transportedChannel,
    ChannelSections.indexedBSC]

/--
@isnad1 id=eq.1h4v.s7.e4fd9c3b96ef from=translated src=- shape=7d33cd52 vocab=1ff0a268
-/
theorem noise_apply_bits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → F2) → ℝ) (x : ι → Bool) :
    (noise ι ρ hρ).apply f (bitsEquiv ι x) =
      (ChannelSections.indexedBSC ι ρ hρ).apply (f ∘ bitsEquiv ι) x := by
  unfold UniformChannel.apply
  rw [← (bitsEquiv ι).sum_comp
    (fun y => (noise ι ρ hρ).weight (bitsEquiv ι x) y * f y)]
  simp only [noise_weight_bits, Function.comp_apply]

def errorMass {ι : Type*} [Fintype ι] (ρ : ℝ) (e : ι → F2) : ℝ :=
  ∏ i, if e i = 0 then (1 + ρ) / 2 else (1 - ρ) / 2

/--
@isnad1 id=iff.0h2v.s5.657c191718dd from=translated src=- shape=57b3104e vocab=a43a7b57
-/
theorem add_eq_zero_iff (x y : F2) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]

/--
@isnad1 id=eq.1h4v.s6.54e6315f8bea from=translated src=- shape=d344ae21 vocab=9fd3be4b
-/
theorem noise_weight_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : ι → F2) :
    (noise ι ρ hρ).weight x y = errorMass ρ (x + y) := by
  simp only [noise, UniformChannel.product, oneStep_weight, errorMass, Pi.add_apply,
    add_eq_zero_iff]

/--
@isnad1 id=le.1h3v.s5.b349dc1a081d from=translated src=- shape=f41b36d2 vocab=fda669b5
-/
theorem errorMass_nonneg {ι : Type*} [Fintype ι] (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (e : ι → F2) : 0 ≤ errorMass ρ e := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [hρ.1, hρ.2]

/--
@isnad1 id=eq.1h2v.s6.17a373d955a2 from=translated src=- shape=879d6e9a vocab=1570256c
-/
theorem errorMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : (∑ e : ι → F2, errorMass ρ e) = 1 := by
  have h := (noise ι ρ hρ).row_sum 0
  simp only [noise_weight_additive, zero_add] at h
  exact h

/--
@isnad1 id=eq.1h4v.s7.5fe9cd7a7103 from=translated src=- shape=9a84bf77 vocab=57212ad5
-/
theorem noise_apply_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → F2) → ℝ) (y : ι → F2) :
    (noise ι ρ hρ).apply f y = ∑ e, errorMass ρ e * f (y + e) := by
  unfold UniformChannel.apply
  rw [← Equiv.sum_comp (Equiv.addLeft y)
    (fun x => (noise ι ρ hρ).weight y x * f x)]
  simp only [Equiv.coe_addLeft, noise_weight_additive]
  have hyy : y + y = 0 := by
    ext i
    exact (add_eq_zero_iff (y i) (y i)).mpr rfl
  simp only [← add_assoc, hyy, zero_add]

end Hellinger.F2Model
