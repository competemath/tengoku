/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.PiecewiseC1PathOn

/-!
# Basic Definitions for Complex Analysis with Principal Values

Core definitions for piecewise C¹ curves, Cauchy principal value integrals,
and generalized winding numbers following Hungerbühler–Wasem.

## Main definitions

* `PiecewiseC1Curve`: a continuous curve `γ : [a, b] → ℂ` that is `C¹` away from a finite
  partition of the interval.
* `PiecewiseC1Immersion`: a piecewise `C¹` curve with nonzero derivative (one-sided limits
  at partition points are nonzero).
* `cauchyPrincipalValue'`: the Cauchy principal value of `∮_γ f(z) dz` excluding
  `ε`-neighbourhoods of a singularity `z₀`.
* `generalizedWindingNumber'`: the winding number of `γ` around `z₀` defined via the
  Cauchy principal value.

## Main results

* `intervalIntegrable_of_piecewise_continuousOn_bounded`: a piecewise continuous bounded
  function is interval integrable.
* `hasDerivWithinAt_zero_of_deriv_zero_off_finite`: if `f` is continuous on `[a, b]` and
  has zero derivative off a finite set, then its right derivative vanishes everywhere on
  `[a, b)`.
* `continuousWithinAt_integral_of_dominated_piecewise`: dominated convergence for
  parametric integrals over a piecewise continuous family.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A piecewise continuously differentiable curve `γ : [a, b] → ℂ`, `C¹` on each
subinterval between partition points. Layers an Icc-style `partition` (endpoints included)
on top of an inherited `PiecewiseC1PathOn a b hab x y` whose partition is Ioo-style. -/
@[ext]
structure PiecewiseC1Curve where
  /-- Left endpoint of the parameter interval. -/
  a : ℝ
  /-- Right endpoint of the parameter interval. -/
  b : ℝ
  /-- Source value `γ(a)`. -/
  x : ℂ
  /-- Target value `γ(b)`. -/
  y : ℂ
  /-- The parameter interval is non-degenerate. -/
  hab : a < b
  /-- Underlying piecewise C¹ path on `[a, b]` from `x` to `y`. -/
  toPiecewiseC1PathOn : PiecewiseC1PathOn a b hab x y
  /-- The Icc-style partition (with endpoints `a, b` included). -/
  partition : Finset ℝ
  /-- The partition lies inside `[a, b]`. -/
  partition_subset : (partition : Set ℝ) ⊆ Icc a b
  /-- Both endpoints `a` and `b` belong to the partition. -/
  endpoints_in_partition : a ∈ partition ∧ b ∈ partition
  /-- The Icc-style partition is the inherited Ioo-style one with endpoints adjoined. -/
  partition_eq : partition = insert a (insert b toPiecewiseC1PathOn.partition)

namespace PiecewiseC1Curve

/-- The underlying function `ℝ → ℂ` of a piecewise `C¹` curve. -/
def toFun (γ : PiecewiseC1Curve) : ℝ → ℂ := γ.toPiecewiseC1PathOn.toFun

instance : CoeFun PiecewiseC1Curve fun _ ↦ ℝ → ℂ where coe := toFun

/--
@isnad1 id=continuo.0h1v.s5.7df42f330a22 from=translated src=- shape=21d96725 vocab=3a0136e7
-/
theorem continuous_toFun (γ : PiecewiseC1Curve) :
    ContinuousOn γ.toFun (Icc γ.a γ.b) := γ.toPiecewiseC1PathOn.continuous_toFun

private theorem notMem_innerPartition_of_notMem_partition (γ : PiecewiseC1Curve) {t : ℝ}
    (htn : t ∉ γ.partition) : t ∉ γ.toPiecewiseC1PathOn.partition := fun h_in => htn <| by
  rw [γ.partition_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_in)

/-- Differentiability off the (Icc-style) partition.
@isnad1 id=differen.2h2v.s6.80f5775486b7 from=translated src=- shape=44508a61 vocab=43666d52
-/
theorem smooth_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Icc γ.a γ.b, t ∉ γ.partition → DifferentiableAt ℝ γ.toFun t := fun t ht htn => by
  have h_ne_a : t ≠ γ.a := fun h => htn (h ▸ γ.endpoints_in_partition.1)
  have h_ne_b : t ≠ γ.b := fun h => htn (h ▸ γ.endpoints_in_partition.2)
  exact γ.toPiecewiseC1PathOn.differentiable_off t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h_ne_a), lt_of_le_of_ne ht.2 h_ne_b⟩
    (γ.notMem_innerPartition_of_notMem_partition htn)

/--
@isnad1 id=continuo.2h2v.s6.db24d049f712 from=translated src=- shape=3860fe84 vocab=461f02d7
-/
theorem deriv_continuous_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Ioo γ.a γ.b, t ∉ γ.partition → ContinuousAt (deriv γ.toFun) t := fun t ht htn =>
  γ.toPiecewiseC1PathOn.deriv_continuous_off t ht
    (γ.notMem_innerPartition_of_notMem_partition htn)

/-- **Smart constructor** from the legacy Icc-style field set. Reconstructs the underlying
`PiecewiseC1PathOn` by carving the partition's interior `partition.erase a |>.erase b`. -/
def ofIccPartition (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b) (partition : Finset ℝ)
    (partition_subset : (partition : Set ℝ) ⊆ Icc a b)
    (endpoints_in_partition : a ∈ partition ∧ b ∈ partition)
    (continuous_toFun : ContinuousOn toFun (Icc a b))
    (smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t)
    (deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition →
      ContinuousAt (deriv toFun) t) : PiecewiseC1Curve := by
  classical
  let openPart : Finset ℝ := (partition.erase a).erase b
  have h_eq : partition = insert a (insert b openPart) := by
    ext s
    by_cases h_a : s = a
    · simp [h_a, endpoints_in_partition.1]
    by_cases h_b : s = b
    · simp [h_b, endpoints_in_partition.2]
    simp [openPart, Finset.mem_insert, Finset.mem_erase, h_a, h_b]
  have h_sub : (openPart : Set ℝ) ⊆ Ioo a b := fun t ht => by
    obtain ⟨h_ne_b, ht'⟩ := Finset.mem_erase.mp ht
    obtain ⟨h_ne_a, h_in⟩ := Finset.mem_erase.mp ht'
    have h_icc := partition_subset h_in
    exact ⟨lt_of_le_of_ne h_icc.1 (Ne.symm h_ne_a), lt_of_le_of_ne h_icc.2 h_ne_b⟩
  have h_not : ∀ {t : ℝ}, t ∈ Ioo a b → t ∉ openPart → t ∉ partition :=
    fun {t} ht htn h_in => htn <| Finset.mem_erase.mpr ⟨ne_of_lt ht.2,
      Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, h_in⟩⟩
  exact
    { a := a, b := b, hab := hab, x := toFun a, y := toFun b
      toPiecewiseC1PathOn :=
        { toFun := toFun, source := rfl, target := rfl
          continuous_toFun := continuous_toFun
          partition := openPart, partition_subset := h_sub
          differentiable_off := fun t ht htn =>
            smooth_off_partition t (Ioo_subset_Icc_self ht) (h_not ht htn)
          deriv_continuous_off := fun t ht htn =>
            deriv_continuous_off_partition t ht (h_not ht htn) }
      partition := partition
      partition_subset := partition_subset
      endpoints_in_partition := endpoints_in_partition
      partition_eq := h_eq }

/--
@isnad1 id=eq.6h4v.s8.f01f9c268389 from=translated src=- shape=4c029a89 vocab=4b986563
-/
@[simp] theorem ofIccPartition_toFun (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).toFun = toFun := rfl

/--
@isnad1 id=eq.6h4v.s8.3c2c3b59dec4 from=translated src=- shape=d7f58ba0 vocab=81675d27
-/
@[simp] theorem ofIccPartition_a (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).a = a := rfl

/--
@isnad1 id=eq.6h4v.s8.3462818cb13a from=translated src=- shape=ba6a1438 vocab=fcd30ea9
-/
@[simp] theorem ofIccPartition_b (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).b = b := rfl

end PiecewiseC1Curve

/-- A closed curve has γ(a) = γ(b). -/
def PiecewiseC1Curve.IsClosed (γ : PiecewiseC1Curve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise `C¹` immersion: a piecewise `C¹` curve whose derivative is nonzero and
admits nonzero one-sided limits at every partition point. -/
@[ext]
structure PiecewiseC1Immersion extends PiecewiseC1Curve where
  /-- The derivative is nonzero off the partition. -/
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toPiecewiseC1PathOn.toFun t ≠ 0
  /-- At every interior partition point the left limit of the derivative is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, a < p →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[<] p) (𝓝 L)
  /-- At every interior partition point the right limit of the derivative is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, p < b →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[>] p) (𝓝 L)

/-- The Cauchy principal value of ∮_γ f(z) dz exists with value `L`: the ε-truncated
integral along `γ` over `[a, b]` (excluding the ε-neighbourhood of `z₀`) tends to `L`
as `ε → 0⁺`. **Primary API predicate** (Tendsto-based, raw `ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPV' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε ↦
      ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] 0) (𝓝 L)

/-- The Cauchy principal value of ∮_γ f(z) dz, excluding ε-neighborhoods of z₀.
limUnder-based; secondary. Returns junk when the limit does not exist; use
`HasCauchyPV'` for the predicate. -/
def cauchyPrincipalValue' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists; abbreviation `∃ L, HasCauchyPV' f γ a b z₀ L`. -/
def CauchyPrincipalValueExists' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, HasCauchyPV' f γ a b z₀ L

/-- Bridge theorem: if `HasCauchyPV' f γ a b z₀ L`, then
`cauchyPrincipalValue' f γ a b z₀ = L`.
@isnad1 id=eq.1h6v.s5.b4365312aa2f from=translated src=- shape=cfe81e18 vocab=cb5eea94
-/
theorem HasCauchyPV'.cauchyPV_eq {f : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z₀ : ℂ} {L : ℂ} (h : HasCauchyPV' f γ a b z₀ L) :
    cauchyPrincipalValue' f γ a b z₀ = L :=
  h.limUnder_eq

/-- The limit in `HasCauchyPV'` is unique.
@isnad1 id=eq.2h7v.s5.4a9b625ef927 from=translated src=- shape=cd526d90 vocab=a650366e
-/
theorem HasCauchyPV'.unique {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPV' f γ a b z₀ L₁) (h₂ : HasCauchyPV' f γ a b z₀ L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

/-! ### Algebraic API for `HasCauchyPV'`

These lemmas let downstream sites stop hand-rolling the `Tendsto` manipulation that
arises whenever one CPV is built from another via an algebraic identity on the
integrand. -/

/-- The CPV integrand `if ε < ‖γ t - z₀‖ then f(γ t) * deriv γ t else 0` is congr in `f`.
@isnad1 id=hascauch.2h7v.s5.7ab9aa84a9cd from=translated src=- shape=731396d0 vocab=a650366e
-/
theorem HasCauchyPV'.congr_along_curve {f g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (h_eq : ∀ t, f (γ t) = g (γ t)) :
    HasCauchyPV' g γ a b z₀ L := by
  show Tendsto _ _ _
  refine Filter.Tendsto.congr (fun ε => intervalIntegral.integral_congr fun t _ => ?_) h
  split_ifs <;> simp [h_eq]

/-- Scalar multiplication: if the CPV of `f` is `L`, then the CPV of `c * f` is `c * L`.
@isnad1 id=hascauch.1h7v.s5.e5b544c69b4d from=translated src=- shape=a583240e vocab=17c472ef
-/
theorem HasCauchyPV'.const_mul {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (c : ℂ) :
    HasCauchyPV' (fun z => c * f z) γ a b z₀ (c * L) := by
  have h_eq : (fun ε => ∫ t in a..b, if ‖γ t - z₀‖ > ε
        then (c * f (γ t)) * deriv γ t else 0) =
      fun ε => c * ∫ t in a..b, if ‖γ t - z₀‖ > ε
        then f (γ t) * deriv γ t else 0 := by
    ext ε
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    split_ifs <;> ring
  show Tendsto _ _ _
  rw [h_eq]
  exact Filter.Tendsto.const_mul c h

/-- Right-multiplication by a scalar: CPV of `f * c` is `L * c`.
@isnad1 id=hascauch.1h7v.s5.0fd32da02f71 from=translated src=- shape=22cdfc27 vocab=17c472ef
-/
theorem HasCauchyPV'.mul_const {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (c : ℂ) :
    HasCauchyPV' (fun z => f z * c) γ a b z₀ (L * c) := by
  simpa [mul_comm] using h.const_mul c

/-- The shift `f z = g (z - c)` translates the CPV: if `HasCauchyPV' g (γ - c) … L`,
then `HasCauchyPV' f γ … L` (when `f` agrees with `g (· - c)` on the curve).
@isnad1 id=hascauch.2h7v.s5.2fc549c35745 from=translated src=- shape=b5952611 vocab=a650366e
-/
theorem HasCauchyPV'.of_eventuallyEq_along_curve
    {f g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' g γ a b z₀ L) (h_eq : ∀ t, g (γ t) = f (γ t)) :
    HasCauchyPV' f γ a b z₀ L :=
  h.congr_along_curve h_eq

/-- Avoidance: if `γ` stays away from `z₀` on `[a, b]`, then the CPV equals the
ordinary integral; in particular it exists.
@isnad1 id=hascauch.3h5v.s7.9fe22835f423 from=translated src=- shape=99209ce4 vocab=f35c4302
-/
theorem HasCauchyPV'.of_avoidance {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    HasCauchyPV' f γ a b z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, left_mem_Icc.mpr hab⟩ (h_cont.sub continuousOn_const).norm
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 ‖γ t₀ - z₀‖,
    Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))), fun ε hε => ?_⟩
  exact intervalIntegral.integral_congr fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact (ite_eq_left (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

/-- Concatenation: CPV on adjacent intervals `[a, b]` and `[b, c]` glues to `[a, c]`.
@isnad1 id=hascauch.5h8v.s7.41c09a87f2ec from=translated src=- shape=26152bef vocab=085b0958
-/
theorem HasCauchyPV'.concat {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b c : ℝ} {z₀ : ℂ}
    {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPV' f γ a b z₀ L₁) (h_bc : HasCauchyPV' f γ b c z₀ L₂)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    HasCauchyPV' f γ a c z₀ (L₁ + L₂) := by
  show Tendsto _ _ _
  refine Filter.Tendsto.congr' ?_ (Filter.Tendsto.add h_ab h_bc)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hII := h_int ε hε
  have hac := hab.trans hbc
  exact intervalIntegral.integral_add_adjacent_intervals
    (hII.mono_set <| by rw [uIcc_of_le hab, uIcc_of_le hac]; exact Icc_subset_Icc_right hbc)
    (hII.mono_set <| by rw [uIcc_of_le hbc, uIcc_of_le hac]; exact Icc_subset_Icc_left hab)

/-- Existence version of avoidance.
@isnad1 id=cauchypr.3h5v.s6.be97786af8ac from=translated src=- shape=e3ea94e6 vocab=61652196
-/
theorem cauchyPrincipalValueExists'_of_avoidance {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {z₀ : ℂ} (h_cont : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    CauchyPrincipalValueExists' f γ a b z₀ :=
  ⟨_, HasCauchyPV'.of_avoidance h_cont hab h_avoid⟩

/-- Existence version of concatenation.
@isnad1 id=cauchypr.5h6v.s7.41f1dd094c7f from=translated src=- shape=6a886021 vocab=b17dc581
-/
theorem CauchyPrincipalValueExists'.concat {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b c : ℝ}
    {z₀ : ℂ} (h_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (h_bc : CauchyPrincipalValueExists' f γ b c z₀) (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    CauchyPrincipalValueExists' f γ a c z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂ hab hbc h_int⟩

/-- The generalized winding number of γ around z₀, defined via principal value.
`n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)`. -/
def generalizedWindingNumber' (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t ↦ γ t - z₀) a b 0

end
