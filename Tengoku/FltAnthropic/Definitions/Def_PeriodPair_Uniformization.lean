import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped PeriodPair UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

/--
@isnad1 id=eq.0h1v.s3.dfec7f651dc2 from=translated src=- shape=562e4a6d vocab=de78572c
-/
@[simp] theorem weierstrassCurve_a₁ : L.weierstrassCurve.a₁ = 0 := rfl
/--
@isnad1 id=eq.0h1v.s3.d6b2f25689c4 from=translated src=- shape=562e4a6d vocab=811dde72
-/
@[simp] theorem weierstrassCurve_a₂ : L.weierstrassCurve.a₂ = 0 := rfl
/--
@isnad1 id=eq.0h1v.s3.2232698e709f from=translated src=- shape=562e4a6d vocab=81982a83
-/
@[simp] theorem weierstrassCurve_a₃ : L.weierstrassCurve.a₃ = 0 := rfl
/--
@isnad1 id=eq.0h1v.s4.fa43eaee63ad from=translated src=- shape=35fdf16a vocab=73e9b82a
-/
@[simp] theorem weierstrassCurve_a₄ : L.weierstrassCurve.a₄ = -L.g₂ / 4 := rfl
/--
@isnad1 id=eq.0h1v.s4.7103c3b39d36 from=translated src=- shape=35fdf16a vocab=bf0ed8d6
-/
@[simp] theorem weierstrassCurve_a₆ : L.weierstrassCurve.a₆ = -L.g₃ / 4 := rfl

/--
@isnad1 id=eq.0h1v.s6.c6d6bae7bc59 from=translated src=- shape=4d98a53f vocab=2d5f940d
-/
theorem weierstrassCurve_Δ : L.weierstrassCurve.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring

/--
@isnad1 id=eq.0h1v.s4.7eeba68e1938 from=translated src=- shape=5d8fa2f0 vocab=63cc2ab4
-/
theorem weierstrassCurve_c₄ : L.weierstrassCurve.c₄ = 12 * L.g₂ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, weierstrassCurve_a₁,
    weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄]
  ring

/--
@isnad1 id=equation.1h2v.s6.c8f2331d4893 from=translated src=- shape=36ddfcec vocab=fb364317
-/
theorem equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := L.derivWeierstrassP_sq z hz
  show (℘'[L] z / 2) ^ 2 + L.weierstrassCurve.a₁ * ℘[L] z * (℘'[L] z / 2) +
      L.weierstrassCurve.a₃ * (℘'[L] z / 2) = ℘[L] z ^ 3 + L.weierstrassCurve.a₂ * ℘[L] z ^ 2 +
      L.weierstrassCurve.a₄ * ℘[L] z + L.weierstrassCurve.a₆
  rw [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  linear_combination (1 / 4 : ℂ) * h

def DiscriminantNeZero : Prop :=
  L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0

/--
@isnad1 id=ne.1h1v.s4.6e2240d1e276 from=translated src=- shape=fd8e17d5 vocab=09b285fb
-/
theorem DiscriminantNeZero.weierstrassCurve_Δ_ne_zero {L : PeriodPair}
    (h : L.DiscriminantNeZero) : L.weierstrassCurve.Δ ≠ 0 := by
  rwa [L.weierstrassCurve_Δ]

open Classical in

def toPoint (h : L.DiscriminantNeZero) (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0
  else .some _ _ ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    h.weierstrassCurve_Δ_ne_zero).mp (L.equation_weierstrassP hz))

/--
@isnad1 id=eq.2h2v.s6.bb34340c4f3d from=translated src=- shape=1e0cf6d2 vocab=e8467a67
-/
@[simp]
theorem toPoint_of_mem (h : L.DiscriminantNeZero) {z : ℂ} (hz : z ∈ L.lattice) :
    L.toPoint h z = 0 := by simp [toPoint, hz]

/--
@isnad1 id=eq.1h1v.s5.693ca16b1933 from=translated src=- shape=4a826490 vocab=c289855c
-/
@[simp]
theorem toPoint_zero (h : L.DiscriminantNeZero) : L.toPoint h 0 = 0 :=
  L.toPoint_of_mem h (zero_mem _)

/--
@isnad1 id=eq.2h2v.s6.189866b31939 from=translated src=- shape=6005459c vocab=c0a6ee6d
-/
theorem toPoint_of_notMem (h : L.DiscriminantNeZero) {z : ℂ} (hz : z ∉ L.lattice) :
    L.toPoint h z = .some _ _ ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      h.weierstrassCurve_Δ_ne_zero).mp (L.equation_weierstrassP hz)) := by
  simp [toPoint, hz]

def IsUniformization (h : L.DiscriminantNeZero) : Prop :=
  (∀ z w, L.toPoint h (z + w) = L.toPoint h z + L.toPoint h w) ∧
    Function.Surjective (L.toPoint h) ∧
      ∀ z, L.toPoint h z = 0 → z ∈ L.lattice

def jLattice : ℂ := 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

/--
@isnad1 id=eq.0h1v.s5.6f62c5f62255 from=translated src=- shape=b0f0d339 vocab=9cc4f663
-/
theorem jLattice_eq_c₄_pow_three_div_Δ :
    L.jLattice = L.weierstrassCurve.c₄ ^ 3 / L.weierstrassCurve.Δ := by
  rw [jLattice, weierstrassCurve_c₄, weierstrassCurve_Δ]
  by_cases h : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 0
  · rw [h, div_zero, div_zero]
  · rw [div_eq_div_iff h h]
    ring

def JSurjective : Prop :=
  ∀ c : ℂ, ∃ L : PeriodPair, L.DiscriminantNeZero ∧ L.jLattice = c

/--
@isnad1 id=linearin.0h1v.s6.7933d861fb0f from=translated src=- shape=5dd7ed49 vocab=129793df
-/
theorem linearIndependent_coe_upperHalfPlane_one (τ : ℍ) :
    LinearIndependent ℝ ![(τ : ℂ), (1 : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have him : (a • (τ : ℂ) + b • (1 : ℂ)).im = 0 := by rw [h]; simp
  simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_zero, add_zero] at him
  have ha : a = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt τ.im_pos)
  subst ha
  simp only [zero_smul, zero_add, smul_eq_zero, one_ne_zero, or_false] at h
  exact ⟨rfl, h⟩

def ofTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := linearIndependent_coe_upperHalfPlane_one τ

/--
@isnad1 id=eq.0h1v.s3.4af8f1f070ad from=translated src=- shape=7718e021 vocab=c221786c
-/
@[simp] theorem ofTau_ω₁ (τ : ℍ) : (ofTau τ).ω₁ = (τ : ℂ) := rfl
/--
@isnad1 id=eq.0h1v.s3.568dba1556e7 from=translated src=- shape=f6b6ad72 vocab=9cf2dc74
-/
@[simp] theorem ofTau_ω₂ (τ : ℍ) : (ofTau τ).ω₂ = 1 := rfl

/--
@isnad1 id=eq.0h1v.s5.647bacf580b1 from=translated src=- shape=0c82983b vocab=994631bd
-/
@[simp] theorem ofTau_lattice (τ : ℍ) :
    (ofTau τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := rfl

section Scale

variable (α : ℂˣ)

/--
@isnad1 id=linearin.0h2v.s6.86bec2e33db8 from=translated src=- shape=a5ced6a6 vocab=5cefbb44
-/
theorem scale_indep : LinearIndependent ℝ ![(α : ℂ) * L.ω₁, (α : ℂ) * L.ω₂] := by
  have h : ![(α : ℂ) * L.ω₁, (α : ℂ) * L.ω₂] = (LinearMap.mulLeft ℝ (α : ℂ)) ∘ ![L.ω₁, L.ω₂] := by
    funext i; fin_cases i <;> simp
  rw [h]
  exact L.indep.map' (LinearMap.mulLeft ℝ (α : ℂ))
    (LinearMap.ker_eq_bot_of_injective (mul_right_injective₀ α.ne_zero))

def scale : PeriodPair where
  ω₁ := (α : ℂ) * L.ω₁
  ω₂ := (α : ℂ) * L.ω₂
  indep := L.scale_indep α

/--
@isnad1 id=eq.0h2v.s4.46c26f951ed3 from=translated src=- shape=29ac6188 vocab=7a1ce2ed
-/
@[simp] theorem scale_ω₁ : (L.scale α).ω₁ = (α : ℂ) * L.ω₁ := rfl
/--
@isnad1 id=eq.0h2v.s4.84934869f16b from=translated src=- shape=29ac6188 vocab=9b88390e
-/
@[simp] theorem scale_ω₂ : (L.scale α).ω₂ = (α : ℂ) * L.ω₂ := rfl

end Scale

def sublatticeIndex (L L' : PeriodPair) : ℕ :=
  (L'.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).index

abbrev sublatticeQuotient (L L' : PeriodPair) :=
  L.lattice.toAddSubgroup ⧸ L'.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup

end PeriodPair

end
