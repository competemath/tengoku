import Tengoku.RainichKaluzaReconstruction.RainichKaluza.ComplexionCouplingSystem
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exterior-form complexion identities

This file upgrades the scalar derivative model to the actual algebraic types
of exterior calculus.  A one-form-valued derivative of a duality parameter is
wedged with a two-form to produce the three-form product-rule terms.  The
result isolates the exact two EMD closure equations and shows that a
nontrivial dilaton source generically breaks the residual constant duality
circle down to the overall sign.
-/

namespace RainichKaluza

variable {One Two Three : Type*}
  [AddCommGroup One] [Module ℝ One]
  [AddCommGroup Two] [Module ℝ Two]
  [AddCommGroup Three] [Module ℝ Three]

/-- The relevant exterior product, abstracted as a bilinear map
`Ω¹ × Ω² → Ω³`.-/
abbrev OneWedgeTwo (One Two Three : Type*)
    [AddCommGroup One] [Module ℝ One]
    [AddCommGroup Two] [Module ℝ Two]
    [AddCommGroup Three] [Module ℝ Three] :=
  One →ₗ[ℝ] Two →ₗ[ℝ] Three

/-- First-order data of a local duality rotation.  `F0,G0` are a seed and its
Hodge partner; `dF0,dG0` are their exterior derivatives.-/
structure ExteriorDualityJet (One Two Three : Type*) where
  c : ℝ
  s : ℝ
  dc : One
  ds : One
  F0 : Two
  G0 : Two
  dF0 : Three
  dG0 : Three

namespace ExteriorDualityJet

variable (J : ExteriorDualityJet One Two Three)

/-- Rotated two-form.-/
def rotatedF : Two := J.c • J.F0 + J.s • J.G0

/-- Hodge partner in the convention `**=-1`.-/
def rotatedG : Two := (-J.s) • J.F0 + J.c • J.G0

/-- Exterior derivative of the rotated form, with every product-rule term
displayed.-/
def rotatedDF (wedge : OneWedgeTwo One Two Three) : Three :=
  wedge J.dc J.F0 + J.c • J.dF0 +
    wedge J.ds J.G0 + J.s • J.dG0

/-- Exterior derivative of the rotated Hodge partner.-/
def rotatedDG (wedge : OneWedgeTwo One Two Three) : Three :=
  -(wedge J.ds J.F0) + (-J.s) • J.dF0 +
    wedge J.dc J.G0 + J.c • J.dG0

/-- Seed-derivative contribution in the first channel.-/
def rotatedSeedDF : Three := J.c • J.dF0 + J.s • J.dG0

/-- Seed-derivative contribution in the Hodge channel.-/
def rotatedSeedDG : Three := (-J.s) • J.dF0 + J.c • J.dG0

/-- **Exterior complexion product rule, first channel.**-/
theorem rotatedDF_eq
    (wedge : OneWedgeTwo One Two Three) (omega : One)
    (hdc : J.dc = (-J.s) • omega) (hds : J.ds = J.c • omega) :
    J.rotatedDF wedge =
      wedge omega J.rotatedG + J.rotatedSeedDF := by
  unfold rotatedDF rotatedG rotatedSeedDF
  rw [hdc, hds]
  simp only [map_add, map_smul, LinearMap.smul_apply]
  module

/-- **Exterior complexion product rule, Hodge channel.**-/
theorem rotatedDG_eq
    (wedge : OneWedgeTwo One Two Three) (omega : One)
    (hdc : J.dc = (-J.s) • omega) (hds : J.ds = J.c • omega) :
    J.rotatedDG wedge =
      -(wedge omega J.rotatedF) + J.rotatedSeedDG := by
  unfold rotatedDG rotatedF rotatedSeedDG
  rw [hdc, hds]
  simp only [map_add, map_smul, LinearMap.smul_apply]
  module

end ExteriorDualityJet

/-- The two rescaled EMD Bianchi/Maxwell equations at the three-form level.-/
def EMDExteriorClosure
    (wedge : OneWedgeTwo One Two Three) (v : One) (a : ℝ)
    (F G : Two) (dF dG : Three) : Prop :=
  dF = (a / 2) • wedge v F ∧
    dG = -(a / 2) • wedge v G

/-- Scalar-orientation covariance of the rescaled EMD exterior system.
Reversing the reconstructed scalar covector reverses the signed coupling and
leaves both physical closure equations unchanged.-/
theorem emdExteriorClosure_neg_scalar_coupling
    (wedge : OneWedgeTwo One Two Three) (v : One) (a : ℝ)
    (F G : Two) (dF dG : Three) :
    EMDExteriorClosure wedge (-v) (-a) F G dF dG ↔
      EMDExteriorClosure wedge v a F G dF dG := by
  unfold EMDExteriorClosure
  simp only [map_neg, neg_div, neg_smul, neg_neg]
  constructor <;> rintro ⟨hF, hG⟩ <;> constructor
  · simpa only [LinearMap.neg_apply, smul_neg, neg_smul, neg_neg] using hF
  · simpa only [LinearMap.neg_apply, smul_neg, neg_smul, neg_neg] using hG
  · simpa only [LinearMap.neg_apply, smul_neg, neg_smul, neg_neg] using hF
  · simpa only [LinearMap.neg_apply, smul_neg, neg_smul, neg_neg] using hG

/-- **Exterior-form complexion/coupling reduction.** Once the unit-circle
derivatives are written using their one-form complexion `omega`, the full EMD
closure equations are equivalent to two explicit equations for the seed
derivative channels.-/
theorem emdExteriorClosure_iff_seedChannels
    (wedge : OneWedgeTwo One Two Three)
    (J : ExteriorDualityJet One Two Three) (omega v : One) (a : ℝ)
    (hdc : J.dc = (-J.s) • omega) (hds : J.ds = J.c • omega) :
    EMDExteriorClosure wedge v a J.rotatedF J.rotatedG
        (J.rotatedDF wedge) (J.rotatedDG wedge) ↔
      J.rotatedSeedDF =
          (a / 2) • wedge v J.rotatedF - wedge omega J.rotatedG ∧
        J.rotatedSeedDG =
          wedge omega J.rotatedF - (a / 2) • wedge v J.rotatedG := by
  rw [J.rotatedDF_eq wedge omega hdc hds,
    J.rotatedDG_eq wedge omega hdc hds]
  unfold EMDExteriorClosure
  constructor
  · rintro ⟨hF, hG⟩
    constructor
    · apply (eq_sub_iff_add_eq).2
      rw [add_comm]
      exact hF
    · apply (eq_sub_iff_add_eq).2
      calc
        J.rotatedSeedDG + (a / 2) • wedge v J.rotatedG =
            wedge omega J.rotatedF +
              ((-(wedge omega J.rotatedF) + J.rotatedSeedDG) -
                (-(a / 2) • wedge v J.rotatedG)) := by module
        _ = wedge omega J.rotatedF := by rw [hG]; abel
  · rintro ⟨hF, hG⟩
    constructor
    · rw [hF]
      abel
    · rw [hG]
      module

/-- If a seed pair and a constant duality rotation of it both satisfy the
same EMD equations, the sine component is annihilated by both scalar-source
channels.-/
theorem constantDuality_emd_obstruction
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0)
    (hFrot : c • dF0 + s • dG0 =
      (a / 2) • wedge v (c • F0 + s • G0))
    (hGrot : (-s) • dF0 + c • dG0 =
      -(a / 2) • wedge v ((-s) • F0 + c • G0)) :
    (a * s) • wedge v F0 = 0 ∧ (a * s) • wedge v G0 = 0 := by
  constructor
  · calc
      (a * s) • wedge v F0 =
          -(((-s) • dF0 + c • dG0) -
            (-(a / 2) • wedge v ((-s) • F0 + c • G0))) := by
              rw [hF0, hG0]
              simp only [map_add, map_smul]
              module
      _ = 0 := by rw [hGrot]; simp
  · calc
      (a * s) • wedge v G0 =
          -((c • dF0 + s • dG0) -
            ((a / 2) • wedge v (c • F0 + s • G0))) := by
              rw [hF0, hG0]
              simp only [map_add, map_smul]
              module
      _ = 0 := by rw [hFrot]; simp

/-- On a nonzero-coupling branch with at least one active scalar-source
channel, a constant duality rotation preserving the EMD equations has
vanishing sine component.-/
theorem constantDuality_s_eq_zero_of_emd
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ) (ha : a ≠ 0)
    (hactive : wedge v F0 ≠ 0 ∨ wedge v G0 ≠ 0)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0)
    (hFrot : c • dF0 + s • dG0 =
      (a / 2) • wedge v (c • F0 + s • G0))
    (hGrot : (-s) • dF0 + c • dG0 =
      -(a / 2) • wedge v ((-s) • F0 + c • G0)) :
    s = 0 := by
  obtain ⟨hVF, hVG⟩ := constantDuality_emd_obstruction wedge v F0 G0
    dF0 dG0 c s a hF0 hG0 hFrot hGrot
  have has : a * s = 0 := by
    rcases hactive with hactive | hactive
    · exact (smul_eq_zero.mp hVF).resolve_right hactive
    · exact (smul_eq_zero.mp hVG).resolve_right hactive
  exact (mul_eq_zero.mp has).resolve_left ha

/-- **Generic constant-duality collapse.** For a unit duality parameter, the
same hypotheses reduce the full circle to the overall sign `(±1,0)`.-/
theorem constantDuality_eq_sign_of_emd
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) (ha : a ≠ 0)
    (hactive : wedge v F0 ≠ 0 ∨ wedge v G0 ≠ 0)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0)
    (hFrot : c • dF0 + s • dG0 =
      (a / 2) • wedge v (c • F0 + s • G0))
    (hGrot : (-s) • dF0 + c • dG0 =
      -(a / 2) • wedge v ((-s) • F0 + c • G0)) :
    (c = 1 ∨ c = -1) ∧ s = 0 := by
  have hs := constantDuality_s_eq_zero_of_emd wedge v F0 G0 dF0 dG0
    c s a ha hactive hF0 hG0 hFrot hGrot
  have hcSq : c ^ 2 = 1 := by
    rw [hs, zero_pow (by norm_num)] at hunit
    linarith
  exact ⟨sq_eq_one_iff.mp hcSq, hs⟩

/-- If both scalar-source wedge channels vanish, every constant duality
rotation of a seed solution remains a solution.  This is the exceptional
locus complementary to the generic sign-only theorem.-/
theorem constantDuality_emd_of_inactive_source
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ)
    (hVF : wedge v F0 = 0) (hVG : wedge v G0 = 0)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0) :
    c • dF0 + s • dG0 =
        (a / 2) • wedge v (c • F0 + s • G0) ∧
      (-s) • dF0 + c • dG0 =
        -(a / 2) • wedge v ((-s) • F0 + c • G0) := by
  rw [hF0, hG0]
  simp only [map_add, map_smul, hVF, hVG, smul_zero, add_zero]
  exact ⟨trivial, trivial⟩

/-- In the uncoupled branch `a=0`, every constant duality rotation of a seed
solution remains closed.-/
theorem constantDuality_emd_of_zero_coupling
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ) (ha : a = 0)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0) :
    c • dF0 + s • dG0 =
        (a / 2) • wedge v (c • F0 + s • G0) ∧
      (-s) • dF0 + c • dG0 =
        -(a / 2) • wedge v ((-s) • F0 + c • G0) := by
  subst a
  simp at hF0 hG0
  rw [hF0, hG0]
  simp

end RainichKaluza
