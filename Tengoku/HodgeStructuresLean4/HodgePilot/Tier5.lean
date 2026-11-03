import Tengoku.HodgeStructuresLean4.HodgePilot.Tier3

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tier 5 (the audit's ℚ-transfer spike): conjugation `σ = conj ⊗ id` on the
complexification `ℂ ⊗[ℚ] V` of a RATIONAL vector space, as a
`starRingEnd ℂ`-semilinear involutive equivalence; plus a ℤ smoke test. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

/-- Complex conjugation as a `ℚ`-linear map (restriction of scalars of the
`ℝ`-algebra automorphism).-/
def conjQ : ℂ →ₗ[ℚ] ℂ :=
  Complex.conjAe.toLinearMap.restrictScalars ℚ

/--
@isnad1 id=eq.0h1v.s7.0e047e6520b5 from=translated src=- shape=41c5cfe3 vocab=1b76ed9d
-/
@[simp] theorem conjQ_apply (z : ℂ) : conjQ z = (starRingEnd ℂ) z := rfl

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Conjugation `σ = conj ⊗ id` on `ℂ ⊗[ℚ] V`, as a `ℚ`-linear map.-/
def sigmaQR : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.map conjQ LinearMap.id

/--
@isnad1 id=eq.0h3v.s9.d7e2ad1cac3b from=translated src=- shape=722d4ea0 vocab=fba768b7
-/
@[simp] theorem sigmaQR_tmul (c : ℂ) (v : V) :
    sigmaQR V (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ) c ⊗ₜ[ℚ] v := by
  simp [sigmaQR, TensorProduct.map_tmul]

/--
@isnad1 id=eq.0h2v.s10.5b361900d01b from=translated src=- shape=f1d3ebae vocab=5979e13f
-/
theorem sigmaQR_involutive (x : ℂ ⊗[ℚ] V) : sigmaQR V (sigmaQR V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
@isnad1 id=eq.0h3v.s10.698519779392 from=translated src=- shape=75c60031 vocab=3bffb384
-/
theorem sigmaQR_smul (c : ℂ) (x : ℂ ⊗[ℚ] V) :
    sigmaQR V (c • x) = (starRingEnd ℂ) c • sigmaQR V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c' v =>
      rw [TensorProduct.smul_tmul', sigmaQR_tmul, sigmaQR_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Conjugation on `ℂ ⊗[ℚ] V` as a `starRingEnd ℂ`-semilinear map.-/
def sigmaQ : (ℂ ⊗[ℚ] V) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℚ] V) where
  toFun := sigmaQR V
  map_add' := map_add (sigmaQR V)
  map_smul' := sigmaQR_smul V

/--
@isnad1 id=eq.0h2v.s10.bff310713f5a from=translated src=- shape=1b22459c vocab=806ff481
-/
@[simp] theorem sigmaQ_apply (x : ℂ ⊗[ℚ] V) : sigmaQ V x = sigmaQR V x := rfl

/--
@isnad1 id=eq.0h2v.s10.3756d7bff26a from=translated src=- shape=0fb1eb48 vocab=9466d1ce
-/
theorem sigmaQ_sigmaQ (x : ℂ ⊗[ℚ] V) : sigmaQ V (sigmaQ V x) = x := by
  simp [sigmaQR_involutive]

/--
@isnad1 id=surjecti.0h1v.s9.943c69c5e349 from=translated src=- shape=c0e197d0 vocab=1755abcc
-/
theorem sigmaQ_surjective : Function.Surjective (sigmaQ V) :=
  fun x => ⟨sigmaQ V x, sigmaQ_sigmaQ V x⟩

/-- The audit's requested `LinearEquiv` upgrade: `σ` as a semilinear
equivalence of `ℂ ⊗[ℚ] V` with itself.-/
def sigmaQEquiv : (ℂ ⊗[ℚ] V) ≃ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℚ] V) :=
  { sigmaQ V with
    invFun := sigmaQ V
    left_inv := sigmaQ_sigmaQ V
    right_inv := sigmaQ_sigmaQ V }

/-! ### ℤ smoke test (integral coefficients) -/

variable (W : Type*) [AddCommGroup W]

/-- Conjugation `conj ⊗ id` on `ℂ ⊗[ℤ] W`, integral smoke test.-/
def sigmaZR : ℂ ⊗[ℤ] W →ₗ[ℤ] ℂ ⊗[ℤ] W :=
  TensorProduct.map ((starRingEnd ℂ : ℂ →+* ℂ).toAddMonoidHom.toIntLinearMap)
    LinearMap.id

/--
@isnad1 id=eq.0h3v.s8.b2288953a51a from=translated src=- shape=19b95258 vocab=56bb4a2a
-/
@[simp] theorem sigmaZR_tmul (c : ℂ) (w : W) :
    sigmaZR W (c ⊗ₜ[ℤ] w) = (starRingEnd ℂ) c ⊗ₜ[ℤ] w := rfl

/--
@isnad1 id=eq.0h2v.s9.47abdd2d4066 from=translated src=- shape=7ca71ce0 vocab=fe21bc6e
-/
theorem sigmaZR_involutive (x : ℂ ⊗[ℤ] W) : sigmaZR W (sigmaZR W x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c w => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end HodgePilot
