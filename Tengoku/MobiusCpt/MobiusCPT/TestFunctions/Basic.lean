import Tengoku.Seed.Algebra.Ring.Periodic
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
import Tengoku.Seed.Geometry.Manifold.Algebra.SmoothFunctions
import Tengoku.Seed.Geometry.Manifold.Instances.Sphere

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MobiusCPT.TestFunctions.Basic

The smooth test-function space on the circle and its angle-picture bridge.
-/

namespace MobiusCPT

open scoped Topology Manifold ContDiff

attribute [local instance] finrank_real_complex_fact'

noncomputable section

/-- [T26], §3; the test-function space `C^∞(S¹)` in the manifold picture.-/
def TestFn : Type := ContMDiffMap (𝓡 1) 𝓘(ℝ, ℂ) Circle ℂ ∞

/-- The pointwise function underlying a smooth circle-valued-domain map.-/
instance : FunLike TestFn Circle ℂ where
  coe f := f.1
  coe_injective := Subtype.coe_injective

/-- [T26], §3; the additive group structure on `C^∞(S¹)`.-/
instance testFnAddCommGroup : AddCommGroup TestFn :=
  inferInstanceAs (AddCommGroup (ContMDiffMap (𝓡 1) 𝓘(ℝ, ℂ) Circle ℂ ∞))

/-- [T26], §3; complex scalar multiplication on `C^∞(S¹)`.-/
instance instSMul : SMul ℂ TestFn where
  smul c f :=
    ⟨fun z => c * f z, by
      have hmul : ContDiff ℝ ∞ (fun w : ℂ => c * w) := by
        simpa only [smul_eq_mul] using
          (contDiff_const_smul (𝕜 := ℝ) (F := ℂ) c)
      change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
        ((fun w : ℂ => c * w) ∘ (f : Circle → ℂ))
      exact
        hmul.comp_contMDiff (ContMDiffMap.contMDiff f)⟩

namespace TestFn

/-- The coercion preserves addition.
@isnad1 id=eq.0h2v.s6.9aca7a2bdbc4 from=translated src=- shape=052a5e00 vocab=c5820b84
-/
@[simp] theorem coe_add (f g : TestFn) : ⇑(f + g) = f + g := by
  funext z
  rfl

/-- The coercion preserves scalar multiplication by complex constants.
@isnad1 id=eq.0h2v.s5.8980336c738a from=translated src=- shape=775851c0 vocab=1b30313c
-/
@[simp] theorem coe_smul (c : ℂ) (f : TestFn) : ⇑(c • f) = c • (f : Circle → ℂ) := by
  funext z
  rfl

/-- The coercion preserves zero.
@isnad1 id=eq.0h0v.s5.c5f083262b63 from=translated src=- shape=c397a401 vocab=bbcf982d
-/
@[simp] theorem coe_zero : ⇑(0 : TestFn) = (0 : Circle → ℂ) := by
  funext z
  rfl

/-- The coercion preserves negation.
@isnad1 id=eq.0h1v.s5.a2d92a6208d7 from=translated src=- shape=ef237146 vocab=7c05587f
-/
@[simp] theorem coe_neg (f : TestFn) : ⇑(-f) = -f := by
  funext z
  rfl

/-- The coercion preserves subtraction.
@isnad1 id=eq.0h2v.s6.3a5bc046a232 from=translated src=- shape=052a5e00 vocab=73af0d47
-/
@[simp] theorem coe_sub (f g : TestFn) : ⇑(f - g) = f - g := by
  funext z
  rfl

/-- Extensionality for smooth test functions.
@isnad1 id=eq.1h2v.s4.039e8dafa176 from=translated src=- shape=4d06d4cc vocab=bbcf982d
-/
@[ext] theorem ext {f g : TestFn} (h : ∀ z, f z = g z) : f = g := by
  exact DFunLike.ext f g h

end TestFn

/-- [T26], §3; the complex module structure on `C^∞(S¹)`.-/
instance testFnModule : Module ℂ TestFn :=
  Function.Injective.module ℂ
    (ContMDiffMap.coeFnAddMonoidHom : TestFn →+ Circle → ℂ)
    (fun _ _ h => TestFn.ext (fun z => congrFun h z)) TestFn.coe_smul

/-- [T26], §3; the angle picture of a test function: `θ ↦ f(e^{iθ})`.-/
def toAngle (f : TestFn) : ℝ → ℂ := fun θ => f (Circle.exp θ)

/-- [T26], §3; angle evaluation preserves smoothness.
@isnad1 id=contdiff.0h1v.s5.d0c785203a0e from=translated src=- shape=caa53032 vocab=240be9bd
-/
theorem contDiff_toAngle (f : TestFn) : ContDiff ℝ ∞ (toAngle f) := by
  change ContDiff ℝ ∞ ((f : Circle → ℂ) ∘ Circle.exp)
  exact (((ContMDiffMap.contMDiff f).comp (contMDiff_circleExp (m := ∞))).contDiff)

/-- [T26], §3; the angle picture has period `2 * Real.pi`.
@isnad1 id=periodic.0h1v.s4.9482fe1eb868 from=translated src=- shape=f3462cf1 vocab=be62e344
-/
theorem periodic_toAngle (f : TestFn) : Function.Periodic (toAngle f) (2 * Real.pi) := by
  intro θ
  simp only [toAngle, Circle.exp_add, Circle.exp_two_pi, mul_one]

/-- [T26], §3; angle evaluation is injective because `Circle.exp` is surjective.
@isnad1 id=injectiv.0h0v.s2.cedde7beb0ad from=translated src=- shape=5033b664 vocab=e34a285e
-/
theorem toAngle_injective : Function.Injective toAngle := by
  intro f g h
  apply TestFn.ext
  intro z
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  have hfg := congrFun h θ
  change f (Circle.exp θ) = g (Circle.exp θ) at hfg
  rw [hθ] at hfg
  exact hfg

/-- [T26], §3; angle evaluation preserves addition.
@isnad1 id=eq.0h2v.s5.85a03cb80d96 from=translated src=- shape=285516c7 vocab=d56c3309
-/
theorem toAngle_add (f g : TestFn) : toAngle (f + g) = toAngle f + toAngle g := by
  funext θ
  rfl

/-- [T26], §3; angle evaluation preserves complex scalar multiplication.
@isnad1 id=eq.0h2v.s5.0077c857ef75 from=translated src=- shape=1c6ee18f vocab=08e47ed9
-/
theorem toAngle_smul (c : ℂ) (f : TestFn) : toAngle (c • f) = c • toAngle f := by
  funext θ
  rfl

/-- [T26], §3; angle evaluation preserves zero.
@isnad1 id=eq.0h0v.s5.f9b7b4af8c20 from=translated src=- shape=8a79115c vocab=bf4857e5
-/
theorem toAngle_zero : toAngle (0 : TestFn) = 0 := by
  funext θ
  rfl

/-- [T26], §3; the angle bridge as a `ℂ`-linear map.-/
def toAngleₗ : TestFn →ₗ[ℂ] (ℝ → ℂ) where
  toFun := toAngle
  map_add' := toAngle_add
  map_smul' := toAngle_smul

/-- [T26], §3; every smooth periodic angle function descends to the circle.
@isnad1 id=ex.2h1v.s6.ead1f499b0e1 from=translated src=- shape=1f0332cc vocab=82f4ffff
-/
theorem exists_toAngle_eq {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g (2 * Real.pi)) :
    ∃ f : TestFn, toAngle f = g := by
  let f : TestFn :=
    ⟨fun z : Circle => g (Complex.arg (z : ℂ)), by
      intro z₀
      let θ₀ : ℝ := Complex.arg (z₀ : ℂ)
      have hθ₀ : Circle.exp θ₀ = z₀ := by
        dsimp [θ₀]
        exact Circle.exp_arg z₀
      let σ : ℂ → ℝ := fun w => θ₀ + Complex.arg (w / (z₀ : ℂ))
      have hlog : ContDiffAt ℝ ∞ Complex.log (1 : ℂ) :=
        (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
      have harg : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.arg w) (1 : ℂ) := by
        have hfun : (fun w : ℂ => Complex.arg w) = Complex.imCLM ∘ Complex.log := by
          funext w
          simp only [Function.comp_apply, Complex.imCLM_apply, Complex.log_im]
        rw [hfun]
        exact Complex.imCLM.contDiff.contDiffAt.comp (1 : ℂ) hlog
      have hratio : ContDiffAt ℝ ∞ (fun w : ℂ => w / (z₀ : ℂ)) (z₀ : ℂ) := by
        exact (contDiff_id : ContDiff ℝ ∞ (fun w : ℂ => w)).contDiffAt.div_const (z₀ : ℂ)
      have hzratio : (z₀ : ℂ) / (z₀ : ℂ) = (1 : ℂ) := by
        exact div_self (Circle.coe_ne_zero z₀)
      have harg_ratio :
          ContDiffAt ℝ ∞ (fun w : ℂ => Complex.arg w) ((z₀ : ℂ) / (z₀ : ℂ)) := by
        simpa [hzratio] using harg
      have hsigma : ContDiffAt ℝ ∞ σ (z₀ : ℂ) := by
        dsimp [σ]
        exact
          (contDiffAt_const :
              ContDiffAt ℝ ∞ (fun _ : ℂ => θ₀) (z₀ : ℂ)).add
            (harg_ratio.comp (f := fun w : ℂ => w / (z₀ : ℂ)) (z₀ : ℂ) hratio)
      have hlocal :
          ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
            (fun z : Circle => g (σ (z : ℂ))) z₀ := by
        have hcoe :
            ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) z₀ :=
          (contMDiff_coe_sphere : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ))).contMDiffAt
        have hsigma_circle :
            ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (σ ∘ (↑)) z₀ :=
          hsigma.comp_contMDiffAt hcoe
        change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (g ∘ σ ∘ (↑)) z₀
        exact hg.contDiffAt.comp_contMDiffAt hsigma_circle
      have hratio_cont :
          ContinuousAt (fun z : Circle => (z : ℂ) / (z₀ : ℂ)) z₀ :=
        continuous_subtype_val.continuousAt.div_const (z₀ : ℂ)
      have hslit :
          Complex.slitPlane ∈ 𝓝 ((z₀ : ℂ) / (z₀ : ℂ)) := by
        rw [hzratio]
        exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
      have hratio_nhds :
          ∀ᶠ z : Circle in 𝓝 z₀, (z : ℂ) / (z₀ : ℂ) ∈ Complex.slitPlane :=
        hratio_cont.eventually_mem hslit
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [hratio_nhds] with z hz
      symm
      have harg_ratio_exp :
          Circle.exp (Complex.arg ((z : ℂ) / (z₀ : ℂ))) = z / z₀ := by
        simpa only [Circle.coe_div] using Circle.exp_arg (z / z₀)
      have hsection : Circle.exp (σ (z : ℂ)) = z := by
        calc
          Circle.exp (σ (z : ℂ)) =
              Circle.exp θ₀ * Circle.exp (Complex.arg ((z : ℂ) / (z₀ : ℂ))) := by
                dsimp [σ]
                exact Circle.exp_add _ _
          _ = z₀ * (z / z₀) := by rw [hθ₀, harg_ratio_exp]
          _ = z := by
            rw [div_eq_mul_inv, ← mul_assoc, mul_comm z₀ z, mul_assoc, mul_inv_cancel, mul_one]
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (hsection.trans (Circle.exp_arg z).symm)
      calc
        g (σ (z : ℂ)) =
            g (Complex.arg (z : ℂ) + m * (2 * Real.pi)) := by rw [hm]
        _ = g (Complex.arg (z : ℂ)) := hper.int_mul m _⟩
  refine ⟨f, ?_⟩
  funext θ
  change g (Complex.arg ((Circle.exp θ : Circle) : ℂ)) = g θ
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp θ))
  calc
    g (Complex.arg ((Circle.exp θ : Circle) : ℂ)) =
        g (θ + m * (2 * Real.pi)) := by rw [hm]
    _ = g θ := hper.int_mul m _

/-- [T26], §3; the angle bridge is a bijection onto smooth periodic functions.
@isnad1 id=bijon.0h0v.s6.6dc5307bc76a from=translated src=- shape=2de97dfb vocab=f5291193
-/
theorem toAngle_bijOn :
    Set.BijOn toAngle Set.univ
      {g : ℝ → ℂ | ContDiff ℝ ∞ g ∧ Function.Periodic g (2 * Real.pi)} := by
  refine ⟨?_, ?_, ?_⟩
  · intro f _
    exact ⟨contDiff_toAngle f, periodic_toAngle f⟩
  · intro f _ g _ h
    exact toAngle_injective h
  · intro g hg
    obtain ⟨f, hf⟩ := exists_toAngle_eq hg.1 hg.2
    exact ⟨f, Set.mem_univ _, hf⟩

end

end MobiusCPT
