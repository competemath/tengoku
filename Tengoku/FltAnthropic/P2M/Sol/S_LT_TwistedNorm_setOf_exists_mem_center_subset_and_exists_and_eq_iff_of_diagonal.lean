import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Tengoku.FltAnthropic.Theorems.Thm_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal
import Tengoku.FltAnthropic.Theorems.Thm_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
import Tengoku.FltAnthropic.Theorems.Thm_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal.lean`: wrote out 9 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 6 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal

set_option autoImplicit false

namespace LT
export _root_.LT (mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace TwistedNorm
export _root_.LT.TwistedNorm (SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace CuspClassesProof
open _root_.LT.TwistedNorm open _root_.LT

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open Matrix

/--
@isnad1 id=eq.0h6v.s9.84d2c39d8331 from=translated src=- shape=e67dd1b7 vocab=acf132d0
-/
theorem coe_map_apply (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      σ ((g : Matrix (Fin 2) (Fin 2) L) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

/--
@isnad1 id=ne.0h2v.s8.d281cc3e395d from=translated src=- shape=4825fade vocab=11017d9b
-/
theorem det_ne (g : GL (Fin 2) L) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (g : Matrix (Fin 2) (Fin 2) L) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) L) 0 1 * (g : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h

/--
@isnad1 id=eq.2h3v.s9.f911e7228e04 from=translated src=- shape=edfbd415 vocab=141f71be
-/
theorem upper_mul {a b : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hb : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : ((a * b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

/--
@isnad1 id=eq.1h2v.s8.72b0104d993c from=translated src=- shape=13b91a81 vocab=cb9213b0
-/
theorem upper_inv {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  have h00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    have h := det_ne a; rw [ha, mul_zero, sub_zero] at h; exact left_ne_zero_of_mul h
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M 1 0) (Units.inv_mul a)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha, mul_zero, add_zero,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h
  exact (mul_eq_zero.mp h).resolve_right h00

/--
@isnad1 id=eq.1h4v.s9.de47732f2cee from=translated src=- shape=4cc571d5 vocab=acf132d0
-/
theorem upper_map (σ : L ≃ₐ[K] L) {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [coe_map_apply, ha, map_zero]

/--
@isnad1 id=ex.1h2v.s9.47ce48da8896 from=translated src=- shape=7201fef7 vocab=d5e2bf40
-/
theorem exists_val_eq_smul_one_of_mem_center {z : GL (Fin 2) L} (hz : z ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ c : L, c ≠ 0 ∧ (z : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
  have hc' : (z : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [← hc]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  refine ⟨c, ?_, hc'⟩
  intro h0
  have h := det_ne z
  rw [hc', h0] at h
  simp at h

noncomputable def scalarGL (c : L) (hc : c ≠ 0) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (c • (1 : Matrix (Fin 2) (Fin 2) L))
    (by simp [Matrix.det_fin_two, Matrix.smul_apply, hc])

/--
@isnad1 id=eq.1h2v.s7.1563a47ed188 from=translated src=- shape=c9a5cab3 vocab=f0531522
-/
theorem scalarGL_val (c : L) (hc : c ≠ 0) :
    ((scalarGL c hc : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := rfl

/--
@isnad1 id=mem.1h2v.s8.976760cbc57d from=translated src=- shape=b4e40bb4 vocab=1811ba5e
-/
theorem scalarGL_mem_center (c : L) (hc : c ≠ 0) : scalarGL c hc ∈ Subgroup.center (GL (Fin 2) L) := by
  refine Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, ?_⟩
  change Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) L)
  ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

noncomputable def weylGL : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : L), 1; 1, 0] (by simp [Matrix.det_fin_two])

/--
@isnad1 id=eq.0h1v.s8.87a899b5cdf6 from=translated src=- shape=9c464ae8 vocab=5ac2cd2c
-/
theorem weylGL_val : ((weylGL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![(0 : L), 1; 1, 0] := rfl

/--
@isnad1 id=eq.0h3v.s9.917d91e53bd3 from=translated src=- shape=929e9fc7 vocab=c614ded9
-/
theorem map_weylGL (σ : L ≃ₐ[K] L) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (weylGL : GL (Fin 2) L) = weylGL := by
  ext i j
  rw [coe_map_apply, weylGL_val]
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=iff.0h3v.s10.99062bb2bacd from=translated src=- shape=2984f9be vocab=d34fd249
-/
theorem inv_mul_mem_center_iff' (t X : GL (Fin 2) L) :
    t⁻¹ * X ∈ Subgroup.center (GL (Fin 2) L) ↔ ∃ z ∈ Subgroup.center (GL (Fin 2) L), X = t * z :=
  ⟨fun h => ⟨t⁻¹ * X, h, by rw [mul_inv_cancel_left]⟩, fun ⟨z, hz, hX⟩ => by rwa [hX, inv_mul_cancel_left]⟩

end LT.TwistedNorm.CuspClassesProof

namespace LT
export _root_.LT (mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace TwistedNorm
export _root_.LT.TwistedNorm (SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace CuspClassesProof
open _root_.LT.TwistedNorm open _root_.LT

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
@isnad1 id=ex.4h8v.s12.ca8d0c26eccb from=translated src=- shape=e34d84e1 vocab=ed8341d3
-/
theorem memJ_mono (σ : L ≃ₐ[K] L) {t₁ t₂ A z₁ : GL (Fin 2) L}
    (hA : (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hz₁ : z₁ ∈ Subgroup.center (GL (Fin 2) L))
    (h : t₂ = A⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) A) {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₂⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₁⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, hb, hbz⟩ := hγ
  obtain ⟨z₂, hz₂, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp hz₂
  refine ⟨b * A⁻¹, upper_mul hb (upper_inv hA), ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
  have hγ' : γ = b * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  calc (b * A⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * A⁻¹)
      = A * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * z₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A * z₂) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ := by rw [h]; group
    _ = t₁ * (z₁ * z₂) := by rw [hc₂]; group

/--
@isnad1 id=ex.2h7v.s12.268f4668c351 from=translated src=- shape=404caf4a vocab=ed8341d3
-/
theorem memI_of_memJ (σ : L ≃ₐ[K] L) {t₁ t₂ W : GL (Fin 2) L}
    (h : t₂ = W⁻¹ * t₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) W) {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₂⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ g : GL (Fin 2) L,
      t₁⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, -, hbz⟩ := hγ
  obtain ⟨z₂, hz₂, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp hz₂
  refine ⟨b * W⁻¹, ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₂, hz₂, ?_⟩
  have hγ' : γ = b * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  calc (b * W⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * W⁻¹)
      = W * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [h]; group
    _ = t₁ * z₂ := by rw [hc₂]; group

/--
@isnad1 id=eq.2h5v.s11.8421ca20becc from=translated src=- shape=34396260 vocab=ed8341d3
-/
theorem upper_of_memJ (σ : L ≃ₐ[K] L) {t : GL (Fin 2) L} (ht : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  obtain ⟨b, hb, hbz⟩ := hγ
  obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  obtain ⟨c, -, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
  have hz10 : (z : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by rw [hc]; simp
  have hγ' : γ = b * (t * z) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  rw [hγ']
  exact upper_mul (upper_mul hb (upper_mul ht hz10)) (upper_inv (upper_map σ hb))

theorem eq_weyl_conj (σ : L ≃ₐ[K] L) {t tw : GL (Fin 2) L}
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htw : (tw : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (tw : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htw00 : (tw : Matrix (Fin 2) (Fin 2) L) 0 0 = (t : Matrix (Fin 2) (Fin 2) L) 1 1)
    (htw11 : (tw : Matrix (Fin 2) (Fin 2) L) 1 1 = (t : Matrix (Fin 2) (Fin 2) L) 0 0) :
    tw = (weylGL : GL (Fin 2) L)⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) weylGL := by
  rw [map_weylGL, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul, weylGL_val,
    ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, htw.1, htw.2, htw00, htw11]

/--
@isnad1 id=ex.2h4v.s10.d3c1e25f8a4b from=translated src=- shape=bffa5929 vocab=e91279cd
-/
theorem exists_upper_diag_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L)
    (hγ10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hN : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    ∃ N : GL (Fin 2) L, (N : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ t'' : GL (Fin 2) L,
      ((t'' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t'' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'' = N⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) N := by
  set p := (γ : Matrix (Fin 2) (Fin 2) L) 0 0 with hp
  set q := (γ : Matrix (Fin 2) (Fin 2) L) 0 1 with hq
  set s := (γ : Matrix (Fin 2) (Fin 2) L) 1 1 with hs
  have hps : p * s ≠ 0 := by simpa [hγ10, ← hp, ← hq, ← hs] using det_ne γ
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hps
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hps

  let f : L →ₗ[K] L := p • (σ : L ≃ₐ[K] L).toLinearMap - s • LinearMap.id
  have hf : ∀ v, f v = p * σ v - s * v := by intro v; simp [f]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hf, sub_eq_zero] at hv
    by_contra hv0
    apply hN
    have hNv : Algebra.norm K v ≠ 0 := Algebra.norm_ne_zero_iff.mpr hv0
    have h := congrArg (Algebra.norm K) hv
    rw [map_mul, map_mul, Algebra.norm_eq_of_algEquiv] at h
    have hps' : Algebra.norm K p = Algebra.norm K s := mul_right_cancel₀ hNv h
    have hNs : Algebra.norm K s ≠ 0 := Algebra.norm_ne_zero_iff.mpr hs0
    rw [show Algebra.norm K (p / s) = Algebra.norm K p / Algebra.norm K s from by
      rw [eq_div_iff hNs, ← map_mul, div_mul_cancel₀ p hs0], hps', div_self hNs]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) q
  rw [hf] at hx
  refine ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : L), x; 0, 1] (by simp [Matrix.det_fin_two]))⁻¹,
    upper_inv (by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]),
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, 0; 0, s] (by simp [Matrix.det_fin_two, hp0, hs0]),
    ⟨by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero], by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]⟩, ?_⟩
  rw [inv_inv, map_inv, eq_mul_inv_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul, ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, coe_map_apply, hγ10,
      ← hp, ← hq, ← hs]
  · linear_combination hx

end LT.TwistedNorm.CuspClassesProof

namespace LT
export _root_.LT (mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace TwistedNorm
export _root_.LT.TwistedNorm (SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq)
namespace CuspClassesProof
open _root_.LT.TwistedNorm open _root_.LT

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
@isnad1 id=ex.4h9v.s12.0e378218d43f from=translated src=- shape=d2ca1793 vocab=6ba1f99c
-/
theorem memI_mono (σ : L ≃ₐ[K] L) {t₁ t₂ W z₁ z₂ : GL (Fin 2) L}
    (hz₁ : z₁ ∈ Subgroup.center (GL (Fin 2) L)) (hz₂ : z₂ ∈ Subgroup.center (GL (Fin 2) L))
    (h : t₂ * z₂ = W⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) W) {γ : GL (Fin 2) L}
    (hγ : ∃ g : GL (Fin 2) L,
      t₂⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ g : GL (Fin 2) L,
      t₁⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, hbz⟩ := hγ
  obtain ⟨z₃, hz₃, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂⁻¹ = z₂⁻¹ * g := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz₂)
  have hc₃ : ∀ g : GL (Fin 2) L, g * z₃ = z₃ * g := Subgroup.mem_center_iff.mp hz₃
  refine ⟨b * W⁻¹, ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₁ * z₂⁻¹ * z₃, Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₁ (Subgroup.inv_mem _ hz₂)) hz₃, ?_⟩
  have hγ' : γ = b * (t₂ * z₃) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  have ht₂ : t₂ = W⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂⁻¹ := by rw [← h]; group
  calc (b * W⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * W⁻¹)
      = W * (t₂ * z₃) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * z₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂⁻¹ * z₃) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [ht₂]; group
    _ = t₁ * z₁ * (z₂⁻¹ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₃)) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [hc₂]; group
    _ = t₁ * (z₁ * z₂⁻¹ * z₃) := by rw [hc₃]; group

/--
@isnad1 id=ex.0h4v.s10.be34da77582d from=translated src=- shape=4c0b2ce6 vocab=6ba1f99c
-/
theorem self_memI (σ : L ≃ₐ[K] L) (t : GL (Fin 2) L) :
    ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) :=
  ⟨1, by simp only [inv_one, one_mul, map_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _⟩

end LT.TwistedNorm.CuspClassesProof

open LT.TwistedNorm.CuspClassesProof in
/--
@isnad1 id=and.1h3v.s14.98deb9c4303b from=translated src=- shape=498b318e vocab=589efc70
-/
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ⊆
        {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}) ∧
    (∀ δ : GL (Fin 2) L, δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} →
      ∃ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 ∧
        ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) ∧
    (∀ t t' : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ((t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      (({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ∩
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}).Nonempty ↔
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
      ({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ↔
        ∃ ζ : L, ζ ≠ 0 ∧
          ((Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∨
            (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))))) := by
  have scaled : ∀ {z : GL (Fin 2) L}, z ∈ Subgroup.center (GL (Fin 2) L) →
      ∃ c : L, c ≠ 0 ∧ ∀ (s : GL (Fin 2) L) (i j : Fin 2),
        ((s * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = c * (s : Matrix (Fin 2) (Fin 2) L) i j := by
    intro z hz
    obtain ⟨c, hc0, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
    exact ⟨c, hc0, fun s i j => by rw [Units.val_mul, hc, Matrix.mul_smul, mul_one, Matrix.smul_apply, smul_eq_mul]⟩

  have diag_tz : ∀ {t z : GL (Fin 2) L}, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      z ∈ Subgroup.center (GL (Fin 2) L) →
      (((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 / ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        (t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    intro t z ht hz
    obtain ⟨c, hc0, hcz⟩ := scaled hz
    rw [hcz, hcz, hcz, hcz, ht.1, ht.2, mul_zero, mul_div_mul_left _ _ hc0]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

  have part1 : ∀ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      ∀ δ : GL (Fin 2) L, (∃ g : GL (Fin 2) L,
        t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) →
      ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ := by
    intro t ht hN δ ⟨g, hg⟩
    obtain ⟨z, hz, hgz⟩ := (inv_mul_mem_center_iff' _ _).mp hg
    obtain ⟨htz, hratio⟩ := diag_tz ht hz
    obtain ⟨γK, hγK, hm⟩ := (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
      hgen (t * z) htz.1).mpr (by rw [hratio]; exact hN)
    have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ δ = LT.TwistedNorm.SigmaConjClasses.mk σ (t * z) :=
      LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨g, hgz.symm⟩
    exact ⟨γK, hγK, by rw [hmk, hm]⟩
  refine ⟨fun t ht hN δ hδ => part1 t ht hN δ hδ, ?_, ?_⟩
  ·
    rintro δ ⟨γK, hγK, hm⟩
    obtain ⟨g, hg⟩ := LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq hgen γK hγK δ hm
    set t : GL (Fin 2) L := g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g with ht
    have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ δ = LT.TwistedNorm.SigmaConjClasses.mk σ t :=
      LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨g, rfl⟩
    refine ⟨t, hg, ?_, g, ?_⟩
    · exact (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one hgen t hg.1).mp
        ⟨γK, hγK, by rw [← hmk, hm]⟩
    · rw [← ht, inv_mul_cancel]; exact Subgroup.one_mem _
  ·
    intro t t' ht ht'

    have key : ∀ δ : GL (Fin 2) L,
        (∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
          Subgroup.center (GL (Fin 2) L)) →
        (∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
          Subgroup.center (GL (Fin 2) L)) →
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} := by
      rintro δ ⟨g', hg'⟩ ⟨g, hg⟩
      obtain ⟨z', hz', e'⟩ := (inv_mul_mem_center_iff' _ _).mp hg'
      obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hg
      have hδ : δ = g * (t * z) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) g)⁻¹ := by rw [← e]; group
      have hrel : t' * z' = (g⁻¹ * g')⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) (g⁻¹ * g') := by
        rw [← e', hδ, map_mul, map_inv]; group
      have hrel' : t * z = (g'⁻¹ * g)⁻¹ * (t' * z') * Matrix.GeneralLinearGroup.map (σ : L →+* L) (g'⁻¹ * g) := by
        rw [hrel, map_mul, map_mul, map_inv, map_inv]; group
      ext γ
      exact ⟨fun h => memI_mono σ hz hz' hrel h, fun h => memI_mono σ hz' hz hrel' h⟩
    have meet_iff : ({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} ∩
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)}).Nonempty ↔
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} := by
      constructor
      · rintro ⟨δ, h', h⟩; exact key δ h' h
      · intro h; exact ⟨t, by rw [h]; exact self_memI σ t, self_memI σ t⟩
    refine ⟨meet_iff, ?_⟩

    constructor
    · intro h
      have ht'mem : t' ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
        h ▸ self_memI σ t'
      obtain ⟨g, hg⟩ := ht'mem
      obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hg
      obtain ⟨c, hc0, hcz⟩ := scaled hz
      obtain ⟨htz, -⟩ := diag_tz ht hz
      have hrel : ∃ g₁ : GL (Fin 2) L, t' = g₁⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) g₁ :=
        ⟨g⁻¹, by rw [← e, map_inv]; group⟩
      have E := (LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen (t * z) t' htz ht').2.2.mp hrel
      refine ⟨c, hc0, ?_⟩
      rw [hcz, hcz, map_mul, map_mul] at E
      exact E
    · rintro ⟨ζ, hζ, hnorms⟩
      have hzc : scalarGL ζ hζ ∈ Subgroup.center (GL (Fin 2) L) := scalarGL_mem_center _ _
      obtain ⟨c, hc0, hcz⟩ := scaled hzc
      have hcval : c = ζ := by
        have h := hcz 1 0 0
        simp only [Units.val_one, one_mul, scalarGL_val, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] at h
        exact h.symm
      obtain ⟨htz, -⟩ := diag_tz (z := scalarGL ζ hζ) ht hzc
      obtain ⟨g₁, hg₁⟩ := (LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen
        (t * scalarGL ζ hζ) t' htz ht').2.2.mpr (by rw [hcz, hcz, map_mul, map_mul, hcval]; exact hnorms)
      apply key t' (self_memI σ t')
      refine ⟨g₁⁻¹, ?_⟩
      rw [inv_mul_mem_center_iff']
      exact ⟨scalarGL ζ hζ, hzc, by rw [hg₁, map_inv]; group⟩
