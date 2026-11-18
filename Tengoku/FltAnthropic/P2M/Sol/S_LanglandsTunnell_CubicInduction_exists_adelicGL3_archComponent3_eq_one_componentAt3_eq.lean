import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Tengoku.FltAnthropic.Definitions.Def_AdelicDock_LocalEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

namespace Ws23Embed3

open IsDedekindDomain NumberField AdelicDock

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem matrix_eq_of_forall {n : ℕ} {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

noncomputable def localMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) i j) (g i j)

theorem mapMatrix_localMat3_self (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat3 R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat3]

theorem mapMatrix_localMat3_of_ne (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat3 R K v g) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat3, Matrix.of_apply,
    splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem localMat3_one : localMat3 R K v 1 = 1 := by
  refine matrix_eq_of_forall R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat3_self, map_one]
  · rw [mapMatrix_localMat3_of_ne R K v _ hw, map_one]

theorem localMat3_mul (g h : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    localMat3 R K v (g * h) = localMat3 R K v g * localMat3 R K v h := by
  refine matrix_eq_of_forall R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, mapMatrix_localMat3_self, mapMatrix_localMat3_self, mapMatrix_localMat3_self]
  · rw [map_mul, mapMatrix_localMat3_of_ne R K v _ hw, mapMatrix_localMat3_of_ne R K v _ hw,
      mapMatrix_localMat3_of_ne R K v _ hw, mul_one]

noncomputable def adelicMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (AdeleRing R K) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing K)) i j, localMat3 R K v g i j)

theorem mapMatrix_adeleArch_adelicMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (adelicMat3 R K v g) = 1 := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

theorem mapMatrix_adeleFin_adelicMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (adelicMat3 R K v g) = localMat3 R K v g := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

theorem adelic_matrix_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

theorem adelicMat3_one : adelicMat3 R K v 1 = 1 := by
  refine adelic_matrix_eq R K ?_ ?_
  · rw [mapMatrix_adeleArch_adelicMat3, map_one]
  · rw [mapMatrix_adeleFin_adelicMat3, localMat3_one, map_one]

theorem adelicMat3_mul (g h : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    adelicMat3 R K v (g * h) = adelicMat3 R K v g * adelicMat3 R K v h := by
  refine adelic_matrix_eq R K ?_ ?_
  · rw [map_mul, mapMatrix_adeleArch_adelicMat3, mapMatrix_adeleArch_adelicMat3, mapMatrix_adeleArch_adelicMat3, mul_one]
  · rw [map_mul, mapMatrix_adeleFin_adelicMat3, mapMatrix_adeleFin_adelicMat3, mapMatrix_adeleFin_adelicMat3,
      localMat3_mul]

noncomputable def adelicGL3 (y : GL (Fin 3) (v.adicCompletion K)) : GL (Fin 3) (AdeleRing R K) where
  val := adelicMat3 R K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
  inv := adelicMat3 R K v ((y⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
  val_inv := by rw [← adelicMat3_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, adelicMat3_one]
  inv_val := by rw [← adelicMat3_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, adelicMat3_one]

end Ws23Embed3

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 3) (v.adicCompletion K)) :
    ∃ k : AdelicGL 3 (𝓞 K) K,
      archComponent3 (𝓞 K) K k = 1 ∧ componentAt3 (𝓞 K) K v k = y ∧
      ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → componentAt3 (𝓞 K) K w k = 1 := by
  refine ⟨Ws23Embed3.adelicGL3 (𝓞 K) K v y, ?_, ?_, ?_⟩
  · refine Units.ext ?_
    show (AdelicLevel.adeleArch (𝓞 K) K).mapMatrix
        (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) = 1
    exact Ws23Embed3.mapMatrix_adeleArch_adelicMat3 (𝓞 K) K v _
  · refine Units.ext ?_
    show ((AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K)).mapMatrix
        (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) =
      (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
    have : ((AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K)).mapMatrix
        (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) =
        (AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix
          (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)))) := by
      ext i j; rfl
    rw [this, Ws23Embed3.mapMatrix_adeleFin_adelicMat3, Ws23Embed3.mapMatrix_localMat3_self]
  · intro w hw
    refine Units.ext ?_
    show ((AdelicLevel.finAdeleEval (𝓞 K) K w).comp (AdelicLevel.adeleFin (𝓞 K) K)).mapMatrix
        (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) = 1
    have : ((AdelicLevel.finAdeleEval (𝓞 K) K w).comp (AdelicLevel.adeleFin (𝓞 K) K)).mapMatrix
        (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) =
        (AdelicLevel.finAdeleEval (𝓞 K) K w).mapMatrix ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix
          (Ws23Embed3.adelicMat3 (𝓞 K) K v (y : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)))) := by
      ext i j; rfl
    rw [this, Ws23Embed3.mapMatrix_adeleFin_adelicMat3, Ws23Embed3.mapMatrix_localMat3_of_ne (𝓞 K) K v _ hw]
