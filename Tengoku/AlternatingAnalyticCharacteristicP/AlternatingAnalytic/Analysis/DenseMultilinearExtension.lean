import Tengoku.Seed.Analysis.Normed.Operator.Extend
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending multilinear maps from a dense subspace

Along a dense linear isometry `j : D → E` into a space with complete target `F`,
continuous linear, multilinear and alternating maps on `D` extend uniquely to `E`
without increasing their norms. This is Lemma D.5.
-/

noncomputable section
namespace AlternatingAnalytic

variable {K D E F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
  (j : D →ₗᵢ[K] E) (hd : DenseRange j)

include hd in
theorem denseLinearExtension_raw_apply (f : D →L[K] F) (x : D) :
    f.extend j.toContinuousLinearMap (j x) = f x :=
  ContinuousLinearMap.extend_eq f (e := j.toContinuousLinearMap) hd
    j.isometry.isUniformInducing x

/-- Extension along a dense linear isometry, as a contracting linear operator on maps.-/
def denseLinearExtension : (D →L[K] F) →L[K] (E →L[K] F) :=
  LinearMap.mkContinuous
    { toFun f := f.extend j.toContinuousLinearMap
      map_add' f g := by
        apply ContinuousLinearMap.ext
        have heq := hd.equalizer (f + g |>.extend j.toContinuousLinearMap).continuous
          ((f.extend j.toContinuousLinearMap + g.extend j.toContinuousLinearMap).continuous)
        apply congrFun (heq ?_)
        funext x
        simp only [Function.comp_apply, _root_.add_apply]
        rw [denseLinearExtension_raw_apply j hd (f + g) x,
          denseLinearExtension_raw_apply j hd f x, denseLinearExtension_raw_apply j hd g x]
        rfl
      map_smul' c f := by
        apply ContinuousLinearMap.ext
        have heq := hd.equalizer (c • f |>.extend j.toContinuousLinearMap).continuous
          ((c • f.extend j.toContinuousLinearMap).continuous)
        apply congrFun (heq ?_)
        funext x
        simp only [Function.comp_apply, _root_.smul_apply]
        rw [denseLinearExtension_raw_apply j hd (c • f) x,
          denseLinearExtension_raw_apply j hd f x]
        rfl }
    1 (fun f => by
      change ‖f.extend j.toContinuousLinearMap‖ ≤ 1 * ‖f‖
      simpa only [one_mul, NNReal.coe_one] using
        f.opNorm_extend_le (N := 1) hd (fun x => by simp [j.norm_map]))

@[simp]
theorem denseLinearExtension_apply (f : D →L[K] F) (x : D) :
    denseLinearExtension j hd f (j x) = f x :=
  ContinuousLinearMap.extend_eq _ (e := j.toContinuousLinearMap) hd j.isometry.isUniformInducing x

theorem norm_denseLinearExtension_le (f : D →L[K] F) :
    ‖denseLinearExtension j hd f‖ ≤ ‖f‖ := by
  change ‖f.extend j.toContinuousLinearMap‖ ≤ ‖f‖
  simpa only [one_mul, NNReal.coe_one] using
    f.opNorm_extend_le (N := 1) hd (fun x => by simp [j.norm_map])

include hd in
/-- There is a linear map of norm at most one extending every `n`-linear map along `j`.-/
theorem exists_denseMultilinearExtension (n : ℕ) :
    ∃ T : ContinuousMultilinearMap K (fun _ : Fin n => D) F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin n => E) F,
      (∀ P x, T P (fun i => j (x i)) = P x) ∧ (∀ P, ‖T P‖ ≤ ‖P‖) := by
  induction n with
  | zero =>
    let T := ((continuousMultilinearCurryFin0 K D F).trans
      (continuousMultilinearCurryFin0 K E F).symm).toLinearIsometry.toContinuousLinearMap
    refine ⟨T, ?_, ?_⟩
    · intro P x
      change P 0 = P x
      congr 1
      exact Subsingleton.elim _ _
    · intro P
      exact ((continuousMultilinearCurryFin0 K D F).trans
        (continuousMultilinearCurryFin0 K E F).symm).norm_map P |>.le
  | succ n ih =>
    obtain ⟨T, hT, hnorm⟩ := ih
    let C₀ := (continuousMultilinearCurryLeftEquiv K (fun _ : Fin (n + 1) => D) F).toLinearIsometry.toContinuousLinearMap
    let C₁ := (continuousMultilinearCurryLeftEquiv K (fun _ : Fin (n + 1) => E) F).symm.toLinearIsometry.toContinuousLinearMap
    let U := (ContinuousLinearMap.compL K D
      (ContinuousMultilinearMap K (fun _ : Fin n => D) F)
      (ContinuousMultilinearMap K (fun _ : Fin n => E) F) T).comp C₀
    let S := C₁.comp ((denseLinearExtension j hd).comp U)
    refine ⟨S, ?_, ?_⟩
    · intro P x
      change denseLinearExtension j hd (T.comp P.curryLeft) (j (x 0))
        (fun i => j (x i.succ)) = P x
      rw [denseLinearExtension_apply, ContinuousLinearMap.comp_apply, hT]
      change P (Fin.cons (x 0) (Fin.tail x)) = P x
      rw [Fin.cons_self_tail]
    · intro P
      change ‖ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (n + 1) => E)
        (denseLinearExtension j hd (T.comp P.curryLeft))‖ ≤ ‖P‖
      rw [ContinuousLinearMap.uncurryLeft_norm]
      apply (norm_denseLinearExtension_le j hd _).trans
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      calc
        ‖T (P.curryLeft x)‖ ≤ ‖P.curryLeft x‖ := hnorm _
        _ ≤ ‖P.curryLeft‖ * ‖x‖ := P.curryLeft.le_opNorm x
        _ = ‖P‖ * ‖x‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]

/-- The extension of `n`-linear maps along `j`, of norm at most one.-/
def denseMultilinearExtension (n : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin n => D) F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin n => E) F :=
  (exists_denseMultilinearExtension j hd n).choose

@[simp]
theorem denseMultilinearExtension_apply (n : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin n => D) F) (x : Fin n → D) :
    denseMultilinearExtension j hd n P (fun i => j (x i)) = P x :=
  (exists_denseMultilinearExtension j hd n).choose_spec.1 P x

theorem norm_denseMultilinearExtension_le (n : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin n => D) F) :
    ‖denseMultilinearExtension j hd n P‖ ≤ ‖P‖ :=
  (exists_denseMultilinearExtension j hd n).choose_spec.2 P

/-- The extension of an alternating map vanishes when two arguments are equal.-/
theorem denseMultilinearExtension_alternating (n : ℕ) (P : D [⋀^Fin n]→L[K] F)
    (x : Fin n → E) {a b : Fin n} (hab : a ≠ b) (hx : x a = x b) :
    denseMultilinearExtension j hd n P.toContinuousMultilinearMap x = 0 := by
  classical
  let Q := denseMultilinearExtension j hd n P.toContinuousMultilinearMap
  have hfun : (fun y : Fin n → E => Q (Function.update y b (y a))) = fun _ => 0 := by
    apply (DenseRange.piMap (fun _ : Fin n => hd)).equalizer
      (Q.cont.comp (continuous_id.update b (continuous_apply a))) continuous_const
    funext y
    change Q (Function.update (fun i => j (y i)) b (j (y a))) = 0
    have hupdate : Function.update (fun i => j (y i)) b (j (y a)) =
        (fun i => j (Function.update y b (y a) i)) := by
      ext i
      by_cases hi : i = b <;> simp [hi]
    rw [hupdate, denseMultilinearExtension_apply]
    exact P.map_eq_zero_of_eq _ (by simp [hab]) hab
  have h := congrFun hfun x
  simpa only [hx, Function.update_eq_self] using h

/-- The extension of continuous alternating maps along `j`, of norm at most one.-/
def denseAlternatingExtension (n : ℕ) :
    (D [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F) :=
  LinearMap.mkContinuous
    { toFun P :=
        { toContinuousMultilinearMap := denseMultilinearExtension j hd n P.toContinuousMultilinearMap
          map_eq_zero_of_eq' := fun x a b hx hab =>
            denseMultilinearExtension_alternating j hd n P x hab hx }
      map_add' P Q := by
        apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
        exact map_add (denseMultilinearExtension j hd n) _ _
      map_smul' c P := by
        apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
        exact map_smul (denseMultilinearExtension j hd n) c _ }
    1 (fun P => by
      change ‖denseMultilinearExtension j hd n P.toContinuousMultilinearMap‖ ≤ 1 * ‖P‖
      simpa only [one_mul, ContinuousAlternatingMap.norm_toContinuousMultilinearMap] using
        norm_denseMultilinearExtension_le j hd n P.toContinuousMultilinearMap)

@[simp]
theorem denseAlternatingExtension_apply (n : ℕ) (P : D [⋀^Fin n]→L[K] F) (x : Fin n → D) :
    denseAlternatingExtension j hd n P (fun i => j (x i)) = P x :=
  denseMultilinearExtension_apply j hd n P.toContinuousMultilinearMap x

theorem norm_denseAlternatingExtension_le (n : ℕ) (P : D [⋀^Fin n]→L[K] F) :
    ‖denseAlternatingExtension j hd n P‖ ≤ ‖P‖ :=
  norm_denseMultilinearExtension_le j hd n P.toContinuousMultilinearMap

end AlternatingAnalytic
