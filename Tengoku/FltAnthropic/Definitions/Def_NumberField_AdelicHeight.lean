import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_SiegelReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace NumberField

namespace AdelicHeight

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
  AutomorphicForm.SiegelReduction NumberField.AdelicLevel NumberField.InfinitePlace

section Local

variable {K : Type*} [NormedField K]

def rowMaxNorm (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max ‖M 1 0‖ ‖M 1 1‖

/--
@isnad1 id=le.0h2v.s5.e7648ba4502a from=translated src=- shape=f7312c26 vocab=c4c34938
-/
theorem rowMaxNorm_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ rowMaxNorm M :=
  (norm_nonneg _).trans (le_max_left _ _)

/--
@isnad1 id=lt.0h2v.s6.04093892e37d from=translated src=- shape=69350396 vocab=3b3d8613
-/
theorem rowMaxNorm_pos (g : GL (Fin 2) K) : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  by_contra h
  have h0 : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) = 0 :=
    le_antisymm (not_lt.mp h) (rowMaxNorm_nonneg _)
  have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    norm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans h0.le) (norm_nonneg _))
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 :=
    norm_eq_zero.mp (le_antisymm ((le_max_right _ _).trans h0.le) (norm_nonneg _))
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, h10, h11, mul_zero, mul_zero, sub_zero] at hdet
  exact hdet rfl

def finLocalHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2

/--
@isnad1 id=lt.0h2v.s5.31627795b52e from=translated src=- shape=0ac22ba1 vocab=f1a9f286
-/
theorem finLocalHeight_pos (g : GL (Fin 2) K) : 0 < finLocalHeight g :=
  div_pos (norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero) (pow_pos (rowMaxNorm_pos g) 2)

variable [IsUltrametricDist K]

omit [IsUltrametricDist K] in
private theorem coe_mul' (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

/--
@isnad1 id=le.0h3v.s9.87e219cb116a from=translated src=- shape=ae06de02 vocab=4de40a54
-/
theorem norm_mul_norm_det_le (γ g : GL (Fin 2) K) :
    ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      ≤ rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hid : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 * (g : Matrix (Fin 2) (Fin 2) K).det
      = ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 0
          * (g : Matrix (Fin 2) (Fin 2) K) 1 1
        + -(((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 1
          * (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    simp only [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [← norm_mul, hid, coe_mul']
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul]
  have h1 : ‖((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 0‖
      ≤ rowMaxNorm ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) :=
    le_max_left _ _
  have h2 : ‖((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 1‖
      ≤ rowMaxNorm ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) :=
    le_max_right _ _
  have h3 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) :=
    le_max_right _ _
  have h4 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) :=
    le_max_left _ _
  exact max_le (mul_le_mul h1 h3 (norm_nonneg _) (rowMaxNorm_nonneg _))
    (mul_le_mul h2 h4 (norm_nonneg _) (rowMaxNorm_nonneg _))

/--
@isnad1 id=le.1h3v.s9.53a3e64008d2 from=translated src=- shape=191cc8aa vocab=2d92778b
-/
theorem finLocalHeight_mul_mul_finLocalHeight_le (γ g : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    finLocalHeight (γ * g) * finLocalHeight g
      ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ / ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := by
  have hkey := norm_mul_norm_det_le γ g
  have hr1 := rowMaxNorm_pos (γ * g)
  have hr2 := rowMaxNorm_pos g
  have hc : 0 < ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := by positivity
  have hdet : ‖((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [coe_mul', Matrix.det_mul, norm_mul]
  unfold finLocalHeight
  rw [hdet, div_mul_div_comm, div_le_div_iff₀ (by positivity) hc]
  have hsq : (‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖) ^ 2
      ≤ (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkey 2
  calc ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
        * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖) ^ 2 := by
        ring
    _ ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
    _ = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
            * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2) := by
        ring

/--
@isnad1 id=le.1h2v.s6.c19089cd52bf from=translated src=- shape=f0d973c9 vocab=b99f9204
-/
theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (h 0 0) (norm_nonneg _) (h 1 1)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ (h 0 1) (norm_nonneg _) (h 1 0)

/--
@isnad1 id=eq.2h2v.s8.578635a2a796 from=translated src=- shape=c2ae496f vocab=26717fe0
-/
theorem finLocalHeight_eq_one (g : GL (Fin 2) K)
    (h : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight g = 1 := by
  have hd : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul', mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  have hdet1 : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm hd ?_
    by_contra hlt
    push Not at hlt
    have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
    rw [hprod] at this
    exact lt_irrefl _ this
  have hrow_le : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ≤ 1 := max_le (h 1 0) (h 1 1)
  have hrow_ge : 1 ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    by_contra hlt
    push Not at hlt
    have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ < 1 := (le_max_left _ _).trans_lt hlt
    have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ < 1 := (le_max_right _ _).trans_lt hlt
    have hlt' : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ < 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (h 0 0) (norm_nonneg _) h11
      · rw [norm_neg, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (h 0 1) (norm_nonneg _) h10
    rw [hdet1] at hlt'
    exact lt_irrefl _ hlt'
  unfold finLocalHeight
  rw [hdet1, le_antisymm hrow_le hrow_ge, one_pow, div_one]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

def finHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v g)

def adelicHeight (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)

variable {F}

/--
@isnad1 id=le.1h3v.s7.cd448074f253 from=translated src=- shape=8d1d4a45 vocab=cbcca64e
-/
theorem norm_le_one_of_mem_adicCompletionIntegers {v : HeightOneSpectrum (𝓞 F)}
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

/--
@isnad1 id=eventual.0h2v.s10.da5c6907520c from=translated src=- shape=99d3942c vocab=0fe38dc2
-/
theorem finLocalHeight_finComponent_eventually_eq_one (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      finLocalHeight (finComponent (𝓞 F) F v g) = 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

/--
@isnad1 id=hasfinit.0h2v.s10.a4863f4f7f8f from=translated src=- shape=f33393f6 vocab=134ec055
-/
theorem hasFiniteMulSupport_finLocalHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      finLocalHeight (finComponent (𝓞 F) F v g)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (finLocalHeight_finComponent_eventually_eq_one g)

/--
@isnad1 id=lt.0h2v.s6.1acfd605bd9e from=translated src=- shape=f537951c vocab=393e183e
-/
theorem finHeight_pos (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : 0 < finHeight F g :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun _ => finLocalHeight_pos _

/--
@isnad1 id=lt.0h2v.s5.a0fa94e43496 from=translated src=- shape=ac1f0716 vocab=a9c999cd
-/
theorem adelicHeight_pos (g : AdelicGL2 (𝓞 F) F) : 0 < adelicHeight F g :=
  mul_pos (archHeight_pos F _) (finHeight_pos _)

/--
@isnad1 id=eq.1h2v.s9.31d454fb98dc from=translated src=- shape=ffd34504 vocab=98e0d5ca
-/
theorem finHeight_eq_one_of_mem {g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hg : g ∈ finiteIntegralGL2 (𝓞 F) F) : finHeight F g = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hg
  refine finprod_eq_one_of_forall_eq_one fun v =>
    finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hg.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hg.2 i j v)

/--
@isnad1 id=eq.1h2v.s11.f4ae3c518b69 from=translated src=- shape=264b9404 vocab=48f73e58
-/
theorem adelicHeight_eq_archHeight_of_mem {g : AdelicGL2 (𝓞 F) F}
    (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    adelicHeight F g = archHeight F (glArch (𝓞 F) F g) := by
  rw [adelicHeight, finHeight_eq_one_of_mem hg, mul_one]

/--
@isnad1 id=eq.0h3v.s12.64faa9d5ff9f from=translated src=- shape=1bff76d7 vocab=32681a18
-/
theorem finComponent_globalPoints_eq (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = (FinitePlace.embedding v).mapMatrix (γ : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rfl

/--
@isnad1 id=eq.0h5v.s12.8e0c644a138a from=translated src=- shape=ccb8e31e vocab=cacdf137
-/
theorem finComponent_globalPoints_apply (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F)
    (i j : Fin 2) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) i j) := by
  rw [finComponent_globalPoints_eq]
  rfl

/--
@isnad1 id=eq.0h3v.s12.324f7294cace from=translated src=- shape=46a3f1f2 vocab=325e21b3
-/
theorem det_finComponent_globalPoints (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      = FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det) := by
  rw [finComponent_globalPoints_eq, ← RingHom.map_det]

/--
@isnad1 id=eq.0h3v.s8.f7290df739c7 from=translated src=- shape=7a708978 vocab=10dcd2fa
-/
theorem norm_embedding_eq_equiv_symm (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ = (FinitePlace.equivHeightOneSpectrum.symm v) x := rfl

/--
@isnad1 id=hasfinit.1h2v.s8.d66a0728dd2a from=translated src=- shape=e3bf6492 vocab=e400cb2e
-/
theorem hasFiniteMulSupport_norm_embedding {x : F} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖FinitePlace.embedding v x‖).HasFiniteMulSupport :=
  (FinitePlace.hasFiniteMulSupport hx).fun_comp_of_injective
    FinitePlace.equivHeightOneSpectrum.symm.injective

/--
@isnad1 id=eq.0h2v.s8.a6895e6ddfde from=translated src=- shape=4b076d81 vocab=18ebbcd4
-/
theorem finprod_norm_embedding (x : F) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖ = ∏ᶠ w : FinitePlace F, w x :=
  finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun w : FinitePlace F => w x)

/--
@isnad1 id=le.1h3v.s11.27493d4c6c3f from=translated src=- shape=618c90ec vocab=a373c3ad
-/
theorem finHeight_globalPoints_mul_mul_finHeight_le (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) * finHeight F h
      ≤ (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det))
          / (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)) ^ 2 := by
  have hdet0 : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  set fA := fun v : HeightOneSpectrum (𝓞 F) =>
    finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)) with hfAdef
  set fB := fun v : HeightOneSpectrum (𝓞 F) => finLocalHeight (finComponent (𝓞 F) F v h) with hfBdef
  set nD := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det)‖ with hnDdef
  set nE := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)‖ with hnEdef
  have hfA : fA.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hfB : fB.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hnD : nD.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hdet0
  have hnE : nE.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hγ
  have hle : ∀ v, fA v * fB v ≤ nD v / nE v ^ 2 := by
    intro v
    have h10 : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
          ≠ 0 := by
      rw [finComponent_globalPoints_apply, ← norm_pos_iff, norm_embedding_eq_equiv_symm]
      exact FinitePlace.pos_iff.mpr hγ
    have hv := finLocalHeight_mul_mul_finLocalHeight_le _ (finComponent (𝓞 F) F v h) h10
    rw [det_finComponent_globalPoints, finComponent_globalPoints_apply, ← map_mul] at hv
    exact hv
  have hnn : ∀ v, 0 ≤ fA v * fB v := fun v =>
    mul_nonneg (finLocalHeight_pos _).le (finLocalHeight_pos _).le
  calc finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) * finHeight F h
      = ∏ᶠ v, fA v * fB v := (finprod_mul_distrib hfA hfB).symm
    _ ≤ ∏ᶠ v, nD v / nE v ^ 2 :=
        finprod_le_finprod (hfA.mul hfB) hnn
          (show (fun v => nD v / nE v ^ 2).HasFiniteMulSupport from hnD.div (hnE.pow 2)) hle
    _ = (∏ᶠ v, nD v) / (∏ᶠ v, nE v) ^ 2 := by
        have hnEsq : (fun v => nE v ^ 2).HasFiniteMulSupport := hnE.pow 2
        rw [finprod_div_distrib hnD hnEsq, finprod_pow hnE 2]
    _ = (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det))
          / (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)) ^ 2 := by
        rw [hnDdef, hnEdef, finprod_norm_embedding, finprod_norm_embedding]

/--
@isnad1 id=le.1h3v.s9.d21b3ec6a379 from=translated src=- shape=e5b09f70 vocab=74702f8f
-/
theorem adelicHeight_globalPoints_mul_mul_adelicHeight_le_one (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F γ * g) * adelicHeight F g ≤ 1 := by
  have hdet0 : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  have hA := archHeight_globalPoints_mul_mul_archHeight_le F γ hγ (glArch (𝓞 F) F g)
  rw [← Rat.cast_abs, ← Rat.cast_abs, ← prod_eq_abs_norm, ← prod_eq_abs_norm] at hA
  have hB := finHeight_globalPoints_mul_mul_finHeight_le γ hγ (glFin (𝓞 F) F g)
  have hBnn : 0 ≤ finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * glFin (𝓞 F) F g)
      * finHeight F (glFin (𝓞 F) F g) := mul_nonneg (finHeight_pos _).le (finHeight_pos _).le
  have hQnn : 0 ≤ (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det) ^ w.mult)
      / (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) ^ w.mult) ^ 2 := by
    positivity
  unfold adelicHeight
  rw [map_mul, map_mul, mul_mul_mul_comm]
  refine (mul_le_mul hA hB hBnn hQnn).trans (le_of_eq ?_)
  rw [div_mul_div_comm, ← mul_pow, prod_abs_eq_one hdet0, prod_abs_eq_one hγ, one_pow, div_one]

/--
@isnad1 id=le.3h3v.s13.e35a4d2be739 from=translated src=- shape=15186794 vocab=6d217e11
-/
theorem archHeight_le_of_adelicHeight {γ : GL (Fin 2) F}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hγg : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * g) ∈ finiteIntegralGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * g)) * archHeight F (glArch (𝓞 F) F g)
      ≤ 1 := by
  have h := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ g
  rwa [adelicHeight_eq_archHeight_of_mem hγg, adelicHeight_eq_archHeight_of_mem hg] at h

end Adelic

end AdelicHeight

end NumberField
