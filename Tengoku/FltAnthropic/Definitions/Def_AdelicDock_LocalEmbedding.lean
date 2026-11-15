import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel
import Tengoku.FltAnthropic.Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Tengoku.Seed.NumberTheory.Padics.HeightOneSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrix_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] at hw
  rw [hw]

theorem matrix_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

open scoped Classical in

def splice (a : FiniteAdeleRing R K) (t : v.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨Function.update (⇑a) v t, (Filter.eventually_cofinite_ne v).mp (a.2.mono fun w hw hne => by
    rw [Function.update_of_ne hne]; exact hw)⟩

open scoped Classical in
@[simp] theorem splice_apply_self (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
    splice R K v a t v = t := by
  show Function.update (⇑a) v t v = t
  simp

open scoped Classical in
theorem splice_apply_of_ne (a : FiniteAdeleRing R K) (t : v.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : splice R K v a t w = a w := by
  show Function.update (⇑a) v t w = a w
  simp [Function.update_of_ne hw]

def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) (g i j)

theorem localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    localMat R K v g i j v = g i j := by
  simp [localMat]

theorem localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat R K v g i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  simp only [localMat, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat_apply_self]

theorem mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMat_apply_of_ne R K v g i j hw]

theorem localMat_one : localMat R K v 1 = 1 := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat_self, map_one]
  · rw [mapMatrix_localMat_of_ne R K v _ hw, map_one]

theorem localMat_mul (g h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    localMat R K v (g * h) = localMat R K v g * localMat R K v h := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, mapMatrix_localMat_self, mapMatrix_localMat_self, mapMatrix_localMat_self]
  · rw [map_mul, mapMatrix_localMat_of_ne R K v _ hw, mapMatrix_localMat_of_ne R K v _ hw,
      mapMatrix_localMat_of_ne R K v _ hw, mul_one]

def localEmbed : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat R K v g
      inv := localMat R K v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat_mul, Units.mul_inv, localMat_one]
      inv_val := by rw [← localMat_mul, Units.inv_mul, localMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMat_one R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMat_mul R K v _ _)

@[simp] theorem coe_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    ((localEmbed R K v g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) = localMat R K v g := rfl

theorem finComponent_localEmbed_self (g : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.finComponent R K v (localEmbed R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_self]

theorem finComponent_localEmbed_of_ne (g : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (localEmbed R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_of_ne R K v _ i j hw, Units.val_one]

theorem localEmbed_injective : Function.Injective (localEmbed R K v) := fun g h hgh => by
  rw [← finComponent_localEmbed_self R K v g, ← finComponent_localEmbed_self R K v h, hgh]

def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMat R K g) = 1 := by
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

theorem mapMatrix_fin_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMat R K g) = g := by
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

theorem finMat_one : finMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat, map_one])
    (by rw [mapMatrix_fin_finMat, map_one])

theorem finMat_mul (g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finMat R K (g * h) = finMat R K g * finMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, mapMatrix_fin_finMat])

def finEmbed : GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := finMat R K g
      inv := finMat R K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMat_mul, Units.mul_inv, finMat_one]
      inv_val := by rw [← finMat_mul, Units.inv_mul, finMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMat_mul R K _ _)

@[simp] theorem coe_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((finEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = finMat R K g := rfl

theorem glFin_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glFin R K (finEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glFin_apply, coe_finEmbed]
  rfl

theorem glArch_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glArch R K (finEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, coe_finEmbed, Units.val_one]
  rfl

theorem finEmbed_injective : Function.Injective (finEmbed R K) := fun g h hgh => by
  rw [← glFin_finEmbed R K g, ← glFin_finEmbed R K h, hgh]

theorem finEmbed_mem_levelOne_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelOne R K N ↔ g ∈ AdelicLevel.finiteLevelOne R K N := by
  rw [AdelicLevel.mem_levelOne_iff, glFin_finEmbed]

theorem finEmbed_mem_levelZero_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelZero R K N ↔ g ∈ AdelicLevel.finiteLevelZero R K N := by
  rw [AdelicLevel.mem_levelZero_iff, glFin_finEmbed]

def localLevelOne (N : Ideal R) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  (AdelicLevel.finiteLevelOne R K N).comap (localEmbed R K v)

theorem localEmbed_mem_finiteLevelOne_iff {N : Ideal R} (k : GL (Fin 2) (v.adicCompletion K)) :
    localEmbed R K v k ∈ AdelicLevel.finiteLevelOne R K N ↔ k ∈ localLevelOne R K v N :=
  Iff.rfl

structure IsLocalLevelOne (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop where
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  lowerLeft : Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v
  lowerRight : Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v

theorem isLevelOneMatrix_localMat_iff {N : Ideal R} (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.IsLevelOneMatrix R K N (localMat R K v m) ↔ IsLocalLevelOne R K v N m := by
  constructor
  · rintro ⟨⟨hint, hll⟩, hlr⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := hint i j v
      rwa [localMat_apply_self] at this
    · have := hll v
      rwa [localMat_apply_self] at this
    · have := hlr v
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_self] at this
  · rintro ⟨hint, hll, hlr⟩
    refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hint i j
      · rw [localMat_apply_of_ne R K v m i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hll
      · rw [localMat_apply_of_ne R K v m 1 0 hw, Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le
    · by_cases hw : w = v
      · subst hw; rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_self]; exact hlr
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_of_ne R K v m 1 1 hw,
          Matrix.one_apply_eq, sub_self, map_zero]
        exact zero_le

theorem mem_localLevelOne_iff {N : Ideal R} (k : GL (Fin 2) (v.adicCompletion K)) :
    k ∈ localLevelOne R K v N ↔
      IsLocalLevelOne R K v N k ∧ IsLocalLevelOne R K v N ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _) := by
  rw [localLevelOne, Subgroup.mem_comap, AdelicLevel.mem_finiteLevelOne_iff, ← map_inv, coe_localEmbed,
    coe_localEmbed, isLevelOneMatrix_localMat_iff, isLevelOneMatrix_localMat_iff]

end Generic

section Rat

variable (p : ℕ) [Fact p.Prime]

def padicPlace : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩

def padicRingEquiv : ℚ_[p] ≃+* (padicPlace p).adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toRingEquiv

theorem padicRingEquiv_apply (x : ℚ_[p]) :
    padicRingEquiv p x = Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩ x := rfl

def padicGL : GL (Fin 2) ℚ_[p] →* GL (Fin 2) ((padicPlace p).adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv p).toRingHom

theorem padicGL_apply (k : GL (Fin 2) ℚ_[p]) (i j : Fin 2) :
    (padicGL p k : Matrix _ _ _) i j = padicRingEquiv p ((k : Matrix _ _ _) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j k

theorem padicGL_injective : Function.Injective (padicGL p) := fun g h hgh => by
  refine Matrix.GeneralLinearGroup.ext fun i j => (padicRingEquiv p).injective ?_
  rw [← padicGL_apply, ← padicGL_apply, hgh]

def padicToFinAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (localEmbed (𝓞 ℚ) ℚ (padicPlace p)).comp (padicGL p)

def padicToAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ).comp (padicToFinAdelic p)

theorem padicToFinAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToFinAdelic p k = localEmbed (𝓞 ℚ) ℚ (padicPlace p) (padicGL p k) := rfl

theorem padicToAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToAdelic p k = finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic p k) := rfl

theorem finComponent_padicToFinAdelic_self (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) (padicToFinAdelic p k) = padicGL p k :=
  finComponent_localEmbed_self _ _ _ _

theorem finComponent_padicToFinAdelic_of_ne (k : GL (Fin 2) ℚ_[p]) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ padicPlace p) : AdelicLevel.finComponent (𝓞 ℚ) ℚ w (padicToFinAdelic p k) = 1 :=
  finComponent_localEmbed_of_ne _ _ _ _ hw

theorem glFin_padicToAdelic (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.glFin (𝓞 ℚ) ℚ (padicToAdelic p k) = padicToFinAdelic p k :=
  glFin_finEmbed _ _ _

theorem glArch_padicToAdelic (k : GL (Fin 2) ℚ_[p]) : AdelicLevel.glArch (𝓞 ℚ) ℚ (padicToAdelic p k) = 1 :=
  glArch_finEmbed _ _ _

theorem padicToAdelic_injective : Function.Injective (padicToAdelic p) :=
  (finEmbed_injective _ _).comp ((localEmbed_injective _ _ _).comp (padicGL_injective p))

def ratLevel (N : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(N : 𝓞 ℚ)}

theorem ratLevel_ne_bot {N : ℕ} (hN : N ≠ 0) : ratLevel N ≠ ⊥ := by
  rw [ratLevel, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hN

theorem ratLevel_one : ratLevel 1 = ⊤ := by
  rw [ratLevel, Nat.cast_one, Ideal.span_singleton_one]

theorem idealBound_ratLevel {N : ℕ} (hN : N ≠ 0) :
    AdelicLevel.idealBound (𝓞 ℚ) (ratLevel N) (padicPlace p) = Valued.v (padicRingEquiv p (N : ℚ_[p])) := by
  have hN' : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN
  rw [AdelicLevel.idealBound_of_ne_bot (ratLevel_ne_bot hN), ratLevel,
    ← HeightOneSpectrum.intValuation_if_neg _ hN', ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation, map_natCast]
  congr 1
  exact map_natCast (algebraMap (𝓞 ℚ) ((padicPlace p).adicCompletion ℚ)) N

theorem norm_natCast_eq_zpow_neg_factorization {N : ℕ} (hN : N ≠ 0) :
    ‖(N : ℚ_[p])‖ = (p : ℝ) ^ (-(N.factorization p : ℤ)) := by
  rw [Nat.factorization_def N (Fact.out : p.Prime), Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN),
    Padic.valuation_natCast]

end Rat

end AdelicDock

end
