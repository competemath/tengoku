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

/--
@isnad1 id=eq.1h4v.s10.cf945dcc6238 from=translated src=- shape=fb721868 vocab=511dd26d
-/
theorem matrix_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] at hw
  rw [hw]

/--
@isnad1 id=eq.2h4v.s10.0c81f2609a8c from=translated src=- shape=a68a9bda vocab=10149c39
-/
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
/--
@isnad1 id=eq.0h5v.s6.abe9ee3a4f23 from=translated src=- shape=41734dfb vocab=4a9f1b21
-/
@[simp] theorem splice_apply_self (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
    splice R K v a t v = t := by
  show Function.update (⇑a) v t v = t
  simp

open scoped Classical in
/--
@isnad1 id=eq.1h6v.s7.94cb5e3aa949 from=translated src=- shape=d3b12c18 vocab=4a9f1b21
-/
theorem splice_apply_of_ne (a : FiniteAdeleRing R K) (t : v.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : splice R K v a t w = a w := by
  show Function.update (⇑a) v t w = a w
  simp [Function.update_of_ne hw]

def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) (g i j)

/--
@isnad1 id=eq.0h6v.s7.889c7e68eab9 from=translated src=- shape=8215da48 vocab=6d8b19ba
-/
theorem localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    localMat R K v g i j v = g i j := by
  simp [localMat]

/--
@isnad1 id=eq.1h7v.s8.a4d3b3ee1f51 from=translated src=- shape=e07588f0 vocab=6d8b19ba
-/
theorem localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat R K v g i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  simp only [localMat, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

/--
@isnad1 id=eq.0h4v.s9.df4ad9d30ecd from=translated src=- shape=7bc66f6c vocab=b074fafb
-/
theorem mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat_apply_self]

/--
@isnad1 id=eq.1h5v.s9.f693e2379239 from=translated src=- shape=d5a206f6 vocab=b074fafb
-/
theorem mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMat_apply_of_ne R K v g i j hw]

/--
@isnad1 id=eq.0h3v.s8.16fdcbf21153 from=translated src=- shape=205ffb82 vocab=c2725313
-/
theorem localMat_one : localMat R K v 1 = 1 := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat_self, map_one]
  · rw [mapMatrix_localMat_of_ne R K v _ hw, map_one]

/--
@isnad1 id=eq.0h5v.s9.472b006430cb from=translated src=- shape=238ac770 vocab=02ef8618
-/
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

/--
@isnad1 id=eq.0h4v.s10.5b3f5db79531 from=translated src=- shape=8a2b78fb vocab=95b8435b
-/
@[simp] theorem coe_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    ((localEmbed R K v g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) = localMat R K v g := rfl

/--
@isnad1 id=eq.0h4v.s11.ea0ba5021baa from=translated src=- shape=40c21575 vocab=b3668877
-/
theorem finComponent_localEmbed_self (g : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.finComponent R K v (localEmbed R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_self]

/--
@isnad1 id=eq.1h5v.s11.29385a9c904d from=translated src=- shape=75c295dc vocab=b3668877
-/
theorem finComponent_localEmbed_of_ne (g : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (localEmbed R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_of_ne R K v _ i j hw, Units.val_one]

/--
@isnad1 id=injectiv.0h3v.s10.1ea8217114b5 from=translated src=- shape=d41106f3 vocab=ac513db0
-/
theorem localEmbed_injective : Function.Injective (localEmbed R K v) := fun g h hgh => by
  rw [← finComponent_localEmbed_self R K v g, ← finComponent_localEmbed_self R K v h, hgh]

def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

/--
@isnad1 id=eq.0h3v.s9.43daf3f82db8 from=translated src=- shape=ba4e2f3c vocab=15f6931c
-/
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

/--
@isnad1 id=eq.0h3v.s9.63193f414537 from=translated src=- shape=5cd018af vocab=ebd7a3a2
-/
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

/--
@isnad1 id=eq.0h2v.s8.fd93370d14e5 from=translated src=- shape=11e92986 vocab=0c2f4795
-/
theorem finMat_one : finMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat, map_one])
    (by rw [mapMatrix_fin_finMat, map_one])

/--
@isnad1 id=eq.0h4v.s8.2f32a7e8abab from=translated src=- shape=5bc4571e vocab=f465a5d0
-/
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

/--
@isnad1 id=eq.0h3v.s10.daeb071de96c from=translated src=- shape=5aa4f7f3 vocab=c7168529
-/
@[simp] theorem coe_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((finEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = finMat R K g := rfl

/--
@isnad1 id=eq.0h3v.s11.c6fdda172500 from=translated src=- shape=bacd8f9b vocab=5b94889b
-/
theorem glFin_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glFin R K (finEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glFin_apply, coe_finEmbed]
  rfl

/--
@isnad1 id=eq.0h3v.s11.146db4c19ce4 from=translated src=- shape=64d2b75b vocab=f1d60621
-/
theorem glArch_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glArch R K (finEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, coe_finEmbed, Units.val_one]
  rfl

/--
@isnad1 id=injectiv.0h2v.s10.62b416a4b267 from=translated src=- shape=ddbfbcde vocab=0b796472
-/
theorem finEmbed_injective : Function.Injective (finEmbed R K) := fun g h hgh => by
  rw [← glFin_finEmbed R K g, ← glFin_finEmbed R K h, hgh]

/--
@isnad1 id=iff.0h4v.s11.d1c0957fd6d3 from=translated src=- shape=10b6867a vocab=de6d533a
-/
theorem finEmbed_mem_levelOne_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelOne R K N ↔ g ∈ AdelicLevel.finiteLevelOne R K N := by
  rw [AdelicLevel.mem_levelOne_iff, glFin_finEmbed]

/--
@isnad1 id=iff.0h4v.s11.2c3620eb7c5b from=translated src=- shape=10b6867a vocab=41c790e8
-/
theorem finEmbed_mem_levelZero_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelZero R K N ↔ g ∈ AdelicLevel.finiteLevelZero R K N := by
  rw [AdelicLevel.mem_levelZero_iff, glFin_finEmbed]

def localLevelOne (N : Ideal R) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  (AdelicLevel.finiteLevelOne R K N).comap (localEmbed R K v)

/--
@isnad1 id=iff.0h5v.s11.c3eca957324c from=translated src=- shape=7e52e973 vocab=9cd2b961
-/
theorem localEmbed_mem_finiteLevelOne_iff {N : Ideal R} (k : GL (Fin 2) (v.adicCompletion K)) :
    localEmbed R K v k ∈ AdelicLevel.finiteLevelOne R K N ↔ k ∈ localLevelOne R K v N :=
  Iff.rfl

structure IsLocalLevelOne (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop where
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  lowerLeft : Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v
  lowerRight : Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v

/--
@isnad1 id=iff.0h5v.s6.31bb02466679 from=translated src=- shape=5b4df23d vocab=49d83b03
-/
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

/--
@isnad1 id=iff.0h5v.s10.12955bc6a380 from=translated src=- shape=410a91fc vocab=024b7ac4
-/
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

/--
@isnad1 id=eq.0h2v.s11.c73726dda9e6 from=translated src=- shape=62fe04a6 vocab=f300fb95
-/
theorem padicRingEquiv_apply (x : ℚ_[p]) :
    padicRingEquiv p x = Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩ x := rfl

def padicGL : GL (Fin 2) ℚ_[p] →* GL (Fin 2) ((padicPlace p).adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv p).toRingHom

/--
@isnad1 id=eq.0h4v.s11.e292db492bf5 from=translated src=- shape=2ed209dc vocab=628b0299
-/
theorem padicGL_apply (k : GL (Fin 2) ℚ_[p]) (i j : Fin 2) :
    (padicGL p k : Matrix _ _ _) i j = padicRingEquiv p ((k : Matrix _ _ _) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j k

/--
@isnad1 id=injectiv.0h1v.s10.f9fb7e8252c7 from=translated src=- shape=0a247de3 vocab=34a08e2e
-/
theorem padicGL_injective : Function.Injective (padicGL p) := fun g h hgh => by
  refine Matrix.GeneralLinearGroup.ext fun i j => (padicRingEquiv p).injective ?_
  rw [← padicGL_apply, ← padicGL_apply, hgh]

def padicToFinAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (localEmbed (𝓞 ℚ) ℚ (padicPlace p)).comp (padicGL p)

def padicToAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ).comp (padicToFinAdelic p)

/--
@isnad1 id=eq.0h2v.s11.f59fff278035 from=translated src=- shape=1dd58b3a vocab=94b55c00
-/
theorem padicToFinAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToFinAdelic p k = localEmbed (𝓞 ℚ) ℚ (padicPlace p) (padicGL p k) := rfl

/--
@isnad1 id=eq.0h2v.s11.38e7e2c76970 from=translated src=- shape=97b53b13 vocab=10c1ff03
-/
theorem padicToAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToAdelic p k = finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic p k) := rfl

/--
@isnad1 id=eq.0h2v.s11.97b92ff68d31 from=translated src=- shape=56bc9f72 vocab=18b19a1f
-/
theorem finComponent_padicToFinAdelic_self (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) (padicToFinAdelic p k) = padicGL p k :=
  finComponent_localEmbed_self _ _ _ _

/--
@isnad1 id=eq.1h3v.s11.c5151cfa234b from=translated src=- shape=c2d90e46 vocab=901fa121
-/
theorem finComponent_padicToFinAdelic_of_ne (k : GL (Fin 2) ℚ_[p]) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ padicPlace p) : AdelicLevel.finComponent (𝓞 ℚ) ℚ w (padicToFinAdelic p k) = 1 :=
  finComponent_localEmbed_of_ne _ _ _ _ hw

/--
@isnad1 id=eq.0h2v.s11.19d40f7e2459 from=translated src=- shape=701ae4ae vocab=68d2a82e
-/
theorem glFin_padicToAdelic (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.glFin (𝓞 ℚ) ℚ (padicToAdelic p k) = padicToFinAdelic p k :=
  glFin_finEmbed _ _ _

/--
@isnad1 id=eq.0h2v.s11.abd74c5f95e2 from=translated src=- shape=c94f63f8 vocab=fae9a863
-/
theorem glArch_padicToAdelic (k : GL (Fin 2) ℚ_[p]) : AdelicLevel.glArch (𝓞 ℚ) ℚ (padicToAdelic p k) = 1 :=
  glArch_finEmbed _ _ _

/--
@isnad1 id=injectiv.0h1v.s10.6cd13828ad9f from=translated src=- shape=0072e4c6 vocab=9e92ca02
-/
theorem padicToAdelic_injective : Function.Injective (padicToAdelic p) :=
  (finEmbed_injective _ _).comp ((localEmbed_injective _ _ _).comp (padicGL_injective p))

def ratLevel (N : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(N : 𝓞 ℚ)}

/--
@isnad1 id=ne.1h1v.s6.d011232cd829 from=translated src=- shape=3bf6eab1 vocab=6b7baec6
-/
theorem ratLevel_ne_bot {N : ℕ} (hN : N ≠ 0) : ratLevel N ≠ ⊥ := by
  rw [ratLevel, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hN

/--
@isnad1 id=eq.0h0v.s6.d753ae51cd90 from=translated src=- shape=b1c0b895 vocab=69832812
-/
theorem ratLevel_one : ratLevel 1 = ⊤ := by
  rw [ratLevel, Nat.cast_one, Ideal.span_singleton_one]

/--
@isnad1 id=eq.1h2v.s10.e53296e78e2f from=translated src=- shape=f5f93272 vocab=5eeebdc8
-/
theorem idealBound_ratLevel {N : ℕ} (hN : N ≠ 0) :
    AdelicLevel.idealBound (𝓞 ℚ) (ratLevel N) (padicPlace p) = Valued.v (padicRingEquiv p (N : ℚ_[p])) := by
  have hN' : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN
  rw [AdelicLevel.idealBound_of_ne_bot (ratLevel_ne_bot hN), ratLevel,
    ← HeightOneSpectrum.intValuation_if_neg _ hN', ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation, map_natCast]
  congr 1
  exact map_natCast (algebraMap (𝓞 ℚ) ((padicPlace p).adicCompletion ℚ)) N

/--
@isnad1 id=eq.1h2v.s6.b529ee1d1a6a from=translated src=- shape=51527135 vocab=ccb8adcb
-/
theorem norm_natCast_eq_zpow_neg_factorization {N : ℕ} (hN : N ≠ 0) :
    ‖(N : ℚ_[p])‖ = (p : ℝ) ^ (-(N.factorization p : ℤ)) := by
  rw [Nat.factorization_def N (Fact.out : p.Prime), Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN),
    Padic.valuation_natCast]

end Rat

end AdelicDock

end
