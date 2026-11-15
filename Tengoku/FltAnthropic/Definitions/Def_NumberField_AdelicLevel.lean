import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped Classical in

def idealBound (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

section IdealBound

variable {R}

/--
@isnad1 id=eq.0h2v.s6.6113b7bc56c5 from=translated src=- shape=dc56cebf vocab=365229ab
-/
theorem idealBound_bot (v : HeightOneSpectrum R) : idealBound R ⊥ v = 0 := ite_eq_left rfl

/--
@isnad1 id=eq.1h3v.s7.35d40d36a686 from=translated src=- shape=a8bef6be vocab=1c0f6c66
-/
theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v
      = WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) := by
  classical
  exact ite_eq_right hN

/--
@isnad1 id=ne.1h3v.s6.de3239571088 from=translated src=- shape=c7edcbbc vocab=365229ab
-/
theorem idealBound_ne_zero {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v ≠ 0 := by
  rw [idealBound_of_ne_bot hN]; exact WithZero.exp_ne_zero

/--
@isnad1 id=le.0h3v.s6.16c0d697d501 from=translated src=- shape=149b2c92 vocab=94ae5ed1
-/
theorem idealBound_le_one (N : Ideal R) (v : HeightOneSpectrum R) : idealBound R N v ≤ 1 := by
  by_cases hN : N = ⊥
  · rw [hN, idealBound_bot]; exact zero_le
  · rw [idealBound_of_ne_bot hN, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

/--
@isnad1 id=eq.2h3v.s7.a8c894a0a451 from=translated src=- shape=a8ee29f7 vocab=d0d00d88
-/
theorem idealBound_eq_one_of_not_dvd {N : Ideal R} (hN : N ≠ ⊥) {v : HeightOneSpectrum R}
    (hv : ¬ v.asIdeal ∣ N) : idealBound R N v = 1 := by
  classical
  rw [idealBound_of_ne_bot hN]
  have h0 : (Associates.mk v.asIdeal).count (Associates.mk N).factors = 0 := by
    by_contra h
    exact hv ((Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) v.irreducible).mp h)
  rw [h0]; simp

/--
@isnad1 id=eq.0h2v.s6.0f75e14f89b2 from=translated src=- shape=dc56cebf vocab=b2e7eb21
-/
theorem idealBound_top (v : HeightOneSpectrum R) : idealBound R (⊤ : Ideal R) v = 1 :=
  idealBound_eq_one_of_not_dvd top_ne_bot fun h =>
    v.isPrime.ne_top ((Ideal.dvd_iff_le.mp h).antisymm le_top |>.symm ▸ rfl)

/--
@isnad1 id=finite.1h2v.s6.fbf482543dcf from=translated src=- shape=17b3754a vocab=01f322ec
-/
theorem finite_setOf_idealBound_ne_one {N : Ideal R} (hN : N ≠ ⊥) :
    {v : HeightOneSpectrum R | idealBound R N v ≠ 1}.Finite :=
  (Ideal.finite_factors hN).subset fun _ hv => by
    by_contra h
    exact hv (idealBound_eq_one_of_not_dvd hN h)

end IdealBound

section Local

variable {R K} (v : HeightOneSpectrum R)

/--
@isnad1 id=mem.0h4v.s8.99fa839f06c6 from=translated src=- shape=a952829b vocab=dcbaddea
-/
theorem algebraMap_mem_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

/--
@isnad1 id=eq.0h4v.s9.73716cf88c2b from=translated src=- shape=df1a2a68 vocab=62dad0cd
-/
theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

/--
@isnad1 id=eq.1h4v.s9.9732150a5bde from=translated src=- shape=d47fa21e vocab=efa9471a
-/
theorem setOf_valued_le_eq_preimage (t : v.adicCompletion K) (ht : t ≠ 0) :
    {y : v.adicCompletion K | Valued.v y ≤ Valued.v t}
      = (fun y => y * t⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  rw [mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ht)), one_mul]

/--
@isnad1 id=isopen.1h4v.s9.a5b61c459aa0 from=translated src=- shape=f2009ef7 vocab=8f99f924
-/
theorem isOpen_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (continuous_id.mul continuous_const).isOpen_preimage _ (Valued.isOpen_valuationSubring _)

/--
@isnad1 id=isclosed.0h3v.s7.1698695acdf0 from=translated src=- shape=f3f00d90 vocab=a477cc15
-/
theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring _

/--
@isnad1 id=isclosed.1h4v.s9.ed9710d310bd from=translated src=- shape=f2009ef7 vocab=f866e1c2
-/
theorem isClosed_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (isClosed_adicCompletionIntegers v).preimage (continuous_id.mul continuous_const)

/--
@isnad1 id=ex.0h4v.s8.78464b2dc2f2 from=translated src=- shape=76a45725 vocab=d61aa4c3
-/
theorem exists_valued_eq_exp_neg (n : ℕ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨(algebraMap K (v.adicCompletion K) (algebraMap R K π)) ^ n, ?_, ?_⟩
  · refine pow_ne_zero _ fun h => ?_
    have := valued_algebraMap (K := K) v π
    rw [h, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [map_pow, valued_algebraMap, hπ]
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

/--
@isnad1 id=isopen.1h4v.s8.4ed40723d1b5 from=translated src=- shape=e3f8cdac vocab=79b966d8
-/
theorem isOpen_setOf_valued_le_idealBound {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
    ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
  rw [idealBound_of_ne_bot hN, ← hvt]
  exact isOpen_setOf_valued_le v t ht

/--
@isnad1 id=isclosed.0h4v.s8.4b5149905720 from=translated src=- shape=6d1912e9 vocab=8cceb5b5
-/
theorem isClosed_setOf_valued_le_idealBound (N : Ideal R) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  by_cases hN : N = ⊥
  · have : {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} = {0} := by
      ext y; simp [hN, idealBound_bot]
    rw [this]; exact isClosed_singleton
  · obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
      ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
    rw [idealBound_of_ne_bot hN, ← hvt]
    exact isClosed_setOf_valued_le v t ht

end Local

section Projections

def archEval (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def finAdeleEval (v : HeightOneSpectrum R) : FiniteAdeleRing R K →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/--
@isnad1 id=eq.0h3v.s7.9b0bea299e59 from=translated src=- shape=69ffa2cf vocab=5dade926
-/
theorem archEval_apply (w : InfinitePlace K) (a : InfiniteAdeleRing K) : archEval K w a = a w := rfl
/--
@isnad1 id=eq.0h4v.s8.ac2cb0c524c4 from=translated src=- shape=79ded227 vocab=f0cc672f
-/
theorem finAdeleEval_apply (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
    finAdeleEval R K v a = a v := rfl
/--
@isnad1 id=eq.0h3v.s7.e52b89d57cee from=translated src=- shape=e7163be9 vocab=0243a7e3
-/
theorem adeleArch_apply (a : AdeleRing R K) : adeleArch R K a = a.1 := rfl
/--
@isnad1 id=eq.0h3v.s8.3282b1196326 from=translated src=- shape=207bf988 vocab=3f453abe
-/
theorem adeleFin_apply (a : AdeleRing R K) : adeleFin R K a = a.2 := rfl

/--
@isnad1 id=continuo.0h2v.s7.04425b29f076 from=translated src=- shape=47d524f1 vocab=434ba6ef
-/
theorem continuous_archEval (w : InfinitePlace K) : Continuous (archEval K w) :=
  (continuous_apply w : Continuous fun a : (∀ w : InfinitePlace K, w.Completion) => a w)

/--
@isnad1 id=continuo.0h3v.s8.c0844d865664 from=translated src=- shape=7d2c1ffe vocab=3083ceea
-/
theorem continuous_finAdeleEval (v : HeightOneSpectrum R) : Continuous (finAdeleEval R K v) :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum R, [w.adicCompletion K, w.adicCompletionIntegers K] => x v)

/--
@isnad1 id=continuo.0h2v.s7.ae79f0ed8b48 from=translated src=- shape=8d9d9608 vocab=7b2bc327
-/
theorem continuous_adeleArch : Continuous (adeleArch R K) :=
  (continuous_fst : Continuous fun x : AdeleRing R K => x.1)

/--
@isnad1 id=continuo.0h2v.s8.1cb0f2776264 from=translated src=- shape=334c9b61 vocab=7f0ddaef
-/
theorem continuous_adeleFin : Continuous (adeleFin R K) :=
  (continuous_snd : Continuous fun x : AdeleRing R K => x.2)

def archComponent (w : InfinitePlace K) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

def finComponent (v : HeightOneSpectrum R) :
    GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (finAdeleEval R K v)

def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

/--
@isnad1 id=eq.0h5v.s9.dee23424421f from=translated src=- shape=75caa438 vocab=90455cda
-/
theorem archComponent_apply (w : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    (archComponent K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w := rfl
/--
@isnad1 id=eq.0h6v.s10.f633b30ca306 from=translated src=- shape=3ada945f vocab=654e0123
-/
theorem finComponent_apply (v : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K))
    (i j : Fin 2) : (finComponent R K v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v := rfl
/--
@isnad1 id=eq.0h5v.s10.ca8a9004894a from=translated src=- shape=e6aae420 vocab=6b57f525
-/
theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 := rfl
/--
@isnad1 id=eq.0h5v.s10.5d0a1dcbc3ca from=translated src=- shape=178da064 vocab=8294acce
-/
theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 := rfl

private theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

/--
@isnad1 id=continuo.0h2v.s10.ecb50bc427e0 from=translated src=- shape=0024d22d vocab=8d69a4f1
-/
theorem continuous_archComponent (w : InfinitePlace K) : Continuous (archComponent K w) :=
  continuous_glMap _ (continuous_archEval K w)
/--
@isnad1 id=continuo.0h3v.s10.99b5f1fe4479 from=translated src=- shape=69a3c357 vocab=6c507537
-/
theorem continuous_finComponent (v : HeightOneSpectrum R) : Continuous (finComponent R K v) :=
  continuous_glMap _ (continuous_finAdeleEval R K v)
/--
@isnad1 id=continuo.0h2v.s10.839fe17e0b19 from=translated src=- shape=fc012b35 vocab=49f9bf05
-/
theorem continuous_glArch : Continuous (glArch R K) := continuous_glMap _ (continuous_adeleArch R K)
/--
@isnad1 id=continuo.0h2v.s10.97c9ceeae74b from=translated src=- shape=ddbfbcde vocab=8ad95a85
-/
theorem continuous_glFin : Continuous (glFin R K) := continuous_glMap _ (continuous_adeleFin R K)

end Projections

section FiniteAdelic

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ idealBound R N v}

variable {R K}

section Coe
variable (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
/--
@isnad1 id=eq.0h3v.s7.ed29e8d38298 from=translated src=- shape=b5939b3b vocab=120983fe
-/
theorem coe_zero_apply : (0 : FiniteAdeleRing R K) v = 0 := rfl
/--
@isnad1 id=eq.0h3v.s7.a58c0a81fd1e from=translated src=- shape=b5939b3b vocab=120983fe
-/
theorem coe_one_apply : (1 : FiniteAdeleRing R K) v = 1 := rfl
/--
@isnad1 id=eq.0h5v.s8.ff3c9a641df7 from=translated src=- shape=a4a483da vocab=844643e1
-/
theorem coe_add_apply : (x + y) v = x v + y v := rfl
/--
@isnad1 id=eq.0h5v.s8.1ec907485982 from=translated src=- shape=a4a483da vocab=ae3acdbd
-/
theorem coe_mul_apply : (x * y) v = x v * y v := rfl
/--
@isnad1 id=eq.0h5v.s8.ab84b693843b from=translated src=- shape=a4a483da vocab=59f5a2b0
-/
theorem coe_sub_apply : (x - y) v = x v - y v := rfl
/--
@isnad1 id=eq.0h4v.s8.89c331cb6523 from=translated src=- shape=42734bb0 vocab=20ac1c27
-/
theorem coe_neg_apply : (-x) v = -x v := rfl
end Coe

/--
@isnad1 id=le.0h3v.s6.058be2ebc634 from=translated src=- shape=7ce747f9 vocab=4120a81b
-/
theorem idealBall_subset_integralFiniteAdeles (N : Ideal R) :
    idealBall R K N ⊆ integralFiniteAdeles R K := fun _ hx v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hx v).trans (idealBound_le_one N v))

/--
@isnad1 id=mem.0h3v.s7.f24cbd40f91b from=translated src=- shape=0009d71a vocab=465a913b
-/
theorem zero_mem_idealBall (N : Ideal R) : (0 : FiniteAdeleRing R K) ∈ idealBall R K N :=
  fun v => by rw [coe_zero_apply, map_zero]; exact zero_le

variable (R K)

/--
@isnad1 id=isopen.0h2v.s6.fd48459ec170 from=translated src=- shape=1bb14ae2 vocab=20460cca
-/
theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles R K) :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out

/--
@isnad1 id=isclosed.0h2v.s6.baeb8c6d454c from=translated src=- shape=1bb14ae2 vocab=6b2dd9c1
-/
theorem isClosed_integralFiniteAdeles : IsClosed (integralFiniteAdeles R K) := by
  have : integralFiniteAdeles R K = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x; simp [integralFiniteAdeles]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_adicCompletionIntegers v).preimage (continuous_finAdeleEval R K v)

/--
@isnad1 id=isclosed.0h3v.s6.94cd20540c60 from=translated src=- shape=71739909 vocab=b5bddb45
-/
theorem isClosed_idealBall (N : Ideal R) : IsClosed (idealBall R K N) := by
  have : idealBall R K N = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x; simp [idealBall]
  rw [this]
  exact isClosed_iInter fun v =>
    (isClosed_setOf_valued_le_idealBound v N).preimage (continuous_finAdeleEval R K v)

/--
@isnad1 id=isopen.1h3v.s6.b169b1c053f7 from=translated src=- shape=33cb2224 vocab=f4f83981
-/
theorem isOpen_idealBall {N : Ideal R} (hN : N ≠ ⊥) : IsOpen (idealBall R K N) := by
  have hfin := finite_setOf_idealBound_ne_one hN
  have : idealBall R K N = integralFiniteAdeles R K ∩
      ⋂ v ∈ {v : HeightOneSpectrum R | idealBound R N v ≠ 1},
        (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun hx => ⟨idealBall_subset_integralFiniteAdeles N hx, fun v _ => hx v⟩,
      fun ⟨hint, hT⟩ v => ?_⟩
    by_cases hv : idealBound R N v = 1
    · rw [hv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint v)
    · exact hT v hv
  rw [this]
  exact (isOpen_integralFiniteAdeles R K).inter (hfin.isOpen_biInter fun v _ =>
    (isOpen_setOf_valued_le_idealBound v hN).preimage (continuous_finAdeleEval R K v))

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/--
@isnad1 id=iscompac.0h2v.s6.2b6b21e09c8d from=translated src=- shape=1b1eebbb vocab=a5f30b45
-/
theorem isCompact_integralFiniteAdeles : IsCompact (integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end FiniteAdelic

section FiniteLevel

structure IsLevelZeroMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles R K
  lowerLeft : m 1 0 ∈ idealBall R K N

structure IsLevelOneMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop extends IsLevelZeroMatrix R K N m where
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

variable {R K}
variable {N : Ideal R}

/--
@isnad1 id=mem.0h2v.s7.458f96864158 from=translated src=- shape=c45fa467 vocab=c1e3ba6f
-/
theorem one_mem_integralFiniteAdeles : (1 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => one_mem _

/--
@isnad1 id=mem.0h2v.s7.3f5b393f18ed from=translated src=- shape=c45fa467 vocab=c1e3ba6f
-/
theorem zero_mem_integralFiniteAdeles : (0 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => zero_mem _

/--
@isnad1 id=mem.2h4v.s7.a4aa7b3b1978 from=translated src=- shape=96d63a69 vocab=117e581f
-/
theorem add_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x + y ∈ integralFiniteAdeles R K :=
  fun v => add_mem (hx v) (hy v)

/--
@isnad1 id=mem.2h4v.s7.ab3ac4ad63d2 from=translated src=- shape=96d63a69 vocab=90f9507d
-/
theorem mul_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ integralFiniteAdeles R K :=
  fun v => mul_mem (hx v) (hy v)

/--
@isnad1 id=mem.2h4v.s8.c1df438b2bcd from=translated src=- shape=96d63a69 vocab=1b46541b
-/
theorem sub_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x - y ∈ integralFiniteAdeles R K :=
  fun v => sub_mem (hx v) (hy v)

/--
@isnad1 id=le.1h4v.s8.ff146fde66f0 from=translated src=- shape=17ed635b vocab=49a4f546
-/
theorem valued_apply_le_one {x : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (v : HeightOneSpectrum R) : Valued.v (x v) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v)

/--
@isnad1 id=mem.2h5v.s8.f31bcac8ae9f from=translated src=- shape=576973de vocab=8dada635
-/
theorem add_mem_idealBall {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x + y ∈ idealBall R K N := fun v =>
  (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

/--
@isnad1 id=mem.2h5v.s8.ba098f0f4f16 from=translated src=- shape=239bfaa9 vocab=fac91f0f
-/
theorem mul_mem_idealBall_left {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ idealBall R K N) : x * y ∈ idealBall R K N := fun v => by
  rw [coe_mul_apply, map_mul]
  calc Valued.v (x v) * Valued.v (y v) ≤ 1 * idealBound R N v :=
        mul_le_mul' (valued_apply_le_one hx v) (hy v)
    _ = idealBound R N v := one_mul _

/--
@isnad1 id=mem.2h5v.s8.155f7aa8b376 from=translated src=- shape=2286d977 vocab=fac91f0f
-/
theorem mul_mem_idealBall_right {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ idealBall R K N := by
  rw [mul_comm]; exact mul_mem_idealBall_left hy hx

namespace IsLevelZeroMatrix

/--
@isnad1 id=islevelz.0h3v.s7.7eb51dfbd87d from=translated src=- shape=820107e3 vocab=d59c0aab
-/
protected theorem one : IsLevelZeroMatrix R K N 1 where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide)]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

/--
@isnad1 id=islevelz.2h5v.s8.5ecb5bdbdcb7 from=translated src=- shape=ef13128f vocab=ddfcb1dd
-/
protected theorem mul (hm : IsLevelZeroMatrix R K N m) (hm' : IsLevelZeroMatrix R K N m') :
    IsLevelZeroMatrix R K N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (hm.integral i 0) (hm'.integral 0 j))
      (mul_mem_integralFiniteAdeles (hm.integral i 1) (hm'.integral 1 j))
  lowerLeft := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 0))
      (mul_mem_idealBall_left (hm.integral 1 1) hm'.lowerLeft)

end IsLevelZeroMatrix

namespace IsLevelOneMatrix

/--
@isnad1 id=islevelo.0h3v.s7.3defdbed88ef from=translated src=- shape=820107e3 vocab=df019347
-/
protected theorem one : IsLevelOneMatrix R K N 1 where
  toIsLevelZeroMatrix := .one
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

/--
@isnad1 id=islevelo.2h5v.s8.06c00205b64f from=translated src=- shape=ef13128f vocab=7b21f529
-/
protected theorem mul (hm : IsLevelOneMatrix R K N m) (hm' : IsLevelOneMatrix R K N m') :
    IsLevelOneMatrix R K N (m * m') where
  toIsLevelZeroMatrix := hm.toIsLevelZeroMatrix.mul hm'.toIsLevelZeroMatrix
  lowerRight := by
    have h : (m * m') 1 1 - 1
        = m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 1))
      (add_mem_idealBall (mul_mem_idealBall_right hm.lowerRight (hm'.integral 1 1)) hm'.lowerRight)

end IsLevelOneMatrix

variable (R K) (N)

def finiteLevelZero : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelZeroMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {R K N}

/--
@isnad1 id=iff.0h4v.s10.900bb4e9d5b6 from=translated src=- shape=ad13ab75 vocab=6084ef69
-/
theorem mem_finiteLevelZero_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelZero R K N ↔ IsLevelZeroMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s10.7fe3a87aa594 from=translated src=- shape=ad13ab75 vocab=c0433589
-/
theorem mem_finiteLevelOne_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelOne R K N ↔ IsLevelOneMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

variable (R K N)

/--
@isnad1 id=le.0h3v.s9.2c81bcc58de2 from=translated src=- shape=edd0f222 vocab=6f338156
-/
theorem finiteLevelOne_le_finiteLevelZero : finiteLevelOne R K N ≤ finiteLevelZero R K N :=
  fun _ hg => ⟨hg.1.toIsLevelZeroMatrix, hg.2.toIsLevelZeroMatrix⟩

abbrev finiteIntegralGL2 : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) := finiteLevelZero R K ⊤

variable {R K} in
/--
@isnad1 id=iff.0h3v.s10.7ff02ea3fc7c from=translated src=- shape=b1a1b764 vocab=9005da3e
-/
theorem mem_finiteIntegralGL2_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteIntegralGL2 R K ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
        i j ∈ integralFiniteAdeles R K :=
  ⟨fun h => ⟨h.1.integral, h.2.integral⟩, fun h =>
    ⟨⟨h.1, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.1 1 0) v⟩,
     ⟨h.2, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.2 1 0) v⟩⟩⟩

/--
@isnad1 id=isclosed.0h3v.s7.22a203b6a391 from=translated src=- shape=d08a720f vocab=531215be
-/
theorem isClosed_setOf_isLevelZeroMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isClosed_idealBall R K N).preimage (continuous_id.matrix_elem 1 0))

/--
@isnad1 id=isclosed.0h3v.s7.a1a03a831739 from=translated src=- shape=d08a720f vocab=067454b8
-/
theorem isClosed_setOf_isLevelOneMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_setOf_isLevelZeroMatrix R K N).inter
    ((isClosed_idealBall R K N).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in
/--
@isnad1 id=isopen.1h3v.s7.61ea4d91401d from=translated src=- shape=251dab5a vocab=df51d5d6
-/
theorem isOpen_setOf_isLevelZeroMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isOpen_idealBall R K hN).preimage (continuous_id.matrix_elem 1 0))

variable {N} in
/--
@isnad1 id=isopen.1h3v.s7.e3bd335b77a1 from=translated src=- shape=251dab5a vocab=73304047
-/
theorem isOpen_setOf_isLevelOneMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_setOf_isLevelZeroMatrix R K hN).inter
    ((isOpen_idealBall R K hN).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in

/--
@isnad1 id=isopen.1h3v.s9.99510fa6f535 from=translated src=- shape=5f42edb2 vocab=b9ec4bc7
-/
theorem isOpen_finiteLevelZero (hN : N ≠ ⊥) :
    IsOpen (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_coe_inv)

variable {N} in

/--
@isnad1 id=isopen.1h3v.s9.628845903a08 from=translated src=- shape=5f42edb2 vocab=0e98e955
-/
theorem isOpen_finiteLevelOne (hN : N ≠ ⊥) :
    IsOpen (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_coe_inv)

/--
@isnad1 id=isclosed.0h3v.s9.714c322c0127 from=translated src=- shape=0c2f4706 vocab=a4169954
-/
theorem isClosed_finiteLevelZero :
    IsClosed (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_coe_inv)

/--
@isnad1 id=isclosed.0h3v.s9.e6f18200ebf0 from=translated src=- shape=0c2f4706 vocab=a24e07d4
-/
theorem isClosed_finiteLevelOne :
    IsClosed (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_coe_inv)

section Compact

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/--
@isnad1 id=iscompac.0h2v.s9.466c0df7136e from=translated src=- shape=4bfdde61 vocab=a45a4fa0
-/
theorem isCompact_setOf_integral :
    IsCompact {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K} := by
  set C : Set (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
    {m | ∀ i j, m i j ∈ integralFiniteAdeles R K} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 =>
        Set.pi Set.univ fun _ : Fin 2 => integralFiniteAdeles R K := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles R K
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K}
      = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image, hC_def]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
    · rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
        MulOpposite.op_injective hm'
      rw [← this]; exact hm
  rw [heq]; exact hK

/--
@isnad1 id=iscompac.0h3v.s9.86aa6a1e583c from=translated src=- shape=49002023 vocab=e15c3958
-/
theorem isCompact_finiteLevelZero :
    IsCompact (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_setOf_integral R K).of_isClosed_subset (isClosed_finiteLevelZero R K N)
    fun _ hg => ⟨hg.1.integral, hg.2.integral⟩

/--
@isnad1 id=iscompac.0h3v.s9.748f0b24f1e6 from=translated src=- shape=49002023 vocab=eb3944a3
-/
theorem isCompact_finiteLevelOne :
    IsCompact (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_finiteLevelZero R K N).of_isClosed_subset (isClosed_finiteLevelOne R K N)
    (finiteLevelOne_le_finiteLevelZero R K N)

end Compact

end FiniteLevel

section Adelic

variable (N : Ideal R)

def levelZero : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelZero R K N).comap (glFin R K)

def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

/--
@isnad1 id=iff.0h4v.s11.c24896ab33be from=translated src=- shape=02790547 vocab=0d36d48d
-/
theorem mem_levelZero_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelZero R K N ↔ glFin R K g ∈ finiteLevelZero R K N := Iff.rfl

/--
@isnad1 id=iff.0h4v.s11.7b0ff03b6c7a from=translated src=- shape=02790547 vocab=08d2c591
-/
theorem mem_levelOne_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelOne R K N ↔ glFin R K g ∈ finiteLevelOne R K N := Iff.rfl

variable (R K N)

/--
@isnad1 id=le.0h3v.s9.6aa10364f0b0 from=translated src=- shape=edd0f222 vocab=716c798d
-/
theorem levelOne_le_levelZero : levelOne R K N ≤ levelZero R K N :=
  Subgroup.comap_mono (finiteLevelOne_le_finiteLevelZero R K N)

variable {N} in

/--
@isnad1 id=isopen.1h3v.s9.b3cdd66ae07e from=translated src=- shape=5f42edb2 vocab=f1567dc9
-/
theorem isOpen_levelZero (hN : N ≠ ⊥) : IsOpen (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelZero R K hN).preimage (continuous_glFin R K)

variable {N} in

/--
@isnad1 id=isopen.1h3v.s9.1dd216f7d163 from=translated src=- shape=5f42edb2 vocab=7f8a3ef5
-/
theorem isOpen_levelOne (hN : N ≠ ⊥) : IsOpen (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelOne R K hN).preimage (continuous_glFin R K)

/--
@isnad1 id=isclosed.0h3v.s9.a386a13726df from=translated src=- shape=0c2f4706 vocab=973719f7
-/
theorem isClosed_levelZero : IsClosed (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelZero R K N).preimage (continuous_glFin R K)

/--
@isnad1 id=isclosed.0h3v.s9.fd7c8f755fe8 from=translated src=- shape=0c2f4706 vocab=73138a72
-/
theorem isClosed_levelOne : IsClosed (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelOne R K N).preimage (continuous_glFin R K)

end Adelic

section Gen

def diagOne {A : Type*} [CommRing A] : Aˣ →* GL (Fin 2) A where
  toFun a :=
    { val := Matrix.diagonal ![(a : A), 1]
      inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h4v.s8.21ce10586ad2 from=translated src=- shape=527edda9 vocab=e23e5e63
-/
theorem diagOne_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    (diagOne a : Matrix (Fin 2) (Fin 2) A) i j = Matrix.diagonal ![(a : A), 1] i j := rfl

def finIncl : FiniteAdeleRing R K →* AdeleRing R K where
  toFun x := ((1 : InfiniteAdeleRing K), x)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (one_mul _).symm rfl

/--
@isnad1 id=eq.0h3v.s8.e4400008ac49 from=translated src=- shape=4d05daa2 vocab=a63a872d
-/
theorem finIncl_apply_fst (x : FiniteAdeleRing R K) : (finIncl R K x).1 = 1 := rfl
/--
@isnad1 id=eq.0h3v.s8.612829a7c271 from=translated src=- shape=af88b6ea vocab=62f38e15
-/
theorem finIncl_apply_snd (x : FiniteAdeleRing R K) : (finIncl R K x).2 = x := rfl

variable (v : HeightOneSpectrum R)

open scoped Classical in

def localUnit : (v.adicCompletion K)ˣ →* (FiniteAdeleRing R K)ˣ where
  toFun t :=
    { val := ⟨Function.update 1 v (t : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      inv := ⟨Function.update 1 v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      val_inv := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      inv_val := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw] }
  map_one' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v 1 w = 1
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  map_mul' t t' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
        ((t * t' : (v.adicCompletion K)ˣ) : v.adicCompletion K) w =
      Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t : v.adicCompletion K) w *
        Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t' : v.adicCompletion K) w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]

open scoped Classical in
/--
@isnad1 id=eq.0h4v.s10.7d2cb6f30732 from=translated src=- shape=c4dea8c0 vocab=9afaafe4
-/
theorem localUnit_apply_self (t : (v.adicCompletion K)ˣ) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) v = t
  simp

open scoped Classical in
/--
@isnad1 id=eq.1h5v.s10.25ecc75efb5e from=translated src=- shape=a9fcc6c3 vocab=9afaafe4
-/
theorem localUnit_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R} (hw : w ≠ v) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1 := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) w = 1
  simp [Function.update_of_ne hw]

def heckeGenAt : (v.adicCompletion K)ˣ →* GL (Fin 2) (AdeleRing R K) :=
  diagOne.comp ((Units.map (finIncl R K)).comp (localUnit R K v))

variable {R K v}

/--
@isnad1 id=eq.0h6v.s10.4b5a8c7ee9c3 from=translated src=- shape=908aa912 vocab=3ee230fc
-/
theorem heckeGenAt_fst (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.1h7v.s10.6dd4281d445b from=translated src=- shape=d91c85eb vocab=5bc585fd
-/
theorem heckeGenAt_snd_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R}
    (hw : w ≠ v) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 w
      = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1
    exact localUnit_apply_of_ne R K v t hw
  · rfl
  · rfl
  · rfl

/--
@isnad1 id=eq.0h6v.s10.2781241fbce7 from=translated src=- shape=a2b2b17b vocab=cb14b377
-/
theorem heckeGenAt_snd_apply_self (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 v
      = Matrix.diagonal ![(t : v.adicCompletion K), 1] i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t
    exact localUnit_apply_self R K v t
  · rfl
  · rfl
  · rfl

/--
@isnad1 id=mem.1h6v.s11.1cae470cb92b from=translated src=- shape=d11aea92 vocab=e3fb7fe4
-/
theorem heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (t t' : (v.adicCompletion K)ˣ)
    (h : Valued.v (t : v.adicCompletion K) = Valued.v (t' : v.adicCompletion K)) (N : Ideal R) :
    (heckeGenAt R K v t)⁻¹ * heckeGenAt R K v t' ∈ levelOne R K N := by
  rw [← map_inv, ← map_mul]
  set u : (v.adicCompletion K)ˣ := t⁻¹ * t' with hu
  have ht0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hu1 : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h, ← h,
      inv_mul_cancel₀ ht0]
  have hui : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]

  have hint : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      ((localUnit R K v s : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
        ∈ integralFiniteAdeles R K := by
    intro s hs w
    classical
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
    · rw [localUnit_apply_of_ne R K v s hw]; exact one_mem _
  have key : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      IsLevelOneMatrix R K N (glFin R K (heckeGenAt R K v s) : Matrix _ _ _) := by
    intro s hs
    refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact hint s hs
      · exact zero_mem_integralFiniteAdeles
      · exact zero_mem_integralFiniteAdeles
      · exact one_mem_integralFiniteAdeles
    · exact zero_mem_idealBall N
    · show (1 : FiniteAdeleRing R K) - 1 ∈ idealBall R K N
      rw [sub_self]; exact zero_mem_idealBall N
  refine ⟨key u hu1, ?_⟩
  rw [← map_inv, ← map_inv]
  exact key u⁻¹ hui

variable (K v)

def uniformizer : R := Classical.choose v.intValuation_exists_uniformizer

/--
@isnad1 id=eq.0h2v.s6.e559a72127fd from=translated src=- shape=a16d9664 vocab=c5e0bdbb
-/
theorem intValuation_uniformizer : v.intValuation (uniformizer v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

/--
@isnad1 id=eq.0h3v.s9.b949e61c04b2 from=translated src=- shape=fea40a43 vocab=22d66cf6
-/
theorem valued_uniformizer :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v)))
      = WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap, intValuation_uniformizer]

def uniformizerUnit : (v.adicCompletion K)ˣ :=
  Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v))) fun h => by
    have := valued_uniformizer K v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm

/--
@isnad1 id=eq.0h3v.s8.8eb0e57e2d29 from=translated src=- shape=2f43c1bb vocab=de22c63f
-/
theorem valued_uniformizerUnit :
    Valued.v (uniformizerUnit K v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizer K v

variable (R)

def heckeGen : GL (Fin 2) (AdeleRing R K) := heckeGenAt R K v (uniformizerUnit K v)

variable {R K v}

/--
@isnad1 id=mem.1h5v.s11.4077144faa16 from=translated src=- shape=177347bd vocab=3d6b05e0
-/
theorem heckeGen_inv_mul_heckeGenAt_mem_levelOne (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (N : Ideal R) :
    (heckeGen R K v)⁻¹ * heckeGenAt R K v t ∈ levelOne R K N :=
  heckeGenAt_inv_mul_heckeGenAt_mem_levelOne _ _ ((valued_uniformizerUnit K v).trans ht.symm) N

end Gen

end NumberField.AdelicLevel

end
