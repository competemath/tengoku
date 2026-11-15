import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace ModularCurve

namespace TwoChart

variable (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K]

def chartAlg (S : Set K) : Subalgebra A K where
  carrier := {x | IsIntegral (Algebra.adjoin A S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin A S)
        (algebraMap (Algebra.adjoin A S) K (algebraMap A (Algebra.adjoin A S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

/--
@isnad1 id=iff.0h4v.s7.d7aa86a65e84 from=translated src=- shape=bf1a5be7 vocab=431b3fe1
-/
theorem mem_chartAlg_iff {S : Set K} {x : K} :
    x ∈ chartAlg A K S ↔ IsIntegral (Algebra.adjoin A S) x := Iff.rfl

/--
@isnad1 id=le.0h3v.s6.6009ba00b01f from=translated src=- shape=1970fdbe vocab=5c175f4b
-/
theorem adjoin_le_chartAlg (S : Set K) : Algebra.adjoin A S ≤ chartAlg A K S := fun x hx => by
  rw [mem_chartAlg_iff]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin A S))

/--
@isnad1 id=le.0h3v.s6.4846b9715609 from=translated src=- shape=92097d4b vocab=2c6f0036
-/
theorem subset_chartAlg (S : Set K) : S ⊆ (chartAlg A K S : Set K) := fun _ hx =>
  adjoin_le_chartAlg A K S (Algebra.subset_adjoin hx)

/--
@isnad1 id=le.1h4v.s6.243499b5b2dc from=translated src=- shape=72003919 vocab=6d7b8042
-/
theorem chartAlg_mono {S S' : Set K} (h : S ⊆ S') : chartAlg A K S ≤ chartAlg A K S' := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq
    (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom (RingHom.id K) (by ext; rfl)

abbrev chartIncl {S S' : Set K} (h : S ⊆ S') : chartAlg A K S →ₐ[A] chartAlg A K S' :=
  Subalgebra.inclusion (chartAlg_mono A K h)

/--
@isnad1 id=eq.1h5v.s9.0fcc1bb4b0b2 from=translated src=- shape=57dfc4c7 vocab=4a304311
-/
theorem coe_chartIncl {S S' : Set K} (h : S ⊆ S') (x : chartAlg A K S) :
    (chartIncl A K h x : K) = x :=
  Subalgebra.coe_inclusion _ x

/--
@isnad1 id=injectiv.1h4v.s9.28683c2b9ed7 from=translated src=- shape=e205e75a vocab=1dd2cb6b
-/
theorem chartIncl_injective {S S' : Set K} (h : S ⊆ S') :
    Function.Injective (chartIncl A K h) :=
  Subalgebra.inclusion_injective _

variable {A K}

/--
@isnad1 id=ex.3h5v.s7.0c8d8b020afc from=translated src=- shape=76783abe vocab=6ba0b2c9
-/
theorem exists_pow_mul_mem_adjoin {S : Set K} {s : K} (hs : s ∈ S) (hs0 : s ≠ 0) {x : K}
    (hx : x ∈ Algebra.adjoin A (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin A S := by
  have hsA : s ∈ Algebra.adjoin A S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn

/--
@isnad1 id=ex.3h5v.s7.7e9a7b6cc606 from=translated src=- shape=76783abe vocab=438cc1b9
-/
theorem exists_pow_mul_mem_chartAlg {S : Set K} {s : K} (hs : s ∈ S) (hs0 : s ≠ 0) {x : K}
    (hx : x ∈ chartAlg A K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartAlg A K S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff A K).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : K) ∈ Algebra.adjoin A S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set M : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hnM : ∀ i ≤ p.natDegree, n i ≤ M := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : K[X] := (p.map (algebraMap (Algebra.adjoin A (insert s⁻¹ S)) K)).scaleRoots (s ^ M)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ M * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin A S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ M * (p.natDegree - i) := by
        calc n i ≤ M := hnM i hi.le
          _ = M * 1 := (mul_one M).symm
          _ ≤ M * (p.natDegree - i) := Nat.mul_le_mul_left M (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ M) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : K) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : K)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin A S) K) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, (mem_chartAlg_iff A K).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

variable (A K)

variable (j : K) [Fact (j ≠ 0)]

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=le.0h2v.s5.1f4f6b21cf86 from=translated src=- shape=538975ee vocab=b8e1f400
-/
theorem sFin_subset : ({j} : Set K) ⊆ {j, (j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=le.0h2v.s6.3b37f1ccecea from=translated src=- shape=3ce8a69e vocab=b8e1f400
-/
theorem sInf_subset : ({(j)⁻¹} : Set K) ⊆ {j, (j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)

abbrev chartAlgFin : Subalgebra A K := chartAlg A K {j}

abbrev chartAlgInf : Subalgebra A K := chartAlg A K {(j)⁻¹}

abbrev chartAlgMid : Subalgebra A K := chartAlg A K {j, (j)⁻¹}

def jChartFin : chartAlgFin A K j := ⟨j, subset_chartAlg A K _ rfl⟩

def jInvChartInf : chartAlgInf A K j := ⟨(j)⁻¹, subset_chartAlg A K _ rfl⟩

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=eq.0h3v.s6.12e4fb1f6dc3 from=translated src=- shape=9372c739 vocab=a8866b46
-/
@[simp] theorem coe_jChartFin : (jChartFin A K j : K) = j := rfl
omit [Fact (j ≠ 0)] in
/--
@isnad1 id=eq.0h3v.s6.c2bc62ff2a2b from=translated src=- shape=268bfcfa vocab=f5494d0c
-/
@[simp] theorem coe_jInvChartInf : (jInvChartInf A K j : K) = (j)⁻¹ := rfl

abbrev inclFin : chartAlgFin A K j →ₐ[A] chartAlgMid A K j := chartIncl A K (sFin_subset K j)

abbrev inclInf : chartAlgInf A K j →ₐ[A] chartAlgMid A K j := chartIncl A K (sInf_subset K j)

/--
@isnad1 id=isunit.0h3v.s9.e25445392140 from=translated src=- shape=96ab91a4 vocab=052e2d4a
-/
theorem isUnit_inclFin_jChartFin : IsUnit (inclFin A K j (jChartFin A K j)) := by
  refine .of_mul_eq_one ⟨(j)⁻¹, subset_chartAlg A K _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jChartFin]
  exact mul_inv_cancel₀ ((Fact.out : j ≠ 0))

/--
@isnad1 id=isunit.0h3v.s9.233dfc3ad6ac from=translated src=- shape=96ab91a4 vocab=0a3e39bb
-/
theorem isUnit_inclInf_jInvChartInf : IsUnit (inclInf A K j (jInvChartInf A K j)) := by
  refine .of_mul_eq_one ⟨j, subset_chartAlg A K _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jInvChartInf]
  exact inv_mul_cancel₀ ((Fact.out : j ≠ 0))

/--
@isnad1 id=away.0h3v.s9.c0e5589aeb04 from=translated src=- shape=c9c24b30 vocab=a85b9eee
-/
theorem isLocalization_away_inclFin :
    letI := (inclFin A K j).toRingHom.toAlgebra
    IsLocalization.Away (jChartFin A K j) (chartAlgMid A K j) := by
  letI := (inclFin A K j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclFin_jChartFin A K j).pow n
  · intro z
    have hz : (z : K) ∈ chartAlg A K (insert (j)⁻¹ {j}) := by
      rw [show insert (j)⁻¹ ({j} : Set K) = {j, (j)⁻¹}
        from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _) ((Fact.out : j ≠ 0)) hz
    refine ⟨(⟨(j) ^ n * z, hn⟩, ⟨jChartFin A K j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jChartFin]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective A K _ h]

/--
@isnad1 id=away.0h3v.s9.f4826b166029 from=translated src=- shape=c9c24b30 vocab=839e4653
-/
theorem isLocalization_away_inclInf :
    letI := (inclInf A K j).toRingHom.toAlgebra
    IsLocalization.Away (jInvChartInf A K j) (chartAlgMid A K j) := by
  letI := (inclInf A K j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_jInvChartInf A K j).pow n
  · intro z
    have hz : (z : K) ∈ chartAlg A K (insert (j)⁻¹⁻¹ {(j)⁻¹}) := by
      rw [inv_inv]; exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _)
      (inv_ne_zero ((Fact.out : j ≠ 0))) hz
    refine ⟨(⟨(j)⁻¹ ^ n * z, hn⟩, ⟨jInvChartInf A K j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jInvChartInf]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective A K _ h]

abbrev XFin : Scheme.{u} := Spec (CommRingCat.of (chartAlgFin A K j))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartAlgInf A K j))

abbrev XMid : Scheme.{u} := Spec (CommRingCat.of (chartAlgMid A K j))

abbrev fFin : XMid A K j ⟶ XFin A K j := Spec.map (CommRingCat.ofHom (inclFin A K j).toRingHom)

abbrev fInf : XMid A K j ⟶ XInf A K j := Spec.map (CommRingCat.ofHom (inclInf A K j).toRingHom)

/--
@isnad1 id=isopenim.0h3v.s6.2067ce2287a0 from=translated src=- shape=80f8fe29 vocab=e44aa068
-/
instance isOpenImmersion_fFin : IsOpenImmersion (fFin A K j) := by
  letI := (inclFin A K j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin A K j
  exact IsOpenImmersion.of_isLocalization (jChartFin A K j)

/--
@isnad1 id=isopenim.0h3v.s6.ab7eb8c5e077 from=translated src=- shape=80f8fe29 vocab=9a82e46e
-/
instance isOpenImmersion_fInf : IsOpenImmersion (fInf A K j) := by
  letI := (inclInf A K j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf A K j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf A K j)

def _root_.ModularCurve.TwoChartModel : Scheme.{u} := pushout (fFin A K j) (fInf A K j)

def ιFin : XFin A K j ⟶ TwoChartModel A K j := pushout.inl (fFin A K j) (fInf A K j)

def ιInf : XInf A K j ⟶ TwoChartModel A K j := pushout.inr (fFin A K j) (fInf A K j)

/--
@isnad1 id=eq.0h3v.s7.893f0227af01 from=translated src=- shape=b5d82d01 vocab=b067ee30
-/
theorem glue_condition : fFin A K j ≫ ιFin A K j = fInf A K j ≫ ιInf A K j := pushout.condition

/--
@isnad1 id=isopenim.0h3v.s6.2de19bacf2ab from=translated src=- shape=80f8fe29 vocab=9d995233
-/
instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin A K j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).map_prop WalkingSpan.left

/--
@isnad1 id=isopenim.0h3v.s6.a33b16895a60 from=translated src=- shape=80f8fe29 vocab=f39fc71b
-/
instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf A K j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).map_prop WalkingSpan.right

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=eq.0h3v.s9.07ecda9b61f9 from=translated src=- shape=e0e62640 vocab=59832541
-/
theorem fFin_toBase_eq_fInf_toBase :
    fFin A K j ≫ Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgFin A K j))) =
      fInf A K j ≫ Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgInf A K j))) := by
  have h : (inclFin A K j).toRingHom.comp (algebraMap A (chartAlgFin A K j)) =
      (inclInf A K j).toRingHom.comp (algebraMap A (chartAlgInf A K j)) :=
    RingHom.ext fun a => ((inclFin A K j).commutes a).trans ((inclInf A K j).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def modelTo : TwoChartModel A K j ⟶ Spec (CommRingCat.of A) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgFin A K j))))
    (Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgInf A K j))))
    (fFin_toBase_eq_fInf_toBase A K j)

/--
@isnad1 id=eq.0h3v.s8.88315e9095e7 from=translated src=- shape=4005474d vocab=34964fc4
-/
@[reassoc (attr := simp)]
theorem ιFin_modelTo : ιFin A K j ≫ modelTo A K j =
    Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgFin A K j))) :=
  pushout.inl_desc _ _ _

/--
@isnad1 id=eq.0h3v.s8.3771bf58cd87 from=translated src=- shape=4005474d vocab=ccb9fac4
-/
@[reassoc (attr := simp)]
theorem ιInf_modelTo : ιInf A K j ≫ modelTo A K j =
    Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgInf A K j))) :=
  pushout.inr_desc _ _ _

/--
@isnad1 id=or.0h4v.s9.21d809d14b37 from=translated src=- shape=533acfd6 vocab=5a2cee58
-/
theorem mem_range_ιFin_or_mem_range_ιInf (x : TwoChartModel A K j) :
    x ∈ Set.range (ιFin A K j).base ∨ x ∈ Set.range (ιInf A K j).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).f none =
        fFin A K j ≫ ιFin A K j :=
      (colimit.w (span (fFin A K j) (fInf A K j)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(fFin A K j).base y, ?_⟩
    rw [← hy, hw]; rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

def chartFinOpen : (TwoChartModel A K j).Opens := (ιFin A K j).opensRange

def chartInfOpen : (TwoChartModel A K j).Opens := (ιInf A K j).opensRange

/--
@isnad1 id=isaffine.0h3v.s6.98aa6f03940d from=translated src=- shape=d2521cb7 vocab=ae74bb8f
-/
theorem isAffineOpen_chartFinOpen : IsAffineOpen (chartFinOpen A K j) :=
  isAffineOpen_opensRange (ιFin A K j)

/--
@isnad1 id=isaffine.0h3v.s6.aaa8d0c1f8fc from=translated src=- shape=d2521cb7 vocab=748e9c24
-/
theorem isAffineOpen_chartInfOpen : IsAffineOpen (chartInfOpen A K j) :=
  isAffineOpen_opensRange (ιInf A K j)

/--
@isnad1 id=eq.0h3v.s8.0b5c3d256246 from=translated src=- shape=14409502 vocab=3b5d7336
-/
theorem twoChartCover : chartFinOpen A K j ⊔ chartInfOpen A K j = ⊤ := by
  rw [chartFinOpen, chartInfOpen, ← TopologicalSpace.Opens.coe_inj]
  ext x
  simpa using mem_range_ιFin_or_mem_range_ιInf A K j x

end TwoChart

end ModularCurve

end
