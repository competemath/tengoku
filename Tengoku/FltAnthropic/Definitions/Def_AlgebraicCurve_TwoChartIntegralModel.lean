import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Proper
import Tengoku.Seed.AlgebraicGeometry.Limits
import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.RingTheory.Polynomial.ScaleRoots
import Tengoku.Seed.Algebra.Polynomial.Lifts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {F} in
/--
@isnad1 id=ne.0h2v.s5.39fb409806e2 from=translated src=- shape=f84d8dcd vocab=b1479eb2
-/
theorem j_ne_zero : j ≠ 0 := Fact.out

def chartAlg (S : Set F) : Subalgebra R F where
  carrier := {x | IsIntegral (Algebra.adjoin R S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin R S)
        (algebraMap (Algebra.adjoin R S) F (algebraMap R (Algebra.adjoin R S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

/--
@isnad1 id=iff.0h4v.s7.6ee3dd4b8b95 from=translated src=- shape=bf1a5be7 vocab=6afca7be
-/
theorem mem_chartAlg_iff {S : Set F} {x : F} :
    x ∈ chartAlg R F S ↔ IsIntegral (Algebra.adjoin R S) x := Iff.rfl

/--
@isnad1 id=le.0h3v.s6.cf5a89ec5ec8 from=translated src=- shape=1970fdbe vocab=43f52b0d
-/
theorem adjoin_le_chartAlg (S : Set F) : Algebra.adjoin R S ≤ chartAlg R F S := fun x hx => by
  rw [mem_chartAlg_iff]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin R S))

/--
@isnad1 id=le.0h3v.s6.0ce03bdda221 from=translated src=- shape=92097d4b vocab=017d163b
-/
theorem subset_chartAlg (S : Set F) : S ⊆ (chartAlg R F S : Set F) := fun _ hx =>
  adjoin_le_chartAlg R F S (Algebra.subset_adjoin hx)

/--
@isnad1 id=le.1h4v.s6.a5e5ff9071f6 from=translated src=- shape=72003919 vocab=a54b64b9
-/
theorem chartAlg_mono {S S' : Set F} (h : S ⊆ S') : chartAlg R F S ≤ chartAlg R F S' := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq
    (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom (RingHom.id F) (by ext; rfl)

abbrev chartIncl {S S' : Set F} (h : S ⊆ S') : chartAlg R F S →ₐ[R] chartAlg R F S' :=
  Subalgebra.inclusion (chartAlg_mono R F h)

/--
@isnad1 id=eq.1h5v.s9.79bc62fb555f from=translated src=- shape=57dfc4c7 vocab=d2eb83c6
-/
theorem coe_chartIncl {S S' : Set F} (h : S ⊆ S') (x : chartAlg R F S) :
    (chartIncl R F h x : F) = x :=
  Subalgebra.coe_inclusion _ x

/--
@isnad1 id=injectiv.1h4v.s9.6fcb257b64ad from=translated src=- shape=e205e75a vocab=af6e8c4e
-/
theorem chartIncl_injective {S S' : Set F} (h : S ⊆ S') :
    Function.Injective (chartIncl R F h) :=
  Subalgebra.inclusion_injective _

variable {R F j}

/--
@isnad1 id=ex.3h5v.s7.0c8d8b020afc from=translated src=- shape=76783abe vocab=6ba0b2c9
-/
theorem exists_pow_mul_mem_adjoin {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ Algebra.adjoin R (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin R S := by
  have hsA : s ∈ Algebra.adjoin R S := Algebra.subset_adjoin hs
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
@isnad1 id=ex.3h5v.s7.1be11e01c537 from=translated src=- shape=76783abe vocab=c51874e8
-/
theorem exists_pow_mul_mem_chartAlg {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ chartAlg R F (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartAlg R F S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff R F).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : F) ∈ Algebra.adjoin R S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set M : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hnM : ∀ i ≤ p.natDegree, n i ≤ M := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : F[X] := (p.map (algebraMap (Algebra.adjoin R (insert s⁻¹ S)) F)).scaleRoots (s ^ M)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ M * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin R S := by
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
        show (p.coeff i : F) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : F)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin R S) F) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, (mem_chartAlg_iff R F).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

variable (R F j)

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=le.0h2v.s5.1f4f6b21cf86 from=translated src=- shape=538975ee vocab=b8e1f400
-/
theorem sFin_subset : ({j} : Set F) ⊆ {j, j⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=le.0h2v.s6.3b37f1ccecea from=translated src=- shape=3ce8a69e vocab=b8e1f400
-/
theorem sInf_subset : ({j⁻¹} : Set F) ⊆ {j, j⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)

abbrev chartAlgFin : Subalgebra R F := chartAlg R F {j}

abbrev chartAlgInf : Subalgebra R F := chartAlg R F {j⁻¹}

abbrev chartAlgMid : Subalgebra R F := chartAlg R F {j, j⁻¹}

def jChartFin : chartAlgFin R F j := ⟨j, subset_chartAlg R F _ rfl⟩

def jInvChartInf : chartAlgInf R F j := ⟨j⁻¹, subset_chartAlg R F _ rfl⟩

omit [Fact (j ≠ 0)] in
/--
@isnad1 id=eq.0h3v.s6.7f62e00d1a47 from=translated src=- shape=9372c739 vocab=96dd8cac
-/
@[simp] theorem coe_jChartFin : (jChartFin R F j : F) = j := rfl
omit [Fact (j ≠ 0)] in
/--
@isnad1 id=eq.0h3v.s6.fd9886709217 from=translated src=- shape=268bfcfa vocab=3ac17723
-/
@[simp] theorem coe_jInvChartInf : (jInvChartInf R F j : F) = j⁻¹ := rfl

abbrev inclFin : chartAlgFin R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sFin_subset F j)

abbrev inclInf : chartAlgInf R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sInf_subset F j)

/--
@isnad1 id=isunit.0h3v.s9.2c9f51aff0aa from=translated src=- shape=96ab91a4 vocab=5bdb7acf
-/
theorem isUnit_inclFin_jChartFin : IsUnit (inclFin R F j (jChartFin R F j)) := by
  refine .of_mul_eq_one ⟨j⁻¹, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jChartFin]
  exact mul_inv_cancel₀ (j_ne_zero j)

/--
@isnad1 id=isunit.0h3v.s9.64e5dcef2e52 from=translated src=- shape=96ab91a4 vocab=b5e33aa4
-/
theorem isUnit_inclInf_jInvChartInf : IsUnit (inclInf R F j (jInvChartInf R F j)) := by
  refine .of_mul_eq_one ⟨j, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jInvChartInf]
  exact inv_mul_cancel₀ (j_ne_zero j)

/--
@isnad1 id=away.0h3v.s9.41c2faef07b2 from=translated src=- shape=c9c24b30 vocab=970ea342
-/
theorem isLocalization_away_inclFin :
    letI := (inclFin R F j).toRingHom.toAlgebra
    IsLocalization.Away (jChartFin R F j) (chartAlgMid R F j) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclFin_jChartFin R F j).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg R F (insert j⁻¹ {j}) := by
      rw [show insert j⁻¹ ({j} : Set F) = {j, j⁻¹}
        from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _) (j_ne_zero j) hz
    refine ⟨(⟨j ^ n * z, hn⟩, ⟨jChartFin R F j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jChartFin]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective R F _ h]

/--
@isnad1 id=away.0h3v.s9.ff0ed16f1b51 from=translated src=- shape=c9c24b30 vocab=7a9344d3
-/
theorem isLocalization_away_inclInf :
    letI := (inclInf R F j).toRingHom.toAlgebra
    IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_jInvChartInf R F j).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
      rw [inv_inv]; exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _)
      (inv_ne_zero (j_ne_zero j)) hz
    refine ⟨(⟨j⁻¹ ^ n * z, hn⟩, ⟨jInvChartInf R F j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jInvChartInf]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective R F _ h]

abbrev XFin : Scheme.{u} := Spec (CommRingCat.of (chartAlgFin R F j))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartAlgInf R F j))

abbrev XMid : Scheme.{u} := Spec (CommRingCat.of (chartAlgMid R F j))

abbrev fFin : XMid R F j ⟶ XFin R F j := Spec.map (CommRingCat.ofHom (inclFin R F j).toRingHom)

abbrev fInf : XMid R F j ⟶ XInf R F j := Spec.map (CommRingCat.ofHom (inclInf R F j).toRingHom)

/--
@isnad1 id=isopenim.0h3v.s6.1eeb0c0651a0 from=translated src=- shape=80f8fe29 vocab=de1f59e5
-/
instance isOpenImmersion_fFin : IsOpenImmersion (fFin R F j) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact IsOpenImmersion.of_isLocalization (jChartFin R F j)

/--
@isnad1 id=isopenim.0h3v.s6.4dcac35569d7 from=translated src=- shape=80f8fe29 vocab=28b60577
-/
instance isOpenImmersion_fInf : IsOpenImmersion (fInf R F j) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf R F j)

def _root_.AlgebraicCurve.TwoChartIntegralModel : Scheme.{u} := pushout (fFin R F j) (fInf R F j)

def ιFin : XFin R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j := pushout.inl (fFin R F j) (fInf R F j)

def ιInf : XInf R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j := pushout.inr (fFin R F j) (fInf R F j)

/--
@isnad1 id=eq.0h3v.s7.d313def0db58 from=translated src=- shape=b5d82d01 vocab=062a0071
-/
theorem glue_condition : fFin R F j ≫ ιFin R F j = fInf R F j ≫ ιInf R F j := pushout.condition

/--
@isnad1 id=isopenim.0h3v.s6.4c347dde03df from=translated src=- shape=80f8fe29 vocab=f48c30e5
-/
instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.left

/--
@isnad1 id=isopenim.0h3v.s6.390e49dd9c18 from=translated src=- shape=80f8fe29 vocab=77035c76
-/
instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.right

/--
@isnad1 id=eq.0h3v.s9.2c91d33c81f8 from=translated src=- shape=5c187e16 vocab=18819d13
-/
theorem fFin_toBase_eq_fInf_toBase :
    fFin R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) =
      fInf R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) := by
  have h : (inclFin R F j).toRingHom.comp (algebraMap R (chartAlgFin R F j)) =
      (inclInf R F j).toRingHom.comp (algebraMap R (chartAlgInf R F j)) :=
    RingHom.ext fun a => ((inclFin R F j).commutes a).trans ((inclInf R F j).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def toBase : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))))
    (fFin_toBase_eq_fInf_toBase R F j)

/--
@isnad1 id=eq.0h3v.s8.043f303ce9f9 from=translated src=- shape=4005474d vocab=69755568
-/
@[reassoc (attr := simp)]
theorem ιFin_toBase : ιFin R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) :=
  pushout.inl_desc _ _ _

/--
@isnad1 id=eq.0h3v.s8.ea7ba314dc21 from=translated src=- shape=4005474d vocab=e5f7846d
-/
@[reassoc (attr := simp)]
theorem ιInf_toBase : ιInf R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) :=
  pushout.inr_desc _ _ _

/--
@isnad1 id=or.0h4v.s9.40e84b41a596 from=translated src=- shape=533acfd6 vocab=e10da442
-/
theorem mem_range_ιFin_or_mem_range_ιInf (x : AlgebraicCurve.TwoChartIntegralModel R F j) :
    x ∈ Set.range (ιFin R F j).base ∨ x ∈ Set.range (ιInf R F j).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).f none =
        fFin R F j ≫ ιFin R F j :=
      (colimit.w (span (fFin R F j) (fInf R F j)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(fFin R F j).base y, ?_⟩
    rw [← hy, hw]; rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

def chartFinOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens := (ιFin R F j).opensRange

def chartInfOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens := (ιInf R F j).opensRange

/--
@isnad1 id=isaffine.0h3v.s6.cc65ef115b96 from=translated src=- shape=d2521cb7 vocab=8db4a364
-/
theorem isAffineOpen_chartFinOpen : IsAffineOpen (chartFinOpen R F j) :=
  isAffineOpen_opensRange (ιFin R F j)

/--
@isnad1 id=isaffine.0h3v.s6.6f53854e29d8 from=translated src=- shape=d2521cb7 vocab=89ee0d0e
-/
theorem isAffineOpen_chartInfOpen : IsAffineOpen (chartInfOpen R F j) :=
  isAffineOpen_opensRange (ιInf R F j)

/--
@isnad1 id=eq.0h3v.s8.003f95999e0f from=translated src=- shape=14409502 vocab=5b162668
-/
theorem twoChartCover : chartFinOpen R F j ⊔ chartInfOpen R F j = ⊤ := by
  rw [chartFinOpen, chartInfOpen, ← TopologicalSpace.Opens.coe_inj]
  ext x
  simpa using mem_range_ιFin_or_mem_range_ιInf R F j x

def polynomialToChartFin : Polynomial R →ₐ[R] chartAlgFin R F j := Polynomial.aeval (jChartFin R F j)

def polynomialToChartInf : Polynomial R →ₐ[R] chartAlgInf R F j := Polynomial.aeval (jInvChartInf R F j)

/--
@isnad1 id=eq.0h3v.s8.6eca88c31933 from=translated src=- shape=8a01f642 vocab=aee1806f
-/
@[simp] theorem polynomialToChartFin_X : polynomialToChartFin R F j Polynomial.X = jChartFin R F j :=
  Polynomial.aeval_X _

/--
@isnad1 id=eq.0h3v.s8.1aa7ab24d87f from=translated src=- shape=8a01f642 vocab=00768c4f
-/
@[simp] theorem polynomialToChartInf_X : polynomialToChartInf R F j Polynomial.X = jInvChartInf R F j :=
  Polynomial.aeval_X _

def baseChange (S : Type u) [CommRing S] [Algebra R S] : Scheme.{u} :=
  pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))

def baseChangeι (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ AlgebraicCurve.TwoChartIntegralModel R F j := pullback.fst _ _

def baseChangeToBase (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

abbrev fibre (I : Ideal R) : Scheme.{u} := baseChange R F j (R ⧸ I)

abbrev fibreι (I : Ideal R) : fibre R F j I ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  baseChangeι R F j (R ⧸ I)

abbrev fibreToBase (I : Ideal R) : fibre R F j I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  baseChangeToBase R F j (R ⧸ I)

section BaseChange

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]

/--
@isnad1 id=le.0h4v.s7.178bb7f8fe51 from=translated src=- shape=30a7d67c vocab=9d89a2dc
-/
theorem adjoin_le_adjoin_restrictScalars (S : Set F) :
    Algebra.adjoin R S ≤ (Algebra.adjoin R' S).restrictScalars R :=
  Algebra.adjoin_le Algebra.subset_adjoin

/--
@isnad1 id=le.0h4v.s7.64ca18371abf from=translated src=- shape=66cadbde vocab=b33beb5f
-/
theorem chartAlg_le_chartAlg (S : Set F) :
    (chartAlg R F S).toSubring ≤ (chartAlg R' F S).toSubring := by
  intro x hx
  change IsIntegral (Algebra.adjoin R' S) x
  have hx' : IsIntegral (Algebra.adjoin R S) x := hx
  have hle : (Algebra.adjoin R S).toSubring ≤ ((Algebra.adjoin R' S).restrictScalars R).toSubring :=
    fun y hy => adjoin_le_adjoin_restrictScalars R F R' S hy
  exact hx'.map_of_comp_eq (Subring.inclusion hle) (RingHom.id F) (by ext; rfl)

/--
@isnad1 id=le.0h4v.s7.498b33fc8e97 from=translated src=- shape=30a7d67c vocab=b3b5371c
-/
theorem chartAlg_le_restrictScalars (S : Set F) :
    chartAlg R F S ≤ (chartAlg R' F S).restrictScalars R :=
  fun _ hx => chartAlg_le_chartAlg R F R' S hx

def chartBaseChange (S : Set F) : chartAlg R F S →+* chartAlg R' F S :=
  (Subalgebra.inclusion (chartAlg_le_restrictScalars R F R' S)).toRingHom

/--
@isnad1 id=eq.0h5v.s10.90a5f7853cce from=translated src=- shape=fe5af3e0 vocab=d4f12037
-/
@[simp] theorem coe_chartBaseChange (S : Set F) (x : chartAlg R F S) :
    (chartBaseChange R F R' S x : F) = x :=
  Subalgebra.coe_inclusion _ x

/--
@isnad1 id=eq.0h5v.s10.15511370d43e from=translated src=- shape=7e1cbef7 vocab=9af6f334
-/
theorem chartBaseChange_algebraMap (S : Set F) (r : R) :
    chartBaseChange R F R' S (algebraMap R (chartAlg R F S) r) =
      algebraMap R' (chartAlg R' F S) (algebraMap R R' r) :=
  Subtype.ext (IsScalarTower.algebraMap_apply R R' F r)

end BaseChange

end TwoChartIntegralModel

end AlgebraicCurve

end
