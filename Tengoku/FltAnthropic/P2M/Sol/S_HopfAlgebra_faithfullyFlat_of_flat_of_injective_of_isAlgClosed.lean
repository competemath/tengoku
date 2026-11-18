import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq
import Tengoku.FltAnthropic.Theorems.Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_antipode_antipode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace TakE

variable {k : Type u} [Field k]

/--
@isnad1 id=isopen.0h3v.s7.69d1ee168e46 from=translated src=- shape=14a1c4b6 vocab=7484ea50
-/
theorem isOpen_range_comap (K : Type v) [CommRing K] [Algebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [Algebra k H] [Algebra.FiniteType k H] [Algebra K H] [IsScalarTower k K H]
    [Module.Flat K H] : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap K H))) := by
  haveI : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  haveI : Algebra.FiniteType K H := Algebra.FiniteType.of_restrictScalars_finiteType k K H
  haveI : Algebra.FinitePresentation K H := (Algebra.FinitePresentation.of_finiteType (R := K) (A := H)).mp inferInstance
  haveI : Algebra.HasGoingDown K H := Algebra.HasGoingDown.of_flat
  exact (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := K) (S := H)).isOpen_range

/--
@isnad1 id=eq.1h4v.s8.02b83d2dac77 from=translated src=- shape=c1f4112d vocab=3488dafe
-/
theorem algHom_eq_of_ker_eq {A : Type*} [CommRing A] [Algebra k A] (z z' : A →ₐ[k] k)
    (h : RingHom.ker z = RingHom.ker z') : z = z' := by
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap k A (z x) ∈ RingHom.ker z := by simp [RingHom.mem_ker]
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes] at hx
  exact (sub_eq_zero.mp hx).symm

/--
@isnad1 id=nonempty.0h2v.s6.0b5a1c3e3935 from=translated src=- shape=15c20087 vocab=249f3b0c
-/
theorem exists_algHom_of_finiteType [IsAlgClosed k] {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Nontrivial A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  haveI := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.FiniteType k (A ⧸ M) := inferInstance
  haveI : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
  haveI : Algebra.IsIntegral k (A ⧸ M) := Algebra.IsIntegral.of_finite k (A ⧸ M)
  have hbij : Function.Bijective (algebraMap k (A ⧸ M)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : (A ⧸ M) ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ M)) hbij).symm
  exact ⟨e.toAlgHom.comp (Ideal.Quotient.mkₐ k M)⟩

/--
@isnad1 id=iff.0h4v.s8.990076acaa17 from=translated src=- shape=296428e2 vocab=4acb92ab
-/
theorem mem_range_comap_iff_exists_lift [IsAlgClosed k] (K : Type v) [CommRing K] [Algebra k K]
    (H : Type w) [CommRing H] [Algebra k H] [Algebra.FiniteType k H] [Algebra K H] [IsScalarTower k K H]
    (z : K →ₐ[k] k) :
    (⟨RingHom.ker z.toRingHom, RingHom.ker_isPrime _⟩ : PrimeSpectrum K) ∈
        Set.range (PrimeSpectrum.comap (algebraMap K H)) ↔
      ∃ y : H →ₐ[k] k, y.comp (IsScalarTower.toAlgHom k K H) = z := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    haveI := hM
    haveI : Nontrivial (H ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM.ne_top
    obtain ⟨y₀⟩ := exists_algHom_of_finiteType (k := k) (A := H ⧸ M)
    refine ⟨y₀.comp (Ideal.Quotient.mkₐ k M), ?_⟩
    have hzmax : (RingHom.ker z.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective z.toRingHom (fun c => ⟨algebraMap k K c, by simp⟩)
    symm
    apply algHom_eq_of_ker_eq
    apply hzmax.eq_of_le (RingHom.ker_ne_top _)
    intro x hx
    have hPx : (algebraMap K H x) ∈ P.asIdeal := by
      have := congrArg (fun Q : PrimeSpectrum K => x ∈ Q.asIdeal) hP
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_iff_iff] at this
      exact this.mpr hx
    rw [RingHom.mem_ker]
    show y₀ (Ideal.Quotient.mk M (algebraMap K H x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hPM hPx), map_zero]
  · rintro ⟨y, rfl⟩
    refine ⟨⟨RingHom.ker y.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
    ext x
    simp [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]

/--
@isnad1 id=faithful.1h2v.s6.9a8a96cb0774 from=translated src=- shape=0b72218c vocab=6e9aea8f
-/
theorem faithfullyFlat_of_range_eq_univ (K : Type v) [CommRing K] (H : Type w) [CommRing H] [Algebra K H]
    [Module.Flat K H] (h : Set.range (PrimeSpectrum.comap (algebraMap K H)) = Set.univ) :
    Module.FaithfullyFlat K H :=
  Module.FaithfullyFlat.of_comap_surjective (Set.range_eq_univ.mp h)

end TakE

namespace TakE

variable {k : Type u} [Field k]

section Points
variable (K : Type v) [CommRing K] [HopfAlgebra k K]

noncomputable def antipodeAlgHom : K →ₐ[k] K :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k (A := K)) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

/--
@isnad1 id=eq.0h3v.s9.533ae48a6a58 from=translated src=- shape=31de17bd vocab=5e303242
-/
theorem antipodeAlgHom_apply (a : K) : antipodeAlgHom (k := k) K a = HopfAlgebra.antipode k a := rfl

noncomputable def transl (g : K →ₐ[k] k) : K →ₐ[k] K :=
  (Algebra.TensorProduct.lid k K).toAlgHom.comp
    ((Algebra.TensorProduct.map g (AlgHom.id k K)).comp (Bialgebra.comulAlgHom k K))

/--
@isnad1 id=eq.0h4v.s12.3d965807688e from=translated src=- shape=e7d5799e vocab=1581842b
-/
theorem transl_spec (g : K →ₐ[k] k) (h : K) :
    transl K g h = Algebra.TensorProduct.lid k K (Algebra.TensorProduct.map g (AlgHom.id k K) (Coalgebra.comul h)) :=
  rfl

variable {K}
variable {A : Type w} [CommRing A] [Algebra k A]

/--
@isnad1 id=eq.0h5v.s9.cacb19003e3a from=translated src=- shape=9cb3c68f vocab=2d60c8ea
-/
theorem comp_transl (g : K →ₐ[k] k) (x : K →ₐ[k] A) :
    x.comp (transl K g) = WithConv.ofConv (WithConv.toConv ((Algebra.ofId k A).comp g) * WithConv.toConv x) := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.comp_apply, transl_spec]
  induction (Coalgebra.comul (R := k) c) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lift_tmul,
        map_smul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]

/--
@isnad1 id=eq.0h4v.s9.33b0d56b1f4a from=translated src=- shape=e38eef1c vocab=3d30b8c2
-/
theorem comp_antipode_mul_self (x : K →ₐ[k] A) :
    WithConv.toConv (x.comp (antipodeAlgHom K)) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : K ⊗[k] K, Algebra.TensorProduct.lift (x.comp (antipodeAlgHom K)) x (fun _ _ => Commute.all _ _) t
      = x (LinearMap.mul' k K (LinearMap.rTensor K (HopfAlgebra.antipode k (A := K)) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, antipodeAlgHom_apply]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

/--
@isnad1 id=eq.0h4v.s9.1aa3793cd986 from=translated src=- shape=11a44ea8 vocab=3d30b8c2
-/
theorem mul_comp_antipode_self (x : K →ₐ[k] A) :
    WithConv.toConv x * WithConv.toConv (x.comp (antipodeAlgHom K)) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : K ⊗[k] K, Algebra.TensorProduct.lift x (x.comp (antipodeAlgHom K)) (fun _ _ => Commute.all _ _) t
      = x (LinearMap.mul' k K (LinearMap.lTensor K (HopfAlgebra.antipode k (A := K)) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, antipodeAlgHom_apply]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

def pt (z : K →ₐ[k] k) : PrimeSpectrum K := ⟨RingHom.ker z.toRingHom, RingHom.ker_isPrime _⟩

/--
@isnad1 id=eq.0h4v.s8.c1d7e109b1c5 from=translated src=- shape=5e9cb51f vocab=d009c9fa
-/
theorem comap_pt (β : K →ₐ[k] K) (z : K →ₐ[k] k) :
    PrimeSpectrum.comap β.toRingHom (pt z) = pt (z.comp β) := by
  ext x
  simp [pt, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]

end Points

/--
@isnad1 id=ex.1h3v.s7.4701ffe7d3b8 from=translated src=- shape=fad35926 vocab=d7b7cbc8
-/
theorem exists_pt_eq [IsAlgClosed k] (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (Q : PrimeSpectrum K) (hQ : Q.asIdeal.IsMaximal) : ∃ z : K →ₐ[k] k, pt z = Q := by
  haveI := hQ
  haveI : Nontrivial (K ⧸ Q.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  obtain ⟨y⟩ := exists_algHom_of_finiteType (k := k) (A := K ⧸ Q.asIdeal)
  refine ⟨y.comp (Ideal.Quotient.mkₐ k Q.asIdeal), ?_⟩
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Q.asIdeal
  symm
  apply hQ.eq_of_le (RingHom.ker_ne_top _)
  intro x hx
  rw [RingHom.mem_ker]
  show y (Ideal.Quotient.mk Q.asIdeal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/--
@isnad1 id=ex.2h2v.s6.8487e36c1f80 from=translated src=- shape=8216c730 vocab=9e3f2f98
-/
theorem exists_isMaximal_mem (K : Type v) [CommRing K] [IsJacobsonRing K] (W : Set (PrimeSpectrum K))
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ P ∈ W, P.asIdeal.IsMaximal := by
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := PrimeSpectrum K) hW.isLocallyClosed
  have hne' : (W ∩ closedPoints (PrimeSpectrum K)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, closure_empty] at h
    exact hne.ne_empty (Set.eq_empty_of_subset_empty (h ▸ subset_closure))
  obtain ⟨P, hPW, hPc⟩ := hne'
  exact ⟨P, hPW, (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp (mem_closedPoints_iff.mp hPc)⟩

/--
@isnad1 id=faithful.3h3v.s12.594e27669aa6 from=translated src=- shape=10a41b73 vocab=738d6164
-/
theorem main [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H := by
  classical

  let ι : K →ₐ[k] H := IsScalarTower.toAlgHom k K H
  let ιb : K →ₐc[k] H :=
    BialgHom.mk
      { toLinearMap := ι.toLinearMap
        counit_comp := by ext x; exact hcounit x
        map_comp_comul := by ext x; exact (hcomul x).symm }
      (map_one ι) (map_mul ι)
  have hιb : ((ιb : K →ₐc[k] H) : K →ₐ[k] H) = ι := rfl

  let Lifts : (K →ₐ[k] k) → Prop := fun z => ∃ y : H →ₐ[k] k, y.comp ι = z
  have lifts_mul : ∀ z z', Lifts z → Lifts z' →
      Lifts (WithConv.ofConv (WithConv.toConv z * WithConv.toConv z')) := by
    rintro z z' ⟨y, rfl⟩ ⟨y', rfl⟩
    refine ⟨WithConv.ofConv (WithConv.toConv y * WithConv.toConv y'), ?_⟩
    rw [← hιb]
    exact AlgHom.convMul_comp_bialgHom_distrib (WithConv.toConv y) (WithConv.toConv y') ιb

  let U : Set (PrimeSpectrum K) := Set.range (PrimeSpectrum.comap (algebraMap K H))
  have hUopen : IsOpen U := isOpen_range_comap (k := k) K H
  have hUdense : Dense U := by
    have : DenseRange (PrimeSpectrum.comap (algebraMap K H)) :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
        (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
    exact this
  have hU_iff : ∀ z : K →ₐ[k] k, pt z ∈ U ↔ Lifts z := fun z => mem_range_comap_iff_exists_lift K H z
  haveI : IsJacobsonRing K := isJacobsonRing_of_finiteType (A := k) (B := K)

  obtain ⟨hbij, -, -⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := K)
      (transl K) (fun g h => rfl)

  have key : ∀ z : K →ₐ[k] k, Lifts z := by
    intro z
    let β : K →ₐ[k] K := (antipodeAlgHom K).comp (transl K z)

    let V : Set (PrimeSpectrum K) := (PrimeSpectrum.comap β.toRingHom) ⁻¹' U
    have hVopen : IsOpen V := hUopen.preimage (PrimeSpectrum.continuous_comap β.toRingHom)
    have hβpt : ∀ x : K →ₐ[k] k, PrimeSpectrum.comap β.toRingHom (pt x) =
        pt (WithConv.ofConv (WithConv.toConv z * WithConv.toConv (x.comp (antipodeAlgHom K)))) := by
      intro x
      rw [comap_pt]
      congr 1
      show (x.comp (antipodeAlgHom K)).comp (transl K z) = _
      rw [comp_transl]
      congr 2
    have hzV : pt z ∈ V := by
      show PrimeSpectrum.comap β.toRingHom (pt z) ∈ U
      rw [hβpt, mul_comp_antipode_self, hU_iff]
      refine ⟨WithConv.ofConv 1, ?_⟩
      apply AlgHom.ext
      intro c
      rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
      exact congrArg _ (hcounit c)

    obtain ⟨P, ⟨hPV, hPU⟩, hPmax⟩ :=
      exists_isMaximal_mem K (V ∩ U) (hVopen.inter hUopen) (hUdense.inter_open_nonempty V hVopen ⟨_, hzV⟩)
    obtain ⟨x, rfl⟩ := exists_pt_eq (k := k) K P hPmax
    have hx : Lifts x := (hU_iff x).mp hPU
    have hw : Lifts (WithConv.ofConv (WithConv.toConv z * WithConv.toConv (x.comp (antipodeAlgHom K)))) := by
      rw [← hU_iff, ← hβpt]
      exact hPV
    have := lifts_mul _ _ hw hx
    rwa [WithConv.toConv_ofConv, mul_assoc, comp_antipode_mul_self, mul_one, WithConv.ofConv_toConv] at this

  have hU : U = Set.univ := by
    apply PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal U hUopen
    · obtain ⟨y⟩ : Nonempty (K →ₐ[k] k) := by
        haveI : Nontrivial K := nontrivial_of_ne 1 0 (fun h10 => by
          have := congrArg (Coalgebra.counit (R := k) (A := K)) h10
          rw [Bialgebra.counit_one, map_zero] at this
          exact one_ne_zero this)
        exact exists_algHom_of_finiteType
      exact ⟨pt y, (hU_iff y).mpr (key y)⟩
    · intro P Q _ hQ _
      obtain ⟨z, rfl⟩ := exists_pt_eq (k := k) K Q hQ
      exact (hU_iff z).mpr (key z)
  exact faithfullyFlat_of_range_eq_univ K H hU

end TakE

/--
@isnad1 id=faithful.3h3v.s12.594e27669aa6 from=translated src=- shape=10a41b73 vocab=738d6164
-/
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H :=
  TakE.main K H hinj hcomul hcounit
