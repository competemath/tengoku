import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow

set_option autoImplicit false

open IsLocalRing TrivSqZeroExt

universe u v

namespace P2mCotangentCount

section Setup

variable (𝒪 : Type u) (R : Type v) [CommRing 𝒪] [IsLocalRing 𝒪]
  [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]

abbrev J : Ideal R := (maximalIdeal 𝒪).map (algebraMap 𝒪 R)

/--
@isnad1 id=le.0h2v.s7.d949a15a0527 from=translated src=- shape=7a52f4bf vocab=fce647a0
-/
lemma J_le : J 𝒪 R ≤ maximalIdeal R :=
  Ideal.map_le_iff_le_comap.2 fun o ho => map_nonunit (algebraMap 𝒪 R) o ho

/--
@isnad1 id=ne.0h2v.s7.d7017bb88f9b from=translated src=- shape=cbb1744e vocab=de3d5872
-/
lemma J_ne_top : J 𝒪 R ≠ ⊤ :=
  fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ J_le 𝒪 R))

abbrev R' : Type v := R ⧸ J 𝒪 R

/--
@isnad1 id=nontrivi.0h2v.s6.7c9797ac6999 from=translated src=- shape=a3768bc7 vocab=a53081b6
-/
scoped instance instNontrivialR' : Nontrivial (R' 𝒪 R) :=
  Ideal.Quotient.nontrivial_iff.2 (J_ne_top 𝒪 R)

/--
@isnad1 id=islocalr.0h2v.s6.efe5c6211b65 from=translated src=- shape=a9671f7e vocab=342b362f
-/
scoped instance instIsLocalRingR' : IsLocalRing (R' 𝒪 R) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (J 𝒪 R)) Ideal.Quotient.mk_surjective

abbrev mkR' : R →+* R' 𝒪 R := Ideal.Quotient.mk (J 𝒪 R)

/--
@isnad1 id=iff.0h3v.s8.e03dcce3abb3 from=translated src=- shape=f196d272 vocab=932657e4
-/
lemma mkR'_mem_iff (x : R) : mkR' 𝒪 R x ∈ maximalIdeal (R' 𝒪 R) ↔ x ∈ maximalIdeal R := by
  constructor
  · intro hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  · intro hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hmem : mkR' 𝒪 R x ∈ (maximalIdeal R).map (mkR' 𝒪 R) := Ideal.mem_map_of_mem _ hx
    have hne : (maximalIdeal R).map (mkR' 𝒪 R) ≠ ⊤ := by
      intro htop
      have h1 : (1 : R' 𝒪 R) ∈ (maximalIdeal R).map (mkR' 𝒪 R) := htop ▸ Submodule.mem_top
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
      obtain ⟨y, hy, hy1⟩ := h1
      have : y - 1 ∈ J 𝒪 R := by
        rw [← Ideal.Quotient.eq, hy1, map_one]
      have h2 : (1 : R) ∈ maximalIdeal R := by
        have h := (maximalIdeal R).sub_mem hy (J_le 𝒪 R this)
        simpa using h
      exact (maximalIdeal.isMaximal R).ne_top ((maximalIdeal R).eq_top_of_isUnit_mem h2 isUnit_one)
    exact hne (Ideal.eq_top_of_isUnit_mem _ hmem hu)

noncomputable def ι : ResidueField 𝒪 →+* R' 𝒪 R :=
  Ideal.Quotient.lift (maximalIdeal 𝒪) ((mkR' 𝒪 R).comp (algebraMap 𝒪 R))
    fun _ ho => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ho)

/--
@isnad1 id=eq.0h3v.s8.3687b0806c7e from=translated src=- shape=413f89c3 vocab=8194e4e1
-/
lemma ι_residue (o : 𝒪) : ι 𝒪 R (residue 𝒪 o) = mkR' 𝒪 R (algebraMap 𝒪 R o) := rfl

noncomputable def e : ResidueField 𝒪 →+* ResidueField (R' 𝒪 R) :=
  (residue (R' 𝒪 R)).comp (ι 𝒪 R)

variable {𝒪 R}

/--
@isnad1 id=bijectiv.1h2v.s9.7e24da9de9b8 from=translated src=- shape=30d2707c vocab=374a6f76
-/
lemma e_bijective (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) :
    Function.Bijective (e 𝒪 R) := by
  refine ⟨(e 𝒪 R).injective, fun z => ?_⟩
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
  obtain ⟨o, ho⟩ := hres (residue R r)
  refine ⟨residue 𝒪 o, ?_⟩
  change residue (R' 𝒪 R) (ι 𝒪 R (residue 𝒪 o)) = residue (R' 𝒪 R) (mkR' 𝒪 R r)
  rw [ι_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, mkR'_mem_iff,
    ← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact ho

noncomputable def E (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) :
    ResidueField 𝒪 ≃+* ResidueField (R' 𝒪 R) :=
  RingEquiv.ofBijective (e 𝒪 R) (e_bijective hres)

/--
@isnad1 id=eq.1h3v.s10.eb63ae343f09 from=translated src=- shape=35d0c0b3 vocab=92c6f192
-/
lemma E_apply (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (a : ResidueField 𝒪) :
    E hres a = residue (R' 𝒪 R) (ι 𝒪 R a) := rfl

noncomputable def c (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) :
    R' 𝒪 R →+* ResidueField 𝒪 :=
  ((E hres).symm : ResidueField (R' 𝒪 R) →+* ResidueField 𝒪).comp (residue (R' 𝒪 R))

/--
@isnad1 id=eq.1h3v.s11.24a8dd40dd91 from=translated src=- shape=aa3fa9f2 vocab=c2226752
-/
lemma c_apply (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (r : R' 𝒪 R) :
    c hres r = (E hres).symm (residue (R' 𝒪 R) r) := rfl

/--
@isnad1 id=eq.1h3v.s9.7388edbad670 from=translated src=- shape=5bafeaf9 vocab=0730849f
-/
lemma c_ι (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (a : ResidueField 𝒪) :
    c hres (ι 𝒪 R a) = a := by
  rw [c_apply, ← E_apply hres, RingEquiv.symm_apply_apply]

/--
@isnad1 id=eq.2h3v.s9.cf6d653ca5b0 from=translated src=- shape=ec465ca4 vocab=35689821
-/
lemma c_eq_zero_of_mem (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) {r : R' 𝒪 R}
    (hr : r ∈ maximalIdeal (R' 𝒪 R)) : c hres r = 0 := by
  rw [c_apply, (residue_eq_zero_iff r).2 hr, map_zero]

/--
@isnad1 id=mem.1h3v.s9.87d332a02cec from=translated src=- shape=404a3cee vocab=6a1c27e9
-/
lemma sub_ι_c_mem (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (r : R' 𝒪 R) :
    r - ι 𝒪 R (c hres r) ∈ maximalIdeal (R' 𝒪 R) := by
  rw [← residue_eq_zero_iff, map_sub, ← E_apply hres, c_apply, RingEquiv.apply_symm_apply,
    sub_self]

noncomputable def x' (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (r : R' 𝒪 R) :
    maximalIdeal (R' 𝒪 R) :=
  ⟨r - ι 𝒪 R (c hres r), sub_ι_c_mem hres r⟩

/--
@isnad1 id=eq.1h3v.s9.5a670e377d12 from=translated src=- shape=df242997 vocab=e0da819f
-/
@[scoped simp] lemma x'_coe (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R)) (r : R' 𝒪 R) :
    (x' hres r : R' 𝒪 R) = r - ι 𝒪 R (c hres r) := rfl

end Setup

section Hom

variable {𝒪 : Type u} {R : Type v} [CommRing 𝒪] [IsLocalRing 𝒪]
  [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
  (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R))

local notation "k" => ResidueField 𝒪
local notation "κ'" => ResidueField (R' 𝒪 R)
local notation "V" => CotangentSpace (R' 𝒪 R)

noncomputable def δ (μ : V →ₗ[κ'] κ') (r : R' 𝒪 R) : k :=
  (E hres).symm (μ ((maximalIdeal (R' 𝒪 R)).toCotangent (x' hres r)))

/--
@isnad1 id=eq.1h5v.s10.11ffca027b10 from=translated src=- shape=ce999071 vocab=80d5e57b
-/
lemma δ_add (μ : V →ₗ[κ'] κ') (r s : R' 𝒪 R) : δ hres μ (r + s) = δ hres μ r + δ hres μ s := by
  have hx : x' hres (r + s) = x' hres r + x' hres s := Subtype.ext (by
    simp only [x'_coe, map_add, Submodule.coe_add]; ring)
  unfold δ
  rw [hx, map_add, map_add, map_add]

/--
@isnad1 id=eq.1h5v.s10.4b542117646f from=translated src=- shape=f1349656 vocab=2501358f
-/
lemma δ_mul (μ : V →ₗ[κ'] κ') (r s : R' 𝒪 R) :
    δ hres μ (r * s) = c hres r * δ hres μ s + δ hres μ r * c hres s := by
  unfold δ
  set I := maximalIdeal (R' 𝒪 R)

  have hdec : x' hres (r * s) =
      ι 𝒪 R (c hres r) • x' hres s + ι 𝒪 R (c hres s) • x' hres r + x' hres r * x' hres s := by
    ext
    simp only [x'_coe, map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul,
      MulMemClass.coe_mul]
    ring
  have hsq : I.toCotangent (x' hres r * x' hres s) = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (x' hres r).2 (x' hres s).2
  have hsm : ∀ (a : k) (y : I), μ (I.toCotangent (ι 𝒪 R a • y)) = E hres a * μ (I.toCotangent y) := by
    intro a y
    rw [map_smul, ← IsScalarTower.algebraMap_smul (ResidueField (R' 𝒪 R)), map_smul, smul_eq_mul]
    rfl
  rw [hdec, map_add, hsq, add_zero, map_add, map_add, hsm, hsm, map_add, map_mul, map_mul,
    RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  ring

/--
@isnad1 id=eq.1h3v.s9.c56470042c59 from=translated src=- shape=3928b067 vocab=c056fc6a
-/
lemma δ_one (μ : V →ₗ[κ'] κ') : δ hres μ 1 = 0 := by
  have h := δ_mul hres μ 1 1
  rw [mul_one, map_one, one_mul, mul_one] at h

  simpa using h

noncomputable def ψ (μ : V →ₗ[κ'] κ') : R' 𝒪 R →+* DualNumber k where
  toFun r := inl (c hres r) + inr (δ hres μ r)
  map_one' := by
    rw [map_one, δ_one, inr_zero, add_zero, inl_one]
  map_mul' r s := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [map_mul]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl, fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, δ_mul]
      try ring
  map_zero' := by
    have h0 : δ hres μ 0 = 0 := by
      have h := δ_add hres μ 0 0
      rw [add_zero] at h
      simpa using h
    rw [map_zero, h0, inl_zero, inr_zero, add_zero]
  map_add' r s := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [map_add]
    · simp [δ_add]

/--
@isnad1 id=eq.1h4v.s10.bc05f247ec93 from=translated src=- shape=ae0a1755 vocab=e8e81329
-/
lemma ψ_apply_fst (μ : V →ₗ[κ'] κ') (r : R' 𝒪 R) : (ψ hres μ r).fst = c hres r := by
  simp [ψ]

/--
@isnad1 id=eq.1h4v.s10.921954842df4 from=translated src=- shape=7e4828e0 vocab=806d77e2
-/
lemma ψ_apply_snd (μ : V →ₗ[κ'] κ') (r : R' 𝒪 R) : (ψ hres μ r).snd = δ hres μ r := by
  simp [ψ]

@[reducible] noncomputable def instAlg (𝒪 : Type u) [CommRing 𝒪] [IsLocalRing 𝒪] :
    Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
  ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
    (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra

attribute [local instance] instAlg

/--
@isnad1 id=eq.0h2v.s9.d11dff5fcfa2 from=translated src=- shape=b3de3335 vocab=3fce9fe4
-/
lemma algebraMap_dual_apply (o : 𝒪) :
    algebraMap 𝒪 (DualNumber k) o = inl (residue 𝒪 o) := by
  show algebraMap (ResidueField 𝒪) (DualNumber k) (algebraMap 𝒪 (ResidueField 𝒪) o) = _
  rw [algebraMap_eq_inl]
  rfl

/--
@isnad1 id=eq.2h3v.s9.0e9104b73cdf from=translated src=- shape=9756b580 vocab=d40f5ba5
-/
lemma x'_of_mem {r : R' 𝒪 R} (hr : r ∈ maximalIdeal (R' 𝒪 R)) : x' hres r = ⟨r, hr⟩ := by
  refine Subtype.ext ?_
  rw [x'_coe, c_eq_zero_of_mem hres hr, map_zero, sub_zero]

/--
@isnad1 id=eq.1h4v.s10.fd4b61d490b2 from=translated src=- shape=f9c810dd vocab=9e82c96f
-/
lemma δ_ι (μ : V →ₗ[κ'] κ') (a : k) : δ hres μ (ι 𝒪 R a) = 0 := by
  have hx : x' hres (ι 𝒪 R a) = 0 := Subtype.ext (by
    rw [x'_coe, c_ι, sub_self]; rfl)
  unfold δ
  rw [hx, map_zero, map_zero, map_zero]

noncomputable def Φ (μ : V →ₗ[κ'] κ') : R →ₐ[𝒪] DualNumber k :=
  { (ψ hres μ).comp (mkR' 𝒪 R) with
    commutes' := fun o => by
      show ψ hres μ (mkR' 𝒪 R (algebraMap 𝒪 R o)) = algebraMap 𝒪 (DualNumber k) o
      rw [← ι_residue, algebraMap_dual_apply]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [ψ_apply_fst, c_ι, fst_inl]
      · rw [ψ_apply_snd, δ_ι, snd_inl] }

noncomputable def fstRingHom (φ : R →ₐ[𝒪] DualNumber k) : R →+* k where
  toFun r := (φ r).fst
  map_one' := by rw [map_one, fst_one]
  map_mul' r s := by rw [map_mul, fst_mul]
  map_zero' := by rw [map_zero, fst_zero]
  map_add' r s := by rw [map_add, fst_add]

/--
@isnad1 id=eq.0h4v.s8.be7744d96d03 from=translated src=- shape=004d1168 vocab=0bb4da17
-/
lemma fstRingHom_algebraMap (φ : R →ₐ[𝒪] DualNumber k) (o : 𝒪) :
    fstRingHom φ (algebraMap 𝒪 R o) = residue 𝒪 o := by
  show (φ (algebraMap 𝒪 R o)).fst = _
  rw [AlgHom.commutes, algebraMap_dual_apply, fst_inl]

/--
@isnad1 id=eq.1h4v.s9.20da969bbbca from=translated src=- shape=7a3c6287 vocab=653b4528
-/
lemma fst_eq_zero_of_mem (φ : R →ₐ[𝒪] DualNumber k) {y : R} (hy : y ∈ maximalIdeal R) :
    (φ y).fst = 0 := by
  have hsurj : Function.Surjective (fstRingHom φ) := fun a => by
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨algebraMap 𝒪 R o, fstRingHom_algebraMap φ o⟩
  have hmax := RingHom.ker_isMaximal_of_surjective (fstRingHom φ) hsurj
  have hker : RingHom.ker (fstRingHom φ) = maximalIdeal R := eq_maximalIdeal hmax
  have : y ∈ RingHom.ker (fstRingHom φ) := hker ▸ hy
  exact this

/--
@isnad1 id=eq.1h4v.s9.65db31e702ad from=translated src=- shape=56648f9c vocab=b6769466
-/
lemma fst_eq_c (φ : R →ₐ[𝒪] DualNumber k) (r : R) : (φ r).fst = c hres (mkR' 𝒪 R r) := by
  obtain ⟨o, ho⟩ := hres (residue R r)
  have hy : r - algebraMap 𝒪 R o ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ho.symm
  have h1 : (φ r).fst = residue 𝒪 o := by
    have := fst_eq_zero_of_mem φ hy
    rw [map_sub, fst_sub, sub_eq_zero] at this
    rw [this]; exact fstRingHom_algebraMap φ o
  have h2 : c hres (mkR' 𝒪 R r) = residue 𝒪 o := by
    have h3 : c hres (mkR' 𝒪 R (r - algebraMap 𝒪 R o)) = 0 :=
      c_eq_zero_of_mem hres ((mkR'_mem_iff 𝒪 R _).2 hy)
    rw [map_sub, map_sub, sub_eq_zero] at h3
    rw [h3, ← ι_residue, c_ι]
  rw [h1, h2]

/--
@isnad1 id=eq.1h4v.s9.acf8012b397b from=translated src=- shape=887c6a5a vocab=cb304561
-/
lemma apply_eq_zero_of_mem_J (φ : R →ₐ[𝒪] DualNumber k) {j : R} (hj : j ∈ J 𝒪 R) : φ j = 0 := by
  have hle : J 𝒪 R ≤ RingHom.ker (φ : R →+* DualNumber k) := by
    refine Ideal.map_le_iff_le_comap.2 fun o ho => ?_
    show φ (algebraMap 𝒪 R o) = 0
    rw [AlgHom.commutes, algebraMap_dual_apply, (residue_eq_zero_iff o).2 ho, inl_zero]
  exact hle hj

omit [IsLocalRing R] [IsLocalHom (algebraMap 𝒪 R)] in
/--
@isnad1 id=eq.2h4v.s9.3ead430f31d8 from=translated src=- shape=dccfd1f5 vocab=5a83da3a
-/
lemma mul_eq_mul_of_fst_eq {x₁ x₂ w : DualNumber k} (hx : x₁.fst = x₂.fst) (hw : w.fst = 0) :
    x₁ * w = x₂ * w := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_mul, fst_mul, hx]
  · simp only [snd_mul, hw, hx, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      mul_zero]

include hres in

/--
@isnad1 id=eq.4h6v.s10.7be1a6b02dc4 from=translated src=- shape=2e874a79 vocab=4449ab97
-/
lemma algHom_ext_of_snd_eq {ι' : Type*} (a : ι' → R) (ha : ∀ i, a i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span (Set.range a) ⊔ J 𝒪 R)
    (φ₁ φ₂ : R →ₐ[𝒪] DualNumber k) (h : ∀ i, (φ₁ (a i)).snd = (φ₂ (a i)).snd) : φ₁ = φ₂ := by

  have hm : ∀ y ∈ maximalIdeal R, φ₁ y = φ₂ y := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 (hgen hy)
    rw [map_add, map_add, apply_eq_zero_of_mem_J φ₁ hy₂, apply_eq_zero_of_mem_J φ₂ hy₂]
    congr 1
    refine Submodule.span_induction (p := fun z _ => φ₁ z = φ₂ z ∧ (φ₁ z).fst = 0)
      ?_ ?_ ?_ ?_ hy₁ |>.1
    · rintro _ ⟨i, rfl⟩
      have h0 : (φ₁ (a i)).fst = 0 := fst_eq_zero_of_mem φ₁ (ha i)
      refine ⟨TrivSqZeroExt.ext ?_ (h i), h0⟩
      rw [h0, fst_eq_zero_of_mem φ₂ (ha i)]
    · exact ⟨by rw [map_zero, map_zero], by rw [map_zero, fst_zero]⟩
    · rintro z w - - ⟨hz, hz0⟩ ⟨hw, hw0⟩
      exact ⟨by rw [map_add, map_add, hz, hw], by rw [map_add, fst_add, hz0, hw0, add_zero]⟩
    · rintro r z - ⟨hz, hz0⟩
      refine ⟨?_, ?_⟩
      · rw [smul_eq_mul, map_mul, map_mul, hz]
        exact mul_eq_mul_of_fst_eq (by rw [fst_eq_c hres, fst_eq_c hres]) (hz ▸ hz0)
      · rw [smul_eq_mul, map_mul, fst_mul, hz0, mul_zero]
  refine AlgHom.ext fun r => ?_
  obtain ⟨o, ho⟩ := hres (residue R r)
  have hy : r - algebraMap 𝒪 R o ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ho.symm
  have := hm _ hy
  rwa [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this

end Hom

section Count

variable {𝒪 : Type u} {R : Type v} [CommRing 𝒪] [IsLocalRing 𝒪]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
  (hres : Function.Surjective (residue R ∘ algebraMap 𝒪 R))

local notation "k" => ResidueField 𝒪
local notation "κ'" => ResidueField (R' 𝒪 R)
local notation "V" => CotangentSpace (R' 𝒪 R)

attribute [local instance] instAlg

include hres in
/--
@isnad1 id=ex.1h2v.s9.e881c0ac29a4 from=translated src=- shape=6fd9f344 vocab=5338bd13
-/
theorem main :
    ∃ (m : ℕ) (a : Fin m → R), (∀ i, a i ∈ maximalIdeal R) ∧
      maximalIdeal R ≤ Ideal.span (Set.range a) ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R) ∧
      Nat.card (R →ₐ[𝒪] DualNumber k) = Nat.card k ^ m := by
  classical
  set I := maximalIdeal (R' 𝒪 R) with hI
  let d := Module.finrank κ' V
  let b : Module.Basis (Fin d) κ' V := Module.finBasis κ' V

  have hg : ∀ i, ∃ g : I, I.toCotangent g = b i := fun i => I.toCotangent_surjective (b i)
  choose g hg using hg
  have ha : ∀ i, ∃ a : R, mkR' 𝒪 R a = g i := fun i => Ideal.Quotient.mk_surjective (g i : R' 𝒪 R)
  choose a ha using ha
  have ha𝔪 : ∀ i, a i ∈ maximalIdeal R := fun i => by
    rw [← mkR'_mem_iff 𝒪 R, ha]; exact (g i).2

  have hspan : Submodule.span (R' 𝒪 R) (Set.range g) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
    have : (I.toCotangent ∘ g) = b := funext hg
    rw [this, b.span_eq]
  have hgen : maximalIdeal R ≤ Ideal.span (Set.range a) ⊔ J 𝒪 R := by
    intro x hx
    have hx' : (⟨mkR' 𝒪 R x, (mkR'_mem_iff 𝒪 R x).2 hx⟩ : I) ∈ Submodule.span (R' 𝒪 R) (Set.range g) :=
      hspan ▸ Submodule.mem_top
    have hmap : mkR' 𝒪 R x ∈ (Submodule.span (R' 𝒪 R) (Set.range g)).map I.subtype :=
      ⟨_, hx', rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    have hrange : (I.subtype ∘ g : Fin d → R' 𝒪 R) = mkR' 𝒪 R ∘ a := funext fun i => by
      simp [ha]
    rw [hrange, Set.range_comp] at hmap
    change mkR' 𝒪 R x ∈ Ideal.span (mkR' 𝒪 R '' Set.range a) at hmap
    rw [← Ideal.map_span, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hmap
    exact hmap

  let F : (Fin d → k) → (R →ₐ[𝒪] DualNumber k) := fun v =>
    Φ hres (∑ i, (E hres (v i)) • b.coord i)
  have hF : ∀ v j, (F v (a j)).snd = v j := by
    intro v j
    change (ψ hres _ (mkR' 𝒪 R (a j))).snd = v j
    rw [ψ_apply_snd, ha, δ, x'_of_mem hres (g j).2, Subtype.coe_eta, hg]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same, mul_one, RingEquiv.symm_apply_apply]
    · intro i _ hij; rw [Finsupp.single_eq_of_ne hij, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hFinj : Function.Injective F := fun v w hvw => funext fun j => by
    rw [← hF v j, ← hF w j, hvw]

  let G : (R →ₐ[𝒪] DualNumber k) → (Fin d → k) := fun φ j => (φ (a j)).snd
  have hGinj : Function.Injective G := fun φ₁ φ₂ h12 =>
    algHom_ext_of_snd_eq hres a ha𝔪 hgen φ₁ φ₂ fun i => congrFun h12 i

  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein hFinj hGinj
  refine ⟨d, a, ha𝔪, hgen, ?_⟩
  rw [← Nat.card_eq_of_bijective h hh, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin]

end Count

end P2mCotangentCount
open scoped _root_.P2MW.S_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow.P2mCotangentCount

/--
@isnad1 id=ex.1h2v.s10.767d103496a1 from=translated src=- shape=6fd9f344 vocab=199f7f8f
-/
theorem solution
    {𝒪 : Type*} {R : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(IsLocalRing.residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    ∃ (m : ℕ) (a : Fin m → R), (∀ i, a i ∈ maximalIdeal R) ∧
      maximalIdeal R ≤ Ideal.span (Set.range a) ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R) ∧
      Nat.card (R →ₐ[𝒪] DualNumber (ResidueField 𝒪)) = Nat.card (ResidueField 𝒪) ^ m :=
  P2mCotangentCount.main hres
