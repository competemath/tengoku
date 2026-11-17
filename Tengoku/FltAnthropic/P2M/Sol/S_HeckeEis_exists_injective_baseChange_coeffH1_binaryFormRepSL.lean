import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomologyEigen
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL

set_option autoImplicit false

namespace HAUC

open CongruenceSubgroup HeckeEis MvPolynomial
open scoped MatrixGroups TensorProduct

section MapA

variable {R R' : Type*} [CommRing R] [CommRing R']

noncomputable def mapA (c : R →+ R') (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R' :=
  AddMonoidAlgebra.map c P

/--
@isnad1 id=eq.0h5v.s7.33f81b8741f9 from=translated src=- shape=915676e7 vocab=30459f41
-/
@[scoped simp] theorem coeff_mapA (c : R →+ R') (P : MvPolynomial (Fin 2) R) (m : Fin 2 →₀ ℕ) :
    coeff m (mapA c P) = c (coeff m P) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.1bf78ffa4985 from=translated src=- shape=bbada809 vocab=a8aedbe8
-/
theorem mapA_add (c : R →+ R') (P Q : MvPolynomial (Fin 2) R) : mapA c (P + Q) = mapA c P + mapA c Q := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_add, map_add]

/--
@isnad1 id=eq.0h5v.s8.bf0d28b03819 from=translated src=- shape=bbada809 vocab=beb91263
-/
theorem mapA_sub (c : R →+ R') (P Q : MvPolynomial (Fin 2) R) : mapA c (P - Q) = mapA c P - mapA c Q := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_sub, map_sub]

/--
@isnad1 id=eq.0h4v.s8.41bc7841157c from=translated src=- shape=c965affc vocab=a2583f48
-/
theorem mapA_ringHom (φ : R →+* R') (P : MvPolynomial (Fin 2) R) : mapA φ.toAddMonoidHom P = map φ P := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_mapA, coeff_map]
  rfl

/--
@isnad1 id=ishomoge.1h5v.s6.9512da1d4e4d from=translated src=- shape=d4514d87 vocab=7de2cf1a
-/
theorem isHomogeneous_mapA (c : R →+ R') {P : MvPolynomial (Fin 2) R} {n : ℕ} (hP : P.IsHomogeneous n) :
    (mapA c P).IsHomogeneous n := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_mapA, h0, map_zero]

/--
@isnad1 id=mem.1h5v.s8.02925cea4ab4 from=translated src=- shape=e3115334 vocab=d3f5c8e6
-/
theorem mapA_mem (c : R →+ R') {n : ℕ} {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    mapA c P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  exact isHomogeneous_mapA c hP

/--
@isnad1 id=eq.0h5v.s10.308397182d7f from=translated src=- shape=133141e1 vocab=96c9dafe
-/
theorem map_binarySubst (φ : R →+* R') (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    map φ (binarySubst R M P) = binarySubst R' M (map φ P) := by
  have h : (map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R) =
      (binarySubst R' M : MvPolynomial (Fin 2) R' →+* MvPolynomial (Fin 2) R').comp (map φ) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_C, map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_X, map_X, map_sum, map_mul, map_intCast]
  exact congrFun (congrArg DFunLike.coe h) P

noncomputable def Nz (M : Matrix (Fin 2) (Fin 2) ℤ) (e d : Fin 2 →₀ ℕ) : ℤ :=
  coeff d (binarySubst ℤ M (monomial e 1))

/--
@isnad1 id=eq.0h4v.s9.810ad70f992e from=translated src=- shape=ae66ff28 vocab=559ac665
-/
theorem coeff_binarySubst_monomial_one (M : Matrix (Fin 2) (Fin 2) ℤ) (e d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M (monomial e 1)) = (Nz M e d : R) := by
  have h : binarySubst R M (monomial e 1) = map (Int.castRingHom R) (binarySubst ℤ M (monomial e 1)) := by
    rw [map_binarySubst, MvPolynomial.map_monomial, (Int.castRingHom R).map_one]
  rw [h, coeff_map, Nz, eq_intCast]

/--
@isnad1 id=eq.0h4v.s8.3b9ab5f57478 from=translated src=- shape=7e559b03 vocab=d6ca5a63
-/
theorem coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M P) = ∑ e ∈ P.support, coeff e P * (Nz M e d : R) := by
  conv_lhs => rw [P.as_sum, map_sum]
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show monomial e (coeff e P) = coeff e P • monomial e (1 : R) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, coeff_binarySubst_monomial_one, smul_eq_mul]

/--
@isnad1 id=eq.0h5v.s9.5a131dc1c05f from=translated src=- shape=06264b0f vocab=ecf5a375
-/
theorem mapA_binarySubst (c : R →+ R') (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    mapA c (binarySubst R M P) = binarySubst R' M (mapA c P) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_mapA, coeff_binarySubst, coeff_binarySubst, map_sum]
  have hsub : (mapA c P).support ⊆ P.support := Finsupp.support_mapRange (hf := c.map_zero)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [coeff_mapA, mul_comm (coeff e P), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  · intro e _ he
    have h0 : coeff e (mapA c P) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using he
    rw [mul_comm (coeff e P), ← zsmul_eq_mul, map_zsmul, ← coeff_mapA, h0, smul_zero]

end MapA

section Cochains

variable {R R' : Type*} [CommRing R] [CommRing R'] (N n : ℕ)

noncomputable abbrev ρSym (R : Type*) [CommRing R] (N n : ℕ) : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

variable {N n}

noncomputable def cmap (c : R →+ R') (z : Gamma0 N → ↥(BinaryForm R n)) : Gamma0 N → ↥(BinaryForm R' n) :=
  fun g => ⟨mapA c ((z g : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R), mapA_mem c (z g).2⟩

/--
@isnad1 id=eq.0h7v.s10.947af90e1ece from=translated src=- shape=4f95ee5f vocab=da71af14
-/
@[scoped simp] theorem coe_cmap (c : R →+ R') (z : Gamma0 N → ↥(BinaryForm R n)) (g : Gamma0 N) :
    ((cmap c z g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = mapA c (z g : MvPolynomial (Fin 2) R) := rfl

/--
@isnad1 id=eq.0h5v.s13.51adc5e7b14d from=translated src=- shape=c2004f49 vocab=65212ca7
-/
theorem coe_ρSym_apply (R : Type*) [CommRing R] (g : Gamma0 N) (v : ↥(BinaryForm R n)) :
    ((ρSym R N n g v : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R) =
      binarySubst R ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v := rfl

/--
@isnad1 id=mem.1h6v.s14.334813f2a39e from=translated src=- shape=a7d4a9b6 vocab=7a54a6b1
-/
theorem cmap_mem_coeffCocycles (c : R →+ R') {z : Gamma0 N → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCocycles (ρSym R N n)) : cmap c z ∈ coeffCocycles (ρSym R' N n) := by
  intro g h
  apply Subtype.ext
  rw [Submodule.coe_add, coe_cmap, coe_cmap, coe_ρSym_apply, coe_cmap, hz g h, Submodule.coe_add, mapA_add,
    coe_ρSym_apply, mapA_binarySubst]

/--
@isnad1 id=mem.1h6v.s14.4b281905c807 from=translated src=- shape=a7d4a9b6 vocab=8d4fd5a5
-/
theorem cmap_mem_coeffCoboundaries (c : R →+ R') {z : Gamma0 N → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCoboundaries (ρSym R N n)) : cmap c z ∈ coeffCoboundaries (ρSym R' N n) := by
  rw [mem_coeffCoboundaries_iff] at hz ⊢
  obtain ⟨v, rfl⟩ := hz
  refine ⟨⟨mapA c (v : MvPolynomial (Fin 2) R), mapA_mem c v.2⟩, funext fun g => Subtype.ext ?_⟩
  rw [coe_cmap, Submodule.coe_sub, Submodule.coe_sub, coe_ρSym_apply, coe_ρSym_apply, mapA_sub, mapA_binarySubst]

/--
@isnad1 id=eq.0h7v.s10.262e0a11a4d4 from=translated src=- shape=f508736a vocab=c019856d
-/
theorem coe_cmap_ringHom (φ : R →+* R') (z : Gamma0 N → ↥(BinaryForm R n)) (g : Gamma0 N) :
    ((cmap φ.toAddMonoidHom z g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = map φ (z g : MvPolynomial (Fin 2) R) := by
  rw [coe_cmap, mapA_ringHom]

end Cochains

section Coordinates

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

noncomputable scoped instance algZMod : Algebra (ZMod p) F := ZMod.algebra F p

abbrev JF : Type := Module.Free.ChooseBasisIndex (ZMod p) F

noncomputable def eF : Module.Basis (JF p F) (ZMod p) F := Module.Free.chooseBasis (ZMod p) F

noncomputable def crd (j : JF p F) : F →+ ZMod p where
  toFun x := (eF p F).repr x j
  map_zero' := by simp
  map_add' x y := by simp

/--
@isnad1 id=eq.0h4v.s9.dc4df0e32bd8 from=translated src=- shape=0ddc2377 vocab=e0c045d2
-/
theorem crd_apply (j : JF p F) (x : F) : crd p F j x = (eF p F).repr x j := rfl

open Classical in
/--
@isnad1 id=eq.0h5v.s8.bc53b5747093 from=translated src=- shape=72dc2233 vocab=19a7c56d
-/
theorem crd_smul_basis (i j : JF p F) (a : ZMod p) : crd p F j (a • eF p F i) = if i = j then a else 0 := by
  rw [crd_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

open Classical in

/--
@isnad1 id=eq.0h5v.s8.922414487a83 from=translated src=- shape=a71a6a3c vocab=b401125e
-/
theorem crd_basis_mul_intCast (i j : JF p F) (a : ℤ) :
    crd p F j (eF p F i * (a : F)) = if i = j then (a : ZMod p) else 0 := by
  have h : eF p F i * (a : F) = (a : ZMod p) • eF p F i := by
    rw [Algebra.smul_def, map_intCast, mul_comm]
  rw [h, crd_smul_basis]

/--
@isnad1 id=eq.0h3v.s6.891fcaf943c4 from=translated src=- shape=f1f79c28 vocab=53a09514
-/
theorem natCast_p_smul_eq_zero (x : F) : (p : ℤ) • x = 0 := by
  rw [zsmul_eq_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

/--
@isnad1 id=eq.0h4v.s6.426d6f11ade3 from=translated src=- shape=3515e710 vocab=d23c2665
-/
theorem zmod_smul_eq (a : ZMod p) (x : F) : a • x = ((a.val : ℤ)) • x := by
  rw [Algebra.smul_def, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_val]
  rfl

end Coordinates

section Main

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] (n N : ℕ)

abbrev H1 (R : Type) [CommRing R] : Type := coeffH1 (ρSym R N n)

noncomputable def extF (z : ↥(coeffCocycles (ρSym ℤ N n))) : ↥(coeffCocycles (ρSym F N n)) :=
  ⟨cmap (Int.castRingHom F).toAddMonoidHom z, cmap_mem_coeffCocycles _ z.2⟩

/--
@isnad1 id=eq.0h4v.s7.3d513068287a from=translated src=- shape=1f621292 vocab=7fc43768
-/
theorem toAddMonoidHom_apply' {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (x : R) :
    φ.toAddMonoidHom x = φ x := rfl

open Classical in

/--
@isnad1 id=eq.0h9v.s16.d96543ebe24d from=translated src=- shape=bebc6797 vocab=7d92b0f2
-/
theorem crd_coeff_sum (s : Finset (JF p F)) (z : JF p F → ↥(coeffCocycles (ρSym ℤ N n))) (j₀ : JF p F)
    (g : Gamma0 N) (m : Fin 2 →₀ ℕ) :
    crd p F j₀ (coeff m (((∑ j ∈ s, eF p F j • extF F n N (z j) : ↥(coeffCocycles (ρSym F N n))) :
      Gamma0 N → ↥(BinaryForm F n)) g : MvPolynomial (Fin 2) F)) =
      if j₀ ∈ s then ((coeff m (((z j₀ : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) : ℤ) : ZMod p)
        else 0 := by
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, coeff_sum, coeff_smul,
    map_sum]
  have hterm : ∀ j, crd p F j₀ (eF p F j • coeff m (((extF F n N (z j) : ↥(coeffCocycles (ρSym F N n))) :
      Gamma0 N → ↥(BinaryForm F n)) g : MvPolynomial (Fin 2) F)) =
      if j = j₀ then ((coeff m (((z j : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) : ℤ) : ZMod p)
        else 0 := by
    intro j
    change crd p F j₀ (eF p F j • coeff m (mapA (Int.castRingHom F).toAddMonoidHom _)) = _
    rw [coeff_mapA, toAddMonoidHom_apply', eq_intCast, smul_eq_mul, crd_basis_mul_intCast]
  simp only [hterm]
  rw [Finset.sum_ite_eq' s j₀]

/--
@isnad1 id=ex.0h5v.s12.257f72744bcc from=translated src=- shape=4d76d2c4 vocab=792fad71
-/
theorem exists_finsupp_eq_sum (y : F ⊗[ℤ] H1 n N ℤ) :
    ∃ f : JF p F →₀ H1 n N ℤ, y = f.sum fun j m => eF p F j ⊗ₜ[ℤ] m := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [Finsupp.sum_zero_index]⟩
  | tmul c x =>
    refine ⟨((eF p F).repr c).mapRange (fun a => (a.val : ℤ) • x) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun j => by rw [TensorProduct.tmul_zero])]
    have hc : c = ((eF p F).repr c).sum fun j a => a • eF p F j := by
      conv_lhs => rw [← (eF p F).linearCombination_repr c]
      rw [Finsupp.linearCombination_apply]
    conv_lhs => rw [hc]
    rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← TensorProduct.smul_tmul, zmod_smul_eq]
  | add a b ha hb =>
    obtain ⟨f, rfl⟩ := ha
    obtain ⟨g, rfl⟩ := hb
    refine ⟨f + g, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro j; rw [TensorProduct.tmul_zero]
    · intro j m₁ m₂; rw [TensorProduct.tmul_add]

/--
@isnad1 id=injectiv.4h7v.s18.23371248f781 from=translated src=- shape=f498323e vocab=ec9abe7d
-/
theorem injective_core
    (ΦF : H1 n N ℤ →+ H1 n N F)
    (hFmk : ∀ z : ↥(coeffCocycles (ρSym ℤ N n)), ΦF (coeffH1Mk _ z) = coeffH1Mk _ (extF F n N z))
    (Φp : H1 n N ℤ →+ H1 n N (ZMod p))
    (hp1 : ∀ z : ↥(coeffCocycles (ρSym ℤ N n)), ∃ w : ↥(coeffCocycles (ρSym (ZMod p) N n)),
      (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm (ZMod p) n)) g : MvPolynomial (Fin 2) (ZMod p)) =
        MvPolynomial.map (Int.castRingHom (ZMod p))
          (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ)) ∧
      Φp (coeffH1Mk _ z) = coeffH1Mk _ w)
    (hB : ∀ x : H1 n N ℤ, Φp x = 0 ↔ ∃ y, x = (p : ℤ) • y)
    (Φ : F ⊗[ℤ] H1 n N ℤ →ₗ[F] H1 n N F) (hΦ : ∀ (c : F) (x : H1 n N ℤ), Φ (c ⊗ₜ x) = c • ΦF x) :
    Function.Injective Φ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨f, rfl⟩ := exists_finsupp_eq_sum p F n N y

  have hsurj := coeffH1Mk_surjective (ρSym ℤ N n)
  choose zr hzr using fun j : JF p F => hsurj (f j)

  have hΦy : Φ (f.sum fun j m => eF p F j ⊗ₜ[ℤ] m) =
      coeffH1Mk _ (∑ j ∈ f.support, eF p F j • extF F n N (zr j)) := by
    rw [Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← hzr j, hFmk, map_smul]
  rw [hΦy, coeffH1Mk_eq_zero_iff] at hy

  have hdiv : ∀ j₀ ∈ f.support, ∃ u : H1 n N ℤ, f j₀ = (p : ℤ) • u := by
    intro j₀ hj₀
    rw [← hzr j₀, ← hB]
    obtain ⟨w, hw, hΦpz⟩ := hp1 (zr j₀)
    rw [hΦpz, coeffH1Mk_eq_zero_iff]
    have hcob := cmap_mem_coeffCoboundaries (crd p F j₀) hy
    have heq : (w : Gamma0 N → ↥(BinaryForm (ZMod p) n)) =
        cmap (crd p F j₀) ((∑ j ∈ f.support, eF p F j • extF F n N (zr j) :
          ↥(coeffCocycles (ρSym F N n))) : Gamma0 N → ↥(BinaryForm F n)) := by
      funext g
      apply Subtype.ext
      refine MvPolynomial.ext _ _ fun m => ?_
      rw [hw g, coeff_map, coe_cmap, coeff_mapA, crd_coeff_sum, ite_eq_left hj₀, eq_intCast]
    rw [heq]
    exact hcob

  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨u, hu⟩ := hdiv j hj
  have hu' : f j = (p : ℤ) • u := hu
  rw [hu', ← TensorProduct.smul_tmul, natCast_p_smul_eq_zero, TensorProduct.zero_tmul]

include p in

/--
@isnad1 id=ex.0h4v.s17.63a5e69d6314 from=translated src=- shape=0968354d vocab=e8cba8d9
-/
theorem main :
    ∃ Φ : F ⊗[ℤ] H1 n N ℤ →ₗ[F] H1 n N F,
      Function.Injective Φ ∧
      ∀ (c : F) (z : ↥(coeffCocycles (ρSym ℤ N n))),
        ∃ w : ↥(coeffCocycles (ρSym F N n)),
          (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm F n)) g : MvPolynomial (Fin 2) F) =
              c • MvPolynomial.map (Int.castRingHom F)
                (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ)) ∧
            Φ (c ⊗ₜ[ℤ] coeffH1Mk _ z) = coeffH1Mk _ w := by

  obtain ⟨ΦF, hF1, -, -, -, -⟩ := exists_coeffH1_map_ringHom_binaryFormRepSL (Int.castRingHom F) n N
  obtain ⟨Φp, hp1, -, -, hp4, -⟩ := exists_coeffH1_map_ringHom_binaryFormRepSL (Int.castRingHom (ZMod p)) n N
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hB : ∀ x : H1 n N ℤ, Φp x = 0 ↔ ∃ y, x = (p : ℤ) • y :=
    hp4 (p : ℤ) (ZMod.ringHom_surjective _) (fun a => ZMod.intCast_zmod_eq_zero_iff_dvd a p)
      (fun a b h => mul_left_cancel₀ hp0 h)

  have hFmk : ∀ z : ↥(coeffCocycles (ρSym ℤ N n)), ΦF (coeffH1Mk _ z) = coeffH1Mk _ (extF F n N z) := by
    intro z
    obtain ⟨w, hw, hΦ⟩ := hF1 z
    rw [hΦ]
    congr 1
    exact Subtype.ext (funext fun g => Subtype.ext ((hw g).trans (coe_cmap_ringHom _ _ g).symm))

  let B : F →ₗ[ℤ] H1 n N ℤ →ₗ[ℤ] H1 n N F :=
    LinearMap.mk₂ ℤ (fun c x => c • ΦF x)
      (fun c c' x => show (c + c') • ΦF x = c • ΦF x + c' • ΦF x from add_smul c c' _)
      (fun k c x => show (k • c) • ΦF x = k • (c • ΦF x) from smul_assoc k c (ΦF x))
      (fun c x x' => show c • ΦF (x + x') = c • ΦF x + c • ΦF x' by rw [map_add, smul_add])
      (fun k c x => show c • ΦF (k • x) = k • (c • ΦF x) by rw [map_zsmul, smul_comm])
  let Φz : F ⊗[ℤ] H1 n N ℤ →ₗ[ℤ] H1 n N F := TensorProduct.lift B
  have hΦz : ∀ (c : F) (x : H1 n N ℤ), Φz (c ⊗ₜ x) = c • ΦF x := fun c x => TensorProduct.lift.tmul c x

  have hlin : ∀ (a : F) (y : F ⊗[ℤ] H1 n N ℤ), Φz (a • y) = a • Φz y := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul c x => rw [TensorProduct.smul_tmul', hΦz, hΦz, smul_eq_mul, mul_smul]
    | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add]
  let Φ : F ⊗[ℤ] H1 n N ℤ →ₗ[F] H1 n N F :=
    { toFun := Φz, map_add' := fun a b => map_add Φz a b, map_smul' := fun a y => hlin a y }
  have hΦ : ∀ (c : F) (x : H1 n N ℤ), Φ (c ⊗ₜ x) = c • ΦF x := hΦz
  refine ⟨Φ, injective_core p F n N ΦF hFmk Φp hp1 hB Φ hΦ, fun c z => ?_⟩
  refine ⟨c • extF F n N z, fun g => ?_, ?_⟩
  · rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul]
    exact congrArg (c • ·) (coe_cmap_ringHom _ _ g)
  · rw [hΦ, hFmk, map_smul]

end Main

end HAUC
open scoped _root_.P2MW.S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.HAUC

open scoped TensorProduct in

/--
@isnad1 id=ex.0h4v.s19.888097f23620 from=translated src=- shape=13dd203b vocab=f29ca34a
-/
theorem solution (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] (n N : ℕ) :
    ∃ Φ : F ⊗[ℤ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[F]
        HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      Function.Injective Φ ∧
      ∀ (c : F)
        (z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))),
        ∃ w : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (∀ g : CongruenceSubgroup.Gamma0 N,
              ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F) =
                c • MvPolynomial.map (Int.castRingHom F)
                  (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
            Φ (c ⊗ₜ[ℤ] HeckeEis.coeffH1Mk _ z) = HeckeEis.coeffH1Mk _ w :=
  HAUC.main p F n N
