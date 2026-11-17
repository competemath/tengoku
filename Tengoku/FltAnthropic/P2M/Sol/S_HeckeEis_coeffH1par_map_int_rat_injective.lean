import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffH1par_map_int_rat_injective.lean`: wrote out 19 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 4 `p2m_open`, 11 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero)
namespace CoeffMapAux
open _root_.HeckeEis

open MvPolynomial
open scoped MatrixGroups

variable {R R' : Type*} [CommRing R] [CommRing R']

/--
@isnad1 id=eq.0h4v.s10.baae53d1b001 from=translated src=- shape=bc91d65d vocab=96c9dafe
-/
theorem map_binarySubst_int (φ : ℤ →+* R) (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.map φ (binarySubst ℤ M P) = binarySubst R M (MvPolynomial.map φ P) := by
  have key : (MvPolynomial.map φ).comp (binarySubst ℤ M : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] MvPolynomial (Fin 2) ℤ).toRingHom
      = (binarySubst R M : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R).toRingHom.comp (MvPolynomial.map φ) :=
    MvPolynomial.ringHom_ext (fun a => by simp [binarySubst_C]) (fun j => by simp [binarySubst_X, map_sum])
  exact RingHom.congr_fun key P

def substCoeff (M : Matrix (Fin 2) (Fin 2) ℤ) (d d' : Fin 2 →₀ ℕ) : ℤ :=
  coeff d (binarySubst ℤ M (monomial d' 1))

/--
@isnad1 id=eq.0h3v.s10.42c0635dc614 from=translated src=- shape=4564f336 vocab=648abf1e
-/
theorem binarySubst_monomial_one (M : Matrix (Fin 2) (Fin 2) ℤ) (d' : Fin 2 →₀ ℕ) :
    binarySubst R M (monomial d' 1) = MvPolynomial.map (Int.castRingHom R) (binarySubst ℤ M (monomial d' 1)) := by
  rw [map_binarySubst_int, map_monomial, (Int.castRingHom R).map_one]

/--
@isnad1 id=eq.0h4v.s8.bf4b44c43f72 from=translated src=- shape=8a030645 vocab=84345d32
-/
theorem coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M P) = ∑ d' ∈ P.support, (substCoeff M d d' : R) * coeff d' P := by
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [show monomial d' (coeff d' P) = C (coeff d' P) * monomial d' 1 by rw [C_mul_monomial, mul_one], map_mul, binarySubst_C,
    coeff_C_mul, binarySubst_monomial_one, coeff_map, substCoeff, mul_comm]
  rfl

variable (f : R →+ R')

def pushCoeff (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R' :=
  ∑ d ∈ P.support, monomial d (f (coeff d P))

/--
@isnad1 id=eq.0h5v.s7.fedbdb28b631 from=translated src=- shape=915676e7 vocab=a88f20b5
-/
@[scoped simp] theorem coeff_pushCoeff (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) : coeff d (pushCoeff f P) = f (coeff d P) := by
  classical
  rw [pushCoeff, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

/--
@isnad1 id=le.0h4v.s7.971a18e02999 from=translated src=- shape=93418c0c vocab=910fa824
-/
theorem support_pushCoeff (P : MvPolynomial (Fin 2) R) : (pushCoeff f P).support ⊆ P.support := by
  intro d hd
  rw [mem_support_iff, coeff_pushCoeff] at hd
  rw [mem_support_iff]
  intro h; exact hd (by rw [h, map_zero])

/--
@isnad1 id=mem.1h5v.s8.bcf5be1951e2 from=translated src=- shape=e3115334 vocab=65d5b12f
-/
theorem pushCoeff_mem (n : ℕ) {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : pushCoeff f P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  exact hP (mem_support_iff.mp (support_pushCoeff f P (mem_support_iff.mpr hd)))

/--
@isnad1 id=eq.0h5v.s8.7fcc90abffe5 from=translated src=- shape=bbada809 vocab=ea5c9472
-/
theorem pushCoeff_add (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P + Q) = pushCoeff f P + pushCoeff f Q := by
  ext d; simp

/--
@isnad1 id=eq.0h5v.s8.edf0bf91a920 from=translated src=- shape=bbada809 vocab=84e6ee9e
-/
theorem pushCoeff_sub (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P - Q) = pushCoeff f P - pushCoeff f Q := by
  ext d; simp

/--
@isnad1 id=eq.0h3v.s7.3e0bb2f8e96d from=translated src=- shape=82b20d11 vocab=e3f9878c
-/
theorem pushCoeff_zero : pushCoeff f (0 : MvPolynomial (Fin 2) R) = 0 := by
  ext d; simp

/--
@isnad1 id=eq.0h5v.s9.609f9c9dba58 from=translated src=- shape=06264b0f vocab=c094eb83
-/
theorem pushCoeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    pushCoeff f (binarySubst R M P) = binarySubst R' M (pushCoeff f P) := by
  classical
  ext d
  rw [coeff_pushCoeff, coeff_binarySubst, coeff_binarySubst, map_sum]

  rw [Finset.sum_subset (support_pushCoeff f P)]
  · refine Finset.sum_congr rfl fun d' _ => ?_
    rw [coeff_pushCoeff, ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul]
  · intro d' _ hd'
    rw [notMem_support_iff.mp hd', mul_zero]

def pushForm (n : ℕ) (P : ↥(BinaryForm R n)) : ↥(BinaryForm R' n) := ⟨pushCoeff f P, pushCoeff_mem f n P.2⟩

/--
@isnad1 id=eq.0h5v.s9.de744a3eba0d from=translated src=- shape=67a236c8 vocab=8db90046
-/
@[scoped simp] theorem coe_pushForm (n : ℕ) (P : ↥(BinaryForm R n)) :
    ((pushForm f n P : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f P := rfl

/--
@isnad1 id=eq.0h6v.s11.649f80398fe2 from=translated src=- shape=eddbe453 vocab=603e72c5
-/
theorem pushForm_add (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P + Q) = pushForm f n P + pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_add])

/--
@isnad1 id=eq.0h6v.s11.89774c2d0abb from=translated src=- shape=eddbe453 vocab=931b8405
-/
theorem pushForm_sub (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P - Q) = pushForm f n P - pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_sub])

/--
@isnad1 id=eq.0h4v.s10.90ac30bae035 from=translated src=- shape=5892d76a vocab=5a16057e
-/
theorem pushForm_zero (n : ℕ) : pushForm f n (0 : ↥(BinaryForm R n)) = 0 := Subtype.ext (by simp [pushCoeff_zero])

/--
@isnad1 id=eq.0h6v.s13.7f8ace13f510 from=translated src=- shape=341f1cdc vocab=7db87b70
-/
theorem pushForm_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (P : ↥(BinaryForm R n)) :
    pushForm f n (binaryFormRepSL R n g P) = binaryFormRepSL R' n g (pushForm f n P) :=
  Subtype.ext (by simp [pushCoeff_binarySubst])

section Cocycles

variable {Γ : Subgroup SL(2, ℤ)} (n : ℕ)

/--
@isnad1 id=mem.1h6v.s14.d216f2a3be52 from=translated src=- shape=f6862a2f vocab=f36e4aa3
-/
theorem pushForm_comp_mem_coeffCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffCocycles ((binaryFormRepSL R' n).comp Γ.subtype) := by
  intro g h
  show pushForm f n (z (g * h)) = pushForm f n (z g) + binaryFormRepSL R' n ((g : Γ) : SL(2, ℤ)) (pushForm f n (z h))
  rw [hz g h, pushForm_add, ← pushForm_binaryFormRepSL]
  rfl

/--
@isnad1 id=isparabo.1h6v.s13.1228f39ae6a6 from=translated src=- shape=f4a9af83 vocab=feae4a79
-/
theorem isParabolicCocycle_pushForm_comp {z : Γ → ↥(BinaryForm R n)}
    (hz : IsParabolicCocycle ((binaryFormRepSL R n).comp Γ.subtype) z) :
    IsParabolicCocycle ((binaryFormRepSL R' n).comp Γ.subtype) (fun g => pushForm f n (z g)) := by
  intro γ hγ
  obtain ⟨u, hu⟩ := hz γ hγ
  refine ⟨pushForm f n u, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply] at hu ⊢
  change binaryFormRepSL R n (γ : SL(2, ℤ)) u - u = z γ at hu
  show binaryFormRepSL R' n (γ : SL(2, ℤ)) (pushForm f n u) - pushForm f n u = pushForm f n (z γ)
  rw [← hu, pushForm_sub, pushForm_binaryFormRepSL]

/--
@isnad1 id=mem.1h6v.s14.9328f4302eb2 from=translated src=- shape=c9207529 vocab=81edbaf6
-/
theorem pushForm_comp_mem_coeffParabolicCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype) :=
  ⟨pushForm_comp_mem_coeffCocycles f n hz.1, isParabolicCocycle_pushForm_comp f n hz.2⟩

/--
@isnad1 id=mem.1h6v.s14.f1bb3328858f from=translated src=- shape=f6862a2f vocab=4675284b
-/
theorem pushForm_comp_mem_coeffCoboundaries {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCoboundaries ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffCoboundaries ((binaryFormRepSL R' n).comp Γ.subtype) := by
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hz
  rw [mem_coeffCoboundaries_iff]
  refine ⟨pushForm f n v, funext fun g => ?_⟩
  have h := congrFun hv g
  change binaryFormRepSL R n (g : SL(2, ℤ)) v - v = z g at h
  show binaryFormRepSL R' n (g : SL(2, ℤ)) (pushForm f n v) - pushForm f n v = pushForm f n (z g)
  rw [← h, pushForm_sub, pushForm_binaryFormRepSL]

def pushPar : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))
    →+ ↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype)) where
  toFun z := ⟨fun g => pushForm f n (z.1 g), pushForm_comp_mem_coeffParabolicCocycles f n z.2⟩
  map_zero' := by
    apply Subtype.ext; funext g
    show pushForm f n ((0 : Γ → ↥(BinaryForm R n)) g) = 0
    rw [Pi.zero_apply, pushForm_zero]
  map_add' z w := by
    apply Subtype.ext; funext g
    show pushForm f n (z.1 g + w.1 g) = pushForm f n (z.1 g) + pushForm f n (w.1 g)
    rw [pushForm_add]

/--
@isnad1 id=iff.0h5v.s18.5802f2a4eaff from=translated src=- shape=e9c95d3a vocab=d3b58aa4
-/
theorem mk_eq_mk_iff {S : Type*} [CommRing S] (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))) :
    coeffH1parMk _ a = coeffH1parMk _ b ↔
      ((a - b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))).1
        ∈ coeffCoboundaries ((binaryFormRepSL S n).comp Γ.subtype)) := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]

/--
@isnad1 id=eq.0h7v.s20.8c9a2c981533 from=translated src=- shape=a9ffc37a vocab=e3d68a33
-/
theorem pushPar_sub (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) :
    pushPar f n (a - b) = pushPar f n a - pushPar f n b :=
  map_sub (pushPar f n) a b

/--
@isnad1 id=eq.1h7v.s20.d7c700bcebc2 from=translated src=- shape=85491e7a vocab=4ab9c561
-/
theorem mk_pushPar_congr {a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))}
    (h : coeffH1parMk _ a = coeffH1parMk _ b) :
    coeffH1parMk _ (pushPar f n a) = coeffH1parMk _ (pushPar f n b) := by
  rw [mk_eq_mk_iff] at h ⊢
  rw [← pushPar_sub]
  exact pushForm_comp_mem_coeffCoboundaries f n h

def pushH1par : coeffH1par ((binaryFormRepSL R n).comp Γ.subtype) →+ coeffH1par ((binaryFormRepSL R' n).comp Γ.subtype) where
  toFun x := coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) x))
  map_zero' := by
    have h0 : coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) 0)
        = coeffH1parMk _ (0 : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) := by
      rw [Function.surjInv_eq (coeffH1parMk_surjective _), map_zero]
    show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) 0)) = 0
    rw [mk_pushPar_congr f n h0, map_zero, map_zero]
  map_add' x y := by
    have hxy : coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) (x + y))
        = coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) x
            + Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) y) := by
      rw [map_add, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _),
        Function.surjInv_eq (coeffH1parMk_surjective _)]
    show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) (x + y))) = _
    rw [mk_pushPar_congr f n hxy, map_add, map_add]

end Cocycles

end HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero)
namespace CoeffMapAux
open _root_.HeckeEis

open MvPolynomial
open scoped MatrixGroups

/--
@isnad1 id=eq.0h4v.s8.ed662dc53ec4 from=translated src=- shape=c965affc vocab=a06fa300
-/
theorem pushCoeff_ringHom_eq_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial (Fin 2) R) :
    pushCoeff φ.toAddMonoidHom P = MvPolynomial.map φ P := by
  ext d
  rw [coeff_pushCoeff, coeff_map]
  rfl

end HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero)
namespace RatAux
open _root_.HeckeEis

open MvPolynomial HeckeEis.CoeffMapAux
open scoped MatrixGroups

/--
@isnad1 id=ex.0h1v.s5.4283b24fa3e3 from=translated src=- shape=859b7d79 vocab=42301028
-/
theorem exists_common_den (s : Finset ℚ) : ∃ D : ℤ, D ≠ 0 ∧ ∀ x ∈ s, ∃ m : ℤ, (D : ℚ) * x = m := by
  classical
  refine ⟨∏ y ∈ s, (y.den : ℤ), ?_, fun x hx => ?_⟩
  · rw [Finset.prod_ne_zero_iff]; intro y _; exact_mod_cast y.den_nz
  · refine ⟨(∏ y ∈ s.erase x, (y.den : ℤ)) * x.num, ?_⟩
    rw [← Finset.mul_prod_erase s _ hx]
    push_cast
    rw [mul_comm ((x.den : ℚ)) _, mul_assoc, Rat.den_mul_eq_num]

def IsInt (P : MvPolynomial (Fin 2) ℚ) : Prop := ∀ d, ∃ m : ℤ, coeff d P = m

/--
@isnad1 id=isint.1h2v.s8.5efc08c33d64 from=translated src=- shape=152690eb vocab=dd766e4a
-/
theorem IsInt.binarySubst {P : MvPolynomial (Fin 2) ℚ} (hP : IsInt P) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    IsInt (HeckeEis.binarySubst ℚ M P) := by
  classical
  intro d
  rw [coeff_binarySubst]
  choose m hm using hP
  refine ⟨∑ d' ∈ P.support, substCoeff M d d' * m d', ?_⟩
  push_cast
  exact Finset.sum_congr rfl fun d' _ => by rw [hm d']

def intModel (P : MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 2) ℤ := ∑ d ∈ P.support, monomial d (coeff d P).num

/--
@isnad1 id=eq.0h2v.s5.9677efa1eabd from=translated src=- shape=256db628 vocab=27ae78b5
-/
theorem coeff_intModel (P : MvPolynomial (Fin 2) ℚ) (d : Fin 2 →₀ ℕ) : coeff d (intModel P) = (coeff d P).num := by
  classical
  rw [intModel, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, Rat.num_zero]

/--
@isnad1 id=eq.1h1v.s7.e9f6e1e140ea from=translated src=- shape=6a2d8dbe vocab=7bc99ed6
-/
theorem map_intModel {P : MvPolynomial (Fin 2) ℚ} (hP : IsInt P) : MvPolynomial.map (Int.castRingHom ℚ) (intModel P) = P := by
  ext d
  rw [coeff_map, coeff_intModel]
  obtain ⟨m, hm⟩ := hP d
  rw [hm, Rat.num_intCast]
  rfl

/--
@isnad1 id=mem.1h2v.s8.352f03ed0d86 from=translated src=- shape=26f9e23c vocab=70147350
-/
theorem intModel_mem (n : ℕ) {P : MvPolynomial (Fin 2) ℚ} (hP : P ∈ BinaryForm ℚ n) : intModel P ∈ BinaryForm ℤ n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  rw [coeff_intModel] at hd
  apply hP
  intro h
  exact hd (by rw [h, Rat.num_zero])

/--
@isnad1 id=ex.0h1v.s7.222e034cf78f from=translated src=- shape=64539468 vocab=3b5d6a90
-/
theorem exists_isInt_zsmul (P : MvPolynomial (Fin 2) ℚ) : ∃ D : ℤ, D ≠ 0 ∧ IsInt (D • P) := by
  classical
  obtain ⟨D, hD, h⟩ := exists_common_den (P.support.image fun d => coeff d P)
  refine ⟨D, hD, fun d => ?_⟩
  by_cases hd : d ∈ P.support
  · obtain ⟨m, hm⟩ := h _ (Finset.mem_image_of_mem _ hd)
    exact ⟨m, by rw [← Int.cast_smul_eq_zsmul ℚ D, coeff_smul, smul_eq_mul, hm]⟩
  · exact ⟨0, by rw [← Int.cast_smul_eq_zsmul ℚ D, coeff_smul, notMem_support_iff.mp hd, smul_zero]; simp⟩

/--
@isnad1 id=ex.0h3v.s7.1d5067753371 from=translated src=- shape=80ab7aea vocab=3e4f241c
-/
theorem exists_isInt_zsmul_family {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Fin 2) ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ i ∈ s, IsInt (D • P i) := by
  classical
  obtain ⟨D, hD, h⟩ := exists_common_den (s.biUnion fun i => (P i).support.image fun d => coeff d (P i))
  refine ⟨D, hD, fun i hi d => ?_⟩
  by_cases hd : d ∈ (P i).support
  · obtain ⟨m, hm⟩ := h _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ hd⟩)
    exact ⟨m, by rw [← Int.cast_smul_eq_zsmul ℚ D, coeff_smul, smul_eq_mul, hm]⟩
  · exact ⟨0, by rw [← Int.cast_smul_eq_zsmul ℚ D, coeff_smul, notMem_support_iff.mp hd, smul_zero]; simp⟩

abbrev ιZQ : ℤ →+ ℚ := (Int.castRingHom ℚ).toAddMonoidHom

/--
@isnad1 id=injectiv.0h1v.s8.76563d1fe561 from=translated src=- shape=ca6994f9 vocab=e26f549b
-/
theorem pushForm_ι_injective (n : ℕ) : Function.Injective (pushForm ιZQ n : ↥(BinaryForm ℤ n) → ↥(BinaryForm ℚ n)) := by
  intro P Q h
  apply Subtype.ext
  ext d
  have := congrArg (fun S : ↥(BinaryForm ℚ n) => coeff d (S : MvPolynomial (Fin 2) ℚ)) h
  simp only [coe_pushForm, coeff_pushCoeff] at this
  exact Int.cast_injective this

/--
@isnad1 id=eq.0h2v.s9.6d37bf5e7795 from=translated src=- shape=d4e5bbec vocab=93d63caa
-/
theorem coe_pushForm_ι (n : ℕ) (P : ↥(BinaryForm ℤ n)) :
    ((pushForm ιZQ n P : ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ) = MvPolynomial.map (Int.castRingHom ℚ) P := by
  rw [coe_pushForm]; exact pushCoeff_ringHom_eq_map _ _

/--
@isnad1 id=ex.1h2v.s9.45b7f5d76537 from=translated src=- shape=eeab3051 vocab=af4fc4f8
-/
theorem exists_eq_pushForm_of_isInt (n : ℕ) {Q : ↥(BinaryForm ℚ n)} (hQ : IsInt (Q : MvPolynomial (Fin 2) ℚ)) :
    ∃ P : ↥(BinaryForm ℤ n), pushForm ιZQ n P = Q := by
  refine ⟨⟨intModel Q, intModel_mem n Q.2⟩, Subtype.ext ?_⟩
  rw [coe_pushForm_ι]
  exact map_intModel hQ

/--
@isnad1 id=eq.0h6v.s10.c24ba65d163d from=translated src=- shape=49b98857 vocab=c00fe2d1
-/
theorem pushForm_zsmul {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+ R') (n : ℕ) (m : ℤ) (P : ↥(BinaryForm R n)) :
    pushForm f n (m • P) = m • pushForm f n P :=
  map_zsmul (⟨⟨pushForm f n, pushForm_zero f n⟩, pushForm_add f n⟩ : ↥(BinaryForm R n) →+ ↥(BinaryForm R' n)) m P

end HeckeEis.RatAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

end
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero)
namespace RatAux
open _root_.HeckeEis

open MvPolynomial HeckeEis.CoeffMapAux CongruenceSubgroup
open scoped MatrixGroups

/--
@isnad1 id=injectiv.1h3v.s19.6f2f9d2833d8 from=translated src=- shape=5039b57c vocab=90806ab9
-/
theorem injective_of_clause (n N : ℕ) [NeZero N]
    (Φ : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL ℚ n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)),
      ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp (Gamma0 N).subtype)),
        (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ)
            = MvPolynomial.map (Int.castRingHom ℚ) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (coeffH1parMk _ z) = coeffH1parMk _ w) :
    Function.Injective Φ := by
  classical
  refine (injective_iff_map_eq_zero Φ).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := coeffH1parMk_surjective _ x
  obtain ⟨w, hw, hΦw⟩ := hΦ y
  rw [hΦw, coeffH1parMk_eq_zero_iff] at hx
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hx

  have hwy : ∀ g, (w : Gamma0 N → ↥(BinaryForm ℚ n)) g = pushForm ιZQ n ((y : Gamma0 N → ↥(BinaryForm ℤ n)) g) := fun g =>
    Subtype.ext (by rw [hw g, coe_pushForm_ι])

  obtain ⟨D, hD, hDv⟩ := exists_isInt_zsmul (v : MvPolynomial (Fin 2) ℚ)
  obtain ⟨v', hv'⟩ := exists_eq_pushForm_of_isInt n (Q := D • v) (by simpa [Submodule.coe_smul] using hDv)

  have hcob : (D • (y : Gamma0 N → ↥(BinaryForm ℤ n))) ∈ coeffCoboundaries ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) := by
    rw [mem_coeffCoboundaries_iff]
    refine ⟨v', funext fun g => pushForm_ι_injective n ?_⟩
    have h1 := congrFun hv g

    change binaryFormRepSL ℚ n (g : SL(2, ℤ)) v - v = (w : Gamma0 N → ↥(BinaryForm ℚ n)) g at h1
    show pushForm ιZQ n (binaryFormRepSL ℤ n (g : SL(2, ℤ)) v' - v') = pushForm ιZQ n ((D • (y : Gamma0 N → ↥(BinaryForm ℤ n))) g)
    rw [pushForm_sub, pushForm_binaryFormRepSL, hv', map_zsmul, ← zsmul_sub, h1, hwy g, Pi.smul_apply, pushForm_zsmul]
  have h2 : coeffH1parMk ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (D • y) = 0 := by
    rw [coeffH1parMk_eq_zero_iff]
    simpa [Submodule.coe_smul] using hcob
  rw [map_smul] at h2
  exact HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero n N D hD _ h2

end HeckeEis.RatAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

end
open scoped _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis _root_.P2MW.S_HeckeEis_coeffH1par_map_int_rat_injective.HeckeEis.CoeffMapAux

open scoped MatrixGroups in

/--
@isnad1 id=injectiv.1h3v.s19.6f2f9d2833d8 from=translated src=- shape=5039b57c vocab=90806ab9
-/
theorem solution (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ)
            = MvPolynomial.map (Int.castRingHom ℚ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) :
    Function.Injective Φ :=
  HeckeEis.RatAux.injective_of_clause n N Φ hΦ

