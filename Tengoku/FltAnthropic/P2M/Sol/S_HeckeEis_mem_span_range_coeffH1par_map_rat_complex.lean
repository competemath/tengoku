import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.lean`: wrote out 16 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 4 `p2m_open`, 8 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex

set_option autoImplicit false

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff)
namespace GenAux
open _root_.HeckeEis

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

/--
@isnad1 id=eq.1h5v.s7.2bfa05abcbdc from=translated src=- shape=470191c7 vocab=e53b9774
-/
theorem coeffCocycles_apply_one {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h

  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

/--
@isnad1 id=eq.1h6v.s8.b92d09e02b83 from=translated src=- shape=8245a149 vocab=24ce8911
-/
theorem coeffCocycles_apply_inv {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) (g : G) :
    z g⁻¹ = -(ρ g⁻¹ (z g)) := by
  have h := hz g⁻¹ g
  rw [inv_mul_cancel, coeffCocycles_apply_one hz] at h

  exact eq_neg_of_add_eq_zero_left h.symm

/--
@isnad1 id=mem.4h8v.s9.1d1cd92a6b47 from=translated src=- shape=7eb8e577 vocab=cd52efdf
-/
theorem mem_of_mem_coeffCocycles_of_closure_eq_top {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ)
    (M : AddSubgroup V) (hM : ∀ (g : G) (v : V), v ∈ M → ρ g v ∈ M) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, z g ∈ M) (g : G) : z g ∈ M := by
  let H : Subgroup G :=
    { carrier := {g | z g ∈ M}
      one_mem' := by
        show z 1 ∈ M
        rw [coeffCocycles_apply_one hz]; exact M.zero_mem
      mul_mem' := by
        intro a b ha hb
        show z (a * b) ∈ M
        rw [hz a b]
        exact M.add_mem ha (hM a _ hb)
      inv_mem' := by
        intro a ha
        show z a⁻¹ ∈ M
        rw [coeffCocycles_apply_inv hz]
        exact M.neg_mem (hM _ _ ha) }
  have hle : (⊤ : Subgroup G) ≤ H := by
    rw [← hs, Subgroup.closure_le]
    exact h
  exact hle (Subgroup.mem_top g)

/--
@isnad1 id=eq.4h7v.s8.f6dd6b03fb2f from=translated src=- shape=9db5a248 vocab=6221ada1
-/
theorem coeffCocycles_eq_of_eqOn {ρ : Representation K G V} {z z' : G → V} (hz : z ∈ coeffCocycles ρ) (hz' : z' ∈ coeffCocycles ρ)
    {s : Set G} (hs : Subgroup.closure s = ⊤) (h : ∀ g ∈ s, z g = z' g) : z = z' := by
  have hd : z - z' ∈ coeffCocycles ρ := Submodule.sub_mem _ hz hz'
  funext g
  have := mem_of_mem_coeffCocycles_of_closure_eq_top hd ⊥ (fun g v hv => by
    rw [AddSubgroup.mem_bot] at hv ⊢; rw [hv, map_zero]) hs (fun g hg => by
    rw [AddSubgroup.mem_bot, Pi.sub_apply, h g hg, sub_self]) g
  rw [AddSubgroup.mem_bot, Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end HeckeEis.GenAux

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff)
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
@isnad1 id=eq.0h4v.s8.72de48c64652 from=translated src=- shape=8a030645 vocab=abfcd1cf
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
@isnad1 id=eq.0h5v.s7.0b82a30dd3c6 from=translated src=- shape=915676e7 vocab=6dbdfe93
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
@isnad1 id=le.0h4v.s7.56d0d0d05eae from=translated src=- shape=93418c0c vocab=ae8afce2
-/
theorem support_pushCoeff (P : MvPolynomial (Fin 2) R) : (pushCoeff f P).support ⊆ P.support := by
  intro d hd
  rw [mem_support_iff, coeff_pushCoeff] at hd
  rw [mem_support_iff]
  intro h; exact hd (by rw [h, map_zero])

/--
@isnad1 id=mem.1h5v.s8.a34f3160a0fd from=translated src=- shape=e3115334 vocab=c6906e50
-/
theorem pushCoeff_mem (n : ℕ) {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : pushCoeff f P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  exact hP (mem_support_iff.mp (support_pushCoeff f P (mem_support_iff.mpr hd)))

/--
@isnad1 id=eq.0h5v.s8.f148451e69ed from=translated src=- shape=bbada809 vocab=767ad773
-/
theorem pushCoeff_add (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P + Q) = pushCoeff f P + pushCoeff f Q := by
  ext d; simp

/--
@isnad1 id=eq.0h5v.s8.95282ed9cb12 from=translated src=- shape=bbada809 vocab=ce6e5676
-/
theorem pushCoeff_sub (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P - Q) = pushCoeff f P - pushCoeff f Q := by
  ext d; simp

/--
@isnad1 id=eq.0h3v.s7.f67026e97dc3 from=translated src=- shape=82b20d11 vocab=475aa693
-/
theorem pushCoeff_zero : pushCoeff f (0 : MvPolynomial (Fin 2) R) = 0 := by
  ext d; simp

/--
@isnad1 id=eq.0h5v.s9.cafc93b058c9 from=translated src=- shape=06264b0f vocab=f8cf4d7a
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
@isnad1 id=eq.0h5v.s9.f43814e3e512 from=translated src=- shape=67a236c8 vocab=202357fb
-/
@[scoped simp] theorem coe_pushForm (n : ℕ) (P : ↥(BinaryForm R n)) :
    ((pushForm f n P : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f P := rfl

/--
@isnad1 id=eq.0h6v.s11.d34cc2513595 from=translated src=- shape=eddbe453 vocab=2b9de610
-/
theorem pushForm_add (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P + Q) = pushForm f n P + pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_add])

/--
@isnad1 id=eq.0h6v.s11.d0c4f7eecdf4 from=translated src=- shape=eddbe453 vocab=dec09f91
-/
theorem pushForm_sub (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P - Q) = pushForm f n P - pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_sub])

/--
@isnad1 id=eq.0h4v.s10.4734e327cc9e from=translated src=- shape=5892d76a vocab=2f46e837
-/
theorem pushForm_zero (n : ℕ) : pushForm f n (0 : ↥(BinaryForm R n)) = 0 := Subtype.ext (by simp [pushCoeff_zero])

/--
@isnad1 id=eq.0h6v.s13.68e2bb37b3b1 from=translated src=- shape=341f1cdc vocab=5d234181
-/
theorem pushForm_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (P : ↥(BinaryForm R n)) :
    pushForm f n (binaryFormRepSL R n g P) = binaryFormRepSL R' n g (pushForm f n P) :=
  Subtype.ext (by simp [pushCoeff_binarySubst])

section Cocycles

variable {Γ : Subgroup SL(2, ℤ)} (n : ℕ)

/--
@isnad1 id=mem.1h6v.s14.0bfab6d52751 from=translated src=- shape=f6862a2f vocab=5a5f6db8
-/
theorem pushForm_comp_mem_coeffCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffCocycles ((binaryFormRepSL R' n).comp Γ.subtype) := by
  intro g h
  show pushForm f n (z (g * h)) = pushForm f n (z g) + binaryFormRepSL R' n ((g : Γ) : SL(2, ℤ)) (pushForm f n (z h))
  rw [hz g h, pushForm_add, ← pushForm_binaryFormRepSL]
  rfl

/--
@isnad1 id=isparabo.1h6v.s13.924812fc6628 from=translated src=- shape=f4a9af83 vocab=52610419
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
@isnad1 id=mem.1h6v.s14.396aa9c7c2da from=translated src=- shape=c9207529 vocab=3e6a037c
-/
theorem pushForm_comp_mem_coeffParabolicCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype) :=
  ⟨pushForm_comp_mem_coeffCocycles f n hz.1, isParabolicCocycle_pushForm_comp f n hz.2⟩

/--
@isnad1 id=mem.1h6v.s14.df6eec0e7a0b from=translated src=- shape=f6862a2f vocab=2dd48c60
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
@isnad1 id=eq.0h7v.s18.223c2485c1ad from=translated src=- shape=397d1c44 vocab=b327b91e
-/
theorem pushPar_apply_val (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (g : Γ) :
    (pushPar f n z).1 g = pushForm f n (z.1 g) := rfl

/--
@isnad1 id=iff.0h5v.s18.5802f2a4eaff from=translated src=- shape=e9c95d3a vocab=d3b58aa4
-/
theorem mk_eq_mk_iff {S : Type*} [CommRing S] (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))) :
    coeffH1parMk _ a = coeffH1parMk _ b ↔
      ((a - b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))).1
        ∈ coeffCoboundaries ((binaryFormRepSL S n).comp Γ.subtype)) := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]

/--
@isnad1 id=eq.0h7v.s20.85c64ca59d30 from=translated src=- shape=a9ffc37a vocab=76eead95
-/
theorem pushPar_sub (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) :
    pushPar f n (a - b) = pushPar f n a - pushPar f n b :=
  map_sub (pushPar f n) a b

/--
@isnad1 id=eq.1h7v.s20.f6f50b7a683c from=translated src=- shape=85491e7a vocab=6aab8e6a
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
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff)
namespace CoeffMapAux
open _root_.HeckeEis

open MvPolynomial
open scoped MatrixGroups

/--
@isnad1 id=eq.0h4v.s8.14971fbb82f3 from=translated src=- shape=c965affc vocab=388b9f82
-/
theorem pushCoeff_ringHom_eq_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial (Fin 2) R) :
    pushCoeff φ.toAddMonoidHom P = MvPolynomial.map φ P := by
  ext d
  rw [coeff_pushCoeff, coeff_map]
  rfl

end HeckeEis.CoeffMapAux
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff)
namespace QCAux
open _root_.HeckeEis

open MvPolynomial HeckeEis.CoeffMapAux HeckeEis.GenAux
open scoped MatrixGroups

abbrev ιQC : ℚ →+ ℂ := (algebraMap ℚ ℂ).toAddMonoidHom

abbrev BQC := Module.Basis.ofVectorSpace ℚ ℂ

abbrev πQC (α : Module.Basis.ofVectorSpaceIndex ℚ ℂ) : ℂ →+ ℚ := ((BQC).coord α).toAddMonoidHom

variable (n : ℕ)

/--
@isnad1 id=eq.0h2v.s9.59dc2b3c9bdb from=translated src=- shape=985bfcfc vocab=051b4826
-/
theorem coe_pushForm_ιQC (P : ↥(BinaryForm ℚ n)) :
    ((pushForm ιQC n P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = MvPolynomial.map (algebraMap ℚ ℂ) P := by
  rw [coe_pushForm]; exact pushCoeff_ringHom_eq_map _ _

/--
@isnad1 id=eq.0h4v.s11.4b8bbfccefd6 from=translated src=- shape=252d9b80 vocab=9614fb4b
-/
theorem pushForm_π_smul_ι (α : Module.Basis.ofVectorSpaceIndex ℚ ℂ) (c : ℂ) (Q : ↥(BinaryForm ℚ n)) :
    pushForm (πQC α) n (c • pushForm ιQC n Q) = (BQC.coord α c) • Q := by
  apply Subtype.ext
  ext d
  simp only [coe_pushForm, coeff_pushCoeff, Submodule.coe_smul, coeff_smul, smul_eq_mul]
  show (BQC.coord α) (c * (algebraMap ℚ ℂ) (coeff d (Q : MvPolynomial (Fin 2) ℚ))) = _
  rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

/--
@isnad1 id=eq.1h3v.s11.4053ddc4aaf6 from=translated src=- shape=a8c4326a vocab=d5016d64
-/
theorem sum_smul_pushForm_π (P : ↥(BinaryForm ℂ n)) (A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ))
    (hA : ∀ d ∈ (P : MvPolynomial (Fin 2) ℂ).support, (BQC.repr (coeff d (P : MvPolynomial (Fin 2) ℂ))).support ⊆ A) :
    ∑ α ∈ A, (BQC α : ℂ) • pushForm ιQC n (pushForm (πQC α) n P) = P := by
  classical
  apply Subtype.ext
  ext d
  rw [Submodule.coe_sum, coeff_sum]
  simp only [Submodule.coe_smul, coeff_smul, coe_pushForm, coeff_pushCoeff, smul_eq_mul]
  by_cases hd : d ∈ (P : MvPolynomial (Fin 2) ℂ).support
  ·
    set x : ℂ := coeff d (P : MvPolynomial (Fin 2) ℂ)
    have hx := BQC.linearCombination_repr x
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset (BQC.repr x) (hA d hd) (fun i a => a • (BQC i : ℂ)) (fun i _ => zero_smul ℚ _)] at hx
    conv_rhs => rw [← hx]
    refine Finset.sum_congr rfl fun α _ => ?_
    show (BQC α : ℂ) * (algebraMap ℚ ℂ) (BQC.coord α x) = (BQC.repr x α) • (BQC α : ℂ)
    rw [Algebra.smul_def, mul_comm]
    rfl
  · rw [notMem_support_iff.mp hd]
    refine Finset.sum_eq_zero fun α _ => ?_
    show (BQC α : ℂ) * (algebraMap ℚ ℂ) ((BQC.coord α) (0 : ℂ)) = 0
    rw [map_zero, map_zero, mul_zero]

variable {Γ : Subgroup SL(2, ℤ)}

/--
@isnad1 id=ex.1h4v.s19.e8c90e192533 from=translated src=- shape=caf37bf2 vocab=f1de0caa
-/
theorem exists_eq_sum_smul_pushPar (s : Finset Γ) (hs : Subgroup.closure (s : Set Γ) = ⊤)
    (Z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype))) :
    ∃ A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ),
      Z = ∑ α ∈ A, (BQC α : ℂ) • pushPar ιQC n (pushPar (πQC α) n Z) := by
  classical
  let A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ) :=
    s.biUnion fun g => ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).support.biUnion fun d =>
      (BQC.repr (coeff d ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))).support
  refine ⟨A, Subtype.ext ?_⟩
  set T : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype)) :=
    ∑ α ∈ A, (BQC α : ℂ) • pushPar ιQC n (pushPar (πQC α) n Z) with hT

  refine coeffCocycles_eq_of_eqOn Z.2.1 T.2.1 hs fun g hg => ?_
  rw [hT]
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, pushPar_apply_val]
  symm
  apply sum_smul_pushForm_π
  intro d hd
  exact Finset.subset_biUnion_of_mem (fun d => (BQC.repr (coeff d ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))).support) hd
    |>.trans (Finset.subset_biUnion_of_mem (fun g => ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).support.biUnion fun d =>
      (BQC.repr (coeff d ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))).support) hg)

variable (Ψ : coeffH1par ((binaryFormRepSL ℚ n).comp Γ.subtype) →+ coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype))
  (hΨ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp Γ.subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype)),
    (∀ g : Γ, ((w : Γ → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
        = MvPolynomial.map (algebraMap ℚ ℂ) (((z : Γ → ↥(BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧
    Ψ (coeffH1parMk _ z) = coeffH1parMk _ w)

include hΨ in
/--
@isnad1 id=eq.1h4v.s20.48630031a7bf from=translated src=- shape=751f2751 vocab=93e69509
-/
theorem Ψ_mk (z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp Γ.subtype))) : Ψ (coeffH1parMk _ z) = coeffH1parMk _ (pushPar ιQC n z) := by
  obtain ⟨w, hw, h⟩ := hΨ z
  rw [h]
  congr 1
  apply Subtype.ext; funext g; apply Subtype.ext
  rw [hw g]
  exact (coe_pushForm_ιQC n _).symm

include hΨ in

/--
@isnad1 id=mem.2h5v.s19.2ca604528941 from=translated src=- shape=459ee932 vocab=468cdaaf
-/
theorem mem_span_range (s : Finset Γ) (hs : Subgroup.closure (s : Set Γ) = ⊤) (X : coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype)) :
    X ∈ Submodule.span ℂ (Set.range Ψ) := by
  classical
  obtain ⟨Z, rfl⟩ := coeffH1parMk_surjective _ X
  obtain ⟨A, hA⟩ := exists_eq_sum_smul_pushPar n s hs Z
  rw [hA, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨coeffH1parMk _ (pushPar (πQC α) n Z), ?_⟩)
  exact Ψ_mk n Ψ hΨ _

end HeckeEis.QCAux
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.HeckeEis

open scoped MatrixGroups in

/--
@isnad1 id=mem.1h4v.s19.7c21f54bc2ae from=translated src=- shape=abfb5dea vocab=5bb16670
-/
theorem solution (n : ℕ) (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ]
    (Ψ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype))
    (hΨ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (algebraMap ℚ ℂ)
                (((z : Γ → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧
        Ψ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (X : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)) :
    X ∈ Submodule.span ℂ (Set.range Ψ) := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG Γ)
  exact HeckeEis.QCAux.mem_span_range n Ψ hΨ S hS X

