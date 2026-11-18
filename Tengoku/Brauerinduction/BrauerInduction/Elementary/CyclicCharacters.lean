import Tengoku.Brauerinduction.BrauerInduction.Cyclotomic.CharacterSystem
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.RingTheory.RootsOfUnity
import Tengoku.Brauerinduction.BrauerInduction.Elementary.Associated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclic characters on associated `p`-elementary subgroups

This file constructs the linear characters of the cyclic factor `Cyc a` used
in Bernstein's Fourier expansion. It then inflates these characters to the
associated `p`-elementary subgroup `E(a)` and proves the evaluation and
cyclotomic-coefficient properties needed for the local function.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

namespace BrauerInduction
namespace PElementary

section CyclicCharacters

/-!
## Cyclic exponents and characters of `Cyc a`

This section chooses integer exponents for elements of the cyclic subgroup
`Cyc a` and defines the linear character `chiCyc ζ`, which sends the distinguished
generator `a` to the root of unity `ζ`.
-/

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/-- Extracts the integer exponent n such that a^n = x-/
noncomputable def cycExp {a : G} (x : PElementary.Cyc a) : ℤ :=
  Classical.choose (Subgroup.mem_zpowers_iff.mp x.property)

/-- Guarantees that a ^ (cycExp x) evaluates exactly to x
@isnad1 id=eq.0h3v.s6.68aed6cb73e0 from=translated src=- shape=1c812712 vocab=6a4ea8e5
-/
lemma cycExp_spec {a : G} (x : PElementary.Cyc a) :
    a ^ cycExp x = (x : G) :=
  Classical.choose_spec (Subgroup.mem_zpowers_iff.mp x.property)

/--
The linear character of `Cyc a` sending `a` to a chosen `orderOf a`-th root of
unity.-/
noncomputable def chiCyc
    {a : G} (ζ : rootsOfUnity (orderOf a) k) :
    (PElementary.Cyc a) →* kˣ where
  toFun := fun x => (ζ : kˣ) ^ cycExp x
  map_one' := by
    have hdif : a ^ cycExp 1 = 1 := cycExp_spec 1
    have hdvd : (orderOf a : ℤ) ∣ cycExp 1 := orderOf_dvd_iff_zpow_eq_one.mpr hdif
    obtain ⟨c, hc⟩ := hdvd
    have hζ : (ζ : kˣ) ^ (orderOf a : ℤ) = 1 := by
      have h_prop : (ζ : kˣ) ∈ rootsOfUnity (orderOf a) k := ζ.property
      rw [mem_rootsOfUnity] at h_prop
      exact h_prop
    calc (ζ : kˣ) ^ cycExp 1
       = (ζ : kˣ) ^ ((orderOf a : ℤ) * c) := by rw [hc]
     _ = ((ζ : kˣ) ^ (orderOf a : ℤ)) ^ c := by rw [zpow_mul]
     _ = (1 : kˣ) ^ c := by rw [hζ]
     _ = 1 := by exact one_zpow c
  map_mul' := by
    intro x y
    have hl : a ^ cycExp (x * y) = (x * y : G) := cycExp_spec (x * y)
    have hn : a ^ cycExp x = (x : G) := cycExp_spec x
    have hm : a ^ cycExp y = (y : G) := cycExp_spec y
    have hl_eq : a ^ cycExp (x * y) = a ^ (cycExp x + cycExp y) := by
      calc a ^ cycExp (x * y)
         = (x * y : G) := hl
       _ = (x : G) * (y : G) := rfl
       _ = a ^ cycExp x * a ^ cycExp y := by rw [← hn, ← hm]
       _ = a ^ (cycExp x + cycExp y) := by rw [zpow_add]
    have hdif : a ^ (cycExp (x * y) - (cycExp x + cycExp y)) = 1 := by
      calc a ^ (cycExp (x * y) - (cycExp x + cycExp y))
         = a ^ cycExp (x * y) * a ^ (-(cycExp x + cycExp y)) := by rw [sub_eq_add_neg, zpow_add]
       _ = a ^ (cycExp x + cycExp y) * (a ^ (cycExp x + cycExp y))⁻¹ := by rw [hl_eq, zpow_neg]
       _ = 1 := mul_inv_cancel _
    have hdvd : (orderOf a : ℤ) ∣ cycExp (x * y) - (cycExp x + cycExp y) :=
      orderOf_dvd_iff_zpow_eq_one.mpr hdif
    obtain ⟨c, hc⟩ := hdvd
    have hl_val : cycExp (x * y) = cycExp x + cycExp y + (orderOf a : ℤ) * c := by omega
    have hζ : (ζ : kˣ) ^ (orderOf a : ℤ) = 1 := by
      have h_prop : (ζ : kˣ) ∈ rootsOfUnity (orderOf a) k := ζ.property
      rw [mem_rootsOfUnity] at h_prop
      exact h_prop
    calc (ζ : kˣ) ^ cycExp (x * y)
     _ = (ζ : kˣ) ^ (cycExp x + cycExp y) * (ζ : kˣ) ^ ((orderOf a : ℤ) * c) := by
          rw [hl_val, zpow_add]
     _ = (ζ : kˣ) ^ (cycExp x + cycExp y) * (((ζ : kˣ) ^ (orderOf a : ℤ)) ^ c) := by rw [zpow_mul]
     _ = (ζ : kˣ) ^ (cycExp x + cycExp y) * (1 ^ c) := by rw [hζ]
     _ = (ζ : kˣ) ^ (cycExp x + cycExp y) * 1 := by
          simp only [mul_one, mul_eq_left]; exact one_zpow c
     _ = (ζ : kˣ) ^ (cycExp x + cycExp y) := by rw [mul_one]
     _ = (ζ : kˣ) ^ cycExp x * (ζ : kˣ) ^ cycExp y := by rw [zpow_add]

open PElementary in
/--
The cyclic character `χ_ζ` sends the distinguished generator `a` of `Cyc a` to
the root of unity `ζ`.
@isnad1 id=eq.0h4v.s9.158b57ffb622 from=translated src=- shape=7790e523 vocab=9d729d68
-/
lemma chiCyc_apply_generator
    {G : Type v} [Group G]
    {a : G}
    (ζ : rootsOfUnity (orderOf a) k) :
    (chiCyc ζ) (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) = ζ := by
  simp only [chiCyc, MonoidHom.coe_mk, OneHom.coe_mk]
  have h_cyc : a ^ cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) = a :=
    cycExp_spec (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a)
  have h_an_one :
      a ^ (cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) - 1) = 1 := by
    rw [sub_eq_add_neg, zpow_add, h_cyc, zpow_neg_one, mul_inv_cancel]
  have h_dvd :
      (orderOf a : ℤ) ∣
        cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) - 1 :=
    orderOf_dvd_iff_zpow_eq_one.mpr h_an_one
  obtain ⟨m, hm⟩ := h_dvd
  have h_exp :
      cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) =
        1 + (orderOf a : ℤ) * m := by
    calc
      cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a)
          = 1 + (cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) - 1) := by
              ring
      _ = 1 + (orderOf a : ℤ) * m := by rw [hm]
  calc
    (ζ : kˣ) ^ cycExp (⟨a, Subgroup.mem_zpowers a⟩ : Cyc a)
        = (ζ : kˣ) ^ (1 + (orderOf a : ℤ) * m) := by
            rw [h_exp]
    _ = (ζ : kˣ) ^ (1 : ℤ) *
          ((ζ : kˣ) ^ (orderOf a : ℤ)) ^ m := by
            rw [zpow_add, zpow_mul]
    _ = (ζ : kˣ) * 1 ^ m := by
            have hz : (ζ : kˣ) ^ orderOf a = 1 :=
              (mem_rootsOfUnity (orderOf a) (ζ : kˣ)).mp ζ.property
            have hz_zpow : (ζ : kˣ) ^ (orderOf a : ℤ) = 1 := by
              exact_mod_cast hz
            rw [zpow_one, hz_zpow]
    _ = (ζ : kˣ) := by
            simp only [one_zpow, mul_one]

open PElementary in
/--
The cyclic character `χ_ζ` sends the `n`th power of the distinguished generator
of `Cyc a` to `ζ ^ n`.
@isnad1 id=eq.0h5v.s9.cc1699102cec from=translated src=- shape=d5e0aa01 vocab=d9ed2e35
-/
lemma chiCyc_apply_generator_zpow
    {G : Type v} [Group G]
    {a : G}
    (ζ : rootsOfUnity (orderOf a) k)
    (n : ℤ) :
    (chiCyc ζ)
      ((⟨a, Subgroup.mem_zpowers a⟩ : Cyc a) ^ n) = ζ ^ n := by
  rw [map_zpow, chiCyc_apply_generator (a := a) ζ]

/--
@isnad1 id=mem.0h5v.s9.6cc790abc348 from=translated src=- shape=a7dc299d vocab=37ee1a91
-/
lemma chiCyc_apply_mem_Lambda [Finite G]
    {a : G} (ζ : rootsOfUnity (orderOf a) k)
    (y : PElementary.Cyc a) :
    (((chiCyc ζ) y : kˣ) : k) ∈ ClassFun.Lambda k G := by
  exact ClassFun.Lambda.linearChar_subgroup_apply_mem_Lambda
    (H := PElementary.Cyc a) (chiCyc ζ) y

end CyclicCharacters

section CharactersOnE

/-!
## Characters and one-dimensional representations of `E(a)`

This section extends linear characters of `Cyc a` to `E(a)` using the projection
`E_to_Cyc`.  The root-of-unity family is represented by `psiEZeta`, and
`VpsiEZeta` is the corresponding one-dimensional representation.
-/

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
Extend a linear character of the cyclic factor `Cyc a` to `E(a)` by composing
with the projection `E(a) → Cyc a`.-/
noncomputable def psiE
    (a : G) (ha : IsPRegular p a)
    (ψ : PElementary.Cyc a →* kˣ) :
    E_subgroup p a →* kˣ :=
  ψ.comp (E_to_Cyc p a ha)

/--
The one-dimensional representation of `E(a)` attached to a linear character of
the cyclic factor `Cyc a`.-/
noncomputable def VpsiE
    (a : G) (ha : IsPRegular p a)
    (ψ : PElementary.Cyc a →* kˣ) :
    FDRep k (E_subgroup p a) :=
  FDRep.ofLinearChar (psiE p a ha ψ)

/--
The linear character of `E(a)` obtained from the character of `Cyc a` sending
`a` to the root of unity `ζ`.-/
noncomputable def psiEZeta
    {a : G} (ha : IsPRegular p a)
    (ζ : rootsOfUnity (orderOf a) k) :
    E_subgroup p a →* kˣ := psiE p a ha (chiCyc ζ)

/-- The corresponding one-dimensional representation of `E`.-/
noncomputable def VpsiEZeta
    {a : G} (ha : IsPRegular p a)
    (ζ : rootsOfUnity (orderOf a) k) :
    FDRep k (E_subgroup p a) :=
  FDRep.ofLinearChar (psiEZeta p ha ζ)

/--
Evaluation of `psiEZeta` is evaluation of the corresponding cyclic character on
the cyclic component of the element of `E(a)`.
@isnad1 id=eq.1h6v.s10.07d5f958a496 from=translated src=- shape=f496a2c3 vocab=92b23832
-/
lemma psiE_apply_eq_chiCyc_cycPart
    {a : G} (ha : IsPRegular p a)
    (ζ : rootsOfUnity (orderOf a) k)
    (x : E_subgroup p a) :
    (psiEZeta p ha ζ) x
      =
    (chiCyc ζ) (E_to_Cyc p a ha x) := by
  simp [psiEZeta, psiE]

open PElementary in
/--
If the cyclic component of `y ∈ E(a)` is `a ^ n`, then `ψ_ζ(y) = ζ ^ n`.

This isolates the root-of-unity evaluation used in
`sum_psiEZeta_eq_zero_of_not_mem_P`.
@isnad1 id=eq.2h7v.s10.11fa8b6d7e5d from=translated src=- shape=9ae80c63 vocab=78bf3193
-/
lemma psiEZeta_apply_eq_zpow_of_cycPart_eq_zpow
    {G : Type v} [Group G]
    {a : G} (ha : IsPRegular p a)
    (y : E_subgroup p a)
    {n : ℤ}
    (hn : ((E_to_Cyc p a ha y : PElementary.Cyc a) : G) = a ^ n)
    (ζ : rootsOfUnity (orderOf a) k) :
    (psiEZeta p ha ζ) y = ζ ^ n := by
  rw [psiE_apply_eq_chiCyc_cycPart p ha ζ y]
  have h_c_pow :
      E_to_Cyc p a ha y =
        (⟨a, Subgroup.mem_zpowers a⟩ : PElementary.Cyc a) ^ n := by
    ext
    exact hn
  rw [h_c_pow]
  exact chiCyc_apply_generator_zpow (a := a) ζ n

/--
@isnad1 id=mem.2h5v.s9.d39a90a4c667 from=translated src=- shape=97fb1d8d vocab=4b9e258c
-/
lemma psiEZeta_apply_a_inv_mem_Lambda [Finite G]
    {a : G} (ha : IsPRegular p a)
    (ζ : rootsOfUnity (orderOf a) k)
    (haInvMem : a⁻¹ ∈ E_subgroup p a) :
    (((psiEZeta p ha ζ)
        ⟨a⁻¹, haInvMem⟩ : kˣ) : k) ∈ ClassFun.Lambda k G := by

  have hψ :
      (psiEZeta p ha ζ) ⟨a⁻¹, haInvMem⟩
        =
      (chiCyc ζ) (E_to_Cyc p a ha ⟨a⁻¹, haInvMem⟩) :=
    psiE_apply_eq_chiCyc_cycPart
      p ha ζ ⟨a⁻¹, haInvMem⟩

  have hψk :
      (((psiEZeta p ha ζ) ⟨a⁻¹, haInvMem⟩ : kˣ) : k)
        =
      (((chiCyc ζ)
        (E_to_Cyc p a ha ⟨a⁻¹, haInvMem⟩) : kˣ) : k) := Units.val_inj.mpr hψ

  rw [hψk]

  exact chiCyc_apply_mem_Lambda ζ (E_to_Cyc p a ha ⟨a⁻¹, haInvMem⟩)

open PElementary in

/--
@isnad1 id=eq.2h6v.s9.60c6e9655089 from=translated src=- shape=50c917b5 vocab=cd9a2c8d
-/
lemma psiEZeta_apply_eq_one_of_mem_P [Finite G]
    {a : G} (ha : IsPRegular p a)
    (ζ : rootsOfUnity (orderOf a) k)
    (y : E_subgroup p a)
    (hyP : (y : G) ∈ P_of_Z p a) :
    psiEZeta p ha ζ y = 1 := by
  rw [psiE_apply_eq_chiCyc_cycPart p ha ζ y]

  let yG : G := (y : G)
  have hyH : yG ∈ Cyc a ⊔ P_of_Z p a := y.property
  let ySub : ↥(Cyc a ⊔ P_of_Z p a) := ⟨yG, hyH⟩

  have h_c_one_internal :
      ((mulEquivProd (associatedSubgroup ha)).symm ySub).1 = 1 := by
    let H_elem := associatedSubgroup ha
    let iso := mulEquivProd H_elem
    let pElem : H_elem.P := ⟨ySub, hyP⟩
    have h_iso_fwd : iso (1, pElem) = ySub := by
      ext
      exact one_mul yG
    have h_iso_symm := congr_arg iso.symm h_iso_fwd
    rw [MulEquiv.symm_apply_apply] at h_iso_symm
    exact congr_arg Prod.fst h_iso_symm.symm

  have h_c_one : E_to_Cyc p a ha y = 1 := by
    rw [E_to_Cyc_apply]
    exact (MulEquiv.map_eq_one_iff (E_Cyc_equiv p a ha)).mpr h_c_one_internal

  rw [h_c_one]
  exact MonoidHom.map_one (chiCyc ζ)

end CharactersOnE

end PElementary
end BrauerInduction
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
