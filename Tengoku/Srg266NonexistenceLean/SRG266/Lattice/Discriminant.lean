/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.FieldTheory.ChevalleyWarning
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Basic
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Overlattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

section Discriminant

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {Ñ : Submodule ℤ W} {p : ℕ}

theorem mem_one_iff {x : ℚ} : x ∈ (1 : Submodule ℤ ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x :=
  ⟨fun h => by
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
      exact ⟨n, by simpa using hn⟩,
   fun h => by
      obtain ⟨n, hn⟩ := h
      exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩⟩

theorem intCast_mem_one (n : ℤ) : ((n : ℚ)) ∈ (1 : Submodule ℤ ℚ) :=
  mem_one_iff.mpr ⟨n, rfl⟩

theorem mem_one_of_coprime {a b : ℤ} (hab : IsCoprime a b) {x : ℚ}
    (ha : (a : ℚ) * x ∈ (1 : Submodule ℤ ℚ)) (hb : (b : ℚ) * x ∈ (1 : Submodule ℤ ℚ)) :
    x ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨u, v, huv⟩ := hab
  have huv' : ((u : ℚ)) * (a : ℚ) + (v : ℚ) * (b : ℚ) = 1 := by
    have : ((u * a + v * b : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by rw [huv]
    push_cast at this
    linarith
  have hx : x = u • ((a : ℚ) * x) + v • ((b : ℚ) * x) := by
    simp only [zsmul_eq_mul]
    linear_combination (-x) * huv'
  rw [hx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

variable (B p) in

def discNum (y y' : W) : ℤ := ((p : ℚ) * B y y').num

theorem discNum_eq_of_cast {y y' : W} {n : ℤ} (h : (n : ℚ) = (p : ℚ) * B y y') :
    discNum B p y y' = n := by
  simp [discNum, ← h]

theorem discNum_cast {y y' : W} (hy : y ∈ B.dualSubmodule Ñ) (hy' : (p : ℤ) • y' ∈ Ñ) :
    ((discNum B p y y' : ℤ) : ℚ) = (p : ℚ) * B y y' := by
  have h := hy _ hy'
  rw [map_zsmul, zsmul_eq_mul] at h
  push_cast at h
  obtain ⟨n, hn⟩ := mem_one_iff.mp h
  rw [discNum_eq_of_cast (B := B) (p := p) hn, hn]

theorem discNum_symm (hsymm : B.IsSymm) (y y' : W) :
    discNum B p y y' = discNum B p y' y := by
  simp [discNum, hsymm.eq y y']

theorem discNum_add_left {y₁ y₂ y' : W} (h₁ : y₁ ∈ B.dualSubmodule Ñ)
    (h₂ : y₂ ∈ B.dualSubmodule Ñ) (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p (y₁ + y₂) y' = discNum B p y₁ y' + discNum B p y₂ y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast h₁ hy', discNum_cast h₂ hy', map_add, LinearMap.add_apply]
  ring

theorem discNum_zsmul_left (c : ℤ) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p (c • y) y' = c * discNum B p y y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy hy', map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  ring

theorem discNum_add_right {y y₁' y₂' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (h₁ : (p : ℤ) • y₁' ∈ Ñ) (h₂ : (p : ℤ) • y₂' ∈ Ñ) :
    discNum B p y (y₁' + y₂') = discNum B p y y₁' + discNum B p y y₂' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy h₁, discNum_cast hy h₂, map_add]
  ring

theorem discNum_zsmul_right (c : ℤ) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p y (c • y') = c * discNum B p y y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy hy', map_zsmul, zsmul_eq_mul]
  ring

theorem dvd_discNum_of_mem {y y' : W} (hy : y ∈ B.dualSubmodule Ñ) (hy' : y' ∈ Ñ) :
    (p : ℤ) ∣ discNum B p y y' := by
  obtain ⟨n, hn⟩ := mem_one_iff.mp (hy _ hy')
  exact ⟨n, discNum_eq_of_cast (by rw [← hn]; push_cast; ring)⟩

theorem mem_one_of_dvd_discNum (hp : p ≠ 0) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) (h : (p : ℤ) ∣ discNum B p y y') :
    B y y' ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨m, hm⟩ := h
  have hc := discNum_cast hy hy'
  rw [hm] at hc
  push_cast at hc
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp
  exact mem_one_iff.mpr ⟨m, mul_left_cancel₀ hp0 hc⟩

variable (B Ñ p) in

abbrev discGroup : Type _ :=
  torsionPart B Ñ p ⧸ Ñ.comap (torsionPart B Ñ p).subtype

theorem discGroup_nsmul_eq_zero (q : discGroup B Ñ p) : p • q = 0 :=
  quotient_nsmul_eq_zero (fun _ hy => (mem_torsionPart.mp hy).2) q

instance discGroupZModModule : Module (ZMod p) (discGroup B Ñ p) :=
  AddCommGroup.zmodModule (discGroup_nsmul_eq_zero (B := B) (Ñ := Ñ) (p := p))

theorem torsion_mem_dual (y : torsionPart B Ñ p) : (y : W) ∈ B.dualSubmodule Ñ :=
  (mem_torsionPart.mp y.2).1

theorem torsion_zsmul_mem (y : torsionPart B Ñ p) : (p : ℤ) • (y : W) ∈ Ñ :=
  (mem_torsionPart.mp y.2).2

theorem discGroup_mk_eq_zero_iff {y : torsionPart B Ñ p} :
    (Submodule.Quotient.mk y : discGroup B Ñ p) = 0 ↔ (y : W) ∈ Ñ := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact Iff.rfl

theorem discGroup_finite (hnd : B.Nondegenerate) (hN : IsLattice ℚ Ñ) :
    Module.Finite (ZMod p) (discGroup B Ñ p) := by
  classical
  have hDfg : (B.dualSubmodule Ñ).FG := (dual_isLattice B hN hnd).fg
  have : IsNoetherian ℤ (B.dualSubmodule Ñ) :=
    isNoetherian_of_fg_of_noetherian _ hDfg
  have hle : torsionPart B Ñ p ≤ B.dualSubmodule Ñ := torsionPart_le_dual Ñ p
  have hTfg : (torsionPart B Ñ p).FG := by
    have hcomap := IsNoetherian.noetherian
      ((torsionPart B Ñ p).comap (B.dualSubmodule Ñ).subtype)
    have hmap := hcomap.map (B.dualSubmodule Ñ).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at hmap
  have : Module.Finite ℤ (torsionPart B Ñ p) := Module.Finite.iff_fg.mpr hTfg
  have : Module.Finite ℤ (discGroup B Ñ p) := Module.Finite.quotient ℤ _
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := discGroup B Ñ p)
  refine ⟨⟨S, ?_⟩⟩
  refine top_unique fun q _ => ?_
  have hq : q ∈ Submodule.span ℤ (S : Set (discGroup B Ñ p)) := by
    rw [hS]; exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · exact fun y hy => Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · exact fun y z _ _ hy hz => Submodule.add_mem _ hy hz
  · intro a y _ hy
    rw [← Int.cast_smul_eq_zsmul (ZMod p) a y]
    exact Submodule.smul_mem _ _ hy

variable (B Ñ p) in

def torsionBilin :
    torsionPart B Ñ p →ₗ[ℤ] torsionPart B Ñ p →ₗ[ℤ] ZMod p :=
  LinearMap.mk₂ ℤ (fun y y' => ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p))
    (by
      intro y₁ y₂ y'
      rw [show ((y₁ + y₂ : torsionPart B Ñ p) : W) = (y₁ : W) + (y₂ : W) from rfl,
        discNum_add_left (torsion_mem_dual y₁) (torsion_mem_dual y₂) (torsion_zsmul_mem y')]
      push_cast
      ring)
    (by
      intro c y y'
      rw [show ((c • y : torsionPart B Ñ p) : W) = c • (y : W) from rfl,
        discNum_zsmul_left c (torsion_mem_dual y) (torsion_zsmul_mem y')]
      rw [zsmul_eq_mul]
      push_cast
      ring)
    (by
      intro y y₁' y₂'
      rw [show ((y₁' + y₂' : torsionPart B Ñ p) : W) = (y₁' : W) + (y₂' : W) from rfl,
        discNum_add_right (torsion_mem_dual y) (torsion_zsmul_mem y₁') (torsion_zsmul_mem y₂')]
      push_cast
      ring)
    (by
      intro c y y'
      rw [show ((c • y' : torsionPart B Ñ p) : W) = c • (y' : W) from rfl,
        discNum_zsmul_right c (torsion_mem_dual y) (torsion_zsmul_mem y')]
      rw [zsmul_eq_mul]
      push_cast
      ring)

@[simp]
theorem torsionBilin_apply (y y' : torsionPart B Ñ p) :
    torsionBilin B Ñ p y y' = ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

theorem torsionBilin_ker_right (y : torsionPart B Ñ p) :
    Ñ.comap (torsionPart B Ñ p).subtype ≤ LinearMap.ker (torsionBilin B Ñ p y) := by
  intro z hz
  have hzÑ : (z : W) ∈ Ñ := hz
  simp only [LinearMap.mem_ker, torsionBilin_apply]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_discNum_of_mem (torsion_mem_dual y) hzÑ)

variable (B Ñ p) in

def discPairingRight (y : torsionPart B Ñ p) : discGroup B Ñ p →ₗ[ℤ] ZMod p :=
  Submodule.liftQ _ (torsionBilin B Ñ p y) (torsionBilin_ker_right y)

@[simp]
theorem discPairingRight_mk (y y' : torsionPart B Ñ p) :
    discPairingRight B Ñ p y (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

variable (B Ñ p) in

def discPairingAux : torsionPart B Ñ p →ₗ[ℤ] discGroup B Ñ p →ₗ[ℤ] ZMod p where
  toFun := discPairingRight B Ñ p
  map_add' := by
    intro y₁ y₂
    refine LinearMap.ext fun d => ?_
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show torsionBilin B Ñ p (y₁ + y₂) y' =
      torsionBilin B Ñ p y₁ y' + torsionBilin B Ñ p y₂ y'
    rw [map_add, LinearMap.add_apply]
  map_smul' := by
    intro c y
    refine LinearMap.ext fun d => ?_
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show torsionBilin B Ñ p (c • y) y' = c • torsionBilin B Ñ p y y'
    rw [map_smul, LinearMap.smul_apply]

theorem discPairingAux_ker (hsymm : B.IsSymm) :
    Ñ.comap (torsionPart B Ñ p).subtype ≤ LinearMap.ker (discPairingAux B Ñ p) := by
  intro z hz
  have hzÑ : (z : W) ∈ Ñ := hz
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun d => ?_)
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
  show ((discNum B p (z : W) (y' : W) : ℤ) : ZMod p) = 0
  rw [discNum_symm hsymm]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_discNum_of_mem (torsion_mem_dual y') hzÑ)

variable (B Ñ p) in

def discPairingInt (hsymm : B.IsSymm) :
    discGroup B Ñ p →ₗ[ℤ] discGroup B Ñ p →ₗ[ℤ] ZMod p :=
  Submodule.liftQ _ (discPairingAux B Ñ p) (discPairingAux_ker hsymm)

@[simp]
theorem discPairingInt_mk (hsymm : B.IsSymm) (y y' : torsionPart B Ñ p) :
    discPairingInt B Ñ p hsymm (Submodule.Quotient.mk y) (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

variable (B Ñ p) in

def discPairing (hsymm : B.IsSymm) : LinearMap.BilinForm (ZMod p) (discGroup B Ñ p) where
  toFun d :=
    { toFun := fun d' => discPairingInt B Ñ p hsymm d d'
      map_add' := fun d₁ d₂ => by simp
      map_smul' := fun c d' => by
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
        simp only [RingHom.id_apply]
        rw [Int.cast_smul_eq_zsmul (ZMod p) k d', map_smul,
          Int.cast_smul_eq_zsmul (ZMod p) k _] }
  map_add' := by
    intro d₁ d₂
    refine LinearMap.ext fun d' => ?_
    simp
  map_smul' := by
    intro c d
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    refine LinearMap.ext fun d' => ?_
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Int.cast_smul_eq_zsmul (ZMod p) k d, map_smul, LinearMap.smul_apply,
      Int.cast_smul_eq_zsmul (ZMod p) k _]

@[simp]
theorem discPairing_mk (hsymm : B.IsSymm) (y y' : torsionPart B Ñ p) :
    discPairing B Ñ p hsymm (Submodule.Quotient.mk y) (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

theorem discPairing_isSymm (hsymm : B.IsSymm) : (discPairing B Ñ p hsymm).IsSymm := by
  refine ⟨fun d d' => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d'
  rw [discPairing_mk, discPairing_mk, discNum_symm hsymm]

theorem discPairing_separatingLeft (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hp : p ≠ 0) {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    (discPairing B Ñ p hsymm).SeparatingLeft := by
  intro d hd
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  rw [discGroup_mk_eq_zero_iff]
  have hyd : (y : W) ∈ B.dualSubmodule Ñ := torsion_mem_dual y
  have hcop : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hpq)

  have hTp : ∀ z ∈ torsionPart B Ñ p, B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
    intro z hz
    have hz0 := hd (Submodule.Quotient.mk ⟨z, hz⟩)
    rw [discPairing_mk] at hz0
    exact mem_one_of_dvd_discNum hp hyd (mem_torsionPart.mp hz).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0)

  have hTq : ∀ z ∈ torsionPart B Ñ q, B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
    intro z hz
    have hzd : z ∈ B.dualSubmodule Ñ := (mem_torsionPart.mp hz).1
    have hqz : (q : ℤ) • z ∈ Ñ := (mem_torsionPart.mp hz).2
    have hpy : (p : ℤ) • (y : W) ∈ Ñ := torsion_zsmul_mem y
    have hp' : ((p : ℚ)) * B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
      have h := hzd _ hpy
      rw [map_zsmul, zsmul_eq_mul] at h
      push_cast at h
      rwa [hsymm.eq z (y : W)] at h
    have hq' : ((q : ℚ)) * B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
      have h := hyd _ hqz
      rw [map_zsmul, zsmul_eq_mul] at h
      push_cast at h
      exact h
    exact mem_one_of_coprime hcop (by exact_mod_cast hp') (by exact_mod_cast hq')

  have hdd : (y : W) ∈ B.dualSubmodule (B.dualSubmodule Ñ) := by
    intro z hz
    rw [hsplit] at hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add]
    exact Submodule.add_mem _ (hTp z₁ hz₁) (hTq z₂ hz₂)
  rwa [dual_dual B hN hnd hsymm] at hdd

theorem discPairing_nondegenerate (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hp : p ≠ 0) {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    (discPairing B Ñ p hsymm).Nondegenerate :=
  ((discPairing_isSymm hsymm).isRefl.nondegenerate_iff_separatingLeft).mpr
    (discPairing_separatingLeft hsymm hnd hN hp hpq hsplit)

private theorem bilin_sum_sum {n : ℕ} (a : Fin n → ℤ) (y : Fin n → W) :
    B (∑ i, a i • y i) (∑ j, a j • y j) =
      ∑ i, ∑ j, ((a i * a j : ℤ) : ℚ) * B (y i) (y j) := by
  have key : ∀ w : W, B w (∑ j, a j • y j) = ∑ j, ((a j : ℤ) : ℚ) * B w (y j) := by
    intro w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
  have key₂ : ∀ w : W, B (∑ i, a i • y i) w = ∑ i, ((a i : ℤ) : ℚ) * B (y i) w := by
    intro w
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  rw [key]
  simp_rw [key₂, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem disc_dim_le_two [hp : Fact p.Prime] (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hmax : IsMaximalIntegral B Ñ) :
    Module.finrank (ZMod p) (discGroup B Ñ p) ≤ 2 := by
  classical
  have : NeZero p := ⟨hp.out.pos.ne'⟩
  have : Module.Finite (ZMod p) (discGroup B Ñ p) := discGroup_finite hnd hN
  by_contra hcon

  have h3 : 3 ≤ Module.finrank (ZMod p) (discGroup B Ñ p) := Nat.lt_of_not_le hcon
  set b := Module.finBasis (ZMod p) (discGroup B Ñ p) with hb
  set f : Fin 3 → Fin (Module.finrank (ZMod p) (discGroup B Ñ p)) :=
    fun i => ⟨i.1, lt_of_lt_of_le i.2 h3⟩ with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval := congrArg Fin.val hij
    exact Fin.ext hval
  have hv : LinearIndependent (ZMod p) (fun i => b (f i)) :=
    b.linearIndependent.comp f hfinj

  choose y hy using fun i : Fin 3 => Submodule.Quotient.mk_surjective
    (Ñ.comap (torsionPart B Ñ p).subtype) (b (f i))
  set c : Fin 3 → Fin 3 → ZMod p :=
    fun i j => ((discNum B p (y i : W) (y j : W) : ℤ) : ZMod p) with hc

  set Q : MvPolynomial (Fin 3) (ZMod p) :=
    ∑ i, ∑ j, MvPolynomial.C (c i j) * MvPolynomial.X i * MvPolynomial.X j with hQ
  have hdeg : Q.totalDegree < Fintype.card (Fin 3) := by
    have h2 : Q.totalDegree ≤ 2 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C (c i j) * MvPolynomial.X i).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      have h2 : (MvPolynomial.X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree ≤ 1 := by
        simp [MvPolynomial.totalDegree_X]
      omega
    simpa using Nat.lt_of_le_of_lt h2 (by norm_num)
  have heval : ∀ x : Fin 3 → ZMod p,
      MvPolynomial.eval x Q = ∑ i, ∑ j, c i j * x i * x j := by
    intro x
    simp [hQ]
  have hzero : MvPolynomial.eval (0 : Fin 3 → ZMod p) Q = 0 := by
    rw [heval]
    simp
  have hcw := char_dvd_card_solutions (K := ZMod p) (σ := Fin 3) p hdeg
  have hpos : 0 < Fintype.card { x : Fin 3 → ZMod p // MvPolynomial.eval x Q = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → ZMod p // MvPolynomial.eval x Q = 0 } := by
    have hle := Nat.le_of_dvd hpos hcw
    have := hp.out.two_le
    omega
  obtain ⟨⟨x, hx⟩, hxne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, hzero⟩
  have hx0 : x ≠ 0 := fun h => hxne (Subtype.ext h)

  choose a ha using fun i : Fin 3 => ZMod.intCast_surjective (n := p) (x i)
  set z : torsionPart B Ñ p := ∑ i, a i • y i with hz
  have hzcoe : (z : W) = ∑ i, a i • (y i : W) := by
    rw [hz]
    push_cast
    rfl

  have hznot : (z : W) ∉ Ñ := by
    intro hmem
    have hmk : (Submodule.Quotient.mk z : discGroup B Ñ p) = 0 :=
      discGroup_mk_eq_zero_iff.mpr hmem
    have hsum : ∑ i, x i • b (f i) = 0 := by
      have hexp : (Submodule.Quotient.mk z : discGroup B Ñ p) = ∑ i, x i • b (f i) := by
        have hmkq : (Submodule.Quotient.mk z : discGroup B Ñ p) =
            (Ñ.comap (torsionPart B Ñ p).subtype).mkQ z := rfl
        rw [hmkq, hz, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        show a i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p) = x i • b (f i)
        rw [hy i, ← ha i, Int.cast_smul_eq_zsmul]
      rw [hexp] at hmk
      exact hmk
    have := Fintype.linearIndependent_iff.mp hv x hsum
    exact hx0 (funext this)

  have hzz : B (z : W) (z : W) ∈ (1 : Submodule ℤ ℚ) := by
    set N : ℤ := ∑ i, ∑ j, a i * a j * discNum B p (y i : W) (y j : W) with hN'
    have hNcast : ((N : ℤ) : ℚ) = (p : ℚ) * B (z : W) (z : W) := by
      rw [hzcoe, bilin_sum_sum, hN']
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [discNum_cast (torsion_mem_dual (y i)) (torsion_zsmul_mem (y j))]
      ring
    have hx' : ∑ i, ∑ j, c i j * x i * x j = 0 := by rw [← heval x]; exact hx
    have hNdvd : (p : ℤ) ∣ N := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
      rw [hN']
      push_cast
      calc (∑ i, ∑ j, ((a i : ZMod p)) * ((a j : ZMod p)) *
              ((discNum B p (y i : W) (y j : W) : ℤ) : ZMod p))
          = ∑ i, ∑ j, c i j * x i * x j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hc, ha i, ha j]
            ring
        _ = 0 := hx'
    obtain ⟨k, hk⟩ := hNdvd
    have hp0 : ((p : ℚ)) ≠ 0 := by
      exact_mod_cast (NeZero.ne p)
    refine mem_one_iff.mpr ⟨k, ?_⟩
    have : ((p : ℚ)) * (k : ℚ) = (p : ℚ) * B (z : W) (z : W) := by
      rw [← hNcast, hk]
      push_cast
      ring
    exact mul_left_cancel₀ hp0 this
  have hzv : ∀ v ∈ Ñ, B (z : W) v ∈ (1 : Submodule ℤ ℚ) := fun v hv => torsion_mem_dual z v hv
  have hsup := hmax.maximal (Ñ ⊔ Submodule.span ℤ {(z : W)}) le_sup_left
    (isIntegral_sup_span_singleton B hsymm hmax.integral hzv hzz)
  have hmem : (z : W) ∈ Ñ ⊔ Submodule.span ℤ {(z : W)} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [hsup] at hmem
  exact hznot hmem

variable (B Ñ p) in

structure GlueBasis where

  rank : ℕ

  rank_le : rank ≤ 2

  vec : Fin rank → W

  mem : ∀ i, vec i ∈ torsionPart B Ñ p

  spans : torsionPart B Ñ p = Ñ ⊔ Submodule.span ℤ (Set.range vec)

  ortho : ∀ i j, i ≠ j → B (vec i) (vec j) ∈ (1 : Submodule ℤ ℚ)

  diag : ∀ i, ∃ m : ℤ, ¬ ((p : ℤ) ∣ m) ∧ ((p : ℚ)) * B (vec i) (vec i) = (m : ℚ)

  indep : ∀ c : Fin rank → ℤ, (∑ i, c i • vec i) ∈ Ñ → ∀ i, (p : ℤ) ∣ c i

theorem GlueBasis.exists_unit_diag [Fact p.Prime] (S : GlueBasis B Ñ p) (i : Fin S.rank) :
    ∃ (u : (ZMod p)ˣ) (m : ℤ), ((m : ZMod p)) = (u : ZMod p) ∧
      ((p : ℚ)) * B (S.vec i) (S.vec i) = (m : ℚ) := by
  obtain ⟨m, hdvd, hm⟩ := S.diag i
  have hne : ((m : ZMod p)) ≠ 0 := fun h =>
    hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  exact ⟨(isUnit_iff_ne_zero.mpr hne).unit, m,
    ((isUnit_iff_ne_zero.mpr hne).unit_spec).symm, hm⟩

theorem exists_orthogonal_glue_basis [hp : Fact p.Prime] (hp2 : p ≠ 2) (hsymm : B.IsSymm)
    (hnd : B.Nondegenerate) (hN : IsLattice ℚ Ñ) (hmax : IsMaximalIntegral B Ñ)
    {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    Nonempty (GlueBasis B Ñ p) := by
  classical
  have : NeZero p := ⟨hp.out.pos.ne'⟩
  have : Module.Finite (ZMod p) (discGroup B Ñ p) := discGroup_finite hnd hN
  have : Invertible (2 : ZMod p) := by
    refine invertibleOfNonzero ?_
    intro h2
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp hcast
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd)
  have hsep : (discPairing B Ñ p hsymm).SeparatingLeft :=
    discPairing_separatingLeft hsymm hnd hN (NeZero.ne p) hpq hsplit
  have hsymmD : (discPairing B Ñ p hsymm).IsSymm := discPairing_isSymm hsymm
  obtain ⟨b, hortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hsymmD)
  have hdiag : ∀ i, discPairing B Ñ p hsymm (b i) (b i) ≠ 0 := fun i =>
    hortho.not_isOrtho_basis_self_of_separatingLeft hsep i
  choose y hy using fun i => Submodule.Quotient.mk_surjective
    (Ñ.comap (torsionPart B Ñ p).subtype) (b i)
  refine ⟨{
    rank := Module.finrank (ZMod p) (discGroup B Ñ p)
    rank_le := disc_dim_le_two hsymm hnd hN hmax
    vec := fun i => (y i : W)
    mem := fun i => (y i).2
    spans := ?_
    ortho := ?_
    diag := ?_
    indep := ?_ }⟩
  ·
    refine le_antisymm ?_ ?_
    · intro w hw
      set d : discGroup B Ñ p := Submodule.Quotient.mk ⟨w, hw⟩ with hd
      choose k hk using fun i => ZMod.intCast_surjective (n := p) (b.repr d i)
      have hrepr : d = ∑ i, (k i) • b i := by
        conv_lhs => rw [← b.sum_repr d]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hk i, Int.cast_smul_eq_zsmul]
      set t : torsionPart B Ñ p := ∑ i, k i • y i with ht
      have hmk : (Submodule.Quotient.mk t : discGroup B Ñ p) = d := by
        have hmkq : (Submodule.Quotient.mk t : discGroup B Ñ p) =
            (Ñ.comap (torsionPart B Ñ p).subtype).mkQ t := rfl
        rw [hmkq, ht, map_sum, hrepr]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        show k i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p) = k i • b i
        rw [hy i]
      have hsub : w - (t : W) ∈ Ñ := by
        have hzero : (Submodule.Quotient.mk (⟨w, hw⟩ - t) : discGroup B Ñ p) = 0 := by
          have hmkq : (Submodule.Quotient.mk (⟨w, hw⟩ - t) : discGroup B Ñ p) =
              (Ñ.comap (torsionPart B Ñ p).subtype).mkQ (⟨w, hw⟩ - t) := rfl
          rw [hmkq, map_sub]
          show (Submodule.Quotient.mk ⟨w, hw⟩ : discGroup B Ñ p) -
            (Submodule.Quotient.mk t : discGroup B Ñ p) = 0
          rw [hmk, hd, sub_self]
        have hmem₀ := discGroup_mk_eq_zero_iff.mp hzero
        simpa using hmem₀
      have htmem : (t : W) ∈ Submodule.span ℤ (Set.range fun i => (y i : W)) := by
        rw [ht]
        push_cast
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span ⟨i, rfl⟩
      have hdecomp : w = (w - (t : W)) + (t : W) := by abel
      rw [hdecomp]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hsub)
        (Submodule.mem_sup_right htmem)
    · refine sup_le (le_torsionPart hmax.integral p) ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (y i).2
  ·
    intro i j hij
    have h0 : discPairing B Ñ p hsymm (b i) (b j) = 0 := hortho hij
    rw [← hy i, ← hy j, discPairing_mk] at h0
    exact mem_one_of_dvd_discNum (NeZero.ne p) (torsion_mem_dual (y i))
      (torsion_zsmul_mem (y j)) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  ·
    intro i
    refine ⟨discNum B p (y i : W) (y i : W), ?_, ?_⟩
    · intro hdvd
      refine hdiag i ?_
      rw [← hy i, discPairing_mk]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    · exact (discNum_cast (torsion_mem_dual (y i)) (torsion_zsmul_mem (y i))).symm
  ·
    intro cf hmem i
    have hsum : ∑ i, ((cf i : ZMod p)) • b i = 0 := by
      have hmk : ((Ñ.comap (torsionPart B Ñ p).subtype).mkQ (∑ i, cf i • y i)) = 0 := by
        refine discGroup_mk_eq_zero_iff.mpr ?_
        have hco : ((∑ i, cf i • y i : torsionPart B Ñ p) : W) = ∑ i, cf i • (y i : W) := by
          push_cast
          rfl
        rw [hco]
        exact hmem
      rw [map_sum] at hmk
      rw [← hmk]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      show ((cf i : ZMod p)) • b i = cf i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p)
      rw [hy i, Int.cast_smul_eq_zsmul]
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => ((cf i : ZMod p))) hsum i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

theorem dual_eq_sup_span_glue {q : ℕ} (S : GlueBasis B Ñ p) (T : GlueBasis B Ñ q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    B.dualSubmodule Ñ = Ñ ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec) := by
  rw [hsplit, S.spans, T.spans, Submodule.span_union, sup_sup_sup_comm, sup_idem]

end Discriminant

end SRG266.Lattice
