/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Defs
import Tengoku.Seed.Algebra.Ring.Parity
import Tengoku.Seed.RingTheory.Length

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brick G2XSK2 (route S, K2): the tame symbol of a discrete valuation ring

For a 1-dimensional noetherian local domain `B` with residue field `κ` and fraction field `K`,
Stacks (Chow Homology, "Symbols") defines `d_B(a, b) ∈ κ^×` for `a, b ∈ K^×` via the determinant
of a periodic complex on finite-length modules.  When `B` is a DVR this is the classical tame
symbol

  `d_B(a, b) = (-1)^{ord a · ord b} · a^{ord b} / b^{ord a}  mod 𝔪`.

This file is the DVR case, on pure Mathlib (the general case needs brick K1, the determinant of
finite-length modules, which was not yet published when this file was written).

## Main definitions (namespace `RiemannRoch.SingularTodd.TameSymbolT2`)
`R` is a DVR, `K` a fraction field of `R`, `κ = IsLocalRing.ResidueField R`.
* `ord R : Kˣ → ℤ`, the normalized valuation (independent of choices: `ord_eq_of_eq_smul_zpow`);
  `ord_mul`, `ord_inv`, `ord_one`, `ord_zpow`, `addVal_eq_ord` (compatibility with Mathlib's
  `addVal`) and `length_quotient_span_eq_ord` (`ord r = ℓ_R(R / r)`, the Stacks normalisation).
* `unitPart R : Kˣ → Rˣ`, the unit part w.r.t. the fixed uniformizer `unif R`.
* `tameUnit R a b : Rˣ` with `algebraMap_tameUnit`:
  `algebraMap R K (tameUnit R a b) = (-1)^(ord a * ord b) * a^(ord b) / b^(ord a)`.
* `tame R a b : (ResidueField R)ˣ`, its residue.

## Main results
* `tame_mul_left`, `tame_mul_right`: bimultiplicativity.
* `tame_mul_tame_swap`: `d(a, b) · d(b, a) = 1`.
* `tame_self`: `d(a, a) = (-1)^{ord a}`.
* `tame_of_ord_eq_zero`: for a unit `a` of `R`, `d(a, b) = ā^{ord b}`.
* `tame_eq_residue`: the classical formula modulo `𝔪`: for any `c : R` with
  `algebraMap c = (-1)^(ord a * ord b) * a^(ord b) / b^(ord a)`, `d(a, b) = residue c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RiemannRoch.SingularTodd.TameSymbolT2

open IsDiscreteValuationRing IsLocalRing

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem algebraMap_ne_zero_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    algebraMap R K ϖ ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  exact hϖ.ne_zero

/-- Uniqueness of the decomposition `x = u • ϖ ^ n` in the fraction field of a DVR.-/
theorem smul_zpow_inj {ϖ : R} (hϖ : Irreducible ϖ) {n m : ℤ} {u v : Rˣ}
    (h : u • algebraMap R K ϖ ^ n = v • algebraMap R K ϖ ^ m) : n = m ∧ u = v := by
  have hπ := algebraMap_ne_zero_of_irreducible (K := K) hϖ
  set N : ℕ := (-n).toNat + (-m).toNat with hN
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = n + N := ⟨(n + N).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = m + N := ⟨(m + N).toNat, Int.toNat_of_nonneg (by omega)⟩
  have e : ∀ (w : Rˣ) (k : ℤ) (c : ℕ), (c : ℤ) = k + N →
      algebraMap R K ((w : R) * ϖ ^ c) =
        (w • algebraMap R K ϖ ^ k) * algebraMap R K ϖ ^ (N : ℤ) := by
    intro w k c hc
    rw [Units.smul_def, Algebra.smul_def, mul_assoc, ← zpow_add₀ hπ, ← hc, map_mul, map_pow,
      zpow_natCast]
  have h' : algebraMap R K ((u : R) * ϖ ^ a) = algebraMap R K ((v : R) * ϖ ^ b) := by
    rw [e u n a ha, e v m b hb, h]
  have h'' := IsFractionRing.injective R K h'
  have hab := unit_mul_pow_congr_pow hϖ hϖ u v a b h''
  subst hab
  exact ⟨by omega, unit_mul_pow_congr_unit hϖ u v a a h''⟩

variable (R) in
/-- A fixed uniformizer of the DVR `R`.-/
noncomputable def unif : R := (exists_irreducible R).choose

variable (R) in
theorem irreducible_unif : Irreducible (unif R) := (exists_irreducible R).choose_spec

theorem exists_smul_zpow_unif (x : Kˣ) :
    ∃ (n : ℤ) (u : Rˣ), (x : K) = u • algebraMap R K (unif R) ^ n :=
  exists_units_eq_smul_zpow_of_irreducible (irreducible_unif R) x.ne_zero

variable (R) in
/-- The normalized valuation `ord : Kˣ → ℤ` of the DVR `R`.-/
noncomputable def ord (x : Kˣ) : ℤ := (exists_smul_zpow_unif (R := R) x).choose

variable (R) in
/-- The unit part of `x : Kˣ` with respect to the fixed uniformizer `unif R`.-/
noncomputable def unitPart (x : Kˣ) : Rˣ := (exists_smul_zpow_unif (R := R) x).choose_spec.choose

variable (R) in
theorem coe_eq_unitPart_smul (x : Kˣ) :
    (x : K) = unitPart R x • algebraMap R K (unif R) ^ ord R x :=
  (exists_smul_zpow_unif (R := R) x).choose_spec.choose_spec

/-- Characterisation of `ord` and `unitPart` by a decomposition w.r.t. `unif R`.-/
theorem ord_unitPart_eq {x : Kˣ} {n : ℤ} {u : Rˣ}
    (h : (x : K) = u • algebraMap R K (unif R) ^ n) : ord R x = n ∧ unitPart R x = u :=
  smul_zpow_inj (irreducible_unif R) ((coe_eq_unitPart_smul R x).symm.trans h)

theorem algebraMap_units_zpow (v : Rˣ) (k : ℤ) :
    algebraMap R K ((v ^ k : Rˣ) : R) = algebraMap R K (v : R) ^ k := by
  have := congrArg Units.val (map_zpow (Units.map (algebraMap R K : R →* K)) v k)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at this
  exact this

/-- `ord` can be computed with respect to **any** uniformizer.-/
theorem ord_eq_of_eq_smul_zpow {ϖ : R} (hϖ : Irreducible ϖ) {x : Kˣ} {n : ℤ} {u : Rˣ}
    (h : (x : K) = u • algebraMap R K ϖ ^ n) : ord R x = n := by
  obtain ⟨w, hw⟩ := associated_of_irreducible R hϖ (irreducible_unif R)
  -- `ϖ * w = unif`, so `ϖ = w⁻¹ * unif`
  have hπ0 := algebraMap_ne_zero_of_irreducible (K := K) (irreducible_unif R)
  have hϖ' : algebraMap R K ϖ = algebraMap R K ((w⁻¹ : Rˣ) : R) * algebraMap R K (unif R) := by
    rw [← hw, ← map_mul, mul_left_comm, Units.inv_mul, mul_one]
  refine (ord_unitPart_eq (u := u * (w⁻¹) ^ n) ?_).1
  rw [h, hϖ', mul_zpow, ← algebraMap_units_zpow, Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def,
    Units.val_mul, map_mul, mul_assoc]

theorem smul_zpow_mul_smul_zpow (π : K) (hπ : π ≠ 0) (u v : Rˣ) (n m : ℤ) :
    (u • π ^ n) * (v • π ^ m) = (u * v) • π ^ (n + m) := by
  rw [Units.smul_def, Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def,
    Algebra.smul_def, zpow_add₀ hπ, Units.val_mul, map_mul]
  ring

theorem ord_unitPart_mul (x y : Kˣ) :
    ord R (x * y) = ord R x + ord R y ∧ unitPart R (x * y) = unitPart R x * unitPart R y := by
  apply ord_unitPart_eq
  rw [Units.val_mul, coe_eq_unitPart_smul R x, coe_eq_unitPart_smul R y,
    smul_zpow_mul_smul_zpow _ (algebraMap_ne_zero_of_irreducible (irreducible_unif R))]

theorem ord_mul (x y : Kˣ) : ord R (x * y) = ord R x + ord R y := (ord_unitPart_mul x y).1

theorem unitPart_mul (x y : Kˣ) : unitPart R (x * y) = unitPart R x * unitPart R y :=
  (ord_unitPart_mul x y).2

theorem ord_unitPart_one : ord R (1 : Kˣ) = 0 ∧ unitPart R (1 : Kˣ) = 1 := by
  apply ord_unitPart_eq
  simp

theorem ord_one : ord R (1 : Kˣ) = 0 := (ord_unitPart_one (K := K)).1

theorem unitPart_one : unitPart R (1 : Kˣ) = 1 := (ord_unitPart_one (K := K)).2

theorem ord_inv (x : Kˣ) : ord R x⁻¹ = - ord R x := by
  have := ord_mul (R := R) x x⁻¹
  rw [mul_inv_cancel, ord_one] at this
  omega

theorem unitPart_inv (x : Kˣ) : unitPart R x⁻¹ = (unitPart R x)⁻¹ := by
  have := unitPart_mul (R := R) x x⁻¹
  rw [mul_inv_cancel, unitPart_one] at this
  exact (eq_inv_of_mul_eq_one_right this.symm)

theorem ord_zpow (x : Kˣ) (k : ℤ) : ord R (x ^ k) = k * ord R x := by
  let f : Kˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (ord R y)
      map_one' := by simp [ord_one]
      map_mul' := fun y z => by simp [ord_mul] }
  have := map_zpow f x k
  simpa [f, mul_comm] using congrArg Multiplicative.toAdd this

theorem unitPart_zpow (x : Kˣ) (k : ℤ) : unitPart R (x ^ k) = unitPart R x ^ k := by
  let f : Kˣ →* Rˣ :=
    { toFun := fun y => unitPart R y
      map_one' := unitPart_one
      map_mul' := unitPart_mul }
  exact map_zpow f x k

/-- Compatibility of `ord` with Mathlib's `addVal` on `R`.-/
theorem addVal_eq_ord {r : R} (hr : r ≠ 0) (x : Kˣ) (hx : (x : K) = algebraMap R K r) :
    0 ≤ ord R x ∧ addVal R r = ((ord R x).toNat : ℕ∞) := by
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible hr (irreducible_unif R)
  have hord : ord R x = k := by
    apply (ord_unitPart_eq (u := u) _).1
    rw [hx, hk, zpow_natCast, Units.smul_def, Algebra.smul_def, map_mul, map_pow]
  refine ⟨by omega, ?_⟩
  rw [hord, Int.toNat_natCast, addVal_def r u (irreducible_unif R) k hk]

/-- `ord` of an element of `R` is the length of the quotient, `ord r = ℓ_R(R / r)`.-/
theorem length_quotient_span_eq_ord {r : R} (hr : r ≠ 0) (x : Kˣ)
    (hx : (x : K) = algebraMap R K r) :
    Module.length R (R ⧸ Ideal.span {r}) = ((ord R x).toNat : ℕ∞) := by
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible hr (irreducible_unif R)
  have hord : ord R x = k := by
    apply (ord_unitPart_eq (u := u) _).1
    rw [hx, hk, zpow_natCast, Units.smul_def, Algebra.smul_def, map_mul, map_pow]
  have hspan : Ideal.span {r} = maximalIdeal R ^ k := by
    rw [hk, Ideal.span_singleton_mul_left_unit u.isUnit, (irreducible_unif R).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  rw [hspan, length_quotient_pow_maximalIdeal, hord, Int.toNat_natCast]

end Valuation

section Tame

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The tame symbol before reduction: a unit of `R`,
`(-1)^(ord a * ord b) * u_a ^ (ord b) * u_b ^ (-ord a)`.-/
noncomputable def tameUnit (a b : Kˣ) : Rˣ :=
  (-1) ^ (ord R a * ord R b) * unitPart R a ^ ord R b * (unitPart R b ^ ord R a)⁻¹

/-- The tame symbol `d(a, b) ∈ κ^×` of the DVR `R`.-/
noncomputable def tame (a b : Kˣ) : (ResidueField R)ˣ :=
  Units.map (residue R : R →* ResidueField R) (tameUnit R a b)

variable {R}

/-- **The classical formula**: `tameUnit a b = (-1)^(ord a · ord b) a^(ord b) / b^(ord a)` in `K`;
in particular `tameUnit` (hence `tame`) does not depend on the chosen uniformizer.-/
theorem algebraMap_tameUnit (a b : Kˣ) :
    algebraMap R K (tameUnit R a b : R) =
      (-1) ^ (ord R a * ord R b) * (a : K) ^ ord R b / (b : K) ^ ord R a := by
  have hπ := algebraMap_ne_zero_of_irreducible (K := K) (irreducible_unif R)
  have hub : algebraMap R K (unitPart R b : R) ≠ 0 :=
    ((unitPart R b).isUnit.map (algebraMap R K)).ne_zero
  have ha := coe_eq_unitPart_smul R a
  have hb := coe_eq_unitPart_smul R b
  rw [Units.smul_def, Algebra.smul_def] at ha hb
  rw [ha, hb, tameUnit, Units.val_mul, Units.val_mul, map_mul, map_mul, map_units_inv,
    algebraMap_units_zpow, algebraMap_units_zpow, algebraMap_units_zpow,
    Units.val_neg, Units.val_one, map_neg, map_one]
  generalize ord R a = n at *
  generalize ord R b = m at *
  generalize algebraMap R K (unif R) = π at *
  generalize algebraMap R K (unitPart R a : R) = ua at *
  generalize algebraMap R K (unitPart R b : R) = ub at *
  have hp : π ^ (n * m) ≠ 0 := zpow_ne_zero _ hπ
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm m n, mul_div_assoc,
    mul_div_mul_right _ _ hp, div_eq_mul_inv, mul_assoc]

theorem tame_eq_residue_tameUnit (a b : Kˣ) :
    (tame R a b : ResidueField R) = residue R (tameUnit R a b : R) := rfl

/-- `tame` modulo `𝔪`: any `c : R` representing the classical expression reduces to `tame`.-/
theorem tame_eq_residue (a b : Kˣ) (c : R)
    (hc : algebraMap R K c = (-1) ^ (ord R a * ord R b) * (a : K) ^ ord R b / (b : K) ^ ord R a) :
    (tame R a b : ResidueField R) = residue R c := by
  rw [tame_eq_residue_tameUnit]
  congr 1
  apply IsFractionRing.injective R K
  rw [hc, algebraMap_tameUnit]

theorem tameUnit_mul_left (a a' b : Kˣ) :
    tameUnit R (a * a') b = tameUnit R a b * tameUnit R a' b := by
  simp only [tameUnit, ord_mul, unitPart_mul, add_mul, zpow_add, mul_zpow, mul_inv]
  simp only [mul_left_comm, mul_assoc]

theorem tameUnit_mul_tameUnit_swap (a b : Kˣ) : tameUnit R a b * tameUnit R b a = 1 := by
  simp only [tameUnit]
  rw [mul_comm (ord R b) (ord R a)]
  have h1 : ((-1 : Rˣ) ^ (ord R a * ord R b)) * (-1) ^ (ord R a * ord R b) = 1 := by
    rw [← zpow_add]
    exact Even.neg_one_zpow ⟨_, rfl⟩
  calc _ = ((-1 : Rˣ) ^ (ord R a * ord R b) * (-1) ^ (ord R a * ord R b)) *
        (unitPart R a ^ ord R b * (unitPart R a ^ ord R b)⁻¹) *
        (unitPart R b ^ ord R a * (unitPart R b ^ ord R a)⁻¹) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by rw [h1, mul_inv_cancel, mul_inv_cancel, one_mul, one_mul]

theorem tameUnit_swap (a b : Kˣ) : tameUnit R b a = (tameUnit R a b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (tameUnit_mul_tameUnit_swap a b)

theorem tameUnit_mul_right (a b b' : Kˣ) :
    tameUnit R a (b * b') = tameUnit R a b * tameUnit R a b' := by
  rw [tameUnit_swap, tameUnit_mul_left, mul_inv, ← tameUnit_swap, ← tameUnit_swap]

theorem neg_one_zpow_mul_self {G : Type*} [Monoid G] [HasDistribNeg G] (u : Gˣ) (n : ℤ)
    (hu : u = -1) : u ^ (n * n) = u ^ n := by
  subst hu
  rcases Int.even_or_odd n with h | h
  · rw [Even.neg_one_zpow h, Even.neg_one_zpow (h.mul_right n)]
  · rw [Odd.neg_one_zpow h, Odd.neg_one_zpow (h.mul h)]

theorem tameUnit_self (a : Kˣ) : tameUnit R a a = (-1) ^ ord R a := by
  rw [tameUnit, mul_inv_cancel_right, neg_one_zpow_mul_self _ _ rfl]

theorem tameUnit_of_ord_eq_zero (a b : Kˣ) (ha : ord R a = 0) :
    tameUnit R a b = unitPart R a ^ ord R b := by
  rw [tameUnit, ha, zero_mul, zpow_zero, zpow_zero, inv_one, one_mul, mul_one]

theorem algebraMap_unitPart_of_ord_eq_zero (a : Kˣ) (ha : ord R a = 0) :
    algebraMap R K (unitPart R a : R) = a := by
  rw [coe_eq_unitPart_smul R a, ha, zpow_zero, Units.smul_def, Algebra.smul_def, mul_one]

/-! ### The symbol in `κ^×` -/

theorem tame_mul_left (a a' b : Kˣ) : tame R (a * a') b = tame R a b * tame R a' b := by
  rw [tame, tameUnit_mul_left, map_mul]; rfl

theorem tame_mul_right (a b b' : Kˣ) : tame R a (b * b') = tame R a b * tame R a b' := by
  rw [tame, tameUnit_mul_right, map_mul]; rfl

/-- `d(a, b) · d(b, a) = 1`.-/
theorem tame_mul_tame_swap (a b : Kˣ) : tame R a b * tame R b a = 1 := by
  rw [tame, tame, ← map_mul, tameUnit_mul_tameUnit_swap, map_one]

theorem tame_swap (a b : Kˣ) : tame R b a = (tame R a b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (tame_mul_tame_swap a b)

/-- `d(a, a) = (-1)^{ord a}`.-/
theorem tame_self (a : Kˣ) : tame R a a = (-1) ^ ord R a := by
  rw [tame, tameUnit_self, map_zpow]
  congr 1

/-- For a unit `a` of `R` (`ord a = 0`), `d(a, b) = ā ^ {ord b}`.-/
theorem tame_of_ord_eq_zero (a b : Kˣ) (ha : ord R a = 0) :
    tame R a b = Units.map (residue R : R →* ResidueField R) (unitPart R a) ^ ord R b := by
  rw [tame, tameUnit_of_ord_eq_zero a b ha, map_zpow]

/-- If `a, b` are both units of `R`, then `d(a, b) = 1`.-/
theorem tame_of_ord_eq_zero_of_ord_eq_zero (a b : Kˣ) (ha : ord R a = 0) (hb : ord R b = 0) :
    tame R a b = 1 := by
  rw [tame_of_ord_eq_zero a b ha, hb, zpow_zero]

end Tame

end RiemannRoch.SingularTodd.TameSymbolT2
