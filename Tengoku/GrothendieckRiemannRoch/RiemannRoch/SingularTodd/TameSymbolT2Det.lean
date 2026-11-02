/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.SingularTodd.TameSymbolT2
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.SingularTodd.FiniteLengthDetT2
import Tengoku.Seed.RingTheory.OrderOfVanishing.Basic
import Tengoku.Seed.RingTheory.DiscreteValuationRing.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brick G2XSK2 (route S, K2), general case: the symbol `d_B(a, b)` of a 1-dimensional local domain

Let `B` be a noetherian local domain of dimension `≤ 1` with residue field `κ` and fraction
field `K`.  Following Stacks (Chow Homology, Appendix A, "Symbols"), for `a, b ∈ B ∖ 0` put

  `d_B(a, b) = det_κ(B/(ab), a, b) ∈ κ^×`,

the determinant (brick K1, `FinLenDet.perDet`) of the exact `(2,1)`-periodic complex given by
multiplication by `a` and `b` on the finite length module `B/(ab)`.

## Main definitions (namespace `RiemannRoch.SingularTodd.TameSymbolT2`)
* `Qt z = B ⧸ (z)`, `mulQ z x` (multiplication by `x` on it).
* `symb a b : κ` (`= perDet` on `Qt (a * b)`, junk `1` if `a * b = 0`) and `dB a b : κˣ`.
* `extKHom f hf : Kˣ →* G`: extension of a function multiplicative on `B ∖ 0` to `Kˣ`.
* `dK : Kˣ →* Kˣ →* κˣ`: the symbol on `K^×`, bimultiplicative by construction,
  `dK_unitOf : dK (a) (b) = dB a b` on `B ∖ 0`.
* `ordZ : Kˣ →* Multiplicative ℤ`: the extension of `a ↦ ℓ_B(B/a)` (Mathlib's `Ring.ord`).

## Main results
* On `B ∖ 0`: `dB_mul_right` (via `perDet_comp`, Stacks 42.68.24), `dB_mul_left`,
  `dB_mul_dB_swap` (`d(a,b) d(b,a) = 1`), `dB_self` (`d(a,a) = (-1)^{ℓ(B/a)}`),
  `dB_unit` (`d(u,b) = ū^{ℓ(B/b)}` for a unit `u`).
* On `K^×`: `dK_mul_dK_swap`, `dK_swap`, `dK_self` (`d(x,x) = (-1)^{ord x}`).
* **`dK_eq_tame`**: for a DVR, `d = tame` (the classical tame symbol of `TameSymbolT2.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RiemannRoch.SingularTodd.TameSymbolT2

open IsLocalRing FinLenDet

/-! ### Principal quotients `B ⧸ (z)` -/

section Quot

variable {B : Type*} [CommRing B]

/-- The principal quotient `B ⧸ (z)` as a `B`-module.-/
abbrev Qt (z : B) : Type _ := B ⧸ Ideal.span {z}

/-- Multiplication by `x` on `B ⧸ (z)`.-/
abbrev mulQ (z x : B) : Qt z →ₗ[B] Qt z := x • LinearMap.id

theorem mulQ_mk (z x r : B) :
    mulQ z x (Submodule.Quotient.mk r) = (Submodule.Quotient.mk (x * r) : Qt z) := by
  show x • (Submodule.Quotient.mk r : Qt z) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul]

theorem mk_eq_zero_iff (z r : B) : (Submodule.Quotient.mk r : Qt z) = 0 ↔ z ∣ r := by
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]

theorem mk_mem_ker_mulQ (z x r : B) :
    (Submodule.Quotient.mk r : Qt z) ∈ LinearMap.ker (mulQ z x) ↔ z ∣ x * r := by
  rw [LinearMap.mem_ker, mulQ_mk, mk_eq_zero_iff]

theorem mk_mem_range_mulQ {z y : B} (hy : y ∣ z) (r : B) :
    (Submodule.Quotient.mk r : Qt z) ∈ LinearMap.range (mulQ z y) ↔ y ∣ r := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [mulQ_mk, Submodule.Quotient.eq, Ideal.mem_span_singleton] at hm
    have h2 := dvd_sub (dvd_mul_right y s) (hy.trans hm)
    rwa [sub_sub_cancel] at h2
  · rintro ⟨s, rfl⟩
    exact ⟨Submodule.Quotient.mk s, mulQ_mk _ _ _⟩

theorem mulQ_mul (z x y : B) : mulQ z (x * y) = mulQ z x ∘ₗ mulQ z y :=
  LinearMap.ext fun m => by simp [mulQ, mul_smul]

theorem mulQ_comm (z x y : B) : mulQ z x ∘ₗ mulQ z y = mulQ z y ∘ₗ mulQ z x := by
  rw [← mulQ_mul, ← mulQ_mul, mul_comm]

theorem comp_mulQ {z w : B} (g : Qt z →ₗ[B] Qt w) (x : B) : g ∘ₗ mulQ z x = mulQ w x ∘ₗ g :=
  LinearMap.ext fun m => by simp [mulQ]

/-- Multiplication by `c`, `B ⧸ (z) → B ⧸ (w)`, for `w ∣ c z`.-/
noncomputable def mulMap (z c w : B) (h : w ∣ c * z) : Qt z →ₗ[B] Qt w :=
  Submodule.mapQ (Ideal.span {z}) (Ideal.span {w}) (c • LinearMap.id) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]
    simpa [Ideal.mem_span_singleton] using h)

theorem mulMap_mk (z c w : B) (h : w ∣ c * z) (r : B) :
    mulMap z c w h (Submodule.Quotient.mk r) = (Submodule.Quotient.mk (c * r) : Qt w) := by
  rw [mulMap, Submodule.mapQ_apply]; rfl

/-- The projection `B ⧸ (z) → B ⧸ (w)` for `w ∣ z`.-/
noncomputable def projMap (z w : B) (h : w ∣ z) : Qt z →ₗ[B] Qt w :=
  Submodule.mapQ (Ideal.span {z}) (Ideal.span {w}) LinearMap.id (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]
    simpa [Ideal.mem_span_singleton] using h)

theorem projMap_mk (z w : B) (h : w ∣ z) (r : B) :
    projMap z w h (Submodule.Quotient.mk r) = (Submodule.Quotient.mk r : Qt w) := by
  rw [projMap, Submodule.mapQ_apply]; rfl

theorem map_top_mulMap (z c w : B) (h : w ∣ c * z) :
    (⊤ : Submodule B (Qt z)).map (mulMap z c w h) = LinearMap.range (mulQ w c) := by
  rw [Submodule.map_top]
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    exact ⟨Submodule.Quotient.mk s, by rw [mulQ_mk, mulMap_mk]⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    exact ⟨Submodule.Quotient.mk s, by rw [mulQ_mk, mulMap_mk]⟩

variable [IsDomain B]

theorem ker_mulQ_eq_range {x y z : B} (hx : x ≠ 0) (hz : z = x * y) :
    LinearMap.ker (mulQ z x) = LinearMap.range (mulQ z y) := by
  ext m
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hy : y ∣ z := by rw [hz]; exact dvd_mul_left y x
  rw [mk_mem_ker_mulQ, mk_mem_range_mulQ hy, hz, mul_dvd_mul_iff_left hx]

theorem ker_mulMap {z c w : B} (hc : c ≠ 0) (hw : w = c * z) :
    (⊤ : Submodule B (Qt z)) ⊓
        (⊥ : Submodule B (Qt w)).comap (mulMap z c w (by rw [hw])) ≤ ⊥ := by
  intro m hm
  obtain ⟨-, hm⟩ := Submodule.mem_inf.1 hm
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.mem_comap, mulMap_mk, Submodule.mem_bot, mk_eq_zero_iff, hw,
    mul_dvd_mul_iff_left hc] at hm
  rw [Submodule.mem_bot, mk_eq_zero_iff]
  exact hm

variable [IsNoetherianRing B] [Ring.KrullDimLE 1 B]

/-- `B ⧸ (z)` has finite length for `z ≠ 0` (Mathlib, `dim B ≤ 1`).-/
theorem finLen {z : B} (hz : z ≠ 0) : IsArtinian B (Qt z) ∧ IsNoetherian B (Qt z) := by
  have := isFiniteLength_iff_isNoetherian_isArtinian.1
    (isFiniteLength_quotient_span_singleton B (mem_nonZeroDivisors_of_ne_zero hz))
  exact ⟨this.2, this.1⟩

end Quot

/-! ### The symbol on `B ∖ 0` -/

section Symb

variable {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [Ring.KrullDimLE 1 B]

open Classical in
/-- **Stacks, Symbols**: `d_B(a, b) = det_κ(B/(ab), a, b)` (junk value `1` if `ab = 0`).-/
noncomputable def symb (a b : B) : ResidueField B :=
  if h : a * b = 0 then 1 else
    haveI := (finLen h).1
    haveI := (finLen h).2
    perDet (M := Qt (a * b)) ⊥ ⊤ (mulQ (a * b) a) (mulQ (a * b) b)

theorem symb_eq {a b z : B} (hz : z = a * b) (h0 : z ≠ 0) [IsArtinian B (Qt z)]
    [IsNoetherian B (Qt z)] :
    symb a b = perDet (M := Qt z) ⊥ ⊤ (mulQ z a) (mulQ z b) := by
  subst hz
  rw [symb, dite_eq_right h0]

theorem symb_of_mul_eq_zero {a b : B} (h : a * b = 0) : symb a b = 1 := by
  rw [symb, dite_eq_left h]

theorem perExact_symb {a b z : B} (ha : a ≠ 0) (hb : b ≠ 0) (hz : z = a * b) :
    PerExact (⊥ : Submodule B (Qt z)) ⊤ (mulQ z a) (mulQ z b) :=
  perExact_bot_top_iff.2
    ⟨ker_mulQ_eq_range ha hz, ker_mulQ_eq_range hb (hz.trans (mul_comm a b))⟩

theorem symb_ne_zero (a b : B) : symb a b ≠ 0 := by
  by_cases h : a * b = 0
  · rw [symb_of_mul_eq_zero h]; exact one_ne_zero
  · haveI := (finLen h).1
    haveI := (finLen h).2
    rw [symb_eq rfl h]
    exact perDet_ne_zero (perExact_symb (left_ne_zero_of_mul h) (right_ne_zero_of_mul h) rfl)

/-- `d(a, b) · d(b, a) = 1` (Stacks 42.68.15).-/
theorem symb_mul_symb_swap {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) : symb a b * symb b a = 1 := by
  have hz : a * b ≠ 0 := mul_ne_zero ha hb
  haveI := (finLen hz).1
  haveI := (finLen hz).2
  rw [symb_eq rfl hz, symb_eq (mul_comm a b) hz]
  exact perDet_mul_perDet_symm (perExact_symb ha hb rfl)

/-- `d(a, bc) = d(a, b) d(a, c)` (Stacks 42.68.24 applied to `B/(abc)`).-/
theorem symb_mul_right (a : B) {b c : B} (hb : b ≠ 0) (hc : c ≠ 0) :
    symb a (b * c) = symb a b * symb a c := by
  by_cases ha : a = 0
  · subst ha; simp [symb_of_mul_eq_zero]
  have hz : a * (b * c) ≠ 0 := mul_ne_zero ha (mul_ne_zero hb hc)
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  haveI := (finLen hz).1
  haveI := (finLen hz).2
  haveI := (finLen hab).1
  haveI := (finLen hab).2
  haveI := (finLen hac).1
  haveI := (finLen hac).2
  set z := a * (b * c) with hzdef
  have h1 : LinearMap.range (mulQ z a) = LinearMap.ker (mulQ z b ∘ₗ mulQ z c) := by
    rw [← mulQ_mul]; exact (ker_mulQ_eq_range (mul_ne_zero hb hc) (by rw [hzdef]; ring)).symm
  have h2 : LinearMap.ker (mulQ z a) = LinearMap.range (mulQ z b ∘ₗ mulQ z c) := by
    rw [← mulQ_mul]; exact ker_mulQ_eq_range ha rfl
  have h4 : LinearMap.ker (mulQ z b) = LinearMap.range (mulQ z a ∘ₗ mulQ z c) := by
    rw [← mulQ_mul]; exact ker_mulQ_eq_range hb (by rw [hzdef]; ring)
  have h5 : LinearMap.range (mulQ z c) = LinearMap.ker (mulQ z a ∘ₗ mulQ z b) := by
    rw [← mulQ_mul]; exact (ker_mulQ_eq_range hab (by rw [hzdef]; ring)).symm
  rw [symb_eq rfl hz, mulQ_mul,
    perDet_comp (mulQ_comm _ _ _) (mulQ_comm _ _ _) (mulQ_comm _ _ _) h1 h2 h4 h5]
  congr 1
  · -- `[⊥, c·N] ≅ B/(ab)` via multiplication by `c`
    have hdvd : z ∣ c * (a * b) := ⟨1, by rw [hzdef]; ring⟩
    have key := perDet_map (mulMap (a * b) c z hdvd) (comp_mulQ _ a) (comp_mulQ _ b)
      (perExact_symb ha hb rfl) (ker_mulMap hc (by rw [hzdef]; ring))
    rw [Submodule.map_bot, map_top_mulMap] at key
    rw [key, symb_eq rfl hab]
  · -- `[ker b, ⊤] ≅ B/(ac)` via the projection
    have hdvd : a * c ∣ z := ⟨b, by rw [hzdef]; ring⟩
    have memK : ∀ r : B, (Submodule.Quotient.mk r : Qt z) ∈ LinearMap.ker (mulQ z b) ↔
        a * c ∣ r := fun r => by
      rw [mk_mem_ker_mulQ, show z = b * (a * c) by rw [hzdef]; ring, mul_dvd_mul_iff_left hb]
    have hleγ : LinearMap.ker (mulQ z b) ≤ LinearMap.range (mulQ z c) := by
      intro m hm
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [memK] at hm
      rw [mk_mem_range_mulQ ⟨a * b, by rw [hzdef]; ring⟩]
      exact (dvd_mul_left c a).trans hm
    have hleα : LinearMap.ker (mulQ z b) ≤ LinearMap.range (mulQ z a) := by
      intro m hm
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [memK] at hm
      rw [mk_mem_range_mulQ ⟨b * c, rfl⟩]
      exact (dvd_mul_right a c).trans hm
    have hPE : PerExact (LinearMap.ker (mulQ z b)) ⊤ (mulQ z a) (mulQ z c) := by
      refine ⟨le_top, ?_, ?_⟩
      · rw [top_inf_eq, Submodule.map_top, sup_eq_left.2 hleγ]
        ext m
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [Submodule.mem_comap, mulQ_mk, memK, mk_mem_range_mulQ ⟨a * b, by rw [hzdef]; ring⟩,
          mul_dvd_mul_iff_left ha]
      · rw [top_inf_eq, Submodule.map_top, sup_eq_left.2 hleα]
        ext m
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [Submodule.mem_comap, mulQ_mk, memK, mk_mem_range_mulQ ⟨b * c, rfl⟩, mul_comm a c,
          mul_dvd_mul_iff_left hc]
    have hg : (⊤ : Submodule B (Qt z)) ⊓ (⊥ : Submodule B (Qt (a * c))).comap
        (projMap z (a * c) hdvd) ≤ LinearMap.ker (mulQ z b) := by
      intro m hm
      obtain ⟨-, hm⟩ := Submodule.mem_inf.1 hm
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [Submodule.mem_comap, projMap_mk, Submodule.mem_bot, mk_eq_zero_iff] at hm
      rw [memK]; exact hm
    have hP : (LinearMap.ker (mulQ z b)).map (projMap z (a * c) hdvd) = ⊥ := by
      rw [eq_bot_iff]
      rintro m ⟨n, hn, rfl⟩
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ n
      rw [SetLike.mem_coe, memK] at hn
      rw [projMap_mk, Submodule.mem_bot, mk_eq_zero_iff]
      exact hn
    have hT : (⊤ : Submodule B (Qt z)).map (projMap z (a * c) hdvd) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      exact ⟨Submodule.Quotient.mk r, trivial, projMap_mk _ _ _ _⟩
    have key := perDet_map (projMap z (a * c) hdvd) (comp_mulQ _ a) (comp_mulQ _ c) hPE hg
    rw [hP, hT] at key
    rw [← key, symb_eq rfl hac]

theorem symb_swap {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) : symb b a = (symb a b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (symb_mul_symb_swap ha hb)

theorem symb_mul_left {a a' : B} (b : B) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    symb (a * a') b = symb a b * symb a' b := by
  by_cases hb : b = 0
  · subst hb; simp [symb_of_mul_eq_zero]
  rw [symb_swap hb (mul_ne_zero ha ha'), symb_mul_right b ha ha', mul_inv, ← symb_swap hb ha,
    ← symb_swap hb ha']

/-- `d(a, a) = (-1)^{ℓ(B/a)}` (Stacks 42.68.16).-/
theorem symb_self {a : B} (ha : a ≠ 0) {n : ℕ} (hn : Ring.ord B a = n) :
    symb a a = (-1) ^ n := by
  have hz : a * a ≠ 0 := mul_ne_zero ha ha
  haveI := (finLen hz).1
  haveI := (finLen hz).2
  haveI := (finLen ha).1
  haveI := (finLen ha).2
  rw [symb_eq rfl hz]
  obtain ⟨X, hXT, hX⟩ := exists_image_adm (mulQ (a * a) a) ⊤ ⊥
  rw [perDet_self (perExact_symb ha ha rfl) hX hXT]
  obtain ⟨Z, hZ⟩ := exists_adm (M := Qt a) (bot_le : (⊥ : Submodule B (Qt a)) ≤ ⊤)
  have hlen := hZ.moduleLength_eq
  have hZ' := adm_map (mulMap a a (a * a) ⟨1, by ring⟩) ⊥ (ker_mulMap ha rfl) hZ
  rw [Submodule.map_bot, sup_bot_eq, sup_bot_eq, map_top_mulMap] at hZ'
  rw [sup_bot_eq, Submodule.map_top] at hX
  have hl := hX.length_eq hZ'
  rw [List.length_map, List.length_map] at hl
  have : Z.length = n := by
    have h2 : (Z.length : ℕ∞) = n := by rw [← hlen, ← hn]; rfl
    exact_mod_cast h2
  rw [hl, this]

/-- `d(u, b) = ū^{ℓ(B/b)}` for a unit `u` (Stacks 42.68.17).-/
theorem symb_unit {u b : B} (hu : IsUnit u) (hb : b ≠ 0) {n : ℕ} (hn : Ring.ord B b = n) :
    symb u b = residue B u ^ n := by
  have hz : u * b ≠ 0 := mul_ne_zero hu.ne_zero hb
  haveI := (finLen hz).1
  haveI := (finLen hz).2
  rw [symb_eq rfl hz]
  have h0 : mulQ (u * b) b = 0 := LinearMap.ext fun m => by
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [mulQ_mk, LinearMap.zero_apply, mk_eq_zero_iff, mul_comm u b]
    exact mul_dvd_mul_left b hu.dvd
  rw [h0]
  obtain ⟨X, hX⟩ := exists_adm (M := Qt (u * b)) (bot_le : (⊥ : Submodule B (Qt (u * b))) ≤ ⊤)
  rw [perDet_unit_zero hu hX]
  have hlen := hX.moduleLength_eq
  have : X.length = n := by
    have h2 : (X.length : ℕ∞) = n := by
      rw [← hlen, ← hn, ← Ring.ord_mul_of_isUnit_left hu b]; rfl
    exact_mod_cast h2
  rw [this]

/-! ### Units version -/

/-- `d_B(a, b) ∈ κ^×`.-/
noncomputable def dB (a b : B) : (ResidueField B)ˣ := Units.mk0 (symb a b) (symb_ne_zero a b)

@[simp] theorem coe_dB (a b : B) : (dB a b : ResidueField B) = symb a b := rfl

theorem dB_mul_right (a : B) {b c : B} (hb : b ≠ 0) (hc : c ≠ 0) :
    dB a (b * c) = dB a b * dB a c :=
  Units.ext (by simp [symb_mul_right a hb hc])

theorem dB_mul_left {a a' : B} (b : B) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    dB (a * a') b = dB a b * dB a' b :=
  Units.ext (by simp [symb_mul_left b ha ha'])

theorem dB_mul_dB_swap {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) : dB a b * dB b a = 1 :=
  Units.ext (by simp [symb_mul_symb_swap ha hb])

theorem dB_swap {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) : dB b a = (dB a b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (dB_mul_dB_swap ha hb)

theorem dB_self {a : B} (ha : a ≠ 0) {n : ℕ} (hn : Ring.ord B a = n) : dB a a = (-1) ^ n :=
  Units.ext (by simp [symb_self ha hn])

theorem dB_unit (u : Bˣ) {b : B} (hb : b ≠ 0) {n : ℕ} (hn : Ring.ord B b = n) :
    dB (u : B) b = Units.map (residue B : B →* ResidueField B) u ^ n :=
  Units.ext (by simp [symb_unit u.isUnit hb hn])

theorem dB_pow_right (a : B) {b : B} (hb : b ≠ 0) (n : ℕ) : dB a (b ^ n) = dB a b ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    have h := dB_mul_right a (one_ne_zero (α := B)) (one_ne_zero (α := B))
    rw [one_mul] at h
    exact left_eq_mul.1 h |>.symm ▸ rfl
  | succ n ih => rw [pow_succ, dB_mul_right a (pow_ne_zero n hb) hb, ih, pow_succ]

theorem dB_pow_left {a : B} (ha : a ≠ 0) (b : B) (n : ℕ) : dB (a ^ n) b = dB a b ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    have h := dB_mul_left b (one_ne_zero (α := B)) (one_ne_zero (α := B))
    rw [one_mul] at h
    exact left_eq_mul.1 h |>.symm ▸ rfl
  | succ n ih => rw [pow_succ, dB_mul_left b (pow_ne_zero n ha) ha, ih, pow_succ]

end Symb

/-! ### Extension from `B ∖ 0` to `K^×` -/

section Ext

variable {B : Type*} [CommRing B] [IsDomain B]
variable (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
variable {G : Type*} [CommGroup G]

/-- `a ∈ B ∖ 0` as a unit of `K`.-/
noncomputable def unitOf (a : B) (ha : a ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap B K a) (fun h => ha (IsFractionRing.injective B K (h.trans (map_zero _).symm)))

variable {K}

@[simp] theorem coe_unitOf (a : B) (ha : a ≠ 0) : (unitOf K a ha : K) = algebraMap B K a := rfl

theorem unitOf_mul {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitOf K (a * b) (mul_ne_zero ha hb) = unitOf K a ha * unitOf K b hb :=
  Units.ext (by simp)

theorem unitOf_inj {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) (h : unitOf K a ha = unitOf K b hb) :
    a = b :=
  IsFractionRing.injective B K (congrArg Units.val h)

theorem exists_eq_div (x : Kˣ) :
    ∃ (a c : B) (ha : a ≠ 0) (hc : c ≠ 0), x = unitOf K a ha * (unitOf K c hc)⁻¹ := by
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (A := B) (x : K)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact x.ne_zero hx.symm
  refine ⟨a, c, ha0, hc0, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_unitOf, coe_unitOf, ← div_eq_mul_inv, hx]

variable (K) in
/-- Extension of `f` (multiplicative on `B ∖ 0`) to `K^×`, using chosen fractions.-/
noncomputable def extK (f : B → G) (x : Kˣ) : G :=
  f (exists_eq_div (B := B) (K := K) x).choose / f (exists_eq_div (B := B) (K := K) x).choose_spec.choose

theorem extK_aux {f : B → G} (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y)
    {x : Kˣ} {a0 c0 a c : B} (ha0 : a0 ≠ 0) (hc0 : c0 ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (h0 : x = unitOf K a0 ha0 * (unitOf K c0 hc0)⁻¹) (h : x = unitOf K a ha * (unitOf K c hc)⁻¹) :
    f a0 / f c0 = f a / f c := by
  have e : unitOf K a0 ha0 * unitOf K c hc = unitOf K a ha * unitOf K c0 hc0 := by
    have := h0.symm.trans h
    rwa [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at this
  rw [← unitOf_mul, ← unitOf_mul] at e
  have e' := unitOf_inj _ _ e
  rw [div_eq_div_iff_mul_eq_mul, ← hf _ _ ha0 hc, ← hf _ _ ha hc0, e']

theorem extK_eq {f : B → G} (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y)
    {x : Kˣ} {a c : B} (ha : a ≠ 0) (hc : c ≠ 0) (h : x = unitOf K a ha * (unitOf K c hc)⁻¹) :
    extK K f x = f a / f c := by
  obtain ⟨ha0, hc0, h0⟩ := (exists_eq_div (B := B) (K := K) x).choose_spec.choose_spec
  exact extK_aux hf ha0 hc0 ha hc h0 h

theorem map_one_of_mul {f : B → G} (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y) :
    f 1 = 1 := by
  have h := hf 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  exact (left_eq_mul.1 h)

variable (K) in
/-- The extension as a group homomorphism `K^× →* G`.-/
noncomputable def extKHom (f : B → G) (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y) :
    Kˣ →* G where
  toFun := extK K f
  map_one' := by
    rw [extK_eq hf (a := (1 : B)) (c := (1 : B)) one_ne_zero one_ne_zero (by rw [mul_inv_cancel]),
      div_self']
  map_mul' x y := by
    obtain ⟨a, c, ha, hc, hx⟩ := exists_eq_div (B := B) (K := K) x
    obtain ⟨b, d, hb, hd, hy⟩ := exists_eq_div (B := B) (K := K) y
    have hxy : x * y = unitOf K (a * b) (mul_ne_zero ha hb) *
        (unitOf K (c * d) (mul_ne_zero hc hd))⁻¹ := by
      rw [hx, hy, unitOf_mul ha hb, unitOf_mul hc hd, mul_inv]
      simp only [mul_left_comm, mul_assoc]
    rw [extK_eq hf (mul_ne_zero ha hb) (mul_ne_zero hc hd) hxy, extK_eq hf ha hc hx,
      extK_eq hf hb hd hy, hf _ _ ha hb, hf _ _ hc hd,
      mul_div_mul_comm]

theorem extKHom_eq {f : B → G} (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y)
    {x : Kˣ} {a c : B} (ha : a ≠ 0) (hc : c ≠ 0) (h : x = unitOf K a ha * (unitOf K c hc)⁻¹) :
    extKHom K f hf x = f a / f c :=
  extK_eq hf ha hc h

theorem extKHom_unitOf {f : B → G} (hf : ∀ x y : B, x ≠ 0 → y ≠ 0 → f (x * y) = f x * f y)
    {a : B} (ha : a ≠ 0) : extKHom K f hf (unitOf K a ha) = f a := by
  have h : unitOf K a ha = unitOf K a ha * (unitOf K (1 : B) one_ne_zero)⁻¹ := by
    rw [show unitOf K (1 : B) one_ne_zero = 1 from Units.ext (by simp), inv_one, mul_one]
  rw [extKHom_eq hf ha one_ne_zero h, map_one_of_mul hf, div_one]

variable (B) in
/-- A bimultiplicative pairing on `K^×` is determined by its values on `B ∖ 0`.-/
theorem pairing_ext {F F' : Kˣ →* Kˣ →* G}
    (h : ∀ (a b : B) (ha : a ≠ 0) (hb : b ≠ 0),
      F (unitOf K a ha) (unitOf K b hb) = F' (unitOf K a ha) (unitOf K b hb)) : F = F' := by
  ext x y
  obtain ⟨a, c, ha, hc, rfl⟩ := exists_eq_div (B := B) (K := K) x
  obtain ⟨b, d, hb, hd, rfl⟩ := exists_eq_div (B := B) (K := K) y
  simp only [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
  rw [h a b ha hb, h a d ha hd, h c b hc hb, h c d hc hd]

end Ext

/-! ### The symbol on `K^×` -/

section SymbK

variable {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [Ring.KrullDimLE 1 B]
variable {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]

/-- `y ↦ d_B(a, y)` on `K^×`.-/
noncomputable def dBHom (a : B) : Kˣ →* (ResidueField B)ˣ :=
  extKHom K (dB a) fun _ _ hb hc => dB_mul_right a hb hc

theorem dBHom_mul {a a' : B} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (dBHom (K := K) (a * a')) = dBHom a * dBHom a' := by
  ext1 y
  obtain ⟨b, d, hb, hd, hy⟩ := exists_eq_div (B := B) (K := K) y
  simp only [dBHom, MonoidHom.mul_apply]
  rw [extKHom_eq _ hb hd hy, extKHom_eq _ hb hd hy, extKHom_eq _ hb hd hy,
    dB_mul_left b ha ha', dB_mul_left d ha ha', mul_div_mul_comm]

variable (B K) in
/-- **The symbol `d_B` on `K^× × K^×`**, bimultiplicative by construction.-/
noncomputable def dK : Kˣ →* Kˣ →* (ResidueField B)ˣ :=
  extKHom K (fun a => dBHom (K := K) a) fun _ _ ha ha' => dBHom_mul ha ha'

theorem dK_unitOf {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    dK B K (unitOf K a ha) (unitOf K b hb) = dB a b := by
  rw [dK, extKHom_unitOf, dBHom, extKHom_unitOf]

/-- `d(x, y) · d(y, x) = 1` on `K^×`.-/
theorem dK_mul_dK_swap (x y : Kˣ) : dK B K x y * dK B K y x = 1 := by
  have : dK B K * (dK B K).flip = (1 : Kˣ →* Kˣ →* (ResidueField B)ˣ) := by
    refine pairing_ext B fun a b ha hb => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.flip_apply, dK_unitOf, dK_unitOf,
      MonoidHom.one_apply, MonoidHom.one_apply, dB_mul_dB_swap ha hb]
  have := congrArg (fun F => F x y) this
  simpa using this

theorem dK_swap (x y : Kˣ) : dK B K y x = (dK B K x y)⁻¹ :=
  eq_inv_of_mul_eq_one_right (dK_mul_dK_swap x y)

variable (B K) in
/-- `ord_B : K^× → ℤ` (multiplicatively), extending `a ↦ ℓ_B(B/a)` (Mathlib's `Ring.ord`).-/
noncomputable def ordZ : Kˣ →* Multiplicative ℤ :=
  extKHom K (fun a => Multiplicative.ofAdd ((Ring.ord B a).toNat : ℤ)) fun x y hx hy => by
    rw [Ring.ord_mul B (mem_nonZeroDivisors_of_ne_zero hy),
      ENat.toNat_add (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx))
        (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy))]
    simp [ofAdd_add]

theorem ordZ_unitOf {a : B} (ha : a ≠ 0) :
    ordZ B K (unitOf K a ha) = Multiplicative.ofAdd ((Ring.ord B a).toNat : ℤ) := by
  rw [ordZ, extKHom_unitOf]

theorem dB_self' {a : B} (ha : a ≠ 0) : dB a a = (-1) ^ (Ring.ord B a).toNat :=
  dB_self ha (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm

theorem dK_self_mul (x y : Kˣ) : dK B K (x * y) (x * y) = dK B K x x * dK B K y y := by
  have h := dK_mul_dK_swap (B := B) x y
  simp only [map_mul, MonoidHom.mul_apply]
  rw [mul_assoc, ← mul_assoc (dK B K y x), mul_comm (dK B K y x), h, one_mul]

theorem dK_self_inv (x : Kˣ) : dK B K x⁻¹ x⁻¹ = dK B K x x := by
  simp only [map_inv, MonoidHom.inv_apply, inv_inv]

theorem neg_one_pow_inv {G : Type*} [Group G] [HasDistribNeg G] (k : ℕ) :
    ((-1 : G) ^ k)⁻¹ = (-1) ^ k := by
  rw [← inv_pow, inv_neg_one]

/-- `d(x, x) = (-1)^{ord x}` on `K^×` (Stacks 42.68.16).-/
theorem dK_self (x : Kˣ) : dK B K x x = (-1) ^ (Multiplicative.toAdd (ordZ B K x)) := by
  obtain ⟨a, c, ha, hc, rfl⟩ := exists_eq_div (B := B) (K := K) x
  rw [dK_self_mul, dK_self_inv, dK_unitOf, dK_unitOf, map_mul, map_inv, ordZ_unitOf, ordZ_unitOf,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, zpow_add, zpow_neg, zpow_natCast,
    zpow_natCast, dB_self' ha, dB_self' hc, neg_one_pow_inv]

end SymbK

/-! ### Comparison with the tame symbol for a DVR -/

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R K) in
/-- The tame symbol as a bimultiplicative pairing.-/
noncomputable def tameHom : Kˣ →* Kˣ →* (ResidueField R)ˣ where
  toFun a :=
    { toFun := tame R a
      map_one' := by
        have h := tame_mul_right (R := R) a 1 1
        rw [mul_one] at h
        exact left_eq_mul.1 h
      map_mul' := tame_mul_right a }
  map_one' := MonoidHom.ext fun b => by
    have h := tame_mul_left (R := R) (1 : Kˣ) 1 b
    rw [mul_one] at h
    exact left_eq_mul.1 h
  map_mul' a a' := MonoidHom.ext fun b => tame_mul_left a a' b

theorem units_map_residue_neg_one :
    Units.map (residue R : R →* ResidueField R) (-1) = -1 :=
  Units.ext (by simp)

theorem unitOf_eq_smul (u : Rˣ) (k : ℕ) :
    (unitOf K ((u : R) * unif R ^ k) (mul_ne_zero u.ne_zero (pow_ne_zero _
      (irreducible_unif R).ne_zero)) : K) = u • algebraMap R K (unif R) ^ (k : ℤ) := by
  rw [coe_unitOf, Units.smul_def, Algebra.smul_def, zpow_natCast, map_mul, map_pow]

/-- On `R ∖ 0`: `d_R(a, b)` is the classical tame symbol (Stacks 42.68.37 (DVR case)).-/
theorem dB_eq_tame {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    dB a b = tame R (unitOf K a ha) (unitOf K b hb) := by
  have hϖ := irreducible_unif R
  have hϖ0 : unif R ≠ 0 := hϖ.ne_zero
  have hϖ1 : Ring.ord R (unif R) = ((1 : ℕ) : ℕ∞) := by
    rw [Ring.ord_of_irreducible hϖ]; rfl
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨l, v, hl⟩ := eq_unit_mul_pow_irreducible hb hϖ
  subst hk hl
  have hv0 : Ring.ord R (v : R) = ((0 : ℕ) : ℕ∞) := by
    rw [Ring.ord_of_isUnit v.isUnit]; rfl
  obtain ⟨hka, hua⟩ := ord_unitPart_eq (unitOf_eq_smul (K := K) u k)
  obtain ⟨hkb, hub⟩ := ord_unitPart_eq (unitOf_eq_smul (K := K) v l)
  rw [tame, tameUnit, hka, hkb, hua, hub, map_mul, map_mul, map_inv, map_zpow, map_zpow, map_zpow,
    units_map_residue_neg_one, ← Nat.cast_mul, zpow_natCast, zpow_natCast, zpow_natCast,
    dB_mul_left _ u.ne_zero (pow_ne_zero _ hϖ0), dB_mul_right _ v.ne_zero (pow_ne_zero _ hϖ0),
    dB_mul_right _ v.ne_zero (pow_ne_zero _ hϖ0), dB_pow_right _ hϖ0, dB_pow_right _ hϖ0,
    dB_pow_left hϖ0, dB_pow_left hϖ0, dB_unit u v.ne_zero hv0, dB_unit u hϖ0 hϖ1,
    dB_swap v.ne_zero hϖ0, dB_unit v hϖ0 hϖ1, dB_self hϖ0 hϖ1]
  simp only [pow_zero, pow_one, one_mul, inv_pow, ← pow_mul]
  rw [mul_assoc ((-1) ^ (k * l)), mul_comm ((-1 : (ResidueField R)ˣ) ^ (k * l)), mul_assoc]

/-- **`d = tame` for a DVR**, as pairings on `K^×`.-/
theorem dK_eq_tameHom : dK R K = tameHom R K :=
  pairing_ext R (K := K) fun a b ha hb => by rw [dK_unitOf, dB_eq_tame (K := K) ha hb]; rfl

theorem dK_eq_tame (x y : Kˣ) : dK R K x y = tame R x y := by
  rw [dK_eq_tameHom]; rfl

end DVR

end RiemannRoch.SingularTodd.TameSymbolT2
