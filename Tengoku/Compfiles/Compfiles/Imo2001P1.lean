/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2001, Problem 1

Let ABC be an acute-angled triangle with O as its circumcenter. Let P
on line BC be the foot of the altitude from A. Assume that
∠BCA ≥ ∠ABC + 30°. Prove that ∠CAB + ∠COP < 90°.
-/

namespace Imo2001P1

open scoped EuclideanGeometry

open EuclideanGeometry Affine.Simplex Affine.Triangle

-- We need some instances in order to talk about oriented angles.

/--
@isnad1 id=fact.0h0v.s7.c37f42c39efd from=translated src=- shape=2a1846ce vocab=78c039ea
-/
local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/--
@isnad1 id=eq.2h2v.s5.caeb4ca150f1 from=translated src=- shape=20314242 vocab=4bc6076d
-/
lemma aux₀ {x y : ℝ} (h : ∃ k : ℤ, x = y * k)
  (hx : |x| < y)
  : x = 0 := by
    rcases h with ⟨k, hk⟩
    rw [hk]
    apply mul_eq_zero_of_right
    simp
    contrapose! hx
    rw [hk, abs_mul]
    have h₁ : (1 : ℝ) ≤ |↑k| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs hx
    calc y
        ≤ |y| := le_abs_self y
      _ = |y| * 1 := (mul_one |y|).symm
      _ ≤ |y| * |↑k| := mul_le_mul_of_nonneg_left h₁ (abs_nonneg y)

/--
@isnad1 id=lt.4h3v.s6.cfe2c785d89e from=translated src=- shape=4f4fe155 vocab=892788b3
-/
lemma aux₁ {x y z : ℝ}
  (hx' : 0 ≤ x) (hy' : y ≤ 0)
  (hx : |x| < z) (hy : |y| < z)
  : |x + y| < z := by
    rw [abs_lt]
    constructor
    · calc -z
          _ < y := (abs_lt.mp hy).left
          _ = 0 + y := (zero_add y).symm
          _ ≤ x + y := add_le_add_left hx' y
    · calc x + y
        _ ≤ x + 0 := add_le_add_right hy' x
        _ = x := add_zero x
        _ < z := (abs_lt.mp hx).right

/--
@isnad1 id=eq.3h3v.s5.8ca6e329ad89 from=translated src=- shape=3d803a56 vocab=162b2105
-/
lemma aux₂ {x y z : ℝ} (h : |x + y| = z)
  (hx : |x| < z) (hy : |y| < z)
  : |x| + |y| = z := by
    symm
    rw [← h, abs_add_eq_add_abs_iff]
    contrapose! h
    apply ne_of_lt
    by_cases hx' : 0 ≤ x
    · have hy' := h.left hx'
      exact aux₁ hx' (le_of_lt hy') hx hy
    · push Not at hx'
      have hy' := h.right (le_of_lt hx')
      rw [add_comm]
      exact aux₁ (le_of_lt hy') (le_of_lt hx') hy hx

/--
@isnad1 id=eq.3h2v.s7.4ace854cceab from=translated src=- shape=3f66e79b vocab=c7d3e3f2
-/
lemma aux₃ {a b : Real.Angle} (h : 2 • a + 2 • b = Real.pi)
  (ha : |a.toReal| < Real.pi / 2) (hb : |b.toReal| < Real.pi / 2)
  : |a.toReal| + |b.toReal| = Real.pi / 2 := by
    rw [← Real.Angle.coe_toReal a, ← Real.Angle.coe_toReal b] at h
    set a' := a.toReal
    set b' := b.toReal
    rw [← smul_add] at h
    rw [Real.Angle.two_nsmul_eq_pi_iff, ← Real.Angle.coe_add] at h
    repeat rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    have h₁ : |a' + b'| < Real.pi := by
      calc |a' + b'|
          ≤ |a'| + |b'| := abs_add_le a' b'
        _ < Real.pi / 2 + Real.pi / 2 := add_lt_add ha hb
        _ = Real.pi := by ring
    have h₂ : 0 ≤ Real.pi / 2 := by
      apply div_nonneg Real.pi_nonneg
      norm_num
    have h₃ : |a' + b'| + |Real.pi / 2| < 2 * Real.pi := by
      calc |a' + b'| + |Real.pi / 2|
            < Real.pi + |Real.pi / 2| := add_lt_add_left h₁ _
          _ = Real.pi + Real.pi / 2 := (add_right_inj _).mpr (abs_eq_self.mpr h₂)
          _ ≤ Real.pi + Real.pi / 2 + Real.pi / 2 := (le_add_iff_nonneg_right _).mpr h₂
          _ = 2 * Real.pi := by ring
    have h₄ : |a' + b'| = Real.pi / 2 := by
      rw [abs_eq h₂]
      rcases h with pos|neg
      · left
        apply eq_of_sub_eq_zero
        apply aux₀ pos
        calc |a' + b' - Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := abs_sub _ _
          _ < 2 * Real.pi := h₃
      · right
        apply eq_of_sub_eq_zero
        rw [← neg_div]
        apply aux₀ neg
        rw [neg_div, sub_neg_eq_add]
        calc |a' + b' + Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := abs_add_le _ _
          _ < 2 * Real.pi := h₃
    exact aux₂ h₄ ha hb

/--
@isnad1 id=eq.2h1v.s6.6ea98007e8e3 from=translated src=- shape=575aa821 vocab=e5d27d56
-/
lemma aux₄ {a : Real.Angle} (h : 2 • 2 • a = 0) (ha : |a.toReal| < Real.pi / 2)
  : |a.toReal| = 0 := by
    rw [smul_smul] at h
    have h₁ : 2 * 2 = 4 := by norm_num
    rw [h₁] at h
    rw [← Real.Angle.coe_toReal a] at h
    set a' := a.toReal
    rw [← Real.Angle.coe_nsmul] at h
    rw [Real.Angle.coe_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have h₂ : a' = Real.pi / 2 * k:= by
      calc a'
          = (4 • a') / 4 := by ring
        _ = k • (2 * Real.pi) / 4 := by rw [hk]
        _ = Real.pi / 2 * k := by ring
    rw [abs_eq_zero]
    exact aux₀ ⟨k, h₂⟩ ha

/--
@isnad1 id=le.3h3v.s6.18be3d309860 from=translated src=- shape=7a5ccf70 vocab=585702f7
-/
lemma aux₅ {x y z: ℝ} (h : ∃ k : ℤ, x - y = z * k)
  (hz : 0 < z) (hy : |y| ≤ z / 2)
  : |y| ≤ |x| := by
  rcases h with ⟨k, hk⟩
  by_cases h': k = 0
  · rw [h', Int.cast_zero, mul_zero, sub_eq_zero] at hk
    rw [hk]
  · push Not at h'
    apply le_trans hy
    have h₁ : (1 : ℝ) ≤ |↑k| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs h'
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    rw [le_abs] at *
    rw [abs_le] at *
    rcases h₁ with pos|neg
    · left
      calc z / 2
          = z * 1 + -(z / 2) := by ring
        _ ≤ z * ↑k + y := by
          apply add_le_add
          · rw [mul_le_mul_iff_right₀ hz]
            exact pos
          · exact hy.left
    · right
      calc z / 2
          = z * 1 + -(z / 2) := by ring
        _ ≤ z * (-↑k) + -y := by
            apply add_le_add
            · rw [mul_le_mul_iff_right₀ hz]
              exact neg
            · apply neg_le_neg
              exact hy.right
        _ = -(z * ↑k + y) := by ring

/--
@isnad1 id=le.1h3v.s5.7567d307847a from=translated src=- shape=dcaa1fb6 vocab=a5b232ae
-/
lemma aux₆ {a b c : Real.Angle} (h : a + b = c)
  : |c.toReal| ≤ |a.toReal| + |b.toReal| := by
    rw [← Real.Angle.coe_toReal a] at h
    rw [← Real.Angle.coe_toReal b] at h
    rw [← Real.Angle.coe_toReal c] at h
    set a' := a.toReal
    set b' := b.toReal
    set c' := c.toReal
    rw [← Real.Angle.coe_add] at h
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    calc |c'|
        ≤ |a' + b'| := by
          apply aux₅ h Real.two_pi_pos
          rw [mul_div_cancel_left₀ Real.pi (by norm_num:(2 : ℝ) ≠ 0)]
          exact Real.Angle.abs_toReal_le_pi c
      _ ≤ |a'| + |b'| := by apply abs_add_le

/--
@isnad1 id=eq.0h1v.s4.f16e049776bb from=translated src=- shape=df0095c1 vocab=d3bd36da
-/
lemma aux₇ {a : Real.Angle} : Real.sin |a.toReal| = |a.sin| := by
  nth_rw 2 [← Real.Angle.coe_toReal a]
  rw [Real.Angle.sin_coe]
  have ha' := Real.Angle.abs_toReal_le_pi a
  exact (Real.abs_sin_eq_sin_abs_of_abs_le_pi ha').symm

structure Imo2001q1Cfg where
  (A B C : EuclideanSpace ℝ (Fin 2))
  (hABC : AffineIndependent ℝ ![A, B, C])
  (hAcuteA : ∠ C A B < Real.pi / 2)
  (hAcuteB : ∠ A B C < Real.pi / 2)
  (hAcuteC : ∠ B C A < Real.pi / 2)
  (hAB : ∠ A B C + Real.pi / 6 ≤ ∠ B C A)

namespace Imo2001q1Cfg

variable (cfg : Imo2001q1Cfg)

def ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.A, cfg.B, cfg.C], cfg.hABC⟩

noncomputable def P : EuclideanSpace ℝ (Fin 2) :=
  cfg.ABC.altitudeFoot 0

noncomputable def O :EuclideanSpace ℝ (Fin 2) :=
  cfg.ABC.circumcenter

/--
@isnad1 id=ne.0h1v.s3.2648a5fcaf6e from=translated src=- shape=94695d2c vocab=d39ceb5b
-/
lemma A_ne_B : cfg.A ≠ cfg.B := by
    exact cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

/--
@isnad1 id=ne.0h1v.s3.687188dc93a0 from=translated src=- shape=94695d2c vocab=6a761ded
-/
lemma A_ne_C : cfg.A ≠ cfg.C := by
    exact cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

/--
@isnad1 id=ne.0h1v.s3.0a8ac9ff2d17 from=translated src=- shape=94695d2c vocab=b2c46d71
-/
lemma C_ne_B : cfg.C ≠ cfg.B := by
  exact cfg.hABC.injective.ne (by decide : (2 : Fin 3) ≠ 1)

/--
@isnad1 id=eq.0h1v.s8.e0b9a8b46d27 from=translated src=- shape=facc9dba vocab=05ffda04
-/
lemma CO_circumradius : dist cfg.O cfg.C = cfg.ABC.circumradius := by
  exact dist_circumcenter_eq_circumradius' cfg.ABC 2

/--
@isnad1 id=ne.0h1v.s3.bda3a7327086 from=translated src=- shape=94695d2c vocab=2ef29232
-/
lemma C_ne_O : cfg.O ≠ cfg.C := by
  rw [← dist_pos, CO_circumradius]
  exact circumradius_pos cfg.ABC

/--
@isnad1 id=eq.0h1v.s9.582c321d6487 from=translated src=- shape=828c7cec vocab=c3d0b9a5
-/
lemma A_opposite_BC : {cfg.B, cfg.C} = Set.range (cfg.ABC.faceOpposite 0).points := by
  apply Set.eq_of_subset_of_card_le
  · intro x x_in
    simp at *
    rcases x_in with h'|h'
    · use 1
      rw [h']
      simp
      rfl
    · use 2
      rw [h']
      simp
      rfl
  · simp
    calc (Finset.image cfg.ABC.points {0}ᶜ).card
        ≤ ({0}ᶜ : Finset (Fin (2 + 1))).card := Finset.card_image_le
      _ = 2 := by
        rw [Finset.card_compl]
        simp
      _ = ({cfg.B, cfg.C} : Finset _).card := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp
        exact (C_ne_B cfg).symm

/--
@isnad1 id=collinea.0h1v.s8.8df000c59325 from=translated src=- shape=c56d48d1 vocab=22bba3f5
-/
lemma PBC_collinear : Collinear ℝ {cfg.P, cfg.B, cfg.C} := by
  apply collinear_insert_of_mem_affineSpan_pair
  rw [A_opposite_BC]
  apply altitudeFoot_mem_affineSpan_faceOpposite

/--
@isnad1 id=eq.1h2v.s8.1060906d313f from=translated src=- shape=0c9078db vocab=6b28e3c5
-/
lemma APx_eq : ∀ x ∈ ({cfg.B, cfg.C} : Set _), ∠ cfg.A cfg.P x = Real.pi / 2 := by
  intro x hx
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  rw [real_inner_comm]
  apply Submodule.IsOrtho.inner_eq (vectorSpan_isOrtho_altitude_direction cfg.ABC 0)
  · have h₁ := A_opposite_BC cfg
    simp at h₁
    apply vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
    · rw [← h₁]
      exact mem_affineSpan _ hx
    · rw [← h₁]
      exact Collinear.mem_affineSpan_of_mem_of_ne (PBC_collinear cfg) (by simp:_) (by simp:_) (by simp:_) (C_ne_B cfg).symm
  · apply vsub_mem_vectorSpan _ (mem_altitude cfg.ABC 0) (altitudeFoot_mem_altitude cfg.ABC 0)

/--
@isnad1 id=eq.0h1v.s7.4bcbf536ab12 from=translated src=- shape=cd6bb746 vocab=a8baae1e
-/
lemma APC_eq : ∠ cfg.A cfg.P cfg.C = Real.pi / 2 := by
  apply APx_eq
  simp

/--
@isnad1 id=eq.0h1v.s7.9d1e18221750 from=translated src=- shape=cd6bb746 vocab=0e1d48bb
-/
lemma APB_eq : ∠ cfg.A cfg.P cfg.B = Real.pi / 2 := by
  apply APx_eq
  simp

/--
@isnad1 id=eq.0h1v.s8.37d6363c6717 from=translated src=- shape=a4933a7f vocab=40ff7411
-/
lemma PC_eq : dist cfg.P cfg.C = dist cfg.C cfg.A * Real.cos (∠ cfg.A cfg.C cfg.P) := by
  symm
  rw [mul_comm, angle_comm, dist_comm cfg.C cfg.A, dist_comm cfg.P cfg.C]
  exact cos_angle_mul_dist_of_angle_eq_pi_div_two (APC_eq cfg)

/--
@isnad1 id=not.0h1v.s8.00e619b00419 from=translated src=- shape=0ffba361 vocab=c728a890
-/
lemma non_sbtw_BCP : ¬Sbtw ℝ cfg.B cfg.C cfg.P := by
  intro h
  have h₁ := h.angle₁₂₃_eq_pi
  contrapose! h₁
  apply ne_of_lt
  have h₂ := oangle_add (C_ne_B cfg).symm (A_ne_C cfg) h.ne_right.symm
  have h₃ := angle_le_pi_div_two_of_angle_eq_pi_div_two (APC_eq cfg)
  calc ∠ cfg.B cfg.C cfg.P
      ≤ ∠ cfg.B cfg.C cfg.A + ∠ cfg.P cfg.C cfg.A := by
        rw [angle_comm cfg.P cfg.C cfg.A]
        exact angle_le_angle_add_angle cfg.C cfg.B cfg.A cfg.P
    _ < Real.pi / 2 + Real.pi / 2 := by
      apply add_lt_add_of_lt_of_le cfg.hAcuteC h₃
    _ = Real.pi := by ring

/--
@isnad1 id=or.0h1v.s9.b7db0ee588bd from=translated src=- shape=9f4ccd45 vocab=a9d93686
-/
lemma wbtw_BPC : Wbtw ℝ cfg.P cfg.B cfg.C ∨ Wbtw ℝ cfg.C cfg.P cfg.B := by
  have h₁ := non_sbtw_BCP cfg
  have h₂ := (PBC_collinear cfg).wbtw_or_wbtw_or_wbtw
  contrapose! h₁
  constructor
  · tauto
  · rcases h₁ with ⟨h_PBC, h_CPB⟩
    constructor
    · exact C_ne_B cfg
    · contrapose! h_CPB
      rw [h_CPB]
      apply wbtw_self_left

/--
@isnad1 id=ne.0h1v.s3.27e59cd2e45b from=translated src=- shape=94695d2c vocab=7ab5e64a
-/
lemma P_ne_C : cfg.P ≠ cfg.C := by
  intro h
  have h₁ := cfg.hAcuteC
  contrapose! h₁
  apply le_of_eq
  rw [← h, angle_comm, APB_eq]

/--
@isnad1 id=eq.0h1v.s8.ae46e9e89170 from=translated src=- shape=67c77823 vocab=d5da563c
-/
lemma oriented_BCO_CAB : 2 • ∡ cfg.B cfg.C cfg.O + 2 • ∡ cfg.C cfg.A cfg.B = Real.pi := by
  apply Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  · apply mem_circumsphere cfg.ABC 2
  · apply mem_circumsphere cfg.ABC 0
  · apply mem_circumsphere cfg.ABC 1
  · exact A_ne_C cfg
  · exact A_ne_B cfg
  · exact C_ne_B cfg

/--
@isnad1 id=lt.0h1v.s7.926b9c5b0e6b from=translated src=- shape=cd6bb746 vocab=9ce1cad2
-/
lemma acute_BCO : ∠ cfg.B cfg.C cfg.O < Real.pi / 2 := by
  rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm (C_ne_O cfg)]
  apply Sphere.abs_oangle_center_right_toReal_lt_pi_div_two
  · apply mem_circumsphere cfg.ABC 2
  · apply mem_circumsphere cfg.ABC 1

/--
@isnad1 id=eq.0h1v.s8.fc43b3f32798 from=translated src=- shape=de1c7fec vocab=738317b2
-/
lemma BCO_CAB : ∠ cfg.B cfg.C cfg.O + ∠ cfg.C cfg.A cfg.B = Real.pi / 2 := by
  have h₁ := oriented_BCO_CAB cfg
  have h₂ := acute_BCO cfg
  have h₃ := cfg.hAcuteA
  rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm (C_ne_O cfg)] at *
  rw [angle_eq_abs_oangle_toReal (A_ne_C cfg).symm (A_ne_B cfg).symm] at *
  exact aux₃ h₁ h₂ h₃

/--
@isnad1 id=eq.1h2v.s8.d7494406ba43 from=translated src=- shape=5418e3b4 vocab=1c27476c
-/
lemma xCP_eq_xCB : ∀ x, x ≠ cfg.C → ∠ x cfg.C cfg.P = ∠ x cfg.C cfg.B := by
  intro x hx
  have h₁ : ∡ x cfg.C cfg.P = ∡ x cfg.C cfg.B := by
    apply eq_of_sub_eq_zero
    rw [oangle_sub_left hx (C_ne_B cfg).symm (P_ne_C cfg)]
    rw [oangle_eq_zero_iff_wbtw, wbtw_comm]
    exact wbtw_BPC cfg
  rw [angle_eq_abs_oangle_toReal hx (C_ne_B cfg).symm]
  rw [angle_eq_abs_oangle_toReal hx (P_ne_C cfg)]
  rw [h₁]

/--
@isnad1 id=eq.0h1v.s8.d2d7865e1632 from=translated src=- shape=062d83d3 vocab=1a09d5c5
-/
lemma OCP_eq_OCB : ∠ cfg.O cfg.C cfg.P = ∠ cfg.O cfg.C cfg.B := by
  exact xCP_eq_xCB cfg cfg.O (C_ne_O cfg)

/--
@isnad1 id=eq.0h1v.s8.29bfc8bbd6cf from=translated src=- shape=ab5b3a55 vocab=e331db83
-/
lemma CAB_OCP : ∠ cfg.C cfg.A cfg.B = Real.pi / 2 - ∠ cfg.O cfg.C cfg.P := by
  rw [← BCO_CAB, OCP_eq_OCB, angle_comm cfg.B cfg.C cfg.O]
  ring

/--
@isnad1 id=eq.0h1v.s8.d00287a5550b from=translated src=- shape=ef8d1b37 vocab=04fad8ea
-/
lemma oriented_BOC_BAC : ∡ cfg.B cfg.O cfg.C = 2 • ∡ cfg.B cfg.A cfg.C:= by
  apply Sphere.oangle_center_eq_two_zsmul_oangle
  · apply mem_circumsphere cfg.ABC 1
  · apply mem_circumsphere cfg.ABC 0
  · apply mem_circumsphere cfg.ABC 2
  · exact A_ne_B cfg
  · exact A_ne_C cfg

/--
@isnad1 id=ne.1h4v.s10.edb7a7d9f84f from=translated src=- shape=ec09eee5 vocab=e54a710d
-/
lemma angle_in_ABC_pos (i j k : Fin 3) (h : Function.Injective ![i, j, k])
  : ∠ (cfg.ABC.points i) (cfg.ABC.points j) (cfg.ABC.points k) ≠ 0 := by
  intro h'
  rw [angle_eq_zero_iff_ne_and_wbtw] at h'
  have h₁ : Function.Injective ![j, i, k] := by
    have h' : ![j, i, k] = Function.comp ![i, j, k] ![1, 0, 2]  := by
      ext x
      fin_cases x <;> simp
    rw [h']
    exact Function.Injective.comp h (by decide)
  have h₂ : Function.Injective ![j, k, i] := by
    have h' : ![j, k, i] = Function.comp ![i, j, k] ![1, 2, 0]  := by
      ext x
      fin_cases x <;> simp
    rw [h']
    exact Function.Injective.comp h (by decide)
  have h₃ := AffineIndependent.not_wbtw_of_injective j i k h₁ cfg.ABC.independent
  have h₄ := AffineIndependent.not_wbtw_of_injective j k i h₂ cfg.ABC.independent
  tauto

/--
@isnad1 id=not.0h1v.s8.21ebf2d09baf from=translated src=- shape=f3b4c4a2 vocab=70f9378d
-/
lemma BOC_non_collinear : ¬Collinear ℝ {cfg.B, cfg.O, cfg.C} := by
  intro h
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear] at h
  rw [oriented_BOC_BAC] at h
  apply Real.Angle.two_zsmul_eq_zero_iff.mpr at h
  have h₁ := cfg.hAcuteA
  rw [angle_comm] at h₁
  rw [angle_eq_abs_oangle_toReal (A_ne_B cfg).symm (A_ne_C cfg).symm] at h₁
  have h₂ := aux₄ h h₁
  rw [← angle_eq_abs_oangle_toReal (A_ne_B cfg).symm (A_ne_C cfg).symm] at h₂
  apply angle_in_ABC_pos cfg (1 : Fin 3) 0 2 (by decide)
  exact h₂

/--
@isnad1 id=not.0h1v.s8.d2bbc25fb913 from=translated src=- shape=f3b4c4a2 vocab=98d240f7
-/
lemma OCP_non_collinear : ¬Collinear ℝ {cfg.P, cfg.C, cfg.O} := by
  intro h
  apply BOC_non_collinear cfg
  have h₁ : cfg.O ∈ affineSpan ℝ {cfg.P, cfg.C} := by
    exact Collinear.mem_affineSpan_of_mem_of_ne h (by simp:_) (by simp:_) (by simp:_) (P_ne_C cfg)
  have h₂ : cfg.B ∈ affineSpan ℝ {cfg.P, cfg.C} := by
    exact Collinear.mem_affineSpan_of_mem_of_ne (PBC_collinear cfg) (by simp:_) (by simp:_) (by simp:_) (P_ne_C cfg)
  have h₃ := collinear_insert_insert_of_mem_affineSpan_pair h₁ h₂
  exact Collinear.subset (by grind:_) (h₃)

/--
@isnad1 id=eq.0h1v.s8.a87282f8a571 from=translated src=- shape=062d83d3 vocab=5d6a4f2c
-/
lemma ACP_eq_ACB : ∠ cfg.A cfg.C cfg.P = ∠ cfg.A cfg.C cfg.B := by
  exact xCP_eq_xCB cfg cfg.A (A_ne_C cfg)

/--
@isnad1 id=eq.0h1v.s8.5768e1a3375e from=translated src=- shape=de057873 vocab=c351c20a
-/
lemma CA_eq : dist cfg.C cfg.A = 2 * cfg.ABC.circumradius * Real.sin (∠ cfg.A cfg.B cfg.C) := by
  rw [angle_eq_abs_oangle_toReal (A_ne_B cfg) (C_ne_B cfg)]
  rw [aux₇]
  have h₁ : |(∡ cfg.A cfg.B cfg.C).sin| ≠ 0 := by
    rw [abs_ne_zero, Real.Angle.sin_ne_zero_iff]
    constructor
    · intro h'
      rw [oangle_eq_zero_iff_angle_eq_zero (A_ne_B cfg) (C_ne_B cfg)] at h'
      apply angle_in_ABC_pos cfg (0 : Fin 3) 1 2 (by decide)
      exact h'
    · apply oangle_eq_pi_iff_angle_eq_pi.not.mpr
      exact ne_of_lt (lt_trans cfg.hAcuteB (div_two_lt_of_pos Real.pi_pos))
  have h₂ : dist cfg.C cfg.A / |(∡ cfg.A cfg.B cfg.C).sin| = 2 * cfg.ABC.circumradius := by
    rw [circumradius, dist_comm]
    apply Sphere.dist_div_sin_oangle_eq_two_mul_radius
    · apply mem_circumsphere cfg.ABC 0
    · apply mem_circumsphere cfg.ABC 1
    · apply mem_circumsphere cfg.ABC 2
    · exact A_ne_B cfg
    · exact A_ne_C cfg
    · exact (C_ne_B cfg).symm
  exact (div_eq_iff h₁).mp h₂

/--
@isnad1 id=le.0h1v.s8.7923a2f55839 from=translated src=- shape=eb1a1456 vocab=9fd926fd
-/
lemma four_sin_B_cos_A_le_one : 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B) ≤ 1 := by
  have h₁ : Real.cos (∠ cfg.A cfg.C cfg.B) ≤ Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · apply add_nonneg (angle_nonneg _ _ _)
      positivity
    · apply angle_le_pi
    · nth_rw 2 [angle_comm]
      exact cfg.hAB
  have h₂ : 0 < Real.sin (∠ cfg.A cfg.B cfg.C) := by
    apply Real.sin_pos_of_mem_Ioo
    simp
    constructor
    · apply lt_of_le_of_ne (angle_nonneg _ _ _)
      symm
      exact angle_in_ABC_pos cfg (0 : Fin 3) 1 2 (by decide)
    · exact lt_trans cfg.hAcuteB (div_two_lt_of_pos Real.pi_pos)
  calc 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B)
      ≤ 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6) := by
        rw [mul_le_mul_iff_right₀]
        · exact h₁
        · positivity
    _ = 2 * (2 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by ring
    _ = 2 * (Real.sin (∠ cfg.A cfg.B cfg.C - (∠ cfg.A cfg.B cfg.C + Real.pi / 6)) + Real.sin (∠ cfg.A cfg.B cfg.C + (∠ cfg.A cfg.B cfg.C + Real.pi / 6))) := by
        rw [Real.two_mul_sin_mul_cos]
    _ = 2 * (Real.sin (- Real.pi / 6) + Real.sin (2 * ∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by ring_nf
    _ = 2 * (- 1 / 2 + Real.sin (2 * ∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by
        rw [neg_div, Real.sin_neg, Real.sin_pi_div_six, neg_div]
    _ ≤ 2 * (- 1 / 2 + 1) := by
        rw [mul_le_mul_iff_right₀]
        · rw [add_le_add_iff_left]
          apply Real.sin_le_one
        · norm_num
    _ = 1 := by norm_num

/--
@isnad1 id=le.0h1v.s8.0843e798f5d4 from=translated src=- shape=7f6d86a7 vocab=894b7cef
-/
lemma two_mul_PC_le_circumradius : 2 * dist cfg.P cfg.C ≤ cfg.ABC.circumradius := by
  rw [PC_eq, ACP_eq_ACB, CA_eq]
  calc 2 * (2 * circumradius cfg.ABC * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B))
      = circumradius cfg.ABC * (4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B)) := by ring
    _ ≤ circumradius cfg.ABC * 1 := by
      rw [mul_le_mul_iff_right₀ (circumradius_pos cfg.ABC)]
      exact four_sin_B_cos_A_le_one cfg
    _ = circumradius cfg.ABC := by ring

/--
@isnad1 id=lt.0h1v.s6.dfd578c911f4 from=translated src=- shape=64f957a3 vocab=0f7ca183
-/
lemma PC_lt_PO : dist cfg.P cfg.C < dist cfg.P cfg.O := by
  have h₁ : dist cfg.O cfg.C < dist cfg.O cfg.P + dist cfg.P cfg.C := by
    rw [dist_lt_dist_add_dist_iff]
    intro h'
    apply OCP_non_collinear cfg
    exact Collinear.subset (by grind:_) (h'.collinear)
  calc dist cfg.P cfg.C
      = 2 * dist cfg.P cfg.C - dist cfg.P cfg.C:= by ring
    _ ≤ cfg.ABC.circumradius - dist cfg.P cfg.C := sub_le_sub_right (two_mul_PC_le_circumradius cfg) _
    _ = dist cfg.O cfg.C - dist cfg.P cfg.C := by rw [CO_circumradius]
    _ < dist cfg.O cfg.P + dist cfg.P cfg.C - dist cfg.P cfg.C := sub_lt_sub_right h₁ _
    _ = dist cfg.O cfg.P := by ring
    _ = dist cfg.P cfg.O := by apply dist_comm

/--
@isnad1 id=lt.0h1v.s8.64816ff46a8a from=translated src=- shape=7ccc49c9 vocab=79db7510
-/
lemma COP_le_OCP : ∠ cfg.C cfg.O cfg.P < ∠ cfg.O cfg.C cfg.P := by
  rw [angle_comm cfg.C cfg.O cfg.P, angle_comm cfg.O cfg.C cfg.P]
  rw [angle_lt_iff_dist_lt (OCP_non_collinear cfg)]
  exact PC_lt_PO cfg

/--
@isnad1 id=lt.0h1v.s9.3fcb4170be92 from=translated src=- shape=e424e00e vocab=d536275e
-/
theorem result : ∠ cfg.C cfg.A cfg.B + ∠ cfg.C cfg.ABC.circumcenter cfg.P < Real.pi / 2 := by
  rw [CAB_OCP]
  calc Real.pi / 2 - ∠ cfg.O cfg.C cfg.P + ∠ cfg.C cfg.O cfg.P
      < Real.pi / 2 - ∠ cfg.O cfg.C cfg.P + ∠ cfg.O cfg.C cfg.P := add_lt_add_right (COP_le_OCP cfg) _
    _ = Real.pi / 2 := by ring

end Imo2001q1Cfg

end Imo2001P1
