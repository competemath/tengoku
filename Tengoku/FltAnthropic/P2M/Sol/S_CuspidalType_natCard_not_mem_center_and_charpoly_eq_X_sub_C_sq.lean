import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq

set_option autoImplicit false

open Polynomial CuspidalType

namespace Ws23C2

open Polynomial Matrix

section Generic

variable {F : Type*} [Field F] [DecidableEq F]

/--
@isnad1 id=and.1h2v.s8.813c6d69bc62 from=translated src=- shape=df19191c vocab=7ca00d32
-/
theorem nil_rel (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    N 1 1 = -N 0 0 ∧ N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
  have h := fun i j => congrFun (congrFun hN i) j
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h01 h10 h11
  refine ⟨?_, h00⟩
  by_contra hne
  have hsum : N 0 0 + N 1 1 ≠ 0 := fun hs => hne (by linear_combination hs)
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have ha : N 0 0 = 0 := by
    rw [hb, zero_mul, add_zero] at h00
    exact mul_self_eq_zero.mp h00
  have hd : N 1 1 = 0 := by
    rw [hb, mul_zero, zero_add] at h11
    exact mul_self_eq_zero.mp h11
  exact hsum (by rw [ha, hd, add_zero])

def nilOf (s t : F) : Matrix (Fin 2) (Fin 2) F :=
  if s = 0 then !![0, 0; t, 0] else !![t, s; -(t * t) / s, -t]

/--
@isnad1 id=eq.0h3v.s7.da2b842d5109 from=translated src=- shape=9f97dee5 vocab=ec69306a
-/
theorem nilOf_mul_self (s t : F) : nilOf s t * nilOf s t = 0 := by
  unfold nilOf
  split_ifs with hs
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; field_simp; ring)

/--
@isnad1 id=eq.0h3v.s5.f572f465d047 from=translated src=- shape=ffb14f58 vocab=e6b192fe
-/
theorem nilOf_apply_01 (s t : F) : nilOf s t 0 1 = s := by
  unfold nilOf; split_ifs with hs <;> simp [hs]

/--
@isnad1 id=iff.0h3v.s7.9fb9a16db665 from=translated src=- shape=f701a11a vocab=5e3f3612
-/
theorem nilOf_eq_zero_iff (s t : F) : nilOf s t = 0 ↔ s = 0 ∧ t = 0 := by
  constructor
  · intro h
    have hs : s = 0 := by simpa [nilOf_apply_01] using congrFun (congrFun h 0) 1
    refine ⟨hs, ?_⟩
    have h10 := congrFun (congrFun h 1) 0
    simpa [nilOf, hs] using h10
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf]

/--
@isnad1 id=injectiv.0h1v.s5.e924552f6531 from=translated src=- shape=2a7403dc vocab=aeffb873
-/
theorem nilOf_injective : Function.Injective (fun p : F × F => nilOf p.1 p.2) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only at h
  have hs : s = s' := by
    have := congrFun (congrFun h 0) 1
    rwa [nilOf_apply_01, nilOf_apply_01] at this
  subst hs
  by_cases hs0 : s = 0
  · have h10 := congrFun (congrFun h 1) 0
    simp [nilOf, hs0] at h10
    simp [h10]
  · have h00 := congrFun (congrFun h 0) 0
    simp [nilOf, hs0] at h00
    simp [h00]

/--
@isnad1 id=ex.1h2v.s7.36095bd70c1e from=translated src=- shape=1110ad1c vocab=ec69306a
-/
theorem exists_nilOf_eq (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    ∃ s t : F, nilOf s t = N := by
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  by_cases hb : N 0 1 = 0
  · have ha : N 0 0 = 0 := by
      rw [hb, zero_mul, add_zero] at hadbc
      exact mul_self_eq_zero.mp hadbc
    refine ⟨0, N 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf, ha, hb, hd]
  · refine ⟨N 0 1, N 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf, hb, hd]

    field_simp
    linear_combination -hadbc

/--
@isnad1 id=bijectiv.0h1v.s10.dd28b9332e6d from=translated src=- shape=dad02c8f vocab=adb5c2ff
-/
theorem nilOf_bijective :
    Function.Bijective (fun p : {p : F × F // p ≠ 0} =>
      (⟨nilOf p.1.1 p.1.2, fun h => p.2 (Prod.ext ((nilOf_eq_zero_iff _ _).mp h).1 ((nilOf_eq_zero_iff _ _).mp h).2),
        nilOf_mul_self _ _⟩ : {N : Matrix (Fin 2) (Fin 2) F // N ≠ 0 ∧ N * N = 0})) := by
  constructor
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have := congrArg Subtype.val h
    exact Subtype.ext (nilOf_injective this)
  · rintro ⟨N, hN0, hN⟩
    obtain ⟨s, t, rfl⟩ := exists_nilOf_eq N hN
    refine ⟨⟨(s, t), fun h => hN0 ?_⟩, rfl⟩
    rw [Prod.mk_eq_zero] at h
    exact (nilOf_eq_zero_iff s t).mpr h

def glOf (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) : GL (Fin 2) F :=
  ⟨z • (1 + N), z⁻¹ • (1 - N),
    by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz, one_smul]
      simp [mul_sub, add_mul, hN],
    by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz, one_smul]
      simp [sub_mul, mul_add, hN]⟩

omit [DecidableEq F] in
/--
@isnad1 id=eq.2h3v.s8.51d0b73aeda8 from=translated src=- shape=dda21ddb vocab=863027f8
-/
@[scoped simp] theorem val_glOf (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    ((glOf z hz N hN : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = z • (1 + N) := rfl

/--
@isnad1 id=eq.1h3v.s9.7b6f5efe39cb from=translated src=- shape=5455e67f vocab=5999f700
-/
theorem charpoly_smul_one_add (z : F) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    (z • (1 + N)).charpoly = (X - C z) ^ 2 := by
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  have htr : (z • (1 + N)).trace = 2 * z := by
    simp [Matrix.trace_fin_two, hd]; ring
  have hdet : (z • (1 + N)).det = z ^ 2 := by
    simp [Matrix.det_fin_two, hd]
    linear_combination (-(z ^ 2)) * hadbc
  rw [Matrix.charpoly_fin_two, htr, hdet, map_mul, map_pow, show C (2 : F) = (2 : F[X]) from map_ofNat C 2]
  ring

/--
@isnad1 id=not.3h3v.s9.702ef3e155de from=translated src=- shape=c8dd4020 vocab=c1f0bbfa
-/
theorem smul_one_add_not_mem_range_scalar (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F)
    (hN : N * N = 0) (hN0 : N ≠ 0) : z • (1 + N) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  have h := fun i j => congrFun (congrFun ha i) j
  have h01 := h 0 1
  have h10 := h 1 0
  simp [Matrix.scalar_apply, hz] at h01 h10

  have ha0 : N 0 0 = 0 := by
    rw [h01, zero_mul, add_zero] at hadbc
    exact mul_self_eq_zero.mp hadbc
  apply hN0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, ha0, hd]

abbrev S (F : Type*) [Field F] : Type _ :=
  {g : GL (Fin 2) F // g ∉ Subgroup.center (GL (Fin 2) F) ∧
      ∃ z : F, (g : Matrix (Fin 2) (Fin 2) F).charpoly = (X - C z) ^ 2}

def phi (x : Fˣ × {N : Matrix (Fin 2) (Fin 2) F // N ≠ 0 ∧ N * N = 0}) : S F :=
  ⟨glOf (x.1 : F) x.1.ne_zero x.2.1 x.2.2.2,
    by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, val_glOf]
      exact smul_one_add_not_mem_range_scalar _ x.1.ne_zero _ x.2.2.2 x.2.2.1,
    ⟨(x.1 : F), by rw [val_glOf]; exact charpoly_smul_one_add _ _ x.2.2.2⟩⟩

omit [DecidableEq F] in
theorem eq_of_X_sub_C_sq_eq {z z' : F} (h : (X - C z) ^ 2 = (X - C z') ^ 2) : z = z' := by
  have h1 := congrArg (Polynomial.eval z) h
  simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self] at h1
  have h2 : (z - z') ^ 2 = 0 := by
    rw [← h1]; norm_num
  have h3 : z - z' = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linear_combination h3

/--
@isnad1 id=injectiv.0h1v.s8.6ae681b8aa4c from=translated src=- shape=d3643413 vocab=318ddd74
-/
theorem phi_injective : Function.Injective (phi (F := F)) := by
  rintro ⟨z, N, hN0, hN⟩ ⟨z', N', hN0', hN'⟩ h
  have hval : (z : F) • (1 + N) = (z' : F) • (1 + N') := by
    have := congrArg (fun s : S F => ((s.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [phi] using this
  have hz : (z : F) = z' := by
    have h1 := charpoly_smul_one_add (z : F) N hN
    have h2 := charpoly_smul_one_add (z' : F) N' hN'
    rw [hval] at h1
    exact eq_of_X_sub_C_sq_eq (h1.symm.trans h2)
  have hzu : z = z' := Units.ext hz
  subst hzu
  have hN1 : 1 + N = 1 + N' := smul_right_injective _ z.ne_zero hval
  have : N = N' := add_left_cancel hN1
  subst this
  rfl

/--
@isnad1 id=surjecti.0h1v.s8.9194c8a90769 from=translated src=- shape=d3643413 vocab=12666e3d
-/
theorem phi_surjective : Function.Surjective (phi (F := F)) := by
  rintro ⟨g, hgc, z, hchar⟩

  have hCH : ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) * ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) = 0 := by
    have := Matrix.aeval_self_charpoly (g : Matrix (Fin 2) (Fin 2) F)
    rw [hchar] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sq] using this
  have hz : z ≠ 0 := by
    rintro rfl
    simp only [zero_smul, sub_zero] at hCH
    have h1 : ((g * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [Units.val_mul]; exact hCH
    exact (g * g).ne_zero h1
  set N : Matrix (Fin 2) (Fin 2) F := z⁻¹ • ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) with hNdef
  have hN : N * N = 0 := by
    rw [hNdef, smul_mul_assoc, mul_smul_comm, hCH, smul_zero, smul_zero]
  have hgN : z • (1 + N) = (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [hNdef, smul_add, smul_smul, mul_inv_cancel₀ hz, one_smul]
    abel
  have hN0 : N ≠ 0 := by
    intro h0
    apply hgc
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨z, ?_⟩
    rw [← hgN, h0, add_zero, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  refine ⟨⟨Units.mk0 z hz, ⟨N, hN0, hN⟩⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp [phi, hgN]

/--
@isnad1 id=bijectiv.0h1v.s8.d8451cbb8d9b from=translated src=- shape=d3643413 vocab=eea28c2e
-/
theorem phi_bijective : Function.Bijective (phi (F := F)) := ⟨phi_injective, phi_surjective⟩

end Generic

/--
@isnad1 id=eq.0h1v.s8.27a838103738 from=translated src=- shape=fb4cfce0 vocab=07fbda10
-/
theorem card_nil (q : ℕ) [Fact q.Prime] :
    Nat.card {N : Matrix (Fin 2) (Fin 2) (ZMod q) // N ≠ 0 ∧ N * N = 0} = q ^ 2 - 1 := by
  rw [← Nat.card_eq_of_bijective _ nilOf_bijective, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Fintype.card_subtype_eq, sq]

/--
@isnad1 id=eq.0h1v.s6.7322d86f5c21 from=translated src=- shape=ed31da93 vocab=2928254c
-/
theorem card_S (q : ℕ) [Fact q.Prime] : Nat.card (S (ZMod q)) = (q - 1) * (q ^ 2 - 1) := by
  rw [← Nat.card_eq_of_bijective _ phi_bijective, Nat.card_prod, card_nil, Nat.card_eq_fintype_card,
    ZMod.card_units]

end Ws23C2
open scoped _root_.P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq.Ws23C2

/--
@isnad1 id=eq.0h1v.s9.2fdfa194e8ba from=translated src=- shape=fbef39ab vocab=b6781a40
-/
theorem solution
    (q : ℕ) [Fact q.Prime]
    :
    Nat.card {g : GL2 q // g ∉ Subgroup.center (GL2 q) ∧
      ∃ z : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (X - C z) ^ 2} = (q - 1) * (q ^ 2 - 1) :=
  Ws23C2.card_S q
