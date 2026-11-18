import Tengoku.FltAnthropic.Definitions.Def_IharaAmalgamMap
import Tengoku.Seed.GroupTheory.PushoutI
import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.RingTheory.Coprime.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ihara_amalgamToGamma0Away_injective.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ihara_amalgamToGamma0Away_injective

namespace Ihara
export _root_.Ihara (slToAway coe_slToAway algebraMap_ZAway_injective slToAway_injective vertexZero vertexOne coe_vertexOne_eq vertex_compat amalgamToAway N_dvd_entry amalgamToGamma0Away amalgamToGamma0Away_injective_iff iharaEdge iharaEdge_zero iharaEdge_one pairFamily pairFamily_zero pairFamily_one pairFamily_compat ι₀ iota0_injective q_dvd_entry ι₁ iota1_injective mem_range_iota1_iff ZAway q_mul_invSelf)
namespace SolA2
open _root_.Ihara

namespace PingPong

open Monoid Monoid.PushoutI Subgroup

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
variable {K : Type*} [Group K] {X : Type*} [MulAction K X]
variable (φ : ∀ i, H →* G i) (f : ∀ i, G i →* K) (k : H →* K)

structure Data (Xs : ι → Set X) (o : X) : Prop where

  o_notMem : ∀ i, o ∉ Xs i

  base_smul_o : ∀ h : H, k h • o = o

  base_smul_mem : ∀ (h : H) (i : ι), ∀ x ∈ Xs i, k h • x ∈ Xs i

  of_smul_o : ∀ (i : ι) (g : G i), g ∉ (φ i).range → f i g • o ∈ Xs i

  of_smul_mem : ∀ (i j : ι), j ≠ i → ∀ (g : G i), g ∉ (φ i).range →
    ∀ x ∈ Xs j, f i g • x ∈ Xs i

variable {φ f k} {hf : ∀ i, (f i).comp (φ i) = k} {Xs : ι → Set X} {o : X}

section NormalWordOrbit

open _root_.Monoid.PushoutI.NormalWord

/--
@isnad1 id=eq.1h6v.s7.cd1cec3d4c2e from=translated src=- shape=12ca3525 vocab=29450aee
-/
theorem toWord_eq_empty_of_fstIdx_eq_none {d : Transversal φ} {w : NormalWord d}
    (hw : w.fstIdx = none) : w.toWord = CoprodI.Word.empty := by
  have hnil : w.toWord.toList = [] := by
    simpa [CoprodI.Word.fstIdx, List.head?_eq_none_iff] using hw
  exact CoprodI.Word.ext hnil

/--
@isnad1 id=eq.2h6v.s7.d70c72927d95 from=translated src=- shape=35406e71 vocab=161e70c2
-/
theorem prod_eq_one_of_fstIdx_eq_none {d : Transversal φ} {w : NormalWord d}
    (hw : w.fstIdx = none) (hhead : w.head = 1) : w.prod = 1 := by
  simp [NormalWord.prod, hhead, toWord_eq_empty_of_fstIdx_eq_none hw]

/--
@isnad1 id=eq.2h8v.s7.95c2b0634fa9 from=translated src=- shape=54ffd93f vocab=ecaa7c02
-/
theorem fstIdx_cons {d : Transversal φ} {i : ι} (g : G i) (w : NormalWord d)
    (hmw : w.fstIdx ≠ some i) (hgr : g ∉ (φ i).range) :
    (cons g w hmw hgr).fstIdx = some i := by
  simp [NormalWord.cons, CoprodI.Word.fstIdx, CoprodI.Word.cons]

variable (hf) in

/--
@isnad1 id=mem.3h13v.s9.5ba921bdaff6 from=translated src=- shape=b0ae1ee2 vocab=17f24cf6
-/
theorem lift_prod_smul_o_mem (pp : Data φ f k Xs o) {d : Transversal φ} (w : NormalWord d) :
    ∀ j ∈ w.fstIdx, PushoutI.lift f k hf w.prod • o ∈ Xs j := by
  classical
  induction w using NormalWord.consRecOn with
  | empty =>
    intro j hj
    simp [NormalWord.empty, CoprodI.Word.fstIdx] at hj
  | cons i g w hmw _hgn hgr hw1 ih =>
    intro j hj
    have hji : j = i := by
      rw [fstIdx_cons g w hmw hgr, Option.mem_def, Option.some.injEq] at hj
      exact hj.symm
    subst hji
    rw [prod_cons, map_mul, lift_of, mul_smul]
    rcases hw : w.fstIdx with _ | j'
    · rw [prod_eq_one_of_fstIdx_eq_none hw hw1, map_one, one_smul]
      exact pp.of_smul_o j g hgr
    · have hj'i : j' ≠ j := fun heq => hmw (by rw [hw, heq])
      exact pp.of_smul_mem j j' hj'i g hgr _ (ih j' (by rw [hw]; rfl))
  | base h w hw1 ih =>
    intro j hj
    have hj' : j ∈ w.fstIdx := by
      rw [show ((base φ) h • w).fstIdx = w.fstIdx from rfl] at hj
      exact hj
    rw [NormalWord.prod_smul, map_mul, lift_base, mul_smul]
    exact pp.base_smul_mem h j _ (ih j hj')

variable (hf) in

/--
@isnad1 id=ne.3h12v.s9.85d32abbba6a from=translated src=- shape=711beb92 vocab=842c026e
-/
theorem lift_prod_ne_one_of_fstIdx_isSome (pp : Data φ f k Xs o) {d : Transversal φ}
    (w : NormalWord d) (hw : w.fstIdx.isSome) :
    PushoutI.lift f k hf w.prod ≠ 1 := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hw
  intro hlift
  have := lift_prod_smul_o_mem hf pp w j (by rw [hj]; rfl)
  rw [hlift, one_smul] at this
  exact pp.o_notMem j this

end NormalWordOrbit

variable (hf) in

/--
@isnad1 id=injectiv.4h10v.s9.ffcf1cb1729d from=translated src=- shape=e2253809 vocab=e053fe3e
-/
theorem lift_injective (hφ : ∀ i, Function.Injective (φ i))
    (hk : Function.Injective k) (pp : Data φ f k Xs o) :
    Function.Injective (PushoutI.lift f k hf) := by
  classical
  rcases NormalWord.transversal_nonempty φ hφ with ⟨d⟩
  rw [injective_iff_map_eq_one]
  intro p hp
  set w : NormalWord d := NormalWord.equiv p with hw
  have hprod : w.prod = p := by
    rw [hw]; exact (NormalWord.equiv (d := d)).symm_apply_apply p
  rw [← hprod] at hp ⊢
  rcases hfst : w.fstIdx with _ | j
  · have hprod' : w.prod = PushoutI.base φ w.head := by
      simp [NormalWord.prod, toWord_eq_empty_of_fstIdx_eq_none hfst]
    rw [hprod', lift_base] at hp
    have hhead : w.head = 1 := hk (by rw [hp, map_one])
    rw [hprod', hhead, map_one]
  · exact absurd hp (lift_prod_ne_one_of_fstIdx_isSome hf pp w (by rw [hfst]; rfl))

end PingPong

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Reduction

variable (q : ℕ)

abbrev red (B : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  B.map (Int.castRingHom (ZMod q))

abbrev toAway (B : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  B.map (algebraMap ℤ (ZAway q))

/--
@isnad1 id=injectiv.1h1v.s5.c8a66db60d0e from=translated src=- shape=9b707f05 vocab=b7e6cb06
-/
theorem toAway_injective {q : ℕ} (hq : q ≠ 0) : Function.Injective (toAway q) :=
  Matrix.map_injective (algebraMap_ZAway_injective hq)

/--
@isnad1 id=eq.0h3v.s8.4a69d8b6b02c from=translated src=- shape=5365791d vocab=a465a862
-/
theorem toAway_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) : toAway q (A * B) = toAway q A * toAway q B :=
  Matrix.map_mul

/--
@isnad1 id=eq.0h3v.s7.81194cdb0e0a from=translated src=- shape=5365791d vocab=33a3fa3b
-/
theorem red_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) : red q (A * B) = red q A * red q B :=
  Matrix.map_mul

/--
@isnad1 id=eq.0h3v.s8.000a39ec778d from=translated src=- shape=430a421b vocab=f0d77034
-/
theorem row_one_mul {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 1 = A 1 0 • B 0 + A 1 1 • B 1 := by
  funext j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h3v.s8.a95845f3d3ac from=translated src=- shape=430a421b vocab=f0d77034
-/
theorem row_zero_mul {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 = A 0 0 • B 0 + A 0 1 • B 1 := by
  funext j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=ne.2h3v.s8.5d24db1b3e15 from=translated src=- shape=7ef6cd0e vocab=e9af30aa
-/
theorem smul_row_ne_zero {q : ℕ} [Fact q.Prime] {c : ZMod q} {v : Fin 2 → ZMod q}
    (hc : c ≠ 0) (hv : v ≠ 0) : c • v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hj := congrFun h j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left hc

/--
@isnad1 id=ne.2h2v.s7.8f1f313edbb3 from=translated src=- shape=dd76f03b vocab=11a849e9
-/
theorem row_zero_ne_zero_of_ne_zero {R : Type*} [Zero R] {B : Matrix (Fin 2) (Fin 2) R}
    (hB : B ≠ 0) (h1 : B 1 = 0) : B 0 ≠ 0 := by
  intro h0
  apply hB
  ext i j
  fin_cases i
  · exact congrFun h0 j
  · exact congrFun h1 j

/--
@isnad1 id=ne.1h2v.s8.2ef3a869d8ba from=translated src=- shape=1ccfe7c9 vocab=146e8739
-/
theorem red_one_one_ne_zero {q : ℕ} [Fact q.Prime] (γ : SL(2, ℤ))
    (h10 : red q (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    red q (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≠ 0 := by
  intro h11
  have hdet := congrArg (Int.castRingHom (ZMod q)) γ.det_coe
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at hdet
  simp only [red, map_apply] at h10 h11
  rw [h10, h11, mul_zero, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

/--
@isnad1 id=ne.1h3v.s8.d1eb76dcc5cf from=translated src=- shape=bffda1c3 vocab=30df2697
-/
theorem red_SL_mul_ne_zero {q : ℕ} (γ : SL(2, ℤ)) {B : Matrix (Fin 2) (Fin 2) (ZMod q)}
    (hB : B ≠ 0) : red q (γ : Matrix (Fin 2) (Fin 2) ℤ) * B ≠ 0 := by
  intro h
  apply hB
  have hinv : red q ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * red q (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = 1 := by
    rw [← red_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc B = (red q ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      red q (γ : Matrix (Fin 2) (Fin 2) ℤ)) * B := by rw [hinv, one_mul]
    _ = 0 := by rw [mul_assoc, h, mul_zero]

variable {q} in
/--
@isnad1 id=eq.0h3v.s8.a0d3390fb050 from=translated src=- shape=a5288a9d vocab=3d5d9ffd
-/
theorem smul_toAway (c : ℤ) (B : Matrix (Fin 2) (Fin 2) ℤ) :
    (algebraMap ℤ (ZAway q) c) • toAway q B = toAway q (c • B) := by
  ext i j
  simp only [toAway, Matrix.smul_apply, Matrix.map_apply]
  simp only [smul_eq_mul, map_mul]

variable {q} in
/--
@isnad1 id=eq.0h3v.s8.fb405471943d from=translated src=- shape=ab57a902 vocab=e55b575d
-/
theorem qpow_smul_toAway (n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) :
    (q : ZAway q) ^ n • toAway q B = toAway q (((q : ℤ) ^ n) • B) := by
  rw [← smul_toAway, map_pow, map_natCast]

def hMat (a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * a 0 0, a 0 1; (q : ℤ) * ((q : ℤ) * a 1 0), (q : ℤ) * a 1 1]

/--
@isnad1 id=eq.0h2v.s6.e81e3ab38fbc from=translated src=- shape=d30a105e vocab=26165b91
-/
theorem red_hMat_zero_zero (a : SL(2, ℤ)) : red q (hMat q a) 0 0 = 0 := by
  show (((q : ℤ) * a 0 0 : ℤ) : ZMod q) = 0
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/--
@isnad1 id=eq.0h2v.s7.34d62562a656 from=translated src=- shape=0aa01299 vocab=ab6890d5
-/
theorem red_hMat_zero_one (a : SL(2, ℤ)) :
    red q (hMat q a) 0 1 = red q (a : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := rfl

/--
@isnad1 id=eq.0h2v.s6.9fb5ff6972f7 from=translated src=- shape=d30a105e vocab=26165b91
-/
theorem red_hMat_one_zero (a : SL(2, ℤ)) : red q (hMat q a) 1 0 = 0 := by
  show (((q : ℤ) * ((q : ℤ) * a 1 0) : ℤ) : ZMod q) = 0
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/--
@isnad1 id=eq.0h2v.s6.6f8d7117c13b from=translated src=- shape=d30a105e vocab=26165b91
-/
theorem red_hMat_one_one (a : SL(2, ℤ)) : red q (hMat q a) 1 1 = 0 := by
  show (((q : ℤ) * a 1 1 : ℤ) : ZMod q) = 0
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/--
@isnad1 id=eq.0h3v.s8.1dd58eb24a3e from=translated src=- shape=034b8811 vocab=c4aba56b
-/
theorem red_hMat_mul_row_zero (a : SL(2, ℤ)) (B : Matrix (Fin 2) (Fin 2) ℤ) :
    red q (hMat q a * B) 0 = red q (a : Matrix (Fin 2) (Fin 2) ℤ) 0 1 • red q B 1 := by
  rw [red_mul, row_zero_mul, red_hMat_zero_zero, red_hMat_zero_one, zero_smul, zero_add]

/--
@isnad1 id=eq.0h3v.s7.48553c55dddc from=translated src=- shape=1364361c vocab=31d79d78
-/
theorem red_hMat_mul_row_one (a : SL(2, ℤ)) (B : Matrix (Fin 2) (Fin 2) ℤ) :
    red q (hMat q a * B) 1 = 0 := by
  rw [red_mul, row_one_mul, red_hMat_one_zero, red_hMat_one_one, zero_smul, zero_smul, add_zero]

end Reduction

section Sides

variable (q : ℕ)

def SideOne (g : SL(2, ZAway q)) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
    (q : ZAway q) ^ n • (g : Matrix (Fin 2) (Fin 2) (ZAway q)) = toAway q B ∧
      red q B ≠ 0 ∧ red q B 1 = 0

def SideZero (g : SL(2, ZAway q)) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
    (q : ZAway q) ^ n • (g : Matrix (Fin 2) (Fin 2) (ZAway q)) = toAway q B ∧ red q B 1 ≠ 0) ∨
  (∃ G : SL(2, ℤ), g = slToAway q G ∧ red q (G : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0)

variable {q}

/--
@isnad1 id=eq.3h4v.s10.ca71673bfbb8 from=translated src=- shape=9c6d2d36 vocab=974e88f9
-/
theorem red_eq_zero_of_integral (hq : q ≠ 0) {n : ℕ} (hn : 1 ≤ n) (G : SL(2, ℤ))
    {B : Matrix (Fin 2) (Fin 2) ℤ}
    (hB : (q : ZAway q) ^ n • ((slToAway q G : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q))
      = toAway q B) : red q B = 0 := by
  rw [coe_slToAway] at hB
  change (q : ZAway q) ^ n • toAway q (G : Matrix (Fin 2) (Fin 2) ℤ) = toAway q B at hB
  rw [qpow_smul_toAway] at hB
  have hB' : B = ((q : ℤ) ^ n) • (G : Matrix (Fin 2) (Fin 2) ℤ) := (toAway_injective hq hB).symm
  rw [hB']
  ext i j
  simp only [red, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
  simp only [smul_eq_mul, Int.coe_castRingHom, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.mp hn), zero_mul]

/--
@isnad1 id=eq.1h5v.s10.89d89b6f784f from=translated src=- shape=ff93c5ec vocab=984634a5
-/
theorem qpow_smul_slToAway_mul (γ : SL(2, ℤ)) {n : ℕ} {g : SL(2, ZAway q)}
    {B : Matrix (Fin 2) (Fin 2) ℤ}
    (hB : (q : ZAway q) ^ n • (g : Matrix (Fin 2) (Fin 2) (ZAway q)) = toAway q B) :
    (q : ZAway q) ^ n • ((slToAway q γ * g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      toAway q ((γ : Matrix (Fin 2) (Fin 2) ℤ) * B) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slToAway, toAway_mul, ← hB]
  exact (Matrix.mul_smul (toAway q (γ : Matrix (Fin 2) (Fin 2) ℤ)) ((q : ZAway q) ^ n)
    (g : Matrix (Fin 2) (Fin 2) (ZAway q))).symm

/--
@isnad1 id=sideone.2h3v.s10.1c5d593034fe from=translated src=- shape=a82d76c0 vocab=71928cef
-/
theorem SideOne.mul_left [Fact q.Prime] (γ : SL(2, ℤ))
    (hγ : red q (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) {g : SL(2, ZAway q)} (hg : SideOne q g) :
    SideOne q (slToAway q γ * g) := by
  obtain ⟨n, hn, B, hB, hB0, hB1⟩ := hg
  refine ⟨n, hn, (γ : Matrix (Fin 2) (Fin 2) ℤ) * B, qpow_smul_slToAway_mul γ hB, ?_, ?_⟩
  · rw [red_mul]
    exact red_SL_mul_ne_zero γ hB0
  · rw [red_mul, row_one_mul, hγ, hB1, zero_smul, smul_zero, add_zero]

/--
@isnad1 id=sidezero.2h3v.s10.c06245a31a87 from=translated src=- shape=a82d76c0 vocab=76ad8df2
-/
theorem SideZero.mul_left [Fact q.Prime] (γ : SL(2, ℤ))
    (hγ : red q (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) {g : SL(2, ZAway q)} (hg : SideZero q g) :
    SideZero q (slToAway q γ * g) := by
  have h11 := red_one_one_ne_zero γ hγ
  rcases hg with ⟨n, hn, B, hB, hB1⟩ | ⟨G, rfl, hG⟩
  · refine Or.inl ⟨n, hn, (γ : Matrix (Fin 2) (Fin 2) ℤ) * B, qpow_smul_slToAway_mul γ hB, ?_⟩
    rw [red_mul, row_one_mul, hγ, zero_smul, zero_add]
    exact smul_row_ne_zero h11 hB1
  · refine Or.inr ⟨γ * G, by rw [map_mul], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, red_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hγ, zero_mul, zero_add]
    exact mul_ne_zero h11 hG

end Sides

section PingPongDatum

variable (N q : ℕ)

def edgeStab : Subgroup SL(2, ZAway q) := ((vertexZero N q).comp (ι₀ N q)).range

abbrev EdgeSpace : Type := SL(2, ZAway q) ⧸ edgeStab N q

def baseEdge : EdgeSpace N q := ((1 : SL(2, ZAway q)) : EdgeSpace N q)

def halfSpace : Fin 2 → Set (EdgeSpace N q) :=
  ![{x | ∃ g : SL(2, ZAway q), (g : EdgeSpace N q) = x ∧ SideZero q g},
    {x | ∃ g : SL(2, ZAway q), (g : EdgeSpace N q) = x ∧ SideOne q g}]

variable {N q}

/--
@isnad1 id=iff.0h3v.s11.56989bc6b746 from=translated src=- shape=b5c0cf8a vocab=073a48fd
-/
theorem mem_range_iota0_iff (a : Gamma0 N) :
    a ∈ (ι₀ N q).range ↔ (a : SL(2, ℤ)) ∈ Gamma0 (N * q) := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact γ.2
  · intro h
    exact ⟨⟨a, h⟩, Subtype.ext rfl⟩

/--
@isnad1 id=ex.1h3v.s10.9ee50e8e3f26 from=translated src=- shape=2cccaf94 vocab=99d7fc98
-/
theorem exists_of_coe_eq_baseEdge {g : SL(2, ZAway q)} (hg : (g : EdgeSpace N q) = baseEdge N q) :
    ∃ γ : Gamma0 (N * q), g = slToAway q (γ : SL(2, ℤ)) := by
  rw [baseEdge, QuotientGroup.eq, mul_one] at hg
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (inv_mem_iff.mp hg)
  exact ⟨γ, hγ.symm⟩

/--
@isnad1 id=eq.0h3v.s9.e2dbf6efb0fd from=translated src=- shape=fe2524ac vocab=3f95b137
-/
theorem red_gamma0_mul_one_zero (γ : Gamma0 (N * q)) :
    red q (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = 0 := by
  simp only [red, map_apply, Int.coe_castRingHom]
  rw [CharP.intCast_eq_zero_iff (ZMod q) q]
  exact q_dvd_entry N q γ

/--
@isnad1 id=eq.0h3v.s11.8704f8c3a0f0 from=translated src=- shape=5d772318 vocab=90d1b9a4
-/
theorem q_smul_vertexOne (a : Gamma0 N) :
    (q : ZAway q) • ((vertexOne N q a : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      toAway q (hMat q (a : SL(2, ℤ))) := by
  rw [coe_vertexOne_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · show (q : ZAway q) • algebraMap ℤ (ZAway q) ((a : SL(2, ℤ)) 0 0) =
      algebraMap ℤ (ZAway q) ((q : ℤ) * (a : SL(2, ℤ)) 0 0)
    rw [map_mul, map_natCast, smul_eq_mul]
  · show (q : ZAway q) • (algebraMap ℤ (ZAway q) ((a : SL(2, ℤ)) 0 1) *
        IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) =
      algebraMap ℤ (ZAway q) ((a : SL(2, ℤ)) 0 1)
    rw [smul_eq_mul, mul_left_comm, q_mul_invSelf, mul_one]
  · show (q : ZAway q) • ((q : ZAway q) * algebraMap ℤ (ZAway q) ((a : SL(2, ℤ)) 1 0)) =
      algebraMap ℤ (ZAway q) ((q : ℤ) * ((q : ℤ) * (a : SL(2, ℤ)) 1 0))
    rw [map_mul, map_mul, map_natCast, smul_eq_mul]
  · show (q : ZAway q) • algebraMap ℤ (ZAway q) ((a : SL(2, ℤ)) 1 1) =
      algebraMap ℤ (ZAway q) ((q : ℤ) * (a : SL(2, ℤ)) 1 1)
    rw [map_mul, map_natCast, smul_eq_mul]

/--
@isnad1 id=eq.1h6v.s12.2ed5126fc5da from=translated src=- shape=30bb2fbc vocab=325ec563
-/
theorem qpow_succ_smul_vertexOne_mul (a : Gamma0 N) {n : ℕ} {g : SL(2, ZAway q)}
    {B : Matrix (Fin 2) (Fin 2) ℤ}
    (hB : (q : ZAway q) ^ n • (g : Matrix (Fin 2) (Fin 2) (ZAway q)) = toAway q B) :
    (q : ZAway q) ^ (n + 1) •
        ((vertexOne N q a * g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      toAway q (hMat q (a : SL(2, ℤ)) * B) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, toAway_mul, ← q_smul_vertexOne, ← hB, pow_succ', ← smul_smul]
  have h1 := (Matrix.mul_smul ((vertexOne N q a : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q))
    ((q : ZAway q) ^ n) (g : Matrix (Fin 2) (Fin 2) (ZAway q))).symm
  have h2 := (Matrix.smul_mul (q : ZAway q)
    ((vertexOne N q a : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q))
    ((q : ZAway q) ^ n • (g : Matrix (Fin 2) (Fin 2) (ZAway q)))).symm
  rw [← h2, ← h1]

/--
@isnad1 id=ne.2h3v.s11.86292d2fb8aa from=translated src=- shape=cd9e3cf4 vocab=08ae1909
-/
theorem red_one_zero_ne_zero_of_not_mem_range (hqN : N.Coprime q) {a : Gamma0 N}
    (ha : a ∉ (ι₀ N q).range) : red q ((a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0 := by
  intro h10
  apply ha
  rw [mem_range_iota0_iff, Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)]
  simp only [red, map_apply, Int.coe_castRingHom] at h10
  rw [CharP.intCast_eq_zero_iff (ZMod q) q] at h10
  have hN : (N : ℤ) ∣ ((a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := N_dvd_entry N a
  push_cast
  exact (Nat.isCoprime_iff_coprime.mpr hqN).mul_dvd hN h10

/--
@isnad1 id=ne.2h3v.s11.ab4af621a2c7 from=translated src=- shape=63a820b7 vocab=a4de33f8
-/
theorem red_zero_one_ne_zero_of_not_mem_range (hq : q ≠ 0) {b : Gamma0 N}
    (hb : b ∉ (ι₁ N q).range) : red q ((b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ≠ 0 := by
  intro h
  apply hb
  rw [mem_range_iota1_iff N hq]
  simp only [red, map_apply, Int.coe_castRingHom] at h
  exact (CharP.intCast_eq_zero_iff (ZMod q) q _).mp h

section Conditions

/--
@isnad1 id=not.0h2v.s5.44301dcc3d4e from=translated src=- shape=52892dc0 vocab=27cb7cc8
-/
theorem baseEdge_notMem_halfSpace_zero [Fact q.Prime] : baseEdge N q ∉ halfSpace N q 0 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rintro ⟨g, hg, hside⟩
  obtain ⟨γ, rfl⟩ := exists_of_coe_eq_baseEdge hg
  rcases hside with ⟨n, hn, B, hB, hB1⟩ | ⟨G, hG, hG10⟩
  · exact hB1 (by rw [red_eq_zero_of_integral hq0 hn _ hB]; rfl)
  · rw [(slToAway_injective hq0 hG).symm] at hG10
    exact hG10 (red_gamma0_mul_one_zero γ)

/--
@isnad1 id=not.0h2v.s5.cd1f375ff1ad from=translated src=- shape=52892dc0 vocab=27cb7cc8
-/
theorem baseEdge_notMem_halfSpace_one [Fact q.Prime] : baseEdge N q ∉ halfSpace N q 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rintro ⟨g, hg, n, hn, B, hB, hB0, -⟩
  obtain ⟨γ, rfl⟩ := exists_of_coe_eq_baseEdge hg
  exact hB0 (red_eq_zero_of_integral hq0 hn _ hB)

/--
@isnad1 id=eq.0h3v.s12.94014ccae169 from=translated src=- shape=4336dfa0 vocab=2d111597
-/
theorem base_smul_baseEdge (h : Gamma0 (N * q)) :
    (vertexZero N q).comp (ι₀ N q) h • baseEdge N q = baseEdge N q := by
  rw [baseEdge, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact Subgroup.inv_mem _ ⟨h, rfl⟩

/--
@isnad1 id=mem.1h4v.s12.83bc01f1adf2 from=translated src=- shape=1c1cbd5b vocab=4e434974
-/
theorem base_smul_mem_halfSpace_zero [Fact q.Prime] (h : Gamma0 (N * q)) :
    ∀ x ∈ halfSpace N q 0, (vertexZero N q).comp (ι₀ N q) h • x ∈ halfSpace N q 0 := by
  rintro x ⟨g, rfl, hside⟩
  exact ⟨(vertexZero N q).comp (ι₀ N q) h * g, by rw [MulAction.Quotient.smul_coe, smul_eq_mul],
    hside.mul_left _ (red_gamma0_mul_one_zero h)⟩

/--
@isnad1 id=mem.1h4v.s12.cb4ef4d73d07 from=translated src=- shape=1c1cbd5b vocab=4e434974
-/
theorem base_smul_mem_halfSpace_one [Fact q.Prime] (h : Gamma0 (N * q)) :
    ∀ x ∈ halfSpace N q 1, (vertexZero N q).comp (ι₀ N q) h • x ∈ halfSpace N q 1 := by
  rintro x ⟨g, rfl, hside⟩
  exact ⟨(vertexZero N q).comp (ι₀ N q) h * g, by rw [MulAction.Quotient.smul_coe, smul_eq_mul],
    hside.mul_left _ (red_gamma0_mul_one_zero h)⟩

/--
@isnad1 id=mem.2h3v.s12.16f87a5c2cb2 from=translated src=- shape=c2617e20 vocab=d8f4e975
-/
theorem vertexZero_smul_baseEdge (hqN : N.Coprime q) {a : Gamma0 N} (ha : a ∉ (ι₀ N q).range) :
    vertexZero N q a • baseEdge N q ∈ halfSpace N q 0 := by
  refine ⟨vertexZero N q a, by rw [baseEdge, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one], ?_⟩
  exact Or.inr ⟨(a : SL(2, ℤ)), rfl, red_one_zero_ne_zero_of_not_mem_range hqN ha⟩

/--
@isnad1 id=mem.1h3v.s12.6d35729231a9 from=translated src=- shape=f4c8909a vocab=4d56ae45
-/
theorem vertexOne_smul_baseEdge [Fact q.Prime] {b : Gamma0 N} (hb : b ∉ (ι₁ N q).range) :
    vertexOne N q b • baseEdge N q ∈ halfSpace N q 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨vertexOne N q b, by rw [baseEdge, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one], ?_⟩
  refine ⟨1, le_rfl, hMat q (b : SL(2, ℤ)), by rw [pow_one, q_smul_vertexOne], ?_, ?_⟩
  · intro h0
    exact red_zero_one_ne_zero_of_not_mem_range hq0 hb
      (by rw [← red_hMat_zero_one]; exact congrFun (congrFun h0 0) 1)
  · funext j
    fin_cases j
    · exact red_hMat_one_zero q _
    · exact red_hMat_one_one q _

/--
@isnad1 id=mem.3h4v.s12.8da83fd39a11 from=translated src=- shape=0f8c63f6 vocab=05d642ae
-/
theorem vertexZero_smul_mem [Fact q.Prime] (hqN : N.Coprime q) {a : Gamma0 N} (ha : a ∉ (ι₀ N q).range) :
    ∀ x ∈ halfSpace N q 1, vertexZero N q a • x ∈ halfSpace N q 0 := by
  rintro x ⟨g, rfl, n, hn, B, hB, hB0, hB1⟩
  refine ⟨vertexZero N q a * g, by rw [MulAction.Quotient.smul_coe, smul_eq_mul], ?_⟩
  refine Or.inl ⟨n, hn, ((a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B,
    qpow_smul_slToAway_mul (a : SL(2, ℤ)) hB, ?_⟩
  rw [red_mul, row_one_mul, hB1, smul_zero, add_zero]
  exact smul_row_ne_zero (red_one_zero_ne_zero_of_not_mem_range hqN ha)
    (row_zero_ne_zero_of_ne_zero hB0 hB1)

/--
@isnad1 id=mem.2h4v.s12.82bcfe3e0b14 from=translated src=- shape=42bef50c vocab=2b5336c2
-/
theorem vertexOne_smul_mem [Fact q.Prime] {b : Gamma0 N} (hb : b ∉ (ι₁ N q).range) :
    ∀ x ∈ halfSpace N q 0, vertexOne N q b • x ∈ halfSpace N q 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hβ := red_zero_one_ne_zero_of_not_mem_range hq0 hb
  rintro x ⟨g, rfl, hside⟩
  refine ⟨vertexOne N q b * g, by rw [MulAction.Quotient.smul_coe, smul_eq_mul], ?_⟩
  rcases hside with ⟨n, hn, B, hB, hB1⟩ | ⟨G, rfl, hG⟩
  · refine ⟨n + 1, by omega, hMat q (b : SL(2, ℤ)) * B, qpow_succ_smul_vertexOne_mul b hB, ?_,
      red_hMat_mul_row_one q _ B⟩
    intro h0
    have h := red_hMat_mul_row_zero q (b : SL(2, ℤ)) B
    rw [h0] at h
    exact smul_row_ne_zero hβ hB1 (show _ = (0 : Fin 2 → ZMod q) from h.symm)
  · have hG' : (q : ZAway q) ^ 0 •
        ((slToAway q G : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
          toAway q (G : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [pow_zero, one_smul, coe_slToAway]
    refine ⟨0 + 1, le_rfl, hMat q (b : SL(2, ℤ)) * (G : Matrix (Fin 2) (Fin 2) ℤ),
      qpow_succ_smul_vertexOne_mul b hG', ?_, red_hMat_mul_row_one q _ _⟩
    intro h0
    have h := red_hMat_mul_row_zero q (b : SL(2, ℤ)) (G : Matrix (Fin 2) (Fin 2) ℤ)
    rw [h0] at h
    have hG1 : red q ((G : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 ≠ 0 := fun h1 => hG (congrFun h1 0)
    exact smul_row_ne_zero hβ hG1 (show _ = (0 : Fin 2 → ZMod q) from h.symm)

end Conditions

/--
@isnad1 id=data.2h2v.s11.91ac823dcdb5 from=translated src=- shape=25e19fdd vocab=e0e9a18d
-/
theorem pingPongData (hq : q.Prime) (hqN : N.Coprime q) :
    PingPong.Data (X := EdgeSpace N q) (iharaEdge N q)
      (pairFamily (vertexZero N q) (vertexOne N q)) ((vertexZero N q).comp (ι₀ N q))
      (halfSpace N q) (baseEdge N q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨?_, base_smul_baseEdge, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.mpr ⟨baseEdge_notMem_halfSpace_zero, baseEdge_notMem_halfSpace_one⟩
  · intro h
    exact Fin.forall_fin_two.mpr ⟨base_smul_mem_halfSpace_zero h, base_smul_mem_halfSpace_one h⟩
  · refine Fin.forall_fin_two.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rw [iharaEdge_zero] at ha
      rw [pairFamily_zero]
      exact vertexZero_smul_baseEdge hqN ha
    · rw [iharaEdge_one] at hb
      rw [pairFamily_one]
      exact vertexOne_smul_baseEdge hb
  · refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun h => absurd rfl h, fun _ a ha => ?_⟩,
      Fin.forall_fin_two.mpr ⟨fun _ b hb => ?_, fun h => absurd rfl h⟩⟩
    · rw [iharaEdge_zero] at ha
      rw [pairFamily_zero]
      exact vertexZero_smul_mem hqN ha
    · rw [iharaEdge_one] at hb
      rw [pairFamily_one]
      exact vertexOne_smul_mem hb

/--
@isnad1 id=injectiv.2h2v.s9.06ca0ec364aa from=translated src=- shape=d9bd4498 vocab=6e7744d3
-/
theorem amalgamToAway_injective (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (amalgamToAway N q) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hφ : ∀ i, Function.Injective (iharaEdge N q i) :=
    Fin.forall_fin_two.mpr ⟨iota0_injective N q, iota1_injective N hq0⟩
  have hk : Function.Injective ((vertexZero N q).comp (ι₀ N q)) :=
    (slToAway_injective hq0).comp (Subtype.val_injective.comp (iota0_injective N q))
  exact PingPong.lift_injective (hf := pairFamily_compat _ _ (vertex_compat N q)) hφ hk
    (pingPongData hq hqN)

/--
@isnad1 id=injectiv.2h2v.s12.109f3e1a0579 from=translated src=- shape=10814efe vocab=df54f38e
-/
theorem amalgamToGamma0Away_injective (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (amalgamToGamma0Away N q) :=
  (amalgamToGamma0Away_injective_iff N q).mpr (amalgamToAway_injective hq hqN)

end PingPongDatum

end Ihara.SolA2
open scoped _root_.P2MW.S_Ihara_amalgamToGamma0Away_injective.Ihara _root_.P2MW.S_Ihara_amalgamToGamma0Away_injective.Ihara.SolA2
open scoped _root_.P2MW.S_Ihara_amalgamToGamma0Away_injective.Ihara

/--
@isnad1 id=injectiv.2h2v.s12.109f3e1a0579 from=translated src=- shape=10814efe vocab=df54f38e
-/
theorem solution {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (Ihara.amalgamToGamma0Away N q) :=
  Ihara.SolA2.amalgamToGamma0Away_injective hq hqN
