import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite

set_option autoImplicit false

open Matrix MatrixGroups

namespace P2mDicksonCore

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

def tr (M : 𝕄) : K := M 0 0 + M 1 1

/--
@isnad1 id=eq.0h4v.s8.b3afc7feee32 from=translated src=- shape=7ab46a6b vocab=f15d903d
-/
lemma tr_smul_one_add (x y : K) (g : 𝕄) : tr (x • (1 : 𝕄) + y • g) = 2 * x + y * tr g := by
  simp [tr]; ring

/--
@isnad1 id=eq.0h4v.s9.d7084d1a2f9d from=translated src=- shape=a271978c vocab=165806dd
-/
lemma det_smul_one_add (x y : K) (g : 𝕄) :
    (x • (1 : 𝕄) + y • g).det = x ^ 2 + x * y * tr g + y ^ 2 * g.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [tr]; ring

/--
@isnad1 id=eq.0h3v.s7.b13da4671060 from=translated src=- shape=6ebd863d vocab=9b757888
-/
lemma tr_mul_comm (a b : 𝕄) : tr (a * b) = tr (b * a) := by
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two]; ring

/--
@isnad1 id=eq.1h4v.s8.85ed47e8a4d2 from=translated src=- shape=c4b3340f vocab=9b757888
-/
lemma tr_conj {a b c : 𝕄} (h : c * a = 1) : tr (a * b * c) = tr b := by
  rw [tr_mul_comm, ← mul_assoc, h, one_mul]

/--
@isnad1 id=eq.0h1v.s6.fe20d13a37b9 from=translated src=- shape=715f3820 vocab=ef0e28bd
-/
lemma tr_one : tr (1 : 𝕄) = 2 := by simp [tr]; norm_num

/--
@isnad1 id=eq.0h2v.s6.fbbde28b7ff5 from=translated src=- shape=5bd024ce vocab=ebbc08d5
-/
lemma tr_neg (a : 𝕄) : tr (-a) = -tr a := by simp [tr]; ring

/--
@isnad1 id=eq.0h3v.s6.e0384f4f826a from=translated src=- shape=54fd0571 vocab=a0eb3276
-/
lemma tr_smul (c : K) (a : 𝕄) : tr (c • a) = c * tr a := by simp [tr]; ring

def IsScalarMat (g : 𝕄) : Prop := ∃ c : K, g = c • (1 : 𝕄)

/--
@isnad1 id=iff.0h2v.s7.6df610cc9690 from=translated src=- shape=d165eb2d vocab=5e844358
-/
lemma isScalarMat_iff (g : 𝕄) : IsScalarMat g ↔ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 0 = g 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨h01, h10, h00⟩
    refine ⟨g 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

lemma eq_smul_one_add_smul_of_entries {m g : 𝕄} {x y : K}
    (h00 : m 0 0 = x + y * g 0 0) (h01 : m 0 1 = y * g 0 1) (h10 : m 1 0 = y * g 1 0)
    (h11 : m 1 1 = x + y * g 1 1) : m = x • (1 : 𝕄) + y • g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

/--
@isnad1 id=iff.1h3v.s9.97d763dfc17a from=translated src=- shape=3b788de1 vocab=9bd6a5ad
-/
lemma commute_iff {g : 𝕄} (hg : ¬ IsScalarMat g) (m : 𝕄) :
    m * g = g * m ↔ ∃ x y : K, m = x • (1 : 𝕄) + y • g := by
  constructor
  · intro h
    have e := fun i j => congrFun (congrFun h i) j
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    rw [isScalarMat_iff] at hg
    push Not at hg
    by_cases hb : g 0 1 = 0
    · by_cases hc : g 1 0 = 0
      ·
        have hsub : g 0 0 - g 1 1 ≠ 0 := sub_ne_zero.mpr (hg hb hc)
        rw [hb] at e01; rw [hc] at e10
        obtain ⟨y, hy⟩ : ∃ y : K, y = (m 0 0 - m 1 1) / (g 0 0 - g 1 1) := ⟨_, rfl⟩
        refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) ?_ ?_ ?_⟩
        · rw [hb, mul_zero]
          have : m 0 1 * (g 0 0 - g 1 1) = 0 := by linear_combination -e01
          exact (mul_eq_zero.mp this).resolve_right hsub
        · rw [hc, mul_zero]
          have : m 1 0 * (g 0 0 - g 1 1) = 0 := by linear_combination e10
          exact (mul_eq_zero.mp this).resolve_right hsub
        · have : y * (g 0 0 - g 1 1) = m 0 0 - m 1 1 := by rw [hy]; field_simp
          linear_combination this
      ·
        obtain ⟨y, hy⟩ : ∃ y : K, y = m 1 0 / g 1 0 := ⟨_, rfl⟩
        have hy' : y * g 1 0 = m 1 0 := by rw [hy]; field_simp
        refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) ?_ ?_ ?_⟩
        · rw [hb, mul_zero]
          rw [hb] at e11
          have : g 1 0 * m 0 1 = 0 := by linear_combination -e11
          exact (mul_eq_zero.mp this).resolve_left hc
        · exact hy'.symm
        · have : g 1 0 * (m 1 1 - m 0 0 - y * (g 1 1 - g 0 0)) = 0 := by
            linear_combination e10 - (g 1 1 - g 0 0) * hy'
          have := (mul_eq_zero.mp this).resolve_left hc
          linear_combination this
    ·
      obtain ⟨y, hy⟩ : ∃ y : K, y = m 0 1 / g 0 1 := ⟨_, rfl⟩
      have hy' : y * g 0 1 = m 0 1 := by rw [hy]; field_simp
      refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) hy'.symm ?_ ?_⟩
      · have : g 0 1 * (m 1 0 - y * g 1 0) = 0 := by
          linear_combination -e00 - g 1 0 * hy'
        have := (mul_eq_zero.mp this).resolve_left hb
        linear_combination this
      · have : g 0 1 * (m 1 1 - m 0 0 - y * (g 1 1 - g 0 0)) = 0 := by
          linear_combination -e01 - (g 1 1 - g 0 0) * hy'
        have := (mul_eq_zero.mp this).resolve_left hb
        linear_combination this
  · rintro ⟨x, y, rfl⟩
    rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul,
      mul_one]

/--
@isnad1 id=or.4h4v.s10.f4b57c0e08b8 from=translated src=- shape=d58682c3 vocab=820161e3
-/
lemma smul_one_add_eq_of_tr_sq_eq_four {g : 𝕄} (hg : (tr g) ^ 2 ≠ 4) (hdetg : g.det = 1)
    {x y : K} (hdet : (x • (1 : 𝕄) + y • g).det = 1)
    (htr : (tr (x • (1 : 𝕄) + y • g)) ^ 2 = 4) :
    x • (1 : 𝕄) + y • g = 1 ∨ x • (1 : 𝕄) + y • g = -1 := by
  rw [det_smul_one_add, hdetg, mul_one] at hdet
  rw [tr_smul_one_add] at htr
  have hy : y ^ 2 * (4 - (tr g) ^ 2) = 0 := by linear_combination 4 * hdet - htr
  have hy0 : y = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact pow_eq_zero_iff two_ne_zero |>.mp h
    · exact absurd (by linear_combination -h) hg
  subst hy0
  have hx : (x - 1) * (x + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hx with h | h
  · left; rw [sub_eq_zero.mp h]; simp
  · right; rw [eq_neg_of_add_eq_zero_left h]; simp

/--
@isnad1 id=or.5h4v.s10.178f21f37096 from=translated src=- shape=524d0ea3 vocab=c18487bf
-/
lemma smul_one_add_eq_of_tr_eq (h2 : (2 : K) ≠ 0) {g : 𝕄} (hg : (tr g) ^ 2 ≠ 4)
    (hdetg : g.det = 1) {x y : K} (hdet : (x • (1 : 𝕄) + y • g).det = 1)
    (htr : tr (x • (1 : 𝕄) + y • g) = tr g) :
    x • (1 : 𝕄) + y • g = g ∨ x • (1 : 𝕄) + y • g = tr g • (1 : 𝕄) - g := by
  rw [det_smul_one_add, hdetg, mul_one] at hdet
  rw [tr_smul_one_add] at htr
  have hy : ((tr g) ^ 2 - 4) * ((y - 1) * (y + 1)) = 0 := by
    linear_combination (2 * x + y * tr g + tr g) * htr - 4 * hdet
  rcases mul_eq_zero.mp hy with h | h
  · exact absurd (by linear_combination h) hg
  rcases mul_eq_zero.mp h with h | h
  · have hy1 : y = 1 := by linear_combination h
    subst hy1
    have hx : x = 0 := by
      have : 2 * x = 0 := by linear_combination htr
      exact (mul_eq_zero.mp this).resolve_left h2
    subst hx; left; simp
  · have hy1 : y = -1 := by linear_combination h
    subst hy1
    have hx : x = tr g := by
      have : 2 * (x - tr g) = 0 := by linear_combination htr
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    subst hx; right; simp [sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s9.1b2ef43f7c39 from=translated src=- shape=9ab58852 vocab=3776fd44
-/
lemma coe_inv_eq (s : SL(2, K)) : ((s⁻¹ : SL(2, K)) : 𝕄) = tr (s : 𝕄) • (1 : 𝕄) - s := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.eta_fin_two (s : 𝕄)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [tr]

/--
@isnad1 id=not.1h2v.s7.26b6b3c3bd6b from=translated src=- shape=f671a3cd vocab=743b453b
-/
lemma not_isScalarMat_of_tr_sq (s : SL(2, K)) (hs : (tr (s : 𝕄)) ^ 2 ≠ 4) :
    ¬ IsScalarMat (s : 𝕄) := by
  rintro ⟨c, hc⟩
  apply hs
  have hdet : (s : 𝕄).det = 1 := s.2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  rw [hc, tr_smul, tr_one]
  linear_combination (4 : K) * hdet

section Tori

variable {H : Type} [Group H] (ρ : H →* SL(2, K))

abbrev mat (h : H) : 𝕄 := ((ρ h : SL(2, K)) : 𝕄)

/--
@isnad1 id=eq.0h5v.s8.7ec4f38e5b72 from=translated src=- shape=7c9a69cc vocab=81c70048
-/
lemma mat_mul (a b : H) : mat ρ (a * b) = mat ρ a * mat ρ b := by
  simp [mat, map_mul]

def Zsub : Subgroup H where
  carrier := {h | mat ρ h = 1 ∨ mat ρ h = -1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, mat, map_mul, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  one_mem' := by simp [mat]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, mat, map_inv] at ha ⊢
    rw [coe_inv_eq]
    rcases ha with ha | ha
    · left; rw [ha, tr_one]; ext i j; fin_cases i <;> fin_cases j <;> norm_num
    · right; rw [ha, tr_neg, tr_one]; ext i j; fin_cases i <;> fin_cases j <;> norm_num

variable {ρ}

/--
@isnad1 id=iff.0h4v.s8.07b251767b42 from=translated src=- shape=c72e69c9 vocab=7ea1dec3
-/
lemma mem_Zsub_iff (h : H) : h ∈ Zsub ρ ↔ mat ρ h = 1 ∨ mat ρ h = -1 := Iff.rfl

def IsSS (ρ : H →* SL(2, K)) (h : H) : Prop := (tr (mat ρ h)) ^ 2 ≠ 4

abbrev torus (h : H) : Subgroup H := Subgroup.centralizer {h}

/--
@isnad1 id=iff.0h3v.s6.e1e0b2ee1f5c from=translated src=- shape=a9252b74 vocab=3a4e7999
-/
lemma mem_torus_iff (h g : H) : g ∈ torus h ↔ g * h = h * g := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact ⟨fun e => e.symm, fun e => e.symm⟩

variable (hρ : Function.Injective ρ)
include hρ

/--
@isnad1 id=injectiv.1h3v.s8.9646cd45c3dc from=translated src=- shape=c8f08748 vocab=b31837bb
-/
lemma mat_injective : Function.Injective (mat ρ) := fun _ _ h =>
  hρ (Subtype.ext h)

/--
@isnad1 id=iff.1h5v.s9.f64635af1a20 from=translated src=- shape=a5aabc4f vocab=43a9bdb7
-/
lemma mem_torus_iff_mat (h g : H) : g ∈ torus h ↔ mat ρ g * mat ρ h = mat ρ h * mat ρ g := by
  rw [mem_torus_iff]
  constructor
  · intro e
    have := congrArg (mat ρ) e
    simpa [mat, map_mul] using this
  · intro e
    apply mat_injective hρ
    simpa [mat, map_mul] using e

/--
@isnad1 id=iff.2h5v.s9.37f71daa1888 from=translated src=- shape=b24b622e vocab=4a891a91
-/
lemma mem_torus_iff_exists {h : H} (hh : IsSS ρ h) (g : H) :
    g ∈ torus h ↔ ∃ x y : K, mat ρ g = x • (1 : 𝕄) + y • mat ρ h := by
  rw [mem_torus_iff_mat hρ, commute_iff (not_isScalarMat_of_tr_sq (ρ h) hh)]

/--
@isnad1 id=le.1h4v.s8.f8ccf246f6a3 from=translated src=- shape=0af7a1d1 vocab=c5b1f9d1
-/
lemma Zsub_le_torus (h : H) : Zsub ρ ≤ torus h := by
  intro g hg
  rw [mem_torus_iff_mat hρ]
  rcases hg with hg | hg <;> rw [hg] <;> simp

omit hρ in
/--
@isnad1 id=mem.0h2v.s4.ccc2adb58436 from=translated src=- shape=cac0901d vocab=08d9f9c2
-/
lemma self_mem_torus (h : H) : h ∈ torus h := (mem_torus_iff h h).mpr rfl

/--
@isnad1 id=isss.4h5v.s8.f7030d4a8b57 from=translated src=- shape=5d958f1d vocab=a78c2a02
-/
lemma isSS_of_mem_torus {h : H} (hh : IsSS ρ h) {g : H} (hg : g ∈ torus h)
    (hgZ : g ∉ Zsub ρ) : IsSS ρ g := by
  intro htr
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh g).mp hg
  apply hgZ
  rw [mem_Zsub_iff, hxy]
  refine smul_one_add_eq_of_tr_sq_eq_four hh (ρ h).2 ?_ ?_
  · rw [← hxy]; exact (ρ g).2
  · rw [← hxy]; exact htr

/--
@isnad1 id=eq.4h5v.s8.855040c8b633 from=translated src=- shape=518d1592 vocab=a78c2a02
-/
lemma torus_eq_of_mem {h : H} (hh : IsSS ρ h) {g : H} (hg : g ∈ torus h)
    (hgZ : g ∉ Zsub ρ) : torus g = torus h := by
  have hgss := isSS_of_mem_torus hρ hh hg hgZ
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh g).mp hg
  have hy : y ≠ 0 := by
    rintro rfl
    apply hgZ
    rw [mem_Zsub_iff, hxy]
    simp only [zero_smul, add_zero]
    have hdet : (x • (1 : 𝕄)).det = 1 := by
      have := (ρ g).2; rw [show ((ρ g : SL(2, K)) : 𝕄) = mat ρ g from rfl, hxy] at this
      simpa using this
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have : (x - 1) * (x + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with e | e
    · left; rw [sub_eq_zero.mp e, one_smul]
    · right; rw [eq_neg_of_add_eq_zero_left e]; simp

  have hh' : mat ρ h = (-(x * y⁻¹)) • (1 : 𝕄) + y⁻¹ • mat ρ g := by
    rw [hxy, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hy, one_smul, ← add_assoc,
      ← add_smul]
    ring_nf; simp
  ext k
  rw [mem_torus_iff_exists hρ hgss, mem_torus_iff_exists hρ hh]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a + b * x, b * y, by rw [hab, hxy, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a + b * (-(x * y⁻¹)), b * y⁻¹, ?_⟩
    rw [hab, hh', smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/--
@isnad1 id=eq.5h5v.s9.3059631e6fb0 from=translated src=- shape=bf0136ea vocab=52c4eea1
-/
lemma conj_eq_inv_of_mem_normalizer (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {n : H}
    (hn : n ∈ Subgroup.normalizer (torus h : Set H)) (hnT : n ∉ torus h) : n * h * n⁻¹ = h⁻¹ := by

  have hmem : n * h * n⁻¹ ∈ torus h := by
    rw [Subgroup.mem_normalizer_iff] at hn
    exact (hn h).mp (self_mem_torus h)
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh _).mp hmem
  have hdet : (x • (1 : 𝕄) + y • mat ρ h).det = 1 := by rw [← hxy]; exact (ρ _).2
  have htr : tr (x • (1 : 𝕄) + y • mat ρ h) = tr (mat ρ h) := by
    rw [← hxy]
    simp only [mat, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul]
    refine tr_conj ?_
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  rcases smul_one_add_eq_of_tr_eq h2 hh (ρ h).2 hdet htr with e | e
  · exfalso; apply hnT
    rw [mem_torus_iff]
    have : n * h * n⁻¹ = h := mat_injective hρ (hxy.trans e)
    calc n * h = n * h * n⁻¹ * n := by group
      _ = h * n := by rw [this]
  · apply mat_injective hρ
    rw [hxy, e]
    change _ = ((ρ h⁻¹ : SL(2, K)) : 𝕄)
    rw [map_inv, coe_inv_eq]

/--
@isnad1 id=mem.7h6v.s9.11bf46eb0a0e from=translated src=- shape=ad83c61f vocab=52c4eea1
-/
lemma inv_mul_mem_torus (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {n₁ n₂ : H}
    (hn₁ : n₁ ∈ Subgroup.normalizer (torus h : Set H)) (hn₁T : n₁ ∉ torus h)
    (hn₂ : n₂ ∈ Subgroup.normalizer (torus h : Set H)) (hn₂T : n₂ ∉ torus h) : n₂⁻¹ * n₁ ∈ torus h := by
  have e₁ := conj_eq_inv_of_mem_normalizer hρ h2 hh hn₁ hn₁T
  have e₂ := conj_eq_inv_of_mem_normalizer hρ h2 hh hn₂ hn₂T
  rw [mem_torus_iff]
  have e₂' : n₂⁻¹ * h⁻¹ * n₂ = h := by
    calc n₂⁻¹ * h⁻¹ * n₂ = n₂⁻¹ * (n₂ * h * n₂⁻¹) * n₂ := by rw [e₂]
      _ = h := by group
  calc n₂⁻¹ * n₁ * h = n₂⁻¹ * (n₁ * h * n₁⁻¹) * n₁ := by group
    _ = n₂⁻¹ * h⁻¹ * n₂ * (n₂⁻¹ * n₁) := by rw [e₁]; group
    _ = h * (n₂⁻¹ * n₁) := by rw [e₂']

/--
@isnad1 id=le.3h4v.s8.fe2778bff78b from=translated src=- shape=5d9c9463 vocab=4ffc2ca6
-/
lemma card_normalizer_le [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) :
    Nat.card (Subgroup.normalizer (torus h : Set H)) ≤ 2 * Nat.card (torus h) := by
  classical
  by_cases hall : ∀ n : H, n ∈ Subgroup.normalizer (torus h : Set H) → n ∈ torus h
  · have : Subgroup.normalizer (torus h : Set H) = torus h :=
      le_antisymm (fun n hn => hall n hn) Subgroup.le_normalizer
    rw [this]; omega
  · push Not at hall
    obtain ⟨n₀, hn₀, hn₀T⟩ := hall

    let f : (Subgroup.normalizer (torus h : Set H)) → Bool × torus h := fun n =>
      if hn : (n : H) ∈ torus h then (false, ⟨n, hn⟩)
      else (true, ⟨n₀⁻¹ * n, inv_mul_mem_torus hρ h2 hh n.2 hn hn₀ hn₀T⟩)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : (a : H) ∈ torus h <;> by_cases hb : (b : H) ∈ torus h <;>
        simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq] at hab
      · have h1 := congrArg Subtype.val hab.2
        exact Subtype.ext h1
      · simp at hab
      · simp at hab
      · have h1 := congrArg Subtype.val hab.2
        exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_prod] using this

end Tori

section Tori2

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)

include hρ in

/--
@isnad1 id=eq.2h5v.s8.63d925e57963 from=translated src=- shape=5829b7a6 vocab=7ddc9d53
-/
lemma comm_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (h : H) : ζ * h = h * ζ := by
  apply mat_injective hρ
  rw [mat_mul, mat_mul]
  rcases hζ with e | e <;> rw [e] <;> simp

/--
@isnad1 id=eq.0h2v.s5.2217daeaaee1 from=translated src=- shape=ba745d85 vocab=fa293aec
-/
lemma card_subtype_add_card_subtype_not {α : Type} [Finite α] (q : α → Prop) :
    Nat.card {x // q x} + Nat.card {x // ¬ q x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl q)]

/--
@isnad1 id=iff.0h4v.s7.934a02c29055 from=translated src=- shape=634a9f11 vocab=fc69d917
-/
lemma mem_torus_conj_iff (w c g : H) : g ∈ torus (w * c * w⁻¹) ↔ w⁻¹ * g * w ∈ torus c := by
  rw [mem_torus_iff, mem_torus_iff]
  constructor
  · intro h
    calc w⁻¹ * g * w * c = w⁻¹ * (g * (w * c * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * c * w⁻¹) * g) * w := by rw [h]
      _ = c * (w⁻¹ * g * w) := by group
  · intro h
    calc g * (w * c * w⁻¹) = w * ((w⁻¹ * g * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * g * w)) * w⁻¹ := by rw [h]
      _ = w * c * w⁻¹ * g := by group

end Tori2

section Classes

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)

def IsConjSub (M M' : Subgroup H) : Prop := ∃ s : H, ∀ g : H, g ∈ M' ↔ s⁻¹ * g * s ∈ M

/--
@isnad1 id=isconjsu.0h3v.s6.bc8c093ba5ee from=translated src=- shape=8e6cf042 vocab=4a2fd87f
-/
lemma isConjSub_torus_conj (h s : H) : IsConjSub (torus h) (torus (s * h * s⁻¹)) :=
  ⟨s, fun g => mem_torus_conj_iff s h g⟩

variable (ρ)

def classSet (M : Subgroup H) : Set H := {x | x ∉ Zsub ρ ∧ IsConjSub M (torus x)}

variable {ρ}

include hρ in

/--
@isnad1 id=eq.2h5v.s8.f256aacbd61c from=translated src=- shape=3ce78f7e vocab=3037732b
-/
lemma conj_eq_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (s : H) : s * ζ * s⁻¹ = ζ := by
  rw [← comm_of_mem_Zsub hρ hζ s, mul_inv_cancel_right]

include hρ in

/--
@isnad1 id=eq.2h4v.s9.ab627da1f767 from=translated src=- shape=b2a6fa5c vocab=00754574
-/
lemma card_classSet_mul [Finite H] {h : H} (hh : IsSS ρ h) :
    Nat.card (classSet ρ (torus h)) * Nat.card (Subgroup.normalizer (torus h : Set H)) =
      Nat.card H * (Nat.card (torus h) - Nat.card (Zsub ρ)) := by
  classical

  have hΦmem : ∀ (s : H) (m : torus h), (m : H) ∉ Zsub ρ →
      s * m * s⁻¹ ∈ classSet ρ (torus h) := by
    intro s m hm
    refine ⟨?_, ?_⟩
    · intro hZ
      apply hm
      have : (m : H) = s⁻¹ * (s * m * s⁻¹) * s⁻¹⁻¹ := by group
      rw [this, conj_eq_of_mem_Zsub hρ hZ]
      exact hZ
    · have e := torus_eq_of_mem hρ hh m.2 hm
      have := isConjSub_torus_conj (m : H) s
      rw [e] at this
      exact this
  let Φ : H × {m : torus h // (m : H) ∉ Zsub ρ} → classSet ρ (torus h) := fun sm =>
    ⟨sm.1 * sm.2.1 * sm.1⁻¹, hΦmem sm.1 sm.2.1 sm.2.2⟩

  have hfib : ∀ x : classSet ρ (torus h),
      Nat.card {sm // Φ sm = x} = Nat.card (Subgroup.normalizer (torus h : Set H)) := by
    rintro ⟨x, hxZ, s₀, hs₀⟩

    have hm₀ : s₀⁻¹ * x * s₀ ∈ torus h := (hs₀ x).mp (self_mem_torus x)
    have hm₀Z : s₀⁻¹ * x * s₀ ∉ Zsub ρ := by
      intro hZ; apply hxZ
      have : x = s₀ * (s₀⁻¹ * x * s₀) * s₀⁻¹ := by group
      rw [this, conj_eq_of_mem_Zsub hρ hZ]; exact hZ

    have hkey : ∀ (s : H) (m : H), m ∈ torus h → m ∉ Zsub ρ → s * m * s⁻¹ = x →
        s₀⁻¹ * s ∈ Subgroup.normalizer (torus h : Set H) := by
      intro s m hm hmZ hsm
      have hTm : torus m = torus h := torus_eq_of_mem hρ hh hm hmZ

      have hs : ∀ g : H, g ∈ torus x ↔ s⁻¹ * g * s ∈ torus h := by
        intro g; rw [← hsm, mem_torus_conj_iff, hTm]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have e1 : s₀⁻¹ * s * g * (s₀⁻¹ * s)⁻¹ = s₀⁻¹ * (s * g * s⁻¹) * s₀ := by group
      rw [e1, ← hs₀, hs, show s⁻¹ * (s * g * s⁻¹) * s = g by group]
    refine Nat.card_congr
      { toFun := fun sm => ⟨s₀⁻¹ * sm.1.1, hkey sm.1.1 sm.1.2.1 sm.1.2.1.2 sm.1.2.2
          (congrArg Subtype.val sm.2)⟩
        invFun := fun n => ⟨(s₀ * n, ⟨⟨n⁻¹ * (s₀⁻¹ * x * s₀) * n, ?_⟩, ?_⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    ·
      have := n.2
      rw [Subgroup.mem_normalizer_iff''] at this
      exact (this _).mp hm₀
    ·
      intro hZ
      change (n : H)⁻¹ * (s₀⁻¹ * x * s₀) * n ∈ Zsub ρ at hZ
      apply hm₀Z
      have e := conj_eq_of_mem_Zsub hρ hZ n
      rw [show (n : H) * ((n : H)⁻¹ * (s₀⁻¹ * x * s₀) * n) * (n : H)⁻¹ = s₀⁻¹ * x * s₀ by group]
        at e
      rw [e]; exact hZ
    ·
      obtain ⟨n, hn⟩ := n
      apply Subtype.ext
      change s₀ * n * (n⁻¹ * (s₀⁻¹ * x * s₀) * n) * (s₀ * n)⁻¹ = x
      group
    · rintro ⟨⟨s, m, hm⟩, hsm⟩
      have hsm' : s * m * s⁻¹ = x := congrArg Subtype.val hsm
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      refine ⟨by group, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      change (s₀⁻¹ * s)⁻¹ * (s₀⁻¹ * x * s₀) * (s₀⁻¹ * s) = m
      rw [← hsm']; group
    · intro n
      apply Subtype.ext
      change s₀⁻¹ * (s₀ * n) = n
      group

  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv Φ)
  letI : Fintype (classSet ρ (torus h)) := Fintype.ofFinite _
  rw [Nat.card_sigma] at hsig
  simp_rw [hfib] at hsig
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_eq_nat_card, Nat.card_prod]
    at hsig
  rw [hsig]

  have hZ : Nat.card {m : torus h // (m : H) ∈ Zsub ρ} = Nat.card (Zsub ρ) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨m.1, m.2⟩
        invFun := fun ζ => ⟨⟨ζ, Zsub_le_torus hρ h ζ.2⟩, ζ.2⟩
        left_inv := fun m => rfl
        right_inv := fun ζ => rfl }
  have := card_subtype_add_card_subtype_not (fun m : torus h => (m : H) ∈ Zsub ρ)
  rw [hZ] at this
  congr 1
  omega

end Classes

end P2mDicksonCore

open P2mDicksonCore in
/--
@isnad1 id=and.3h4v.s12.c9fd14766748 from=translated src=- shape=ddcfff26 vocab=d6a1b335
-/
theorem solution
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (h : H) (hh : (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    (∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
      ∃ x y : K, ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧
    (∀ g ∈ Subgroup.centralizer ({h} : Set H),
      ¬ (((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
         ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) →
      Subgroup.centralizer ({g} : Set H) = Subgroup.centralizer ({h} : Set H) ∧
      ((((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4)) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) ≤
      2 * Nat.card (Subgroup.centralizer ({h} : Set H)) ∧
    Nat.card {x : H // ¬ (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
      ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({x} : Set H) ↔
        s⁻¹ * g * s ∈ Subgroup.centralizer ({h} : Set H)} *
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) =
    Nat.card H * (Nat.card (Subgroup.centralizer ({h} : Set H)) -
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1}) := by
  have hh' : IsSS ρ h := hh
  refine ⟨fun g => mem_torus_iff_exists hρ hh' g, fun g hg hgZ => ?_,
    card_normalizer_le hρ h2 hh', ?_⟩
  · exact ⟨torus_eq_of_mem hρ hh' hg hgZ, isSS_of_mem_torus hρ hh' hg hgZ⟩
  · exact card_classSet_mul hρ hh'
