import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

def ratPoint (a c : ℤ) : OnePoint ℚ :=
  if c = 0 then ∞ else (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ)

/--
@isnad1 id=eq.0h1v.s3.c9dcd2d0c6dc from=translated src=- shape=dc845c14 vocab=9b643835
-/
@[simp] lemma ratPoint_zero_right (a : ℤ) : ratPoint a 0 = ∞ := ite_eq_left rfl

/--
@isnad1 id=eq.1h2v.s5.2a7dd57f1e7f from=translated src=- shape=36d1a854 vocab=d2505d6f
-/
lemma ratPoint_of_ne_zero (a : ℤ) {c : ℤ} (hc : c ≠ 0) :
    ratPoint a c = (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ) := ite_eq_right hc

/--
@isnad1 id=eq.0h0v.s4.89629826b7fb from=translated src=- shape=d8cce2ac vocab=9b643835
-/
@[simp] lemma ratPoint_one_zero : ratPoint 1 0 = ∞ := ite_eq_left rfl

/--
@isnad1 id=eq.0h0v.s4.8ae5afce44de from=translated src=- shape=dfd5c9f4 vocab=3dc0070e
-/
@[simp] lemma ratPoint_zero_one : ratPoint 0 1 = ((0 : ℚ) : OnePoint ℚ) := by
  simp [ratPoint]

/--
@isnad1 id=iff.0h2v.s4.8a0d129d9ca8 from=translated src=- shape=f6b75218 vocab=9b643835
-/
lemma ratPoint_eq_infty_iff {a c : ℤ} : ratPoint a c = ∞ ↔ c = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [ratPoint_of_ne_zero a hc, hc]

/--
@isnad1 id=eq.1h3v.s5.c09b254b1776 from=translated src=- shape=594aa8e7 vocab=b23678e2
-/
lemma ratPoint_mul_left {l : ℤ} (hl : l ≠ 0) (a c : ℤ) :
    ratPoint (l * a) (l * c) = ratPoint a c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [ratPoint_of_ne_zero _ (mul_ne_zero hl hc), ratPoint_of_ne_zero _ hc]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hl)]

/--
@isnad1 id=eq.0h2v.s4.cf1841aa4926 from=translated src=- shape=87cbdae6 vocab=4fd65ec8
-/
lemma ratPoint_neg_neg (a c : ℤ) : ratPoint (-a) (-c) = ratPoint a c := by
  simpa using ratPoint_mul_left (l := -1) (by norm_num) a c

/--
@isnad1 id=ex.0h1v.s4.f71825f1a609 from=translated src=- shape=55b13fe8 vocab=fc811ad5
-/
lemma exists_ratPoint_eq (x : OnePoint ℚ) : ∃ a c : ℤ, IsCoprime a c ∧ ratPoint a c = x := by
  cases x with
  | infty => exact ⟨1, 0, isCoprime_one_left, rfl⟩
  | coe q =>
    refine ⟨q.num, (q.den : ℤ), ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using q.reduced
    · rw [ratPoint_of_ne_zero _ (by exact_mod_cast q.den_nz), OnePoint.coe_eq_coe,
        show ((q.den : ℤ) : ℚ) = (q.den : ℚ) by push_cast; ring, Rat.num_div_den]

/--
@isnad1 id=eq.0h3v.s9.081d01c346c3 from=translated src=- shape=531976e2 vocab=abe958ef
-/
@[simp] lemma mapGL_apply_coe (γ : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℚ γ) i j = ((γ i j : ℤ) : ℚ) := by
  simp [mapGL]

/--
@isnad1 id=eq.0h1v.s9.89d619b98193 from=translated src=- shape=377b8e79 vocab=374b27dc
-/
lemma mapGL_smul_infty (γ : SL(2, ℤ)) :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = ratPoint (γ 0 0) (γ 1 0) := by
  rw [smul_infty_eq_ite, mapGL_apply_coe, mapGL_apply_coe]
  rcases eq_or_ne (γ 1 0) 0 with h | h
  · simp [h]
  · rw [ite_eq_right (by exact_mod_cast h), ratPoint_of_ne_zero _ h]

/--
@isnad1 id=eq.1h3v.s10.e066e2c46ba3 from=translated src=- shape=65764758 vocab=1cf1ba0a
-/
lemma mapGL_smul_ratPoint (γ : SL(2, ℤ)) {a c : ℤ} (h : a ≠ 0 ∨ c ≠ 0) :
    mapGL ℚ γ • ratPoint a c =
      ratPoint (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  ·
    replace h : a ≠ 0 := h.resolve_right (by simp)
    rw [ratPoint_zero_right, mapGL_smul_infty]
    simp only [mul_zero, add_zero]
    rw [mul_comm (γ 0 0) a, mul_comm (γ 1 0) a, ratPoint_mul_left h]
  ·
    rw [ratPoint_of_ne_zero _ hc, smul_some_eq_ite]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    have hden : (mapGL ℚ γ) 1 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 1 1
        = (((γ 1 0 * a + γ 1 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe]
      field_simp
      push_cast
      ring
    have hnum : (mapGL ℚ γ) 0 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 0 1
        = (((γ 0 0 * a + γ 0 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe]
      field_simp
      push_cast
      ring
    rcases eq_or_ne (γ 1 0 * a + γ 1 1 * c) 0 with h0 | h0
    · rw [ite_eq_left (by rw [hden, h0]; simp), h0, ratPoint_zero_right]
    · rw [ite_eq_right (by rw [hden]; exact div_ne_zero (by exact_mod_cast h0) hcQ),
        ratPoint_of_ne_zero _ h0, hnum, hden, OnePoint.coe_eq_coe,
        div_div_div_cancel_right₀ hcQ]

/--
@isnad1 id=iscoprim.1h3v.s8.94f86bfbc4a5 from=translated src=- shape=a5a7236b vocab=fd43ffed
-/
lemma isCoprime_smul_pair (γ : SL(2, ℤ)) {a c : ℤ} (h : IsCoprime a c) :
    IsCoprime (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  have := IsCoprime.mulVecSL (v := ![a, c]) (by simpa using h) γ
  simpa [Matrix.mulVec_fin_two] using this

variable (N : ℕ)

def Gamma0Q : Subgroup (GL (Fin 2) ℚ) := (Gamma0 N).map (mapGL ℚ)

/--
@isnad1 id=iff.0h2v.s9.7ce22e6bcaa2 from=translated src=- shape=4887a606 vocab=486f0c32
-/
lemma mem_Gamma0Q {g : GL (Fin 2) ℚ} :
    g ∈ Gamma0Q N ↔ ∃ γ ∈ Gamma0 N, mapGL ℚ γ = g := Iff.rfl

abbrev CuspSpace : Type := MulAction.orbitRel.Quotient (Gamma0Q N) (OnePoint ℚ)

namespace CuspSpace

def mk (x : OnePoint ℚ) : CuspSpace N := ⟦x⟧

/--
@isnad1 id=surjecti.0h1v.s3.c47c453fa944 from=translated src=- shape=ffc59986 vocab=a2323b57
-/
lemma mk_surjective : Function.Surjective (mk N) := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

variable {N}

/--
@isnad1 id=iff.0h3v.s9.17d6947c75c3 from=translated src=- shape=f41d674b vocab=80d62a68
-/
lemma mk_eq_mk_iff {x y : OnePoint ℚ} :
    mk N x = mk N y ↔ ∃ γ ∈ Gamma0 N, mapGL ℚ γ • y = x := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, γ, hγ, rfl⟩, hg⟩
    exact ⟨γ, hγ, hg⟩
  · rintro ⟨γ, hγ, hg⟩
    exact ⟨⟨mapGL ℚ γ, γ, hγ, rfl⟩, hg⟩

/--
@isnad1 id=eq.1h3v.s9.16f08f16ff80 from=translated src=- shape=c5972908 vocab=80d62a68
-/
lemma mk_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    mk N (mapGL ℚ γ • x) = mk N x :=
  mk_eq_mk_iff.mpr ⟨γ, hγ, rfl⟩

variable (N)

/--
@isnad1 id=eq.1h3v.s10.3e1713091443 from=translated src=- shape=35c5175a vocab=53ff53e7
-/
lemma mk_smul_infty_eq_of_mem {a b : SL(2, ℤ)} (hab : a⁻¹ * b ∈ Gamma0 N) :
    mk N (mapGL ℚ a⁻¹ • ∞) = mk N (mapGL ℚ b⁻¹ • ∞) := by
  have key : mapGL ℚ b⁻¹ • (∞ : OnePoint ℚ)
      = mapGL ℚ (a⁻¹ * b)⁻¹ • (mapGL ℚ a⁻¹ • (∞ : OnePoint ℚ)) := by
    have h1 : (a⁻¹ * b)⁻¹ * a⁻¹ = b⁻¹ := by group
    rw [← mul_smul, ← map_mul, h1]
  rw [key]
  exact (mk_smul (inv_mem hab) _).symm

def fromCoset : SL(2, ℤ) ⧸ Gamma0 N → CuspSpace N :=
  Quotient.lift (fun g => mk N (mapGL ℚ g⁻¹ • ∞))
    (fun _ _ hab => mk_smul_infty_eq_of_mem N (QuotientGroup.leftRel_apply.mp hab))

/--
@isnad1 id=eq.0h2v.s9.888d8cdc43b0 from=translated src=- shape=2a9a2332 vocab=3c1b4ee4
-/
@[simp] lemma fromCoset_mk (g : SL(2, ℤ)) :
    fromCoset N ((g : SL(2, ℤ) ⧸ Gamma0 N)) = mk N (mapGL ℚ g⁻¹ • ∞) := rfl

/--
@isnad1 id=surjecti.0h1v.s6.fbbdb225322b from=translated src=- shape=4f59899f vocab=c653eb5b
-/
lemma fromCoset_surjective : Function.Surjective (fromCoset N) := by
  rintro ⟨x⟩
  obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
  exact ⟨(g⁻¹ : SL(2, ℤ)), by rw [fromCoset_mk, inv_inv, hg]; rfl⟩

/--
@isnad1 id=finite.0h1v.s3.e662000c5473 from=translated src=- shape=a4efea94 vocab=00a8417e
-/
instance instFinite [NeZero N] : Finite (CuspSpace N) :=
  Finite.of_surjective _ (fromCoset_surjective N)

/--
@isnad1 id=nonempty.0h1v.s2.32807cf0b832 from=translated src=- shape=76a08d12 vocab=d7210336
-/
instance instNonempty : Nonempty (CuspSpace N) := ⟨mk N ∞⟩

/--
@isnad1 id=subsingl.0h0v.s2.24be25cef328 from=translated src=- shape=8d7dbbf6 vocab=9e349320
-/
instance instSubsingletonOfOne : Subsingleton (CuspSpace 1) := by
  constructor
  rintro ⟨x⟩ ⟨y⟩
  obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
  obtain ⟨h, hh⟩ := OnePoint.exists_mem_SL2 ℤ y
  show mk 1 x = mk 1 y
  have hmem : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 1 := fun γ => by
    rw [Gamma0_mem]; exact Subsingleton.elim _ _
  rw [← hg, ← hh]
  symm
  rw [show (mapGL ℚ h • (∞ : OnePoint ℚ)) = mapGL ℚ (h * g⁻¹) • (mapGL ℚ g • (∞ : OnePoint ℚ))
    by rw [← mul_smul, ← map_mul, inv_mul_cancel_right]]
  exact mk_smul (hmem _) _

def cuspDenomAux (x : OnePoint ℚ) : ℕ :=
  x.elim N fun q => Nat.gcd q.den N

/--
@isnad1 id=eq.0h1v.s3.60b37ff7c853 from=translated src=- shape=41e6d4c6 vocab=71a75347
-/
@[simp] lemma cuspDenomAux_infty : cuspDenomAux N ∞ = N := rfl

/--
@isnad1 id=eq.0h2v.s3.7233e23f766f from=translated src=- shape=f4451025 vocab=8fea8cd1
-/
@[simp] lemma cuspDenomAux_coe (q : ℚ) : cuspDenomAux N (q : OnePoint ℚ) = Nat.gcd q.den N :=
  rfl

variable {N}

/--
@isnad1 id=eq.1h3v.s4.b8b0b28fceaf from=translated src=- shape=3d421f24 vocab=9d08563c
-/
lemma cuspDenomAux_ratPoint {a c : ℤ} (h : IsCoprime a c) :
    cuspDenomAux N (ratPoint a c) = Int.gcd c N := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Int.gcd]
  · rw [ratPoint_of_ne_zero _ hc, cuspDenomAux_coe]
    have hcop : Nat.Coprime a.natAbs c.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
    have hden : (((a : ℚ) / (c : ℚ)).den : ℤ) = (c.natAbs : ℤ) := by
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have : ((a : ℚ) / (c : ℚ)) = (((-a : ℤ) : ℚ) / ((-c : ℤ) : ℚ)) := by
          push_cast; rw [neg_div_neg_eq]
        rw [this, Rat.den_div_eq_of_coprime (by omega) (by simpa using hcop)]
        omega
      · rw [Rat.den_div_eq_of_coprime hpos hcop]
        omega
    have : ((a : ℚ) / (c : ℚ)).den = c.natAbs := by exact_mod_cast hden
    rw [this]
    rfl

/--
@isnad1 id=iff.0h2v.s8.437a3506f329 from=translated src=- shape=265efa57 vocab=5e23b936
-/
lemma _root_.CongruenceSubgroup.Gamma0_mem_iff_dvd {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

/--
@isnad1 id=dvd.1h3v.s9.5d9920a7fb99 from=translated src=- shape=b5012cfe vocab=ba1d2185
-/
lemma cuspDenomAux_dvd_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    cuspDenomAux N x ∣ cuspDenomAux N (mapGL ℚ γ • x) := by
  obtain ⟨a, c, hac, rfl⟩ := exists_ratPoint_eq x
  have hac' : a ≠ 0 ∨ c ≠ 0 := hac.ne_zero_or_ne_zero
  rw [mapGL_smul_ratPoint γ hac', cuspDenomAux_ratPoint hac,
    cuspDenomAux_ratPoint (isCoprime_smul_pair γ hac)]

  have h1 : (Int.gcd c N : ℤ) ∣ γ 1 0 * a + γ 1 1 * c := by
    refine dvd_add (Dvd.dvd.mul_right ?_ a) (Dvd.dvd.mul_left (Int.gcd_dvd_left ..) _)
    exact (Int.gcd_dvd_right ..).trans (Gamma0_mem_iff_dvd.mp hγ)
  exact Int.dvd_gcd h1 (Int.gcd_dvd_right ..)

/--
@isnad1 id=eq.1h3v.s9.4780fa52b710 from=translated src=- shape=943e1e18 vocab=adab675e
-/
lemma cuspDenomAux_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    cuspDenomAux N (mapGL ℚ γ • x) = cuspDenomAux N x := by
  refine Nat.dvd_antisymm ?_ (cuspDenomAux_dvd_smul hγ x)
  have := cuspDenomAux_dvd_smul (inv_mem hγ) (mapGL ℚ γ • x)
  rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at this

variable (N)

def cuspDenom : CuspSpace N → ℕ :=
  Quotient.lift (cuspDenomAux N) (by
    rintro x y ⟨⟨g, γ, hγ, rfl⟩, rfl⟩
    exact cuspDenomAux_smul hγ y)

/--
@isnad1 id=eq.0h2v.s3.033fb2bf715a from=translated src=- shape=99ced154 vocab=2a8489ed
-/
@[simp] lemma cuspDenom_mk (x : OnePoint ℚ) : cuspDenom N (mk N x) = cuspDenomAux N x := rfl

variable {N}

/--
@isnad1 id=eq.1h3v.s4.4ef6223a60ab from=translated src=- shape=25b14924 vocab=927c50a1
-/
lemma cuspDenom_mk_ratPoint {a c : ℤ} (h : IsCoprime a c) :
    cuspDenom N (mk N (ratPoint a c)) = Int.gcd c N :=
  cuspDenomAux_ratPoint h

/--
@isnad1 id=eq.0h1v.s3.d7dd4ad387fc from=translated src=- shape=41d0cf0d vocab=6ad1af36
-/
@[simp] lemma cuspDenom_mk_infty : cuspDenom N (mk N ∞) = N := rfl

/--
@isnad1 id=eq.0h1v.s4.cb993c005b04 from=translated src=- shape=2388b6a6 vocab=bf0dd1f5
-/
@[simp] lemma cuspDenom_mk_zero : cuspDenom N (mk N ((0 : ℚ) : OnePoint ℚ)) = 1 := by
  rw [← ratPoint_zero_one, cuspDenom_mk_ratPoint (isCoprime_zero_left.mpr isUnit_one)]
  simp [Int.gcd]

/--
@isnad1 id=dvd.0h2v.s3.c7ca3b8ba08d from=translated src=- shape=26d77ceb vocab=b63c8c57
-/
lemma cuspDenom_dvd (x : CuspSpace N) : cuspDenom N x ∣ N := by
  obtain ⟨y, rfl⟩ := mk_surjective N x
  obtain ⟨a, c, hac, rfl⟩ := exists_ratPoint_eq y
  rw [cuspDenom_mk_ratPoint hac]
  simpa using Int.gcd_dvd_natAbs_right c (N : ℤ)

def NormalFormCriterion (N : ℕ) : Prop :=
  ∀ (a a' : ℤ) (e : ℕ), e ∣ N → IsCoprime a (e : ℤ) → IsCoprime a' (e : ℤ) →
    (mk N (ratPoint a e) = mk N (ratPoint a' e) ↔
      (a : ZMod (Nat.gcd e (N / e))) = (a' : ZMod (Nat.gcd e (N / e))))

def Classification (N : ℕ) : Prop :=
  Nonempty (CuspSpace N ≃ (d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ)

end CuspSpace

end

end ModularCurve

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

/--
@isnad1 id=eq.1h2v.s5.54410cede7a0 from=translated src=- shape=ff693274 vocab=db18b1e3
-/
theorem gcd_sq_eq_mul_gcd_div {N d : ℕ} (hd : d ∣ N) :
    Nat.gcd (d ^ 2) N = d * Nat.gcd d (N / d) := by
  conv_lhs => rw [pow_two, ← Nat.mul_div_cancel' hd]
  exact Nat.gcd_mul_left d d (N / d)

/--
@isnad1 id=eq.0h2v.s5.48a983a21413 from=translated src=- shape=4024c094 vocab=54fc8b7e
-/
theorem gcd_sq_gcd_left (c N : ℕ) : Nat.gcd (Nat.gcd c N ^ 2) N = Nat.gcd (c ^ 2) N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Nat.gcd_zero_right]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.gcd_zero_left, zero_pow two_ne_zero, Nat.gcd_zero_left,
      Nat.gcd_eq_right (dvd_pow_self N two_ne_zero)]

  set g : ℕ := Nat.gcd c N with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left N hc
  have hgc : g ∣ c := Nat.gcd_dvd_left c N
  have hgN : g ∣ N := Nat.gcd_dvd_right c N
  have hcop : Nat.Coprime (c / g) (N / g) := Nat.coprime_div_gcd_div_gcd hg0

  have hL : Nat.gcd (g ^ 2) N = g * Nat.gcd g (N / g) := gcd_sq_eq_mul_gcd_div hgN

  have hR : Nat.gcd (c ^ 2) N = g * Nat.gcd g (N / g) := by
    have h1 : c ^ 2 = g * (c / g * c) := by
      rw [← mul_assoc, Nat.mul_div_cancel' hgc, ← pow_two]
    have h2 : N = g * (N / g) := (Nat.mul_div_cancel' hgN).symm
    rw [h1]
    conv_lhs => rw [h2]
    rw [Nat.gcd_mul_left]
    congr 1
    rw [Nat.Coprime.gcd_mul_left_cancel c hcop]
    conv_lhs => rw [← Nat.div_mul_cancel hgc]
    rw [Nat.Coprime.gcd_mul_left_cancel g hcop]
  rw [hL, hR]

def cuspWidthOfDenom (N d : ℕ) : ℕ := N / Nat.gcd (d ^ 2) N

/--
@isnad1 id=eq.0h2v.s5.f3bb40b71ecf from=translated src=- shape=789631d4 vocab=89d3e2fd
-/
theorem gcd_mul_cuspWidthOfDenom (N d : ℕ) :
    Nat.gcd (d ^ 2) N * cuspWidthOfDenom N d = N :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

/--
@isnad1 id=dvd.0h2v.s3.f9220c8ff6b8 from=translated src=- shape=03d1ed50 vocab=88ef2974
-/
theorem cuspWidthOfDenom_dvd (N d : ℕ) : cuspWidthOfDenom N d ∣ N :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

/--
@isnad1 id=lt.1h2v.s4.c0ea7b841258 from=translated src=- shape=c55cdd19 vocab=287b892a
-/
theorem cuspWidthOfDenom_pos {N : ℕ} (hN : N ≠ 0) (d : ℕ) : 0 < cuspWidthOfDenom N d :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN))

/--
@isnad1 id=eq.1h2v.s5.791a678ceebe from=translated src=- shape=931a41e7 vocab=50acd675
-/
theorem cuspWidthOfDenom_eq_div_div {N d : ℕ} (hd : d ∣ N) :
    cuspWidthOfDenom N d = N / d / Nat.gcd d (N / d) := by
  unfold cuspWidthOfDenom
  rw [gcd_sq_eq_mul_gcd_div hd, Nat.div_div_eq_div_mul]

/--
@isnad1 id=eq.0h2v.s3.5cc247c49d0e from=translated src=- shape=c2a55ad4 vocab=06214adc
-/
theorem cuspWidthOfDenom_gcd (N d : ℕ) :
    cuspWidthOfDenom N (Nat.gcd d N) = cuspWidthOfDenom N d := by
  unfold cuspWidthOfDenom
  rw [gcd_sq_gcd_left]

/--
@isnad1 id=eq.1h1v.s4.0ced277273bc from=translated src=- shape=ef8e552e vocab=3fc7c9aa
-/
theorem cuspWidthOfDenom_self {N : ℕ} (hN : N ≠ 0) : cuspWidthOfDenom N N = 1 := by
  unfold cuspWidthOfDenom
  rw [Nat.gcd_eq_right (dvd_pow_self N two_ne_zero), Nat.div_self (Nat.pos_of_ne_zero hN)]

/--
@isnad1 id=eq.0h1v.s3.c87813e41fb5 from=translated src=- shape=1fa26838 vocab=3fc7c9aa
-/
theorem cuspWidthOfDenom_one (N : ℕ) : cuspWidthOfDenom N 1 = N := by
  unfold cuspWidthOfDenom
  rw [one_pow, Nat.gcd_one_left, Nat.div_one]

namespace CuspSpace

variable {N : ℕ}

def cuspWidth (x : CuspSpace N) : ℕ := cuspWidthOfDenom N (cuspDenom N x)

/--
@isnad1 id=eq.1h3v.s5.2c9296bedd96 from=translated src=- shape=10c19f3b vocab=83327dd1
-/
theorem cuspWidth_mk_ratPoint {a c : ℤ} (h : IsCoprime a c) :
    cuspWidth (mk N (ratPoint a c)) = N / Nat.gcd (c.natAbs ^ 2) N := by
  have h1 : cuspDenom N (mk N (ratPoint a c)) = Nat.gcd c.natAbs N := by
    rw [cuspDenom_mk_ratPoint h]
    show Nat.gcd c.natAbs (N : ℤ).natAbs = _
    rw [Int.natAbs_natCast]
  show cuspWidthOfDenom N (cuspDenom N (mk N (ratPoint a c))) = _
  rw [h1]
  show N / Nat.gcd (Nat.gcd c.natAbs N ^ 2) N = _
  rw [gcd_sq_gcd_left]

/--
@isnad1 id=dvd.0h2v.s3.150d6d062d92 from=translated src=- shape=26d77ceb vocab=c4125ab4
-/
theorem cuspWidth_dvd (x : CuspSpace N) : cuspWidth x ∣ N := cuspWidthOfDenom_dvd _ _

/--
@isnad1 id=lt.1h2v.s4.50493fe7b16b from=translated src=- shape=a3c73dee vocab=658a8a27
-/
theorem cuspWidth_pos (hN : N ≠ 0) (x : CuspSpace N) : 0 < cuspWidth x :=
  cuspWidthOfDenom_pos hN _

end CuspSpace

end

end ModularCurve
