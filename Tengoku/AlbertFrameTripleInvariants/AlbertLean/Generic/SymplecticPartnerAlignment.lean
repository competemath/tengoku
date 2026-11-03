import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticTransvection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms avoidanceScalar_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms partner_intermediate_pairings` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms partner_centers_fix_first` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms partner_two_step_align` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms partner_two_step_fixes_first` (it only prints; the queue checks the axioms of every declaration). -/

/-! The two-transvection partner correction after the first member of a
hyperbolic pair has been aligned. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def avoidanceScalar (c : K) : K := by
  classical
  exact if c = 1 then 2 else 1

theorem avoidanceScalar_ne_zero (c : K) : avoidanceScalar c ≠ 0 := by
  classical
  unfold avoidanceScalar
  split_ifs <;> norm_num

theorem avoidanceScalar_ne (c : K) : avoidanceScalar c ≠ c := by
  classical
  unfold avoidanceScalar
  split_ifs with h
  · subst c
    norm_num
  · exact fun e => h e.symm

theorem partner_intermediate_pairings
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (e v f : V)
    (hev : omega e v = 1) (hef : omega e f = 1) (a : K) :
    omega (v + a • e) v = a ∧
      omega f (v + a • e) = omega f v - a := by
  have hve := skew_of_alternating omega halt v e
  have hfe := skew_of_alternating omega halt f e
  constructor
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      halt v, zero_add, smul_eq_mul, hev]
    ring
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hfe, hef]
    ring

theorem partner_centers_fix_first
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (e v f : V)
    (hev : omega e v = 1) (hef : omega e f = 1) (a : K) :
    omega ((v + a • e) - v) e = 0 ∧
      omega (f - (v + a • e)) e = 0 := by
  have hee := halt e
  have hve := skew_of_alternating omega halt v e
  have hfe := skew_of_alternating omega halt f e
  constructor
  · simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, hee, sub_self,
      add_sub_cancel_left, smul_eq_mul, mul_zero]
  · simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hee, mul_zero,
      add_zero, hve, hfe, hev, hef]
    ring

theorem partner_two_step_align
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (e v f : V)
    (hev : omega e v = 1) (hef : omega e f = 1) :
    let a := avoidanceScalar (omega f v)
    let w := v + a • e
    equiv omega halt (f - w) (omega f w)⁻¹
      (equiv omega halt (w - v) (omega w v)⁻¹ v) = f := by
  dsimp only
  apply two_step_align omega halt v
  · rw [(partner_intermediate_pairings omega halt e v f hev hef
      (avoidanceScalar (omega f v))).1]
    exact avoidanceScalar_ne_zero (omega f v)
  · rw [(partner_intermediate_pairings omega halt e v f hev hef
      (avoidanceScalar (omega f v))).2]
    exact sub_ne_zero.mpr (avoidanceScalar_ne (omega f v)).symm

theorem partner_two_step_fixes_first
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (e v f : V)
    (hev : omega e v = 1) (hef : omega e f = 1) :
    let a := avoidanceScalar (omega f v)
    let w := v + a • e
    equiv omega halt (f - w) (omega f w)⁻¹
      (equiv omega halt (w - v) (omega w v)⁻¹ e) = e := by
  dsimp only
  obtain ⟨hfirst, hsecond⟩ := partner_centers_fix_first omega halt e v f hev hef
    (avoidanceScalar (omega f v))
  simp only [equiv_apply, hfirst, hsecond, mul_zero, zero_smul, add_zero]

end AlbertLean.Generic.SymplecticTransvection
