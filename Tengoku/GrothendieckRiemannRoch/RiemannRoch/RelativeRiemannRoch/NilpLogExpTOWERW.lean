/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.WeightAlgebraToddRG6B
import Tengoku.Seed.RingTheory.PowerSeries.Log
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.Nilpotent.Exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# TOWERW, brick 2: `log(1+x)`, `exp`, `Td` on nilpotent elements of a commutative `ℚ`-algebra

`exp` is Mathlib's `IsNilpotent.exp`.  `logOnePlus x = log(1+x)` is the finite sum
`∑_{i < nilpotencyClass x} (-1)^(i+1)/i • x^i`.  We prove `exp (log(1+x)) = 1+x`,
`log(exp y) = y`, `log((1+x)^j) = j • log(1+x)`, compatibility with ring homomorphisms, and plug into
`RG6B.ev` / `RG6B.Td` (the Todd series `X / (1 - e^{-X})`).
-/

set_option autoImplicit false

namespace TOWERW

open PowerSeries Finset

section Ev

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/--
@isnad1 id=eq.2h5v.s6.a23fe006cf47 from=translated src=- shape=3d33249f vocab=56363c55
-/
theorem ev_eq_of_le {D D' : ℕ} {a : K} (h : a ^ (D + 1) = 0) (hD : D ≤ D') (f : ℚ⟦X⟧) :
    RG6B.ev D' a f = RG6B.ev D a f := by
  rw [RG6B.ev_eq_sum, RG6B.ev_eq_sum]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => ?_
  have : D + 1 ≤ i := by simpa using hi
  rw [pow_eq_zero_of_le this h, smul_zero]

/--
@isnad1 id=eq.1h3v.s6.030686b20d3a from=translated src=- shape=4a20e2fd vocab=790d24d6
-/
theorem ev_X {D : ℕ} {a : K} (h : a ^ (D + 1) = 0) : RG6B.ev D a (X : ℚ⟦X⟧) = a := by
  rw [RG6B.ev_eq_sum]
  rcases D with _ | D
  · simp at h
    simp [h]
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      simp [coeff_X, hi]
    · intro h1; simp at h1

/-- evaluation of `X^n`
@isnad1 id=eq.1h4v.s6.6b83127009d6 from=translated src=- shape=76d30a43 vocab=1ed4d261
-/
theorem ev_X_pow {D : ℕ} {a : K} (h : a ^ (D + 1) = 0) (n : ℕ) :
    RG6B.ev D a ((X : ℚ⟦X⟧) ^ n) = a ^ n := by
  have e := map_pow (RG6B.evHom D a h) (X : ℚ⟦X⟧) n
  change RG6B.ev D a ((X : ℚ⟦X⟧) ^ n) = (RG6B.ev D a X) ^ n at e
  rw [ev_X h] at e
  exact e

/--
@isnad1 id=eq.1h5v.s7.c945fe7e8b64 from=translated src=- shape=f768c341 vocab=ecef4d55
-/
theorem ev_sub {D : ℕ} {a : K} (h : a ^ (D + 1) = 0) (f g : ℚ⟦X⟧) :
    RG6B.ev D a (f - g) = RG6B.ev D a f - RG6B.ev D a g :=
  map_sub (RG6B.evHom D a h) f g

/-- if `g` has zero constant term then `ev g` is nilpotent with the same bound
@isnad1 id=eq.2h4v.s7.295707bca902 from=translated src=- shape=b521f509 vocab=f57cea55
-/
theorem pow_ev_eq_zero {D : ℕ} {a : K} (h : a ^ (D + 1) = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (RG6B.ev D a g) ^ (D + 1) = 0 := by
  obtain ⟨u, rfl⟩ := (X_dvd_iff.2 hg : (X : ℚ⟦X⟧) ∣ g)
  have e := map_pow (RG6B.evHom D a h) (X * u) (D + 1)
  change RG6B.ev D a ((X * u) ^ (D + 1)) = (RG6B.ev D a (X * u)) ^ (D + 1) at e
  rw [← e, mul_pow, RG6B.ev_mul h, ev_X_pow h, h, zero_mul]

/--
@isnad1 id=eq.2h4v.s9.8f913fbf9b57 from=translated src=- shape=020f8f74 vocab=cac63ac0
-/
theorem ring_hom_eq_aeval_trunc {D : ℕ} (ψ : ℚ⟦X⟧ →+* K)
    (hC : ∀ c : ℚ, ψ (C c) = algebraMap ℚ K c) (hX : ψ (X ^ (D + 1)) = 0) (f : ℚ⟦X⟧) :
    ψ f = Polynomial.aeval (ψ X) (trunc (D + 1) f) := by
  have hdvd : (X : ℚ⟦X⟧) ^ (D + 1) ∣ f - (trunc (D + 1) f : ℚ⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_coe_trunc_of_lt hm, sub_self]
  obtain ⟨h, hh⟩ := hdvd
  have h1 : ψ f = ψ (trunc (D + 1) f : ℚ⟦X⟧) := by
    have : f = (trunc (D + 1) f : ℚ⟦X⟧) + X ^ (D + 1) * h := by rw [← hh]; ring
    conv_lhs => rw [this]
    rw [map_add, map_mul, hX, zero_mul, add_zero]
  rw [h1]
  have h2 : (ψ.comp (Polynomial.coeToPowerSeries.ringHom)) =
      (Polynomial.aeval (ψ X)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [hC, Polynomial.coe_C]
    · simp
  exact DFunLike.congr_fun h2 (trunc (D + 1) f)

/-- composition: `ev_a (f ∘ g) = ev_{ev_a g} f` for `g` of zero constant term.
@isnad1 id=eq.2h5v.s7.bbeb1e4a4de0 from=translated src=- shape=9bdfe796 vocab=85f5e8dd
-/
theorem ev_subst {D : ℕ} {a : K} (ha : a ^ (D + 1) = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    RG6B.ev D a (f.subst g) = RG6B.ev D (RG6B.ev D a g) f := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hb := pow_ev_eq_zero ha hg
  let φ1 : ℚ⟦X⟧ →+* K := (RG6B.evHom D a ha).comp (substAlgHom hs : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧).toRingHom
  have e1 : ∀ f : ℚ⟦X⟧, φ1 f = RG6B.ev D a (f.subst g) := fun f => by
    change RG6B.ev D a ((substAlgHom hs : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧) f) = _
    rw [coe_substAlgHom]
  let φ2 : ℚ⟦X⟧ →+* K := RG6B.evHom D (RG6B.ev D a g) hb
  have hC1 : ∀ c : ℚ, φ1 (C c) = algebraMap ℚ K c := fun c => by
    rw [e1, subst_C]; exact RG6B.ev_C D a c
  have hX1 : φ1 (X ^ (D + 1)) = 0 := by
    rw [e1, subst_pow hs, subst_X hs]
    exact (map_pow (RG6B.evHom D a ha) g (D + 1)).trans hb
  have hC2 : ∀ c : ℚ, φ2 (C c) = algebraMap ℚ K c := fun c => RG6B.ev_C D _ c
  have hX2 : φ2 (X ^ (D + 1)) = 0 := by
    change RG6B.ev D (RG6B.ev D a g) ((X : ℚ⟦X⟧) ^ (D + 1)) = 0
    rw [ev_X_pow hb]; exact hb
  have hX : φ1 X = φ2 X := by
    rw [e1, subst_X hs]; exact (ev_X hb).symm
  calc RG6B.ev D a (f.subst g) = φ1 f := (e1 f).symm
    _ = Polynomial.aeval (φ1 X) (trunc (D + 1) f) := ring_hom_eq_aeval_trunc φ1 hC1 hX1 f
    _ = Polynomial.aeval (φ2 X) (trunc (D + 1) f) := by rw [hX]
    _ = φ2 f := (ring_hom_eq_aeval_trunc φ2 hC2 hX2 f).symm

end Ev

section Series

/-- the ODE `(1+X) u' = u`, `u(0) = 0` has only the zero solution
@isnad1 id=eq.2h1v.s7.7e074d07a89f from=translated src=- shape=a5be15de vocab=ceaef6dc
-/
theorem ode_uniq {u : ℚ⟦X⟧} (h : (1 + X) * d⁄dX ℚ u = u) (h0 : constantCoeff u = 0) : u = 0 := by
  have key : ∀ n, coeff n u = 0 := by
    intro n
    induction n with
    | zero => rwa [coeff_zero_eq_constantCoeff_apply]
    | succ m ih =>
      have e := congrArg (coeff m) h
      rw [add_mul, one_mul, map_add] at e
      rcases m with _ | m
      · rw [coeff_zero_X_mul, coeff_derivative, ih] at e
        simpa using e
      · rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative, ih] at e
        simp only [zero_mul, add_zero] at e
        have hne : ((m + 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
        exact (mul_eq_zero.1 e).resolve_right hne
  ext n; simpa using key n

/--
@isnad1 id=eq.1h2v.s7.10f5f02aedb1 from=translated src=- shape=0ecd46a2 vocab=30bbd488
-/
theorem constantCoeff_subst_of_zero {a : ℚ⟦X⟧} (ha : constantCoeff a = 0) (f : ℚ⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have := constantCoeff_subst hs f
  change constantCoeff (f.subst a) = _ at this
  rw [this, finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    have ha' : MvPowerSeries.constantCoeff a = 0 := ha
    simp [ha', hd]

end Series

section Nilp

variable {K : Type*} [CommRing K] [Algebra ℚ K]

open IsNilpotent in
/-- `log(1+x) = ∑_{i < nilpotencyClass x} (-1)^(i+1)/i • x^i` (junk value `0` if `x` is not
nilpotent).-/
noncomputable def logOnePlus (x : K) : K :=
  ∑ i ∈ range (nilpotencyClass x), (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i

open IsNilpotent in
/--
@isnad1 id=eq.1h3v.s7.e98d9157ded3 from=translated src=- shape=3f831cb6 vocab=db115cb7
-/
theorem logOnePlus_eq_sum {x : K} {k : ℕ} (h : x ^ k = 0) :
    logOnePlus x = ∑ i ∈ range k, (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i := by
  have h₁ : ∑ i ∈ range k, (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i =
      ∑ i ∈ range (nilpotencyClass x), (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i +
        ∑ i ∈ Ico (nilpotencyClass x) k, (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i ∈ Ico (nilpotencyClass x) k, (((-1 : ℚ) ^ (i + 1) / i : ℚ)) • x ^ i = 0 by
    dsimp [logOnePlus]
    rw [h₁, this, add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

/--
@isnad1 id=eq.1h3v.s6.60f8a5ec39d6 from=translated src=- shape=12affe5d vocab=6f48367c
-/
theorem logOnePlus_eq_ev {x : K} {D : ℕ} (h : x ^ (D + 1) = 0) :
    logOnePlus x = RG6B.ev D x (log ℚ) := by
  rw [logOnePlus_eq_sum h, RG6B.ev_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_log]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [ite_eq_right hi.ne']; rfl

/--
@isnad1 id=eq.1h3v.s6.62daa81208a0 from=translated src=- shape=12affe5d vocab=c842b1cc
-/
theorem exp_eq_ev {a : K} {D : ℕ} (h : a ^ (D + 1) = 0) :
    IsNilpotent.exp a = RG6B.ev D a (exp ℚ) := by
  rw [IsNilpotent.exp_eq_sum h, RG6B.ev_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp]
  simp

/--
@isnad1 id=eq.1h3v.s6.06f8c06c530f from=translated src=- shape=fb563c5d vocab=c3bd47fa
-/
theorem pow_logOnePlus_eq_zero {x : K} {D : ℕ} (h : x ^ (D + 1) = 0) :
    (logOnePlus x) ^ (D + 1) = 0 := by
  rw [logOnePlus_eq_ev h]
  exact pow_ev_eq_zero h constantCoeff_log

/--
@isnad1 id=isnilpot.1h2v.s6.345c6ada958c from=translated src=- shape=92840d3c vocab=90a2f0e0
-/
theorem isNilpotent_logOnePlus {x : K} (hx : IsNilpotent x) : IsNilpotent (logOnePlus x) := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n + 1, pow_logOnePlus_eq_zero (D := n) (by rw [pow_succ, hn, zero_mul])⟩

omit [Algebra ℚ K] in
/--
@isnad1 id=isnilpot.1h3v.s6.b63364195009 from=translated src=- shape=2190f7c6 vocab=889f771b
-/
theorem isNilpotent_nsmul {a : K} (ha : IsNilpotent a) (j : ℕ) : IsNilpotent (j • a) := by
  rw [nsmul_eq_mul]; exact Commute.isNilpotent_mul_left (Commute.all _ _) ha

/--
@isnad1 id=eq.1h3v.s6.8237e8f26924 from=translated src=- shape=09ce23a2 vocab=32a9ba1e
-/
theorem exp_nsmul {a : K} (ha : IsNilpotent a) (j : ℕ) :
    IsNilpotent.exp (j • a) = IsNilpotent.exp a ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [succ_nsmul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (isNilpotent_nsmul ha j) ha,
      ih, pow_succ]

/--
@isnad1 id=eq.1h5v.s6.22ae8c649b9a from=translated src=- shape=874e8315 vocab=ef7afdd3
-/
theorem map_logOnePlus {F L : Type*} [CommRing L] [Algebra ℚ L] [FunLike F K L]
    [RingHomClass F K L] {x : K} (hx : IsNilpotent x) (f : F) :
    f (logOnePlus x) = logOnePlus (f x) := by
  obtain ⟨k, hk⟩ := hx
  have hk' : (f x) ^ k = 0 := by rw [← map_pow, hk, map_zero]
  rw [logOnePlus_eq_sum hk, logOnePlus_eq_sum hk', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, map_pow]

end Nilp

section Todd

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/--
@isnad1 id=eq.0h5v.s6.7390f8d4a5e5 from=translated src=- shape=145f46a1 vocab=4e58ce58
-/
theorem ev_rescale (D : ℕ) (c : ℚ) (a : K) (f : ℚ⟦X⟧) :
    RG6B.ev D a (rescale c f) = RG6B.ev D (c • a) f := by
  rw [RG6B.ev_eq_sum, RG6B.ev_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, coeff_rescale, smul_smul, mul_comm]

/--
@isnad1 id=eq.1h3v.s6.8a546188549e from=translated src=- shape=13aa10e7 vocab=89af4875
-/
theorem ev_expNeg {D : ℕ} {a : K} (h : a ^ (D + 1) = 0) :
    RG6B.ev D a RG6B.expNeg = IsNilpotent.exp (-a) := by
  have h' : (-a) ^ (D + 1) = 0 := by rw [neg_pow, h, mul_zero]
  rw [RG6B.expNeg, ev_rescale, neg_smul, one_smul, exp_eq_ev h']

/-- `Td(a) · (1 - e^{-a}) = a` for `a^(D+1) = 0`
@isnad1 id=eq.1h3v.s7.2307cb1a7b99 from=translated src=- shape=a118dc61 vocab=9101fe07
-/
theorem Td_mul_one_sub_exp_neg {a : K} {D : ℕ} (h : a ^ (D + 1) = 0) :
    RG6B.Td D a * (1 - IsNilpotent.exp (-a)) = a := by
  have h1 : 1 - IsNilpotent.exp (-a) = RG6B.ev D a (1 - RG6B.expNeg) := by
    rw [ev_sub h, RG6B.ev_one, ev_expNeg h]
  have h2 : RG6B.ev D a (RG6B.Pser * RG6B.Tdser) = 1 := by
    rw [RG6B.Pser_mul_Tdser, RG6B.ev_one]
  rw [h1, ← RG6B.X_mul_Pser, RG6B.ev_mul h, ev_X h, RG6B.Td]
  rw [RG6B.ev_mul h] at h2
  linear_combination a * h2

/--
@isnad1 id=eq.2h4v.s6.40db2b121590 from=translated src=- shape=49bd4269 vocab=3b1ebb91
-/
theorem Td_indep {a : K} {D D' : ℕ} (h : a ^ (D + 1) = 0) (hD : D ≤ D') :
    RG6B.Td D' a = RG6B.Td D a :=
  ev_eq_of_le h hD _

/--
@isnad1 id=eq.0h6v.s7.af7c46606d15 from=translated src=- shape=a5e4b500 vocab=47d0bb85
-/
theorem map_ev {L : Type*} [CommRing L] [Algebra ℚ L] (f : K →+* L) (D : ℕ) (a : K)
    (g : ℚ⟦X⟧) : f (RG6B.ev D a g) = RG6B.ev D (f a) g := by
  rw [RG6B.ev_eq_sum, RG6B.ev_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, map_pow]

/--
@isnad1 id=eq.0h5v.s7.bf46813b5fd3 from=translated src=- shape=7e9940e3 vocab=1ca11d5f
-/
theorem map_Td {L : Type*} [CommRing L] [Algebra ℚ L] (f : K →+* L) (D : ℕ) (a : K) :
    f (RG6B.Td D a) = RG6B.Td D (f a) :=
  map_ev f D a _

/--
@isnad1 id=eq.0h6v.s7.73079d793792 from=translated src=- shape=1ae2aa6d vocab=ec2dadeb
-/
theorem map_th {L : Type*} [CommRing L] [Algebra ℚ L] (f : K →+* L) (j D : ℕ) (a : K) :
    f (RG6B.th j D a) = RG6B.th j D (f a) :=
  map_ev f D a _

/-- the Todd class of `log(1+x)` as an explicit polynomial in `x = [L] - 1`.
@isnad1 id=eq.1h3v.s6.603afa19df37 from=translated src=- shape=6a228188 vocab=d79fba9a
-/
theorem Td_logOnePlus {x : K} {D : ℕ} (h : x ^ (D + 1) = 0) :
    RG6B.Td D (logOnePlus x) = RG6B.ev D x (RG6B.Tdser.subst (log ℚ)) := by
  rw [RG6B.Td, logOnePlus_eq_ev h, ev_subst h constantCoeff_log]

end Todd

end TOWERW
