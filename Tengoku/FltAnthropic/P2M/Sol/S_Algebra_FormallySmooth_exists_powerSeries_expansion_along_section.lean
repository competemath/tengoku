import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section

open PowerSeries

universe u v

namespace P2M
namespace TadicPS

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

variable (R) in

noncomputable abbrev JX : Ideal R⟦X⟧ := Ideal.span {X}

/--
@isnad1 id=eq.0h2v.s7.9a1b2a71491c from=translated src=- shape=d52bbb56 vocab=dbe051f5
-/
theorem JX_pow (n : ℕ) : JX R ^ n = Ideal.span {(X : R⟦X⟧) ^ n} :=
  Ideal.span_singleton_pow X n

/--
@isnad1 id=iff.0h3v.s8.61ead183d4c2 from=translated src=- shape=157e6ea7 vocab=bff409b6
-/
theorem mem_JX_pow {n : ℕ} {p : R⟦X⟧} : p ∈ JX R ^ n ↔ ∀ k, k < n → coeff k p = 0 := by
  rw [JX_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

/--
@isnad1 id=iff.0h2v.s7.283959ac219f from=translated src=- shape=1b2893e7 vocab=df09952a
-/
theorem mem_JX {p : R⟦X⟧} : p ∈ JX R ↔ constantCoeff p = 0 := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]

/--
@isnad1 id=eq.2h5v.s11.73392909bc5f from=translated src=- shape=9d4b4ad8 vocab=7a6bddc2
-/
theorem coeff_eq_of_mk_eq {n k : ℕ} (hk : k < n) {p q : R⟦X⟧}
    (h : Ideal.Quotient.mk (JX R ^ n) p = Ideal.Quotient.mk (JX R ^ n) q) :
    coeff k p = coeff k q := by
  rw [Ideal.Quotient.eq, mem_JX_pow] at h
  have := h k hk
  rwa [map_sub, sub_eq_zero] at this

/--
@isnad1 id=iff.0h3v.s7.e6d32b36ff14 from=translated src=- shape=23304175 vocab=3972b829
-/
theorem X_pow_succ_dvd_X_pow_mul_iff {n : ℕ} {y : R⟦X⟧} :
    (X : R⟦X⟧) ^ (n + 1) ∣ X ^ n * y ↔ constantCoeff y = 0 := by
  constructor
  · intro h
    have h' := (X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
    rwa [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at h'
  · intro h
    obtain ⟨z, rfl⟩ := X_dvd_iff.mpr h
    exact ⟨z, by ring⟩

/--
@isnad1 id=le.0h2v.s7.370fc68600b4 from=translated src=- shape=f9cc2012 vocab=b37b5151
-/
theorem JX_pow_le (n : ℕ) : JX R ^ (n + 2) ≤ JX R ^ (n + 1) :=
  Ideal.pow_le_pow_right (Nat.le_succ _)

/--
@isnad1 id=isnilpot.0h2v.s11.c421ec340037 from=translated src=- shape=43d61b9b vocab=0af83ac6
-/
theorem isNilpotent_ker_factor (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor (JX_pow_le (R := R) n))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

/--
@isnad1 id=strictmo.0h0v.s4.22cd382cff94 from=translated src=- shape=a257ebec vocab=c431414c
-/
theorem strictMono_add_two : StrictMono fun k : ℕ => k + 2 :=
  fun _ _ h => Nat.add_lt_add_right h 2

variable (e : A →ₐ[R] R)

abbrev kerI : Ideal A := RingHom.ker e.toRingHom

/--
@isnad1 id=iff.0h4v.s7.d447f618dba2 from=translated src=- shape=37fc89ed vocab=abe05e38
-/
theorem mem_kerI {a : A} : a ∈ kerI e ↔ e a = 0 := RingHom.mem_ker

/--
@isnad1 id=eq.0h4v.s7.affac92af83d from=translated src=- shape=1d3488ab vocab=bf4cedfe
-/
theorem e_algebraMap (r : R) : e (algebraMap R A r) = r := e.commutes r

/--
@isnad1 id=mem.0h4v.s7.2a1015d5cbe9 from=translated src=- shape=13749656 vocab=4e14c6a4
-/
theorem sub_algebraMap_mem (a : A) : a - algebraMap R A (e a) ∈ kerI e := by
  rw [mem_kerI, map_sub, e_algebraMap, sub_self]

noncomputable def projI : A →ₗ[R] kerI e :=
  LinearMap.codRestrict ((kerI e).restrictScalars R)
    (LinearMap.id - (Algebra.linearMap R A) ∘ₗ e.toLinearMap) (sub_algebraMap_mem e)

/--
@isnad1 id=eq.0h4v.s9.d3298c310af7 from=translated src=- shape=bfc7103c vocab=46e811da
-/
@[scoped simp]
theorem projI_coe (a : A) : (projI e a : A) = a - algebraMap R A (e a) := rfl

def IsPointDerivation (D : A →ₗ[R] R) : Prop :=
  ∀ a b : A, D (a * b) = e a * D b + e b * D a

namespace IsPointDerivation

variable {e} {D : A →ₗ[R] R}

/--
@isnad1 id=eq.1h4v.s8.01b43fcfd777 from=translated src=- shape=42079d59 vocab=e719fcc9
-/
theorem map_one (hD : IsPointDerivation e D) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, _root_.map_one e, one_mul] at h
  linear_combination -h

/--
@isnad1 id=eq.1h5v.s8.f998700e8b50 from=translated src=- shape=e07cd264 vocab=71f03719
-/
theorem map_algebraMap (hD : IsPointDerivation e D) (r : R) : D (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hD.map_one, smul_zero]

end IsPointDerivation

section Lift

noncomputable def sigma2 {D : A →ₗ[R] R} (hD : IsPointDerivation e D) :
    A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ 2) where
  toFun a := Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X)
  map_one' := by
    simp only [_root_.map_one, hD.map_one, map_zero, zero_mul, add_zero]
  map_mul' a b := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (a * b)) + C (D (a * b)) * X) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) *
        Ideal.Quotient.mk (JX R ^ 2) (C (e b) + C (D b) * X)
    rw [← _root_.map_mul (Ideal.Quotient.mk (JX R ^ 2)), Ideal.Quotient.eq]
    have h : C (e (a * b)) + C (D (a * b)) * X - (C (e a) + C (D a) * X) * (C (e b) + C (D b) * X)
        = -(C (D a * D b) * (X : R⟦X⟧) ^ 2) := by
      simp only [_root_.map_mul, hD a b, map_add]
      ring
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self X) 2))
  map_zero' := by
    simp only [map_zero, zero_mul, add_zero]
  map_add' a b := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (a + b)) + C (D (a + b)) * X) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) +
        Ideal.Quotient.mk (JX R ^ 2) (C (e b) + C (D b) * X)
    rw [← map_add (Ideal.Quotient.mk (JX R ^ 2))]
    congr 1
    simp only [map_add]
    ring
  commutes' r := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (algebraMap R A r)) + C (D (algebraMap R A r)) * X) =
      algebraMap R (R⟦X⟧ ⧸ JX R ^ 2) r
    rw [e_algebraMap, hD.map_algebraMap, map_zero, zero_mul, add_zero]
    rfl

variable [Algebra.FormallySmooth R A]

noncomputable def liftStep (n : ℕ) (σ : A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 1))) :
    A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 2)) :=
  Algebra.FormallySmooth.liftOfSurjective σ (Ideal.Quotient.factorₐ R (JX_pow_le n))
    (Ideal.Quotient.factor_surjective (JX_pow_le n)) (isNilpotent_ker_factor n)

/--
@isnad1 id=eq.0h4v.s10.ec50abf0f885 from=translated src=- shape=3717ae6c vocab=74c2bb8a
-/
theorem factor_comp_liftStep (n : ℕ) (σ : A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 1))) :
    (Ideal.Quotient.factorₐ R (JX_pow_le n)).comp (liftStep n σ) = σ :=
  Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

noncomputable def tower {D : A →ₗ[R] R} (hD : IsPointDerivation e D) :
    (k : ℕ) → (A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (k + 2)))
  | 0 => sigma2 e hD
  | k + 1 => liftStep (k + 1) (tower hD k)

/--
@isnad1 id=eq.1h5v.s11.2784bd284a19 from=translated src=- shape=89cb4b02 vocab=00e0a9db
-/
theorem tower_compat {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (m : ℕ) :
    (Ideal.Quotient.factorPow (JX R) (strictMono_add_two.monotone m.le_succ)).comp
      (tower e hD (m + 1)).toRingHom = (tower e hD m).toRingHom :=
  congrArg AlgHom.toRingHom (factor_comp_liftStep (m + 1) (tower e hD m))

noncomputable def theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) : A →+* R⟦X⟧ :=
  IsAdicComplete.StrictMono.liftRingHom (JX R) strictMono_add_two
    (fun k => (tower e hD k).toRingHom) (fun {m} => tower_compat e hD m)

/--
@isnad1 id=eq.1h6v.s11.b2135546ea32 from=translated src=- shape=cee73a12 vocab=3886a97e
-/
theorem mk_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (k : ℕ) (a : A) :
    Ideal.Quotient.mk (JX R ^ (k + 2)) (theta e hD a) = tower e hD k a :=
  IsAdicComplete.StrictMono.mk_liftRingHom (JX R) strictMono_add_two
    (fun k => (tower e hD k).toRingHom) (fun {m} => tower_compat e hD m) (n := k) a

/--
@isnad1 id=eq.1h5v.s8.bbcd46e7dd8a from=translated src=- shape=53df699a vocab=1d4fc7f1
-/
theorem theta_algebraMap {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (r : R) :
    theta e hD (algebraMap R A r) = C r := by
  ext k
  refine coeff_eq_of_mk_eq (n := k + 2) (by omega) ?_
  rw [mk_theta, AlgHom.commutes, ← Ideal.Quotient.mk_algebraMap, ← C_eq_algebraMap]

/--
@isnad1 id=eq.1h5v.s11.082ea120ae5e from=translated src=- shape=a0a18823 vocab=68217a6f
-/
theorem mk_two_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    Ideal.Quotient.mk (JX R ^ 2) (theta e hD a) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) :=
  mk_theta e hD 0 a

/--
@isnad1 id=eq.1h5v.s8.2d7d7b55e95b from=translated src=- shape=ee43a6ac vocab=f10818b1
-/
theorem constantCoeff_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    constantCoeff (theta e hD a) = e a := by
  have h0 := coeff_eq_of_mk_eq (show 0 < 2 by norm_num) (mk_two_theta e hD a)
  rwa [map_add, coeff_zero_C, coeff_zero_mul_X, add_zero, coeff_zero_eq_constantCoeff_apply] at h0

/--
@isnad1 id=eq.1h5v.s8.8d24a0e0274c from=translated src=- shape=825704df vocab=eb73415e
-/
theorem coeff_one_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    coeff 1 (theta e hD a) = D a := by
  have h1 := coeff_eq_of_mk_eq (show 1 < 2 by norm_num) (mk_two_theta e hD a)
  rwa [map_add, coeff_C_mul, coeff_one_X, coeff_C, ite_eq_right one_ne_zero, zero_add, mul_one] at h1

end Lift

section Triangular

variable {e}

/--
@isnad1 id=mem.2h5v.s8.507f6900cb65 from=translated src=- shape=47466181 vocab=8599a182
-/
theorem theta_mem_JX {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {a : A}
    (ha : a ∈ kerI e) : θ a ∈ JX R := by
  rw [mem_JX, hθ0]
  exact (mem_kerI e).mp ha

/--
@isnad1 id=mem.2h6v.s9.98f14ee59940 from=translated src=- shape=2eb28881 vocab=8f9a0d75
-/
theorem theta_mem_JX_pow {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {n : ℕ}
    {a : A} (ha : a ∈ kerI e ^ n) : θ a ∈ JX R ^ n := by
  have h1 : kerI e ≤ (JX R).comap θ := fun x hx => theta_mem_JX hθ0 hx
  exact ((Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow θ n)) ha

/--
@isnad1 id=ex.3h6v.s9.b5d4528494c5 from=translated src=- shape=10a21952 vocab=f0bd9b1e
-/
theorem gen_pow {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) (n : ℕ) :
    ∀ b ∈ kerI e ^ n, ∃ r : R, b - algebraMap R A r * t₀ ^ n ∈ kerI e ^ (n + 1) := by
  induction n with
  | zero =>
    intro b _
    refine ⟨e b, ?_⟩
    rw [pow_zero, mul_one, zero_add, pow_one]
    exact sub_algebraMap_mem e b
  | succ n ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      obtain ⟨r, hr⟩ := ih x hx
      obtain ⟨s, hs⟩ := hgen y hy
      refine ⟨r * s, ?_⟩
      have hxy : x * y - algebraMap R A (r * s) * t₀ ^ (n + 1) =
          (x - algebraMap R A r * t₀ ^ n) * y +
            algebraMap R A r * (t₀ ^ n * (y - algebraMap R A s * t₀)) := by
        rw [_root_.map_mul]
        ring
      rw [hxy]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ ?_)
      · rw [pow_succ (kerI e) (n + 1)]
        exact Ideal.mul_mem_mul hr hy
      · show _ ∈ kerI e ^ (n + 2)
        rw [pow_add]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ht₀ n) hs
    · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
      refine ⟨r + s, ?_⟩
      have hxy : x + y - algebraMap R A (r + s) * t₀ ^ (n + 1) =
          (x - algebraMap R A r * t₀ ^ (n + 1)) + (y - algebraMap R A s * t₀ ^ (n + 1)) := by
        rw [map_add]
        ring
      rw [hxy]
      exact add_mem hr hs

/--
@isnad1 id=ex.3h5v.s9.76bde1de87c5 from=translated src=- shape=d7738622 vocab=f00572f8
-/
theorem exists_theta_t0_eq {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A}
    (ht₀ : t₀ ∈ kerI e) (hθ1 : coeff 1 (θ t₀) = 1) :
    ∃ v : R⟦X⟧, θ t₀ = X * v ∧ constantCoeff v = 1 := by
  obtain ⟨v, hv⟩ : (X : R⟦X⟧) ∣ θ t₀ := X_dvd_iff.mpr (by rw [hθ0]; exact (mem_kerI e).mp ht₀)
  refine ⟨v, hv, ?_⟩
  have h := coeff_succ_X_mul 0 v
  rw [zero_add, ← hv, hθ1, coeff_zero_eq_constantCoeff_apply] at h
  exact h.symm

/--
@isnad1 id=mem.6h7v.s10.18af0495edc2 from=translated src=- shape=feebf8ce vocab=bb2016c5
-/
theorem mem_pow_of_theta_mem {θ : A →+* R⟦X⟧} (hθC : ∀ r, θ (algebraMap R A r) = C r)
    (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hθ1 : coeff 1 (θ t₀) = 1)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) :
    ∀ (n : ℕ) (a : A), θ a ∈ JX R ^ n → a ∈ kerI e ^ n := by
  obtain ⟨v, hv, hv1⟩ := exists_theta_t0_eq hθ0 ht₀ hθ1
  intro n
  induction n with
  | zero =>
    intro a _
    simp
  | succ n ih =>
    intro a ha
    have ha' : θ a ∈ JX R ^ n := Ideal.pow_le_pow_right n.le_succ ha
    obtain ⟨r, hr⟩ := gen_pow ht₀ hgen n a (ih a ha')
    have h1 : θ (a - algebraMap R A r * t₀ ^ n) ∈ JX R ^ (n + 1) := theta_mem_JX_pow hθ0 hr
    have h2 : θ (algebraMap R A r * t₀ ^ n) ∈ JX R ^ (n + 1) := by
      have := sub_mem ha h1
      rwa [map_sub, sub_sub_cancel] at this
    rw [_root_.map_mul, map_pow, hθC, hv, JX_pow, Ideal.mem_span_singleton,
      show C r * (X * v) ^ n = X ^ n * (C r * v ^ n) by ring,
      X_pow_succ_dvd_X_pow_mul_iff, _root_.map_mul, map_pow, hv1, one_pow, mul_one,
      constantCoeff_C] at h2
    rw [h2, map_zero, zero_mul, sub_zero] at hr
    exact hr

/--
@isnad1 id=ex.4h7v.s9.38fc999e38c3 from=translated src=- shape=1d46e4b8 vocab=3db81166
-/
theorem exists_sub_theta_mem {θ : A →+* R⟦X⟧} (hθC : ∀ r, θ (algebraMap R A r) = C r)
    (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hθ1 : coeff 1 (θ t₀) = 1) :
    ∀ (n : ℕ) (p : R⟦X⟧), ∃ a : A, p - θ a ∈ JX R ^ n := by
  obtain ⟨v, hv, hv1⟩ := exists_theta_t0_eq hθ0 ht₀ hθ1
  intro n
  induction n with
  | zero =>
    intro p
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro p
    obtain ⟨a, ha⟩ := ih p
    rw [JX_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨w, hw⟩ := ha
    refine ⟨a + algebraMap R A (constantCoeff w) * t₀ ^ n, ?_⟩
    rw [JX_pow, Ideal.mem_span_singleton, map_add, _root_.map_mul, map_pow, hθC, hv,
      show p - (θ a + C (constantCoeff w) * (X * v) ^ n) =
        (p - θ a) - C (constantCoeff w) * (X * v) ^ n by ring,
      hw,
      show X ^ n * w - C (constantCoeff w) * (X * v) ^ n =
        X ^ n * (w - C (constantCoeff w) * v ^ n) by ring,
      X_pow_succ_dvd_X_pow_mul_iff, map_sub, _root_.map_mul, map_pow, hv1, one_pow, mul_one,
      constantCoeff_C, sub_self]

end Triangular

/--
@isnad1 id=ex.4h5v.s10.4299f55be870 from=translated src=- shape=ec119501 vocab=99d8f4db
-/
theorem main [Algebra.FormallySmooth R A] {D : A →ₗ[R] R} (hD : IsPointDerivation e D)
    {t₀ : A} (ht₀ : t₀ ∈ kerI e) (hDt : D t₀ = 1)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ kerI e ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by
  have hθ1 : coeff 1 (theta e hD t₀) = 1 := by rw [coeff_one_theta, hDt]
  refine ⟨theta e hD, theta_algebraMap e hD, ?_, ?_⟩
  · intro n a
    rw [← mem_JX_pow]
    exact ⟨mem_pow_of_theta_mem (theta_algebraMap e hD) (constantCoeff_theta e hD) ht₀ hθ1 hgen
      n a, theta_mem_JX_pow (constantCoeff_theta e hD)⟩
  · intro n p
    obtain ⟨a, ha⟩ :=
      exists_sub_theta_mem (theta_algebraMap e hD) (constantCoeff_theta e hD) ht₀ hθ1 n p
    refine ⟨a, fun k hk => ?_⟩
    have := (mem_JX_pow.mp ha) k hk
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

/--
@isnad1 id=ex.1h3v.s9.50b78b19cb96 from=translated src=- shape=dbb92315 vocab=0bfadcf7
-/
theorem exists_data [Module.Free R (kerI e).Cotangent]
    (he : Module.finrank R (kerI e).Cotangent = 1) :
    ∃ (D : A →ₗ[R] R) (t₀ : A), IsPointDerivation e D ∧ t₀ ∈ kerI e ∧ D t₀ = 1 ∧
      ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := Module.subsingleton R A
    refine ⟨0, 0, fun a b => by simp, Ideal.zero_mem _, Subsingleton.elim _ _, fun x _ => ⟨0, ?_⟩⟩
    rw [Subsingleton.elim (x - algebraMap R A 0 * 0) 0]
    exact Ideal.zero_mem _
  · let b := Module.basisUnique Unit he
    obtain ⟨t, ht⟩ := (kerI e).toCotangent_surjective (b default)
    refine ⟨(b.coord default) ∘ₗ ((kerI e).toCotangent.restrictScalars R) ∘ₗ projI e, t, ?_,
      t.2, ?_, ?_⟩
    · intro a c
      have key : (kerI e).toCotangent (projI e (a * c)) =
          e a • (kerI e).toCotangent (projI e c) + e c • (kerI e).toCotangent (projI e a) := by
        rw [← LinearMap.map_smul_of_tower ((kerI e).toCotangent) (e a),
          ← LinearMap.map_smul_of_tower ((kerI e).toCotangent) (e c), ← map_add]
        refine ((kerI e).toCotangent_eq).mpr ?_
        have hcoe : (projI e (a * c) : A) - ((e a • projI e c + e c • projI e a : kerI e) : A) =
            (a - algebraMap R A (e a)) * (c - algebraMap R A (e c)) := by
          simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, projI_coe,
            Algebra.smul_def, _root_.map_mul]
          ring
        rw [hcoe, pow_two]
        exact Ideal.mul_mem_mul (sub_algebraMap_mem e a) (sub_algebraMap_mem e c)
      show b.coord default ((kerI e).toCotangent (projI e (a * c))) =
        e a * b.coord default ((kerI e).toCotangent (projI e c)) +
          e c * b.coord default ((kerI e).toCotangent (projI e a))
      rw [key, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · have hproj : projI e (t : A) = t :=
        Subtype.ext (by rw [projI_coe, (mem_kerI e).mp t.2, map_zero, sub_zero])
      show b.coord default ((kerI e).toCotangent (projI e (t : A))) = 1
      rw [hproj, ht, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    · intro x hx
      have h1 : b.repr ((kerI e).toCotangent ⟨x, hx⟩) default • b default =
          (kerI e).toCotangent ⟨x, hx⟩ := by
        simpa using b.sum_repr ((kerI e).toCotangent ⟨x, hx⟩)
      refine ⟨b.repr ((kerI e).toCotangent ⟨x, hx⟩) default, ?_⟩
      rw [← ht, ← LinearMap.map_smul_of_tower] at h1
      have h2 := ((kerI e).toCotangent_eq).mp h1.symm
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def] at h2
      exact h2

end P2M.TadicPS
open scoped _root_.P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M _root_.P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M.TadicPS
open scoped _root_.P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M

/--
@isnad1 id=ex.1h3v.s10.4c4233812105 from=translated src=- shape=1bff5a8f vocab=edc4c7e9
-/
theorem solution
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by
  obtain ⟨D, t₀, hD, ht₀, hDt, hgen⟩ := P2M.TadicPS.exists_data e he
  exact P2M.TadicPS.main e hD ht₀ hDt hgen
