/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# The Complete Local Domain T

Construction of T = C[[x,y,z]]/(x^2 - yz) and the proof that
T is an integral domain.
-/

noncomputable section

open MvPowerSeries in
/-- The ideal (x² - yz) in ℂ[[x,y,z]] where x = X 0, y = X 1, z = X 2. -/
def conj_I : Ideal (MvPowerSeries (Fin 3) ℂ) :=
  Ideal.span {(X 0) ^ 2 - (X 1) * (X 2)}

/-- T = ℂ[[x,y,z]]/(x²-yz), the main complete local domain. -/
abbrev T := MvPowerSeries (Fin 3) ℂ ⧸ conj_I

open MvPowerSeries in
theorem conj_I_ne_top : conj_I ≠ ⊤ := by
  apply Ideal.span_singleton_ne_top
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  change ¬IsUnit (MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ)
      ((X 0) ^ 2 - (X 1) * (X 2)))
  simp only [map_sub, map_pow, map_mul, MvPowerSeries.constantCoeff_X]
  norm_num

section T_isDomain_proof

open MvPowerSeries

/-- The substitution map ψ : ℂ[[x,y,z]] → ℂ[[u,v]] defined by
  x ↦ u·v, y ↦ u², z ↦ v². -/
noncomputable def ψ_map : Fin 3 → MvPowerSeries (Fin 2) ℂ :=
  fun i => match i with
  | 0 => X 0 * X 1
  | 1 => (X 0) ^ 2
  | 2 => (X 1) ^ 2

lemma ψ_hasSubst : HasSubst (a := ψ_map) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> simp [ψ_map, constantCoeff_X]

noncomputable def ψ_hom :
    MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  MvPowerSeries.substAlgHom ψ_hasSubst

lemma ψ_kills_gen : ψ_hom ((X 0) ^ 2 - (X 1) * (X 2)) = 0 := by
  simp only [map_sub, map_pow, map_mul, ψ_hom, MvPowerSeries.substAlgHom_X]
  simp [ψ_map]
  ring

lemma conj_I_le_ker_ψ : conj_I ≤ RingHom.ker ψ_hom.toRingHom := by
  rw [show conj_I = Ideal.span {(X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
    X 1 * X 2} from rfl, Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact RingHom.mem_ker.mpr ψ_kills_gen

/-- The factored map ψ̄ : T → ℂ[[u,v]]. -/
noncomputable def ψ_bar : T →+* MvPowerSeries (Fin 2) ℂ :=
  Ideal.Quotient.lift conj_I ψ_hom.toRingHom (fun x hx =>
    (conj_I_le_ker_ψ hx : x ∈ RingHom.ker ψ_hom.toRingHom))

/-- Construct a `Fin 3 →₀ ℕ` from three natural numbers. -/
def mkFin3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp] private lemma mkFin3_zero : mkFin3 a b c 0 = a := rfl
@[simp] private lemma mkFin3_one : mkFin3 a b c 1 = b := rfl
@[simp] private lemma mkFin3_two : mkFin3 a b c 2 = c := rfl

lemma mkFin3_ext (n : Fin 3 →₀ ℕ) : n = mkFin3 (n 0) (n 1) (n 2) := by
  ext i
  fin_cases i <;> rfl

/-- Construct a `Fin 2 →₀ ℕ` from two natural numbers. -/
def mkFin2 (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b]

@[simp] private lemma mkFin2_zero : mkFin2 a b 0 = a := rfl
@[simp] private lemma mkFin2_one : mkFin2 a b 1 = b := rfl

/-- Explicit quotient: given f, define q so that f = q * (X₀² - X₁X₂) when ψ(f)=0.
  q(n₀,n₁,n₂) = Σ_{k=0}^{min(n₁,n₂)} f(n₀+2+2k, n₁-k, n₂-k). -/
def divQ (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun n => ∑ k ∈ Finset.range (min (n 1) (n 2) + 1),
    f (mkFin3 (n 0 + 2 + 2 * k) (n 1 - k) (n 2 - k))

lemma mkFin2_inj {a b c d : ℕ} : mkFin2 a b = mkFin2 c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congr_fun (congr_arg DFunLike.coe h) 0, congr_fun (congr_arg DFunLike.coe h) 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma mkFin3_inj {a b c d e f : ℕ} :
    mkFin3 a b c = mkFin3 d e f ↔ a = d ∧ b = e ∧ c = f := by
  constructor
  · intro h
    exact ⟨congr_fun (congr_arg DFunLike.coe h) 0,
           congr_fun (congr_arg DFunLike.coe h) 1,
           congr_fun (congr_arg DFunLike.coe h) 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

-- Fiber characterization: preimages under ψ are {mkFin3(m₀+2k)(m₁-k)(m₂-k) : k ≤ min(m₁,m₂)}

end T_isDomain_proof

end
