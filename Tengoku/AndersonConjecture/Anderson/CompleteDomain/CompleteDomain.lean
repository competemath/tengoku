/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku
import Tengoku.AndersonConjecture.Anderson.CompleteDomain.LocalRing

/-!
# The Complete Local Domain T = C[[x,y,z]]/(x^2-yz)

This folder constructs the complete local domain T used in the
main counterexample. T is the quotient of C[[x,y,z]] by the
ideal (x^2-yz). It is a two-dimensional Noetherian complete local
domain with a height-one prime Q = (x,y) that is not principal.
-/

noncomputable section

open MvPowerSeries in
/-- Q = (x, y)T, the height-1 prime that is not principal.
Here x = image of X 0, y = image of X 1 in T. -/
def Q : Ideal T :=
  Ideal.span {Ideal.Quotient.mk conj_I (X 0), Ideal.Quotient.mk conj_I (X 1)}

/-- Ring hom from MvPowerSeries (Fin 3) ℂ to PowerSeries ℂ that "projects onto X₂":
    φ(f)(n) = coeff (Finsupp.single 2 n) f.
    This sends X₀ ↦ 0, X₁ ↦ 0, X₂ ↦ X. -/
noncomputable def phiToPS : MvPowerSeries (Fin 3) ℂ →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk (fun n => MvPowerSeries.coeff (Finsupp.single 2 n) f)
  map_one' := by
    ext n
    simp only [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, Finsupp.single_eq_zero]
    erw [PowerSeries.coeff_one]
  map_mul' f g := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk]
    erw [PowerSeries.coeff_mul]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    congr 1
    ext ⟨a, b⟩
    simp [PowerSeries.coeff_mk]
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, map_zero]
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]

open MvPowerSeries in
/-- The ideal P = (X₀, X₁) in MvPowerSeries (Fin 3) ℂ. -/
def P_pre : Ideal (MvPowerSeries (Fin 3) ℂ) :=
  Ideal.span {X 0, X 1}

open MvPowerSeries in
/-- "Division by X s": shifts the s-index down by 1. -/
def divX (s : Fin 3) (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun m => f (m + Finsupp.single s 1)

open MvPowerSeries in
/-- f - X s * divX s f vanishes whenever m s ≥ 1, and equals f(m) when m s = 0. -/
theorem coeff_sub_X_mul_divX
    (s : Fin 3) (f : MvPowerSeries (Fin 3) ℂ) (m : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff m (f - X s * divX s f) =
      if m s = 0 then MvPowerSeries.coeff m f else 0 := by
  simp only [map_sub]
  rw [show (X s : MvPowerSeries (Fin 3) ℂ) =
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single s 1) 1
    from rfl]
  rw [MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle hms
  · exfalso
    have := hle s
    simp [Finsupp.single_eq_same] at this
    omega
  · simp only [one_mul]
    simp only [sub_eq_zero]
    change f m = f (m - Finsupp.single s 1 + Finsupp.single s 1)
    rw [tsub_add_cancel_of_le hle]
  · simp
  · exfalso
    apply hle
    intro i
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · subst heq
      omega
    · exact Nat.zero_le _

open MvPowerSeries in
noncomputable def negSubst_map : Fin 2 → MvPowerSeries (Fin 2) ℂ :=
  fun i => -(X i)

lemma negSubst_hasSubst : MvPowerSeries.HasSubst negSubst_map := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  simp [negSubst_map, MvPowerSeries.constantCoeff_X]

noncomputable def negSubst :
    MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  MvPowerSeries.substAlgHom negSubst_hasSubst

open MvPowerSeries in
lemma negSubst_X (i : Fin 2) : negSubst (X i) = -(X i) := by
  change MvPowerSeries.substAlgHom negSubst_hasSubst (X i) = -(X i)
  rw [MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
lemma negSubst_ψ_map (i : Fin 3) : negSubst (ψ_map i) = ψ_map i := by
  fin_cases i
  · change negSubst (X 0 * X 1) = X 0 * X 1
    rw [map_mul, negSubst_X, negSubst_X, neg_mul_neg]
  · change negSubst ((X 0) ^ 2) = (X 0) ^ 2
    rw [map_pow, negSubst_X, neg_sq]
  · change negSubst ((X 1) ^ 2) = (X 1) ^ 2
    rw [map_pow, negSubst_X, neg_sq]

open MvPowerSeries in
lemma negSubst_comp_ψ_hom (f : MvPowerSeries (Fin 3) ℂ) :
    negSubst (ψ_hom f) = ψ_hom f := by
  have h1 : negSubst (ψ_hom f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst negSubst_map (ψ_map s)) f := by
    rw [show ψ_hom f = MvPowerSeries.subst ψ_map f from by
      rw [ψ_hom, MvPowerSeries.coe_substAlgHom]]
    rw [show (negSubst : MvPowerSeries (Fin 2) ℂ → _) = MvPowerSeries.subst negSubst_map from by
      rw [show (negSubst : MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] _) =
        MvPowerSeries.substAlgHom negSubst_hasSubst from rfl, MvPowerSeries.coe_substAlgHom]]
    rw [MvPowerSeries.subst_comp_subst_apply ψ_hasSubst negSubst_hasSubst]
  rw [h1]
  have heq : (fun s => MvPowerSeries.subst negSubst_map (ψ_map s)) = ψ_map := by
    funext s
    have : MvPowerSeries.subst negSubst_map (ψ_map s) = negSubst (ψ_map s) := by
      change _ = MvPowerSeries.substAlgHom negSubst_hasSubst (ψ_map s)
      rw [MvPowerSeries.coe_substAlgHom]
    rw [this, negSubst_ψ_map]
  rw [heq, show MvPowerSeries.subst ψ_map f = ψ_hom f from by
    rw [ψ_hom, MvPowerSeries.coe_substAlgHom]]

open MvPowerSeries in
lemma negSubst_map_eq (s : Fin 2) :
    negSubst_map s = ((-1 : ℂ) • MvPowerSeries.X s : MvPowerSeries (Fin 2) ℂ) := by
  simp [negSubst_map]

lemma Finsupp.sum_fin2
    (m : Fin 2 →₀ ℕ) (f : Fin 2 → ℕ → ℕ) (hf : ∀ i, f i 0 = 0) :
    m.sum f = f 0 (m 0) + f 1 (m 1) := by
  rw [Finsupp.sum]
  refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) (fun i hi => by
    simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.mem_sdiff, Finset.mem_univ,
      true_and] at hi
    rw [hi]
    exact hf i) (fun _ _ => rfl)
  |>.trans ?_
  simp [Finset.univ_fin2]

end
