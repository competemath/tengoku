/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.LeanPool.LeanPool.AndersonConjecture.CompleteDomain.LocalRing
public import Tengoku

/-!
# The Complete Local Domain T = C[[x,y,z]]/(x^2-yz)

This folder constructs the complete local domain T used in the
main counterexample. T is the quotient of C[[x,y,z]] by the
ideal (x^2-yz). It is a two-dimensional Noetherian complete local
domain with a height-one prime Q = (x,y) that is not principal.
-/

@[expose] public section

noncomputable section

open MvPowerSeries in
/-- Q = (x, y)T, the height-1 prime that is not principal.
Here x = image of X 0, y = image of X 1 in T. -/
def Q : Ideal T :=
  Ideal.span {Ideal.Quotient.mk conjI (X 0), Ideal.Quotient.mk conjI (X 1)}

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
    simp_all
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, map_zero]
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]

open MvPowerSeries in
/-- The ideal P = (X₀, X₁) in MvPowerSeries (Fin 3) ℂ. -/
def PPre : Ideal (MvPowerSeries (Fin 3) ℂ) :=
  Ideal.span {X 0, X 1}

open MvPowerSeries in
/-- conjI ≤ PPre: x²-yz ∈ (X₀, X₁) since x² ∈ (X₀) and yz ∈ (X₁). -/
theorem conjI_le_PPre : conjI ≤ PPre := by
  rw [conjI, Ideal.span_le]
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst hf
  change (X (0 : Fin 3)) ^ 2 - (X 1) * (X 2) ∈ PPre
  apply Ideal.sub_mem
  · rw [sq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))

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
  · simp_all
  · simp only [one_mul]
    simp only [sub_eq_zero]
    change f m = f (m - Finsupp.single s 1 + Finsupp.single s 1)
    rw [tsub_add_cancel_of_le hle]
  · simp
  · simp_all

open MvPowerSeries in
/-- ker phiToPS = PPre. -/
theorem ker_phiToPS_eq : RingHom.ker phiToPS = PPre := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have hcoeff : ∀ n, MvPowerSeries.coeff (Finsupp.single 2 n) f = 0 := by
      intro n
      have h1 : PowerSeries.coeff n (phiToPS f) = 0 := by
        rw [hf, map_zero]
      simp only [phiToPS, PowerSeries.coeff_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk] at h1
      exact h1
    -- Decompose f = X₀ * g₀ + X₁ * g₁ via successive division
    set g₀ := divX 0 f with hg₀_def
    set f' := f - X 0 * g₀ with hf'_def
    set g₁ := divX 1 f' with hg₁_def
    set f'' := f' - X 1 * g₁ with hf''_def
    have hf''_zero : f'' = 0 := by
      ext m
      rw [map_zero]
      rw [hf''_def, coeff_sub_X_mul_divX]
      split_ifs with h1
      · rw [hf'_def, coeff_sub_X_mul_divX]
        split_ifs with h0
        · have hm_eq : m = Finsupp.single 2 (m 2) := by
            ext i
            fin_cases i <;> simp [*]
          rw [hm_eq]
          exact hcoeff (m 2)
        · rfl
      · rfl
    have hdecomp : f = X 0 * g₀ + X 1 * g₁ := by
      have hf'eq : f' = X 1 * g₁ := by
        rw [hf''_def] at hf''_zero
        exact sub_eq_zero.mp hf''_zero
      have hfeq : f = X 0 * g₀ + f' := by rw [hf'_def]
                                          abel
      rw [hf'eq] at hfeq
      exact hfeq
    rw [hdecomp]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span
        (Set.mem_insert_iff.mpr (Or.inr rfl)))
  · rw [PPre, Ideal.span_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext n
    change PowerSeries.coeff n (phiToPS f) = PowerSeries.coeff n 0
    simp only [map_zero, phiToPS, PowerSeries.coeff_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    cases hf with
    | inl h =>
      subst h
      simp only [MvPowerSeries.coeff_X]
      split_ifs with heq
      · exfalso
        have := DFunLike.congr_fun heq (0 : Fin 3)
        simp at this
      · rfl
    | inr h =>
      subst h
      simp only [MvPowerSeries.coeff_X]
      split_ifs with heq
      · exfalso
        have := DFunLike.congr_fun heq (1 : Fin 3)
        simp at this
      · rfl

open MvPowerSeries in
/-- PPre is prime because ker phiToPS = PPre and PowerSeries ℂ is a domain. -/
instance PPre_isPrime : PPre.IsPrime := by
  rw [← ker_phiToPS_eq]
  exact RingHom.ker_isPrime phiToPS

open MvPowerSeries in
/-- Q = Ideal.map (mk conjI) PPre. -/
theorem Q_eq_map_PPre :
    Q = Ideal.map (Ideal.Quotient.mk conjI) PPre := by
  simp only [Q, PPre, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

theorem Q_isPrime : Q.IsPrime := by
  rw [Q_eq_map_PPre]
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by
       rw [Ideal.mk_ker]
       exact conjI_le_PPre)

lemma ψBar_mk (f : MvPowerSeries (Fin 3) ℂ) :
    ψBar (Ideal.Quotient.mk conjI f) = ψHom f :=
  Ideal.Quotient.lift_mk conjI ψHom.toRingHom _

open MvPowerSeries in
lemma ψBar_mk_X0 :
    ψBar (Ideal.Quotient.mk conjI (X 0)) =
      (X (0 : Fin 2)) * (X 1 : MvPowerSeries (Fin 2) ℂ) := by
  rw [ψBar_mk, ψHom, MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
lemma ψBar_mk_X1 :
    ψBar (Ideal.Quotient.mk conjI (X 1)) =
      ((X (0 : Fin 2)) : MvPowerSeries (Fin 2) ℂ) ^ 2 := by
  rw [ψBar_mk, ψHom, MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
/-- Substitution data `Xᵢ ↦ -Xᵢ` on `ℂ[[u,v]]`, used to detect odd-parity
vanishing of coefficients (recall `ψMap` sends `X₀ ↦ X₀X₁`, `X₁ ↦ X₀²`,
`X₂ ↦ X₁²`, so the total degree of any monomial in the image is even). -/
noncomputable def negSubstMap : Fin 2 → MvPowerSeries (Fin 2) ℂ :=
  fun i => -(X i)

lemma negSubst_hasSubst : MvPowerSeries.HasSubst negSubstMap := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  simp [negSubstMap, MvPowerSeries.constantCoeff_X]

/-- The algebra hom on `ℂ[[u,v]]` induced by the substitution `Xᵢ ↦ -Xᵢ`. -/
noncomputable def negSubst :
    MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  MvPowerSeries.substAlgHom negSubst_hasSubst

open MvPowerSeries in
lemma negSubst_X (i : Fin 2) : negSubst (X i) = -(X i) := by
  change MvPowerSeries.substAlgHom negSubst_hasSubst (X i) = -(X i)
  rw [MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
lemma negSubst_ψMap (i : Fin 3) : negSubst (ψMap i) = ψMap i := by
  fin_cases i
  · change negSubst (X 0 * X 1) = X 0 * X 1
    rw [map_mul, negSubst_X, negSubst_X, neg_mul_neg]
  · change negSubst ((X 0) ^ 2) = (X 0) ^ 2
    rw [map_pow, negSubst_X, neg_sq]
  · change negSubst ((X 1) ^ 2) = (X 1) ^ 2
    rw [map_pow, negSubst_X, neg_sq]

open MvPowerSeries in
lemma negSubst_comp_ψHom (f : MvPowerSeries (Fin 3) ℂ) :
    negSubst (ψHom f) = ψHom f := by
  have h1 : negSubst (ψHom f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst negSubstMap (ψMap s)) f := by
    rw [show ψHom f = MvPowerSeries.subst ψMap f from by
      rw [ψHom, MvPowerSeries.coe_substAlgHom]]
    rw [show (negSubst : MvPowerSeries (Fin 2) ℂ → _) = MvPowerSeries.subst negSubstMap from by
      rw [show (negSubst : MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] _) =
        MvPowerSeries.substAlgHom negSubst_hasSubst from rfl, MvPowerSeries.coe_substAlgHom]]
    rw [MvPowerSeries.subst_comp_subst_apply ψ_hasSubst negSubst_hasSubst]
  rw [h1]
  have heq : (fun s => MvPowerSeries.subst negSubstMap (ψMap s)) = ψMap := by
    funext s
    have : MvPowerSeries.subst negSubstMap (ψMap s) = negSubst (ψMap s) := by
      change _ = MvPowerSeries.substAlgHom negSubst_hasSubst (ψMap s)
      rw [MvPowerSeries.coe_substAlgHom]
    rw [this, negSubst_ψMap]
  rw [heq, show MvPowerSeries.subst ψMap f = ψHom f from by
    rw [ψHom, MvPowerSeries.coe_substAlgHom]]

open MvPowerSeries in
lemma negSubstMap_eq (s : Fin 2) :
    negSubstMap s = ((-1 : ℂ) • MvPowerSeries.X s : MvPowerSeries (Fin 2) ℂ) := by
  simp [negSubstMap]

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

open MvPowerSeries in
lemma coeff_negSubst (g : MvPowerSeries (Fin 2) ℂ) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (negSubst g) = (-1) ^ (m 0 + m 1) * MvPowerSeries.coeff m g := by
  have hns : negSubst g = MvPowerSeries.subst negSubstMap g := by
    rw [negSubst, MvPowerSeries.coe_substAlgHom]
  rw [hns, MvPowerSeries.coeff_subst negSubst_hasSubst]
  have hprod : ∀ d : Fin 2 →₀ ℕ, d.prod (fun s n => (negSubstMap s) ^ n) =
      MvPowerSeries.monomial d ((-1 : ℂ) ^ (d.sum fun _ n => n)) := by
    intro d
    rw [Finsupp.prod_congr (g2 := fun s n => ((-1 : ℂ) • MvPowerSeries.X s) ^ n)
      (fun s _ => by rw [negSubstMap_eq])]
    exact (MvPowerSeries.monomial_smul_const d (-1)).symm
  simp_rw [hprod, MvPowerSeries.coeff_monomial, smul_eq_mul]
  rw [finsum_eq_single _ m]
  · simp only [ite_true]
    have hsum : m.sum (fun (_ : Fin 2) (n : ℕ) => n) = m 0 + m 1 := by
      rw [Finsupp.sum]
      exact Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => by
           simp_all)
        |>.trans (by simp [Finset.univ_fin2])
    rw [hsum]
    ring
  · intro d hd
    simp only [ite_eq_right (Ne.symm hd), mul_zero]

open MvPowerSeries in
lemma ψHom_coeff_odd_parity (f : MvPowerSeries (Fin 3) ℂ)
    (m : Fin 2 →₀ ℕ) (hm : Odd (m 0 + m 1)) :
    MvPowerSeries.coeff m (ψHom f) = 0 := by
  have h := negSubst_comp_ψHom f
  have h1 := congr_arg (MvPowerSeries.coeff m) h
  rw [coeff_negSubst] at h1
  obtain ⟨k, hk⟩ := hm
  rw [hk, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul] at h1
  have h2 : (2 : ℂ) • MvPowerSeries.coeff m (ψHom f) = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h1
  simp_all

open MvPowerSeries in
lemma Q_le_maximalIdeal : Q ≤ IsLocalRing.maximalIdeal T :=
  IsLocalRing.le_maximalIdeal Q_isPrime.ne_top

open MvPowerSeries in
lemma mk_X2_not_mem_Q :
    (Ideal.Quotient.mk conjI (X (2 : Fin 3)) : T) ∉ Q := by
  rw [Q_eq_map_PPre]
  intro hmem
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hmem
  obtain ⟨f, hf_mem, hf_eq⟩ := hmem
  have hfX2 : f - X 2 ∈ conjI := Ideal.Quotient.eq.mp hf_eq
  have hX2_P : X (2 : Fin 3) ∈ PPre := by
    have h := PPre.sub_mem hf_mem (conjI_le_PPre hfX2)
    rwa [show f - (f - X 2) = X 2 from by ring] at h
  rw [← ker_phiToPS_eq, RingHom.mem_ker] at hX2_P
  have : phiToPS (X 2) ≠ 0 := by
    intro h
    have h1 := congr_arg (PowerSeries.coeff 1) h
    simp only [map_zero] at h1
    change (phiToPS (X 2)).coeff 1 = 0 at h1
    simp only [phiToPS, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      PowerSeries.coeff_mk] at h1
    simp_all
  exact this hX2_P

end
