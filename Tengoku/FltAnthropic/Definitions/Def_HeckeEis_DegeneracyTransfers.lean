import Tengoku.FltAnthropic.Definitions.Def_IharaIota
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

namespace HeckeEis

theorem range_iota1 (N : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (Ihara.ι₁ N q).range = heckeUpper N q :=
  Subgroup.ext fun δ => (Ihara.mem_range_iota1_iff N hq δ).trans (mem_heckeUpper N q).symm

def iotaUpperHom (N q : ℕ) [NeZero q] : Gamma0 (N * q) →* heckeUpper N q where
  toFun γ := ⟨Ihara.ι₁ N q γ, by
    rw [← range_iota1 N (NeZero.ne q)]; exact ⟨γ, rfl⟩⟩
  map_one' := Subtype.ext (map_one (Ihara.ι₁ N q))
  map_mul' γ δ := Subtype.ext (map_mul (Ihara.ι₁ N q) γ δ)

@[simp] theorem coe_iotaUpperHom (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    (iotaUpperHom N q γ : Gamma0 N) = Ihara.ι₁ N q γ := rfl

noncomputable def iotaUpperEquiv (N q : ℕ) [NeZero q] : Gamma0 (N * q) ≃* heckeUpper N q :=
  MulEquiv.ofBijective (iotaUpperHom N q)
    ⟨fun a b h => Ihara.iota1_injective N (NeZero.ne q) (congrArg Subtype.val h),
     fun δ => by
      have hmem : (δ : Gamma0 N) ∈ (Ihara.ι₁ N q).range := by
        rw [range_iota1 N (NeZero.ne q)]; exact δ.2
      obtain ⟨γ, hγ⟩ := hmem
      exact ⟨γ, Subtype.ext hγ⟩⟩

@[simp] theorem iotaUpperEquiv_apply (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    iotaUpperEquiv N q γ = iotaUpperHom N q γ := rfl

theorem coe_iotaUpperEquiv_symm (N q : ℕ) [NeZero q] (δ : ↥(heckeUpper N q)) :
    (((((iotaUpperEquiv N q).symm δ) : Gamma0 (N * q)) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ)
      = !![((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0,
            ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 / (q : ℤ);
          ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 * (q : ℤ),
            ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1] := by
  have hqZ : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  set δ' := (iotaUpperEquiv N q).symm δ with hδ'
  have hι : Ihara.ι₁ N q δ' = (δ : Gamma0 N) :=
    congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply δ)
  have hmat : Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ))
      = (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Ihara.coe_coe_iota1, hι]
  have h00 := congrFun (congrFun hmat 0) 0
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 := congrFun (congrFun hmat 1) 0
  have h11 := congrFun (congrFun hmat 1) 1
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 0 0
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 from rfl] at h00
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 0 1
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 * (q : ℤ)
      from rfl] at h01
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 1 0
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 / (q : ℤ)
      from rfl] at h10
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 1 1
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 from rfl] at h11
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00.symm ▸ rfl
  · show ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
        = ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 / (q : ℤ)
    rw [← h01, Int.mul_ediv_cancel _ hqZ]
  · show ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0
        = ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 * (q : ℤ)
    rw [← h10, Int.ediv_mul_cancel (Ihara.q_dvd_entry N q δ')]
  · exact h11.symm ▸ rfl

theorem heckeConj_iotaUpperHom (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    heckeConj N q (iotaUpperHom N q γ) = Ihara.ι₀ N q γ := by
  have hq : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  refine Subtype.ext (Subtype.ext ?_)
  show (heckeConjSL N q (iotaUpperHom N q γ) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [coe_heckeConjSL]
  have hival : (((iotaUpperHom N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = Ihara.iota1Mat q (γ : SL(2, ℤ)) := Ihara.coe_coe_iota1 N q γ
  rw [hival]
  have hi0 : (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [hi0]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [heckeConjMat, Ihara.iota1Mat]
  · simp [heckeConjMat, Ihara.iota1Mat, Int.mul_ediv_cancel _ hq]
  · simp [heckeConjMat, Ihara.iota1Mat, Int.ediv_mul_cancel (Ihara.q_dvd_entry N q γ)]
  · simp [heckeConjMat, Ihara.iota1Mat]

noncomputable def degeneracyTransfer₁ (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A] :
    (Additive (Gamma0 (N * q)) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (coresHom (heckeUpper N q)).comp
    (pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom))

def conjUpperHom (N q : ℕ) (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    Gamma0 (N * q) →* heckeUpper N q where
  toFun γ := ⟨u * Ihara.ι₀ N q γ * u⁻¹, (mem_heckeUpper N q).mpr (hu γ)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    show u * Ihara.ι₀ N q (γ * δ) * u⁻¹
        = (u * Ihara.ι₀ N q γ * u⁻¹) * (u * Ihara.ι₀ N q δ * u⁻¹)
    rw [map_mul]
    group)

noncomputable def alConjHom (N q : ℕ) [NeZero q] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    Gamma0 (N * q) →* Gamma0 (N * q) :=
  ((iotaUpperEquiv N q).symm.toMonoidHom).comp (conjUpperHom N q u hu)

theorem iota1_alConjHom (N q : ℕ) [NeZero q] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    (γ : Gamma0 (N * q)) :
    Ihara.ι₁ N q (alConjHom N q u hu γ) = u * Ihara.ι₀ N q γ * u⁻¹ :=
  congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply (conjUpperHom N q u hu γ))

noncomputable def degeneracyTransfer₀Aux (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]
    (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    (Additive (Gamma0 (N * q)) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (degeneracyTransfer₁ N q A).comp (pullbackHom (alConjHom N q u hu))

@[simp] theorem degeneracyTransfer₀Aux_apply (N q : ℕ) [NeZero q] (A : Type*)
    [AddCommGroup A] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    (φ : Additive (Gamma0 (N * q)) →+ A) :
    degeneracyTransfer₀Aux N q A u hu φ
      = degeneracyTransfer₁ N q A (pullbackHom (alConjHom N q u hu) φ) := rfl

theorem bezout_of_prime_not_dvd (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    (q : ℤ) * Int.gcdA (q : ℤ) (N : ℤ) - (N : ℤ) * (-Int.gcdB (q : ℤ) (N : ℤ)) = 1 := by
  have hcop : Nat.gcd q N = 1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
  have h := Int.gcd_eq_gcd_ab (q : ℤ) (N : ℤ)
  rw [Int.gcd_natCast_natCast, hcop] at h
  push_cast at h
  linarith

def alConjSqMat (N q : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * a ^ 2 + (N : ℤ) * b, b * (a + 1);
     (N : ℤ) * (q : ℤ) * (a + 1), (N : ℤ) * b + (q : ℤ)]

theorem alConjSqMat_det (N q : ℕ) (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1) :
    Matrix.det (alConjSqMat N q a b) = 1 := by
  rw [alConjSqMat, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * a - (N : ℤ) * b + 1) * hab

def alConjSqElt (N q : ℕ) (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1) :
    Gamma0 (N * q) :=
  ⟨⟨alConjSqMat N q a b, alConjSqMat_det N q a b hab⟩, by
    refine Gamma0_mem.mpr ?_
    show ((alConjSqMat N q a b 1 0 : ℤ) : ZMod (N * q)) = 0
    show (((N : ℤ) * (q : ℤ) * (a + 1) : ℤ) : ZMod (N * q)) = 0
    have hNq : ((N : ZMod (N * q)) * (q : ZMod (N * q))) = 0 := by
      rw [← Nat.cast_mul]
      exact ZMod.natCast_self _
    push_cast
    rw [hNq, zero_mul]⟩

end HeckeEis
