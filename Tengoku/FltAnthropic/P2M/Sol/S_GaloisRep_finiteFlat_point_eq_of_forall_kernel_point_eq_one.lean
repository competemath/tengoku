import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_finiteFlat_point_eq_of_forall_kernel_point_eq_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_finiteFlat_point_eq_of_forall_kernel_point_eq_one

set_option autoImplicit false

section interface
open _root_.Coalgebra open _root_.TensorProduct open _root_.Coalgebra.TensorProduct open _root_.WithConv
variable {R A C : Type*} [CommSemiring R] [Semiring C] [Bialgebra R C] [CommSemiring A] [Algebra R A]

/--
@isnad1 id=eq.0h4v.s8.757ab39babb0 from=translated src=- shape=7ec24753 vocab=d0e83b82
-/
lemma algHom_convOne_apply (c : C) :
    (1 : WithConv (C →ₐ[R] A)) c = algebraMap R A (counit c) :=
  AlgHom.convOne_apply c

/--
@isnad1 id=eq.0h6v.s10.1194ac990825 from=translated src=- shape=267656db vocab=e466257c
-/
lemma algHom_convMul_apply (f g : WithConv (C →ₐ[R] A)) (c : C) :
    (f * g) c = LinearMap.mul' R A (TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap (comul c)) := by
  change (Algebra.TensorProduct.lmul' R (S := A)) (Algebra.TensorProduct.map f.ofConv g.ofConv (comul c)) = _
  induction (comul (R := R) c) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end interface

section CK
open _root_.Coalgebra open _root_.TensorProduct open _root_.Coalgebra.TensorProduct open _root_.WithConv

variable (ℓ : ℕ)

/--
@isnad1 id=eq.0h3v.s10.65be211d296e from=translated src=- shape=2e0952f9 vocab=d91929ee
-/
lemma ck_algebraMap_fixed (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (r : (GaloisRep.ratLocalizedAt ℓ)) : σ (algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r) = algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r :=
  σ.commutes (r : ℚ)

variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]

/--
@isnad1 id=eq.0h7v.s13.6a1d1807c19b from=translated src=- shape=7f7bfa7d vocab=777ce7bb
-/
lemma ck_sweedler (f g : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ))) {c : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr (GaloisRep.ratLocalizedAt ℓ) c ι𝓡) :
    (f * g) c = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  rw [algHom_convMul_apply, ← 𝓡.eq, map_sum, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]

/--
@isnad1 id=eq.3h7v.s13.16863644272a from=translated src=- shape=6de3589f vocab=281c1a06
-/
lemma ck_fixed_mul (D : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) (f g : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ)))
    (hf : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ (f h) = f h)
    (hg : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ (g h) = g h) :
    ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ ((f * g) h) = (f * g) h := by
  intro σ hσ c
  rw [ck_sweedler ℓ H f g (Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt ℓ) c), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hf σ hσ, hg σ hσ]

/--
@isnad1 id=eq.1h5v.s12.74dd0e671c6b from=translated src=- shape=d0a943e0 vocab=bf9bbb0c
-/
lemma ck_fixed_one (D : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) :
    ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ ((1 : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ))) h) = (1 : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ))) h := by
  intro σ _ c
  rw [algHom_convOne_apply]
  exact ck_algebraMap_fixed ℓ σ _

/--
@isnad1 id=eq.2h7v.s13.660f9b5c3fb0 from=translated src=- shape=51db1872 vocab=6fb01399
-/
lemma ck_fixed_pow (D : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) (f : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ)))
    (hf : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ (f h) = f h) (n : ℕ) :
    ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ D → ∀ h : H, σ ((f ^ n) h) = (f ^ n) h := by
  induction n with
  | zero => rw [pow_zero]; exact ck_fixed_one ℓ H D
  | succ n ih => rw [pow_succ]; exact ck_fixed_mul ℓ H D _ _ ih hf

variable (A : ValuationSubring (AlgebraicClosure ℚ))

/--
@isnad1 id=le.1h3v.s9.1c1b4c148f87 from=translated src=- shape=c3c563a4 vocab=aef0d1fe
-/
lemma ck_val_algebraMap_le_one (hA : A.LiesOverPrime ℓ) (r : (GaloisRep.ratLocalizedAt ℓ)) :
    A.valuation (algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r) ≤ 1 := by
  have hr : (r : ℚ).den.Coprime ℓ := r.2
  have hℓ : A.valuation (ℓ : (AlgebraicClosure ℚ)) < 1 := (A.mem_nonunits_iff).1 hA
  have hnum : A.valuation ((r : ℚ).num : (AlgebraicClosure ℚ)) ≤ 1 := A.valuation_le_one ⟨_, intCast_mem A _⟩
  have hden1 : A.valuation ((r : ℚ).den : (AlgebraicClosure ℚ)) ≤ 1 := A.valuation_le_one ⟨_, natCast_mem A _⟩
  have hden : A.valuation ((r : ℚ).den : (AlgebraicClosure ℚ)) = 1 := by
    refine le_antisymm hden1 (not_lt.1 fun hlt => ?_)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hr
    have h1 : (u : (AlgebraicClosure ℚ)) * ((r : ℚ).den : (AlgebraicClosure ℚ)) + (w : (AlgebraicClosure ℚ)) * (ℓ : (AlgebraicClosure ℚ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → (AlgebraicClosure ℚ)) huw
    have hu : A.valuation (u : (AlgebraicClosure ℚ)) ≤ 1 := A.valuation_le_one ⟨_, intCast_mem A _⟩
    have hw : A.valuation (w : (AlgebraicClosure ℚ)) ≤ 1 := A.valuation_le_one ⟨_, intCast_mem A _⟩
    have hx : A.valuation ((u : (AlgebraicClosure ℚ)) * ((r : ℚ).den : (AlgebraicClosure ℚ))) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have hy : A.valuation ((w : (AlgebraicClosure ℚ)) * (ℓ : (AlgebraicClosure ℚ))) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hw le_rfl).trans_lt (by rwa [one_mul])
    have := A.valuation.map_add_lt hx hy
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  have e : algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r = ((r : ℚ) : (AlgebraicClosure ℚ)) := by
    change algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) = _
    exact eq_ratCast _ _
  rw [e, Rat.cast_def, map_div₀, hden, div_one]
  exact hnum

variable [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H]

/--
@isnad1 id=le.1h5v.s10.55b2b8b97590 from=translated src=- shape=f91283cd vocab=57f5f0bb
-/
lemma ck_val_apply_le_one (hA : A.LiesOverPrime ℓ) (φ : H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ)) (h : H) :
    A.valuation (φ h) ≤ 1 := by
  have hint : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (φ h) := (Algebra.IsIntegral.isIntegral (R := GaloisRep.ratLocalizedAt ℓ) h).map φ
  obtain ⟨p, hp, hp0⟩ := hint
  refine le_of_not_gt fun hlt => ?_
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul,
    add_eq_zero_iff_eq_neg] at hp0
  apply_fun A.valuation at hp0
  rw [Valuation.map_neg, Valuation.map_pow] at hp0
  refine ne_of_lt (A.valuation.map_sum_lt ?_ ?_) hp0
  · exact pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hlt))
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc A.valuation (algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (p.coeff i)) * A.valuation (φ h) ^ i
        ≤ 1 * A.valuation (φ h) ^ i := mul_le_mul' (ck_val_algebraMap_le_one ℓ A hA _) le_rfl
      _ = A.valuation (φ h) ^ i := one_mul _
      _ < A.valuation (φ h) ^ p.natDegree := pow_lt_pow_right₀ hlt hi

/--
@isnad1 id=lt.3h7v.s13.c3a495caa3c5 from=translated src=- shape=5563bb69 vocab=e475ed24
-/
lemma ck_kernel_estimate (hA : A.LiesOverPrime ℓ) (f g g' : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt ℓ)] (AlgebraicClosure ℚ))) (hgg' : g * g' = 1)
    (hfg : ∀ h : H, A.valuation (f h - g h) < 1) (c : H) :
    A.valuation ((f * g') c - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (counit c)) < 1 := by
  have e1 : algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (counit c) = (g * g') c := by rw [hgg', algHom_convOne_apply]
  rw [e1, ck_sweedler ℓ H f g' (Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt ℓ) c),
    ck_sweedler ℓ H g g' (Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt ℓ) c), ← Finset.sum_sub_distrib]
  refine A.valuation.map_sum_lt one_ne_zero fun i _ => ?_
  rw [← sub_mul, map_mul]
  calc A.valuation (f _ - g _) * A.valuation (g' _)
      ≤ A.valuation (f _ - g _) * 1 := mul_le_mul' le_rfl (ck_val_apply_le_one ℓ H A hA g'.ofConv _)
    _ < 1 := by rw [mul_one]; exact hfg _

end CK

/--
@isnad1 id=eq.6h6v.s14.f638fe26417b from=translated src=- shape=2f37e4f5 vocab=12e571b3
-/
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (k : ℕ) (hord : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), f ^ ℓ ^ k = 1)
    (hker : ∀ φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (φ h) = φ h) → (∀ h : H, A.valuation (φ h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) → φ ^ ℓ ^ k = 1 → φ = 1)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hf : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (f h) = f h)) (hg : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (g h) = g h))
    (hfg : ∀ h : H, A.valuation (f h - g h) < 1) :
    f = g := by

  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ k = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero k (Fact.out : ℓ.Prime).ne_zero)
  set g' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) := g ^ m with hg'
  have hgg' : g * g' = 1 := by rw [hg', ← pow_succ', ← hm]; exact hord g
  have hg'g : g' * g = 1 := by rw [hg', ← pow_succ, ← hm]; exact hord g

  have hφ : f * g' = 1 :=
    hker (f * g')
      (ck_fixed_mul ℓ H _ f g' hf (ck_fixed_pow ℓ H _ g hg m))
      (ck_kernel_estimate ℓ H A hA f g g' hgg' hfg)
      (hord _)
  calc f = f * (g' * g) := by rw [hg'g, mul_one]
    _ = (f * g') * g := (mul_assoc _ _ _).symm
    _ = g := by rw [hφ, one_mul]
