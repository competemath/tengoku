import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Tengoku.Seed.GroupTheory.Index

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open groupCohomology

namespace HeckeCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ)

def IsTwist (φ : A →ₗ[k] A) : Prop := ∀ (s : S₂) (a : A), φ (A.ρ (c s : Γ) a) = A.ρ (s : Γ) (φ a)

/--
@isnad1 id=eq.1h10v.s12.4780b7837e56 from=translated src=- shape=0ebea4f8 vocab=f82c4477
-/
theorem transport_cocycle (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    ∀ s t : S₂, φ (f (c (s * t) : Γ)) = A.ρ (s : Γ) (φ (f (c t : Γ))) + φ (f (c s : Γ)) := by
  intro s t
  rw [map_mul, Subgroup.coe_mul, (mem_cocycles₁_iff f).1 f.2, map_add, hφ]

noncomputable def rep (q : Quotient (QuotientGroup.rightRel S₂)) : Γ := q.out

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S₂) := Quotient.mk _ g

noncomputable def slip (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) : S₂ :=
  ⟨rep S₂ q * γ * (rep S₂ (cls S₂ (rep S₂ q * γ)))⁻¹, by
    have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ (rep S₂ q * γ))) (rep S₂ q * γ) :=
      Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    simpa [mul_assoc] using h⟩

/--
@isnad1 id=eq.0h4v.s6.c5ffa0dfdbe5 from=translated src=- shape=325b95df vocab=127a24d7
-/
theorem cls_rep_mul (x δ : Γ) : cls S₂ (rep S₂ (cls S₂ x) * δ) = cls S₂ (x * δ) := by
  apply Quotient.sound'
  have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ x)) x := Quotient.exact' (by simp [rep, cls])
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

/--
@isnad1 id=eq.0h5v.s7.cf36464adc9d from=translated src=- shape=c9f84572 vocab=83f0ca37
-/
theorem slip_mul (q : Quotient (QuotientGroup.rightRel S₂)) (γ δ : Γ) :
    slip S₂ q (γ * δ) = slip S₂ q γ * slip S₂ (cls S₂ (rep S₂ q * γ)) δ := by
  apply Subtype.ext
  simp only [slip, Subgroup.coe_mul, cls_rep_mul, mul_assoc, inv_mul_cancel_left]

noncomputable def mulRight (γ : Γ) :
    Quotient (QuotientGroup.rightRel S₂) ≃ Quotient (QuotientGroup.rightRel S₂) where
  toFun := Quotient.map' (· * γ) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  invFun := Quotient.map' (· * γ⁻¹) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  left_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]
  right_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]

/--
@isnad1 id=eq.0h4v.s7.54edd1f7a082 from=translated src=- shape=bd434c52 vocab=cfcdb1dc
-/
theorem mulRight_apply (γ : Γ) (q : Quotient (QuotientGroup.rightRel S₂)) :
    mulRight S₂ γ q = cls S₂ (rep S₂ q * γ) := by
  induction q using Quotient.inductionOn' with
  | h x => simpa [mulRight, Quotient.map'_mk'', cls] using (cls_rep_mul S₂ x γ).symm

/--
@isnad1 id=surjecti.0h3v.s12.1cfbcc1db587 from=translated src=- shape=71e91c08 vocab=c1a272a9
-/
theorem H1π_surjective : Function.Surjective (H1π A) :=
  (ModuleCat.epi_iff_surjective (H1π A)).mp inferInstance

variable [S₂.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def corFun (g : S₂ → A) (γ : Γ) : A :=
  ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q γ))

/--
@isnad1 id=mem.1h5v.s10.4ef971c68e77 from=translated src=- shape=bdbb3a08 vocab=2986d6eb
-/
theorem corFun_mem_cocycles₁ (g : S₂ → A)
    (hg : ∀ s t : S₂, g (s * t) = A.ρ (s : Γ) (g t) + g s) : corFun S₂ A g ∈ cocycles₁ A := by
  rw [mem_cocycles₁_iff]
  intro γ δ
  simp only [corFun]
  have key : ∀ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q (γ * δ))) =
        A.ρ γ (A.ρ (rep S₂ (mulRight S₂ γ q))⁻¹ (g (slip S₂ (mulRight S₂ γ q) δ))) +
          A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q γ)) := fun q => by
    rw [slip_mul, hg, map_add, mulRight_apply]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [slip, mul_assoc, inv_mul_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, ← map_sum]
  congr 1
  exact congrArg _ (Fintype.sum_equiv (mulRight S₂ γ) _ _ fun _ => rfl)

/--
@isnad1 id=eq.0h5v.s12.69c779083859 from=translated src=- shape=66c831b8 vocab=dc7eb496
-/
theorem corFun_coboundary (a : A) :
    corFun S₂ A (fun s => A.ρ (s : Γ) a - a) =
      fun γ => A.ρ γ (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ a) -
        ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ a := by
  funext γ
  simp only [corFun, map_sub, Finset.sum_sub_distrib]
  have key : ∀ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (rep S₂ q)⁻¹ (A.ρ (slip S₂ q γ : Γ) a) = A.ρ γ (A.ρ (rep S₂ (mulRight S₂ γ q))⁻¹ a) := fun q => by
    rw [mulRight_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [slip, mul_assoc, inv_mul_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => key q, ← map_sum]
  congr 2
  exact Fintype.sum_equiv (mulRight S₂ γ) _ _ fun _ => rfl

noncomputable def heckeZ1 (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    cocycles₁ A :=
  ⟨corFun S₂ A (fun s => φ (f (c s : Γ))),
    corFun_mem_cocycles₁ S₂ A _ (transport_cocycle S₁ S₂ c A φ hφ f)⟩

/--
@isnad1 id=eq.1h9v.s11.79ca3322586a from=translated src=- shape=6ef0b1a0 vocab=73faf2ae
-/
theorem heckeZ1_apply (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) (γ : Γ) :
    heckeZ1 S₁ S₂ c A φ hφ f γ =
      ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ (f (c (slip S₂ q γ) : Γ))) := rfl

/--
@isnad1 id=eq.2h9v.s14.9883c421aa09 from=translated src=- shape=d0237ae4 vocab=d73b12d2
-/
theorem heckeZ1_descends (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f f' : cocycles₁ A)
    (h : H1π A f = H1π A f') : H1π A (heckeZ1 S₁ S₂ c A φ hφ f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f') := by
  rw [H1π_eq_iff] at h ⊢
  obtain ⟨a, ha⟩ := h
  have hff' : ∀ x : Γ, f x - f' x = A.ρ x a - a := fun x => by
    show (⇑f - ⇑f') x = _
    rw [← ha]
    rfl
  refine ⟨∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a), funext fun γ => ?_⟩
  calc (d₀₁ A).hom (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)) γ
      = A.ρ γ (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)) -
          ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a) := rfl
    _ = corFun S₂ A (fun s => A.ρ (s : Γ) (φ a) - φ a) γ := (congrFun (corFun_coboundary S₂ A (φ a)) γ).symm
    _ = (⇑(heckeZ1 S₁ S₂ c A φ hφ f) - ⇑(heckeZ1 S₁ S₂ c A φ hφ f')) γ := by
        simp only [Pi.sub_apply, heckeZ1_apply, corFun]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← map_sub, ← map_sub, hff', map_sub φ, hφ]

/--
@isnad1 id=eq.0h6v.s9.6eaa242388b2 from=translated src=- shape=115b2d91 vocab=e87b4a35
-/
theorem corFun_add (g g' : S₂ → A) : corFun S₂ A (g + g') = corFun S₂ A g + corFun S₂ A g' := by
  funext γ
  simp only [corFun, Pi.add_apply, map_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h6v.s10.8ad63bcb9816 from=translated src=- shape=2e9ebd41 vocab=5ba56d54
-/
theorem corFun_smul (r : k) (g : S₂ → A) : corFun S₂ A (r • g) = r • corFun S₂ A g := by
  funext γ
  simp only [corFun, Pi.smul_apply, map_smul, Finset.smul_sum]

noncomputable def heckeZ1Lin (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    cocycles₁ A →ₗ[k] cocycles₁ A where
  toFun := heckeZ1 S₁ S₂ c A φ hφ
  map_add' f f' := cocycles₁_ext fun γ => by
    have h1 : ∀ (x y : cocycles₁ A) (g : Γ), (x + y) g = x g + y g := fun _ _ _ => rfl
    rw [h1, heckeZ1_apply, heckeZ1_apply, heckeZ1_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1, map_add, map_add]
  map_smul' r f := cocycles₁_ext fun γ => by
    have h2 : ∀ (s : k) (x : cocycles₁ A) (g : Γ), (s • x) g = s • x g := fun _ _ _ => rfl
    rw [RingHom.id_apply, h2, heckeZ1_apply, heckeZ1_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h2, map_smul, map_smul]

/--
@isnad1 id=eq.1h8v.s12.4b4bcfc9f5f0 from=translated src=- shape=6279a3c5 vocab=9eb80e78
-/
@[simp] theorem heckeZ1Lin_apply (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    heckeZ1Lin S₁ S₂ c A φ hφ f = heckeZ1 S₁ S₂ c A φ hφ f := rfl

/--
@isnad1 id=le.1h7v.s14.c54a35189618 from=translated src=- shape=78bfc859 vocab=5a138bcb
-/
theorem ker_H1π_le (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    LinearMap.ker (H1π A).hom ≤
      LinearMap.ker ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h0 : H1π A x = H1π A 0 := by rw [map_zero]; exact hx
  have h := heckeZ1_descends S₁ S₂ c A φ hφ x 0 h0
  have hz : heckeZ1 S₁ S₂ c A φ hφ 0 = 0 := map_zero (heckeZ1Lin S₁ S₂ c A φ hφ)
  rw [hz, map_zero] at h
  exact h

noncomputable def heckeH1 (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) : H1 A →ₗ[k] H1 A :=
  (LinearMap.ker (H1π A).hom).liftQ ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ)
      (ker_H1π_le S₁ S₂ c A φ hφ) ∘ₗ
    ((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm.toLinearMap

/--
@isnad1 id=eq.1h8v.s13.03014897196f from=translated src=- shape=5c68aaf9 vocab=860d737f
-/
theorem heckeH1_H1π (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    heckeH1 S₁ S₂ c A φ hφ (H1π A f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f) := by
  show (LinearMap.ker (H1π A).hom).liftQ ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ)
      (ker_H1π_le S₁ S₂ c A φ hφ)
      (((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm ((H1π A).hom f)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

/--
@isnad1 id=eq.2h8v.s13.dc5aabea6755 from=translated src=- shape=58114448 vocab=860d737f
-/
theorem heckeH1_unique (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (T : H1 A → H1 A)
    (hT : ∀ f : cocycles₁ A, T (H1π A f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f)) :
    T = heckeH1 S₁ S₂ c A φ hφ := by
  funext x
  induction x using H1_induction_on with
  | h f => rw [hT, heckeH1_H1π]

noncomputable def norm0 (φ : A →ₗ[k] A) : A →ₗ[k] A where
  toFun a := ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)
  map_add' a b := by simp only [map_add, Finset.sum_add_distrib]
  map_smul' r a := by simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

/--
@isnad1 id=eq.0h6v.s11.ffd63393923d from=translated src=- shape=c7867ee0 vocab=e49bdfb5
-/
theorem norm0_apply (φ : A →ₗ[k] A) (a : A) :
    norm0 S₂ A φ a = ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a) := rfl

/--
@isnad1 id=mem.2h8v.s10.95c7843febc9 from=translated src=- shape=f24aa6bd vocab=7f70ff64
-/
theorem norm0_mem_invariants (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (a : A)
    (ha : a ∈ A.ρ.invariants) : norm0 S₂ A φ a ∈ A.ρ.invariants := by
  rw [Representation.mem_invariants] at ha ⊢
  intro γ
  have hzero : (fun s : S₂ => A.ρ (s : Γ) (φ a) - φ a) = 0 := funext fun s => by
    rw [← hφ, ha (c s : Γ), Pi.zero_apply, sub_self]
  have h := congrFun (corFun_coboundary S₂ A (φ a)) γ
  rw [hzero] at h
  simp only [corFun, Pi.zero_apply, map_zero, Finset.sum_const_zero] at h
  rw [norm0_apply]
  exact (sub_eq_zero.mp h.symm)

noncomputable def heckeInv (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    A.ρ.invariants →ₗ[k] A.ρ.invariants :=
  (norm0 S₂ A φ).restrict fun a ha => norm0_mem_invariants S₁ S₂ c A φ hφ a ha

/--
@isnad1 id=eq.1h8v.s12.a37a323ceed4 from=translated src=- shape=833e8d59 vocab=bd81cda8
-/
@[simp] theorem coe_heckeInv (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (z : A.ρ.invariants) :
    ((heckeInv S₁ S₂ c A φ hφ z : A.ρ.invariants) : A) = norm0 S₂ A φ z :=
  rfl

end HeckeCohomology
