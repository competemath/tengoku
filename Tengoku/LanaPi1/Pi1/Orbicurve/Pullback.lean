module

public import Tengoku.LanaPi1.Pi1.Orbicurve.SubfieldGalois
public import Tengoku.LanaPi1.Pi1.Orbicurve.TameInertia
public import Tengoku.LanaPi1.Pi1.Orbicurve.Morphisms
public import Tengoku.LanaPi1.Pi1.Orbicurve.Embed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pullbacks of finite étale covers of subfield orbicurves

Let `Ω` be algebraically closed and normal over `K₀ = k(t)` (characteristic `0`). For the
finite étale cover `ofSubfield A m_A → ofSubfield B m_B` induced by `B ⊆ A`, every finite étale
`Z → ofSubfield B m_B` is dominated by a finite étale cover of `ofSubfield A m_A`
(`pullback_ofSubfield`): `Z` is `ofSubfield L_Z m_Z` for some `L_Z ⊇ B` (`Pi1.Orbicurve.Embed`),
and the compositum `L_Z ⊔ A` with multiplicities `m(w) = m_B(v) / e(w | v)` is finite étale over
both. The key input is that `e(w | v)` divides `m_B(v)`, since the inertia groups are cyclic
(tame ramification, `Pi1.Orbicurve.TameInertia`) and the ramification indices of `L_Z` and `A`
over `B` divide `m_B(v)` (`ramificationIdx_sup_dvd`). Consequently, orbicurves related by such a
cover have the same `k`-cores (`isCoreOf_ofSubfield_iff`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

section Group

/-- In a finite cyclic group, if two subgroups have index dividing `m`, so does their
intersection.
@isnad1 id=dvd.2h4v.s5.c1c6b35046c8 from=translated src=- shape=f1df0f96 vocab=938538de
-/
lemma index_inf_dvd_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} {m : ℕ} (h₁ : H₁.index ∣ m) (h₂ : H₂.index ∣ m) :
    (H₁ ⊓ H₂).index ∣ m := by
  letI := IsCyclic.commGroup (α := C)
  have hmem : ∀ g : C, g ^ m ∈ H₁ ⊓ H₂ := by
    intro g
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    haveI : H₁.Normal := Subgroup.normal_of_isMulCommutative H₁
    haveI : H₂.Normal := Subgroup.normal_of_isMulCommutative H₂
    refine ⟨?_, ?_⟩
    · rw [ha, pow_mul]; exact H₁.pow_mem (H₁.pow_index_mem g) a
    · rw [hb, pow_mul]; exact H₂.pow_mem (H₂.pow_index_mem g) b
  haveI : (H₁ ⊓ H₂).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : IsCyclic (C ⧸ (H₁ ⊓ H₂)) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rw [Subgroup.index, ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  rintro ⟨g⟩
  change ((g ^ m : C) : C ⧸ (H₁ ⊓ H₂)) = 1
  rw [QuotientGroup.eq_one_iff]
  exact hmem g

/-- A version of `index_inf_dvd_of_isCyclic` for subgroups of a cyclic subgroup, in terms of
cardinalities.
@isnad1 id=dvd.7h8v.s8.8064d96200d8 from=translated src=- shape=ad059830 vocab=bdf01fc2
-/
lemma dvd_of_card_inf {G : Type*} [Group G] [Finite G] {C H₁ H₂ : Subgroup G} [IsCyclic C]
    (h₁ : H₁ ≤ C) (h₂ : H₂ ≤ C) {d₁ d₂ e m : ℕ}
    (hd₁ : d₁ * Nat.card H₁ = Nat.card C) (hd₂ : d₂ * Nat.card H₂ = Nat.card C)
    (he : e * Nat.card (H₁ ⊓ H₂ : Subgroup G) = Nat.card C) (hm₁ : d₁ ∣ m) (hm₂ : d₂ ∣ m) :
    e ∣ m := by
  have key : ∀ {H : Subgroup G} {d : ℕ}, H ≤ C → d * Nat.card H = Nat.card C →
      (H.subgroupOf C).index = d := by
    intro H d hH hd
    have h1 := (H.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h1
    have hpos : 0 < Nat.card H := Nat.card_pos
    rw [← hd, mul_comm d] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have k₁ := key h₁ hd₁
  have k₂ := key h₂ hd₂
  have k := key (inf_le_left.trans h₁) he
  have hinf : (H₁ ⊓ H₂).subgroupOf C = H₁.subgroupOf C ⊓ H₂.subgroupOf C := by
    ext x; simp [Subgroup.mem_subgroupOf]
  rw [hinf] at k
  rw [← k]
  exact index_inf_dvd_of_isCyclic (k₁ ▸ hm₁) (k₂ ▸ hm₂)

end Group

/-- A ring isomorphism is unramified.
@isnad1 id=eq.0h4v.s6.b66c278f8644 from=translated src=- shape=530daa0f vocab=ca44ae1f
-/
lemma ramificationIdx_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [IsDedekindDomain B] (ψ : A ≃+* B) (w : Ideal B) [w.IsPrime] :
    (letI := ψ.toRingHom.toAlgebra; w.ramificationIdx A) = 1 := by
  have h := ramificationIdx_comp ψ.toRingHom ψ.symm.toRingHom ψ.symm.injective
    (w.comap ψ.toRingHom)
  have hw : (w.comap ψ.toRingHom).comap ψ.symm.toRingHom = w := by
    ext x
    simp only [Ideal.mem_comap]
    change ψ (ψ.symm x) ∈ w ↔ x ∈ w
    rw [RingEquiv.apply_symm_apply]
  have hid : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id A := by
    ext x; simp
  rw [hw, hid] at h
  haveI : (w.comap ψ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (letI := (RingHom.id A).toAlgebra; (w.comap ψ.toRingHom).ramificationIdx A) = 1 := by
    have halg : (RingHom.id A).toAlgebra = Algebra.id A := Algebra.algebra_ext _ _ (fun _ => rfl)
    rw [halg]
    exact Ideal.ramificationIdx_eq_one _ A
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Galois

variable {N : IntermediateField (K₀ k t) Ω}

/-- `Gal(N / L ⊔ L') = Gal(N / L) ∩ Gal(N / L')`.
@isnad1 id=eq.2h6v.s13.c6e51f3635aa from=translated src=- shape=e6c0aa1a vocab=cecb7622
-/
lemma fixSub_sup {L L' : IntermediateField (K₀ k t) Ω} (hL : L ≤ N) (hL' : L' ≤ N) :
    fixSub t N (L ⊔ L') = fixSub t N L ⊓ fixSub t N L' := by
  refine le_antisymm (le_inf (fixSub_antitone t le_sup_left) (fixSub_antitone t le_sup_right)) ?_
  rintro σ ⟨hσ, hσ'⟩
  let S : IntermediateField (K₀ k t) Ω :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).map N.val
  have hS : ∀ {F : IntermediateField (K₀ k t) Ω}, F ≤ N → (∀ x : N, (x : Ω) ∈ F → σ x = x) →
      F ≤ S := by
    intro F hFN hF y hy
    refine ⟨⟨y, hFN hy⟩, ?_, rfl⟩
    rintro ⟨τ, n, rfl⟩
    change (σ ^ n) _ = _
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hF _ hy]; exact ih
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : σ⁻¹ ⟨y, hFN hy⟩ = ⟨y, hFN hy⟩ := by
        conv_lhs => rw [← hF ⟨y, hFN hy⟩ hy]
        exact σ.symm_apply_apply _
      rw [this]; exact ih
  intro x hx
  obtain ⟨z, hz, hzx⟩ := sup_le (hS hL hσ) (hS hL' hσ') hx
  have : z = x := Subtype.ext hzx
  subst this
  exact (IntermediateField.mem_fixedField_iff _ _).mp hz σ (Subgroup.mem_zpowers σ)

variable (N) [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]

omit [IsGalois (K₀ k t) N] in
/-- `Gal(N / K₀)` acts faithfully on the coordinate ring of `N`.
@isnad1 id=faithful.0h4v.s17.40544ddb28cd from=translated src=- shape=e248befc vocab=50e80757
-/
lemma faithfulSMul_coordRing : FaithfulSMul (N ≃ₐ[K₀ k t] N) (coordRing k t N) := by
  refine ⟨fun {σ τ} h => ?_⟩
  have hc : ∀ (ρ : N ≃ₐ[K₀ k t] N) (b : coordRing k t N), ((ρ • b : coordRing k t N) : N) = ρ b :=
    fun _ _ => rfl
  have hb : ∀ b : coordRing k t N, σ (b : N) = τ b := fun b => by
    rw [← hc, ← hc, h b]
  haveI := isFractionRing_coordRing t N
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := coordRing k t N) x
  rw [map_div₀, map_div₀]
  exact congrArg Subtype.val (congrArg₂ (· / ·) (hb a) (hb b))

variable [CharZero k]

/-- **Tame inertia is cyclic**: the inertia groups of `Gal(N / K₀)` at the maximal ideals of the
coordinate ring of `N` are cyclic (characteristic `0`).
@isnad1 id=iscyclic.2h5v.s17.2344fcfc7b7f from=translated src=- shape=586f5891 vocab=7db11a0f
-/
theorem isCyclic_inertia_coordRing (ht : Transcendental k t) (u : Ideal (coordRing k t N))
    [u.IsMaximal] (hu0 : u ≠ ⊥) : IsCyclic (u.inertia (N ≃ₐ[K₀ k t] N)) := by
  haveI := isDedekindDomain_ring t ht N
  haveI := faithfulSMul_coordRing t N
  haveI : CharZero (IsLocalRing.ResidueField (Localization.AtPrime u)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime u))).injective
  exact TameInertia.isCyclic_inertia u hu0

variable {N}

end Galois

section Pullback

variable [CharZero k] [Normal (K₀ k t) Ω] (ht : Transcendental k t)

variable [IsAlgClosed Ω]

end Pullback

end AffOrbicurve
