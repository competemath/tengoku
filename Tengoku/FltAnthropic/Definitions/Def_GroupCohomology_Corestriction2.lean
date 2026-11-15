import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

section Transversal
variable {G : Type} [Group G] (H : Subgroup G)

structure Transversal where
  σ : G ⧸ H → G
  mk_σ : ∀ q, (σ q : G ⧸ H) = q
  σ_one : σ ((1 : G) : G ⧸ H) = 1

namespace Transversal
variable {H}

/--
@isnad1 id=nonempty.0h2v.s3.e3cfd1f07cd4 from=translated src=- shape=6fdbd89e vocab=c5d5f327
-/
lemma nonempty : Nonempty (Transversal H) := by
  classical
  refine ⟨⟨Function.update Quotient.out ((1 : G) : G ⧸ H) 1, fun q => ?_, Function.update_self _ _ _⟩⟩
  by_cases hq : q = ((1 : G) : G ⧸ H)
  · subst hq; rw [Function.update_self]
  · rw [Function.update_of_ne hq]; exact q.out_eq

variable (τ : Transversal H)

abbrev qinv (x : G) : G ⧸ H := ((x⁻¹ : G) : G ⧸ H)

/--
@isnad1 id=mem.0h4v.s5.42a2c653b651 from=translated src=- shape=50f62e31 vocab=0f38b968
-/
lemma lam_mem (x : G) : x * τ.σ (qinv (H := H) x) ∈ H := by
  have h : ((τ.σ (qinv (H := H) x) : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := τ.mk_σ _
  rw [QuotientGroup.eq] at h
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

def lam (x : G) : H := ⟨x * τ.σ (qinv (H := H) x), τ.lam_mem x⟩

/--
@isnad1 id=eq.0h4v.s6.28b5323be9cb from=translated src=- shape=dbab4b23 vocab=4a604ed4
-/
lemma coe_lam (x : G) : (τ.lam x : G) = x * τ.σ (qinv (H := H) x) := rfl

/--
@isnad1 id=eq.0h4v.s6.3aa5a6652dbe from=translated src=- shape=723329f1 vocab=0120137f
-/
lemma lam_mul_σ_inv (x : G) : (τ.lam x : G) * (τ.σ (qinv (H := H) x))⁻¹ = x := by rw [coe_lam, mul_inv_cancel_right]

/--
@isnad1 id=eq.2h6v.s6.1c6e4592b09b from=translated src=- shape=bd61f354 vocab=04beec67
-/
lemma qinv_eq_of_eq {y μ : G} (hμ : μ ∈ H) {q : G ⧸ H} (h : y = μ * (τ.σ q)⁻¹) : qinv (H := H) y = q := by
  rw [qinv, ← τ.mk_σ q, QuotientGroup.eq, inv_inv, h, mul_assoc, inv_mul_cancel, mul_one]; exact hμ

/--
@isnad1 id=eq.2h6v.s6.ee016a6a4955 from=translated src=- shape=a6ba5a0c vocab=3d95a45e
-/
lemma coe_lam_eq_of_eq {y μ : G} (hμ : μ ∈ H) {q : G ⧸ H} (h : y = μ * (τ.σ q)⁻¹) : (τ.lam y : G) = μ := by
  rw [coe_lam, τ.qinv_eq_of_eq hμ h, h, inv_mul_cancel_right]

/--
@isnad1 id=eq.1h4v.s5.93840e7ac94d from=translated src=- shape=4ccbd4e0 vocab=2f0a2543
-/
lemma coe_lam_of_mem {s : G} (hs : s ∈ H) : (τ.lam s : G) = s :=
  τ.coe_lam_eq_of_eq hs (q := ((1 : G) : G ⧸ H)) (by rw [τ.σ_one, inv_one, mul_one])

/--
@isnad1 id=eq.0h4v.s6.2c315f4b5d1e from=translated src=- shape=75ab9be7 vocab=f5576e95
-/
lemma coe_lam_σ_inv (q : G ⧸ H) : (τ.lam (τ.σ q)⁻¹ : G) = 1 := τ.coe_lam_eq_of_eq H.one_mem (by rw [one_mul])

/--
@isnad1 id=eq.0h5v.s7.55570187c6f9 from=translated src=- shape=50056c7d vocab=0120137f
-/
lemma coe_lam_mul (x g : G) : (τ.lam (x * g) : G) = τ.lam x * τ.lam ((τ.σ (qinv (H := H) x))⁻¹ * g) := by
  apply τ.coe_lam_eq_of_eq (H.mul_mem (τ.lam x).2 (τ.lam _).2) (q := qinv (H := H) ((τ.σ (qinv (H := H) x))⁻¹ * g))
  conv_lhs => rw [← τ.lam_mul_σ_inv x, mul_assoc, ← τ.lam_mul_σ_inv ((τ.σ (qinv (H := H) x))⁻¹ * g)]
  rw [mul_assoc]

/--
@isnad1 id=eq.0h5v.s7.4e91b11645b7 from=translated src=- shape=dcffbe4b vocab=12aa4ef3
-/
lemma lam_mul (x g : G) : τ.lam (x * g) = τ.lam x * τ.lam ((τ.σ (qinv (H := H) x))⁻¹ * g) := Subtype.ext (τ.coe_lam_mul x g)

/--
@isnad1 id=eq.0h5v.s7.8910c43fba10 from=translated src=- shape=4b2198f2 vocab=b0549a05
-/
lemma qinv_σ_inv_mul (q : G ⧸ H) (g : G) : qinv (H := H) ((τ.σ q)⁻¹ * g) = g⁻¹ • q := by
  rw [qinv, mul_inv_rev, inv_inv]
  conv_rhs => rw [← τ.mk_σ q]
  rfl

/--
@isnad1 id=eq.0h5v.s7.c8c7d633f845 from=translated src=- shape=1bbfecd0 vocab=ec8e940a
-/
lemma mul_σ (q : G ⧸ H) (g : G) : g * τ.σ (g⁻¹ • q) = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : G) := by
  have hσ : (τ.σ (qinv (H := H) ((τ.σ q)⁻¹ * g)))⁻¹ = (τ.σ (g⁻¹ • q))⁻¹ := by rw [qinv_σ_inv_mul]
  have h1 := τ.lam_mul_σ_inv ((τ.σ q)⁻¹ * g)
  rw [hσ] at h1
  calc g * τ.σ (g⁻¹ • q) = τ.σ q * ((τ.σ q)⁻¹ * g) * τ.σ (g⁻¹ • q) := by group
    _ = τ.σ q * ((τ.lam ((τ.σ q)⁻¹ * g) : G) * (τ.σ (g⁻¹ • q))⁻¹) * τ.σ (g⁻¹ • q) := by rw [h1]
    _ = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : G) := by group

/--
@isnad1 id=eq.0h4v.s6.2e7969c5b6c0 from=translated src=- shape=736d7cd7 vocab=b5a73360
-/
lemma lam_of_mem (s : H) : τ.lam (s : G) = s := Subtype.ext (τ.coe_lam_of_mem s.2)

end Transversal
end Transversal

section Cor
variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

@[reducible, local instance] noncomputable def fintypeQuot : Fintype (G ⧸ H) := Fintype.ofFinite _

noncomputable def cor₁ (u : H → A) : G → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g)))

noncomputable def cor₂ (u : H × H → A) : G × G → A := fun gg =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * gg.1), (τ.lam ((τ.σ q)⁻¹ * gg.1))⁻¹ * τ.lam ((τ.σ q)⁻¹ * gg.1 * gg.2)))

/--
@isnad1 id=eq.0h8v.s10.a43a9d0bfe02 from=translated src=- shape=a64faf5c vocab=e5ae4250
-/
lemma cor₂_apply (u : H × H → A) (g₁ g₂ : G) : cor₂ A τ u (g₁, g₂) =
    ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g₁), (τ.lam ((τ.σ q)⁻¹ * g₁))⁻¹ * τ.lam ((τ.σ q)⁻¹ * g₁ * g₂))) := rfl

/--
@isnad1 id=mem.1h6v.s12.416e27d1476e from=translated src=- shape=945b6bad vocab=ad18f93e
-/
theorem cor₂_mem_cocycles₂ {u : H × H → A} (hu : u ∈ cocycles₂ (Rep.res H.subtype A)) : cor₂ A τ u ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff] at hu ⊢
  intro g h j
  simp only [cor₂_apply]

  rw [map_sum]
  have hre : ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * h), (τ.lam ((τ.σ q)⁻¹ * h))⁻¹ * τ.lam ((τ.σ q)⁻¹ * h * j)))) =
      ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ (g⁻¹ • q)) (u (τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h),
        (τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h))⁻¹ * τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h * j)))) :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun q => rfl).symm
  rw [hre, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_

  set x : G := (τ.σ q)⁻¹ with hx
  set x' : G := (τ.σ (g⁻¹ • q))⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (H := H) (x * g)))⁻¹ = x' := by rw [hx, Transversal.qinv_σ_inv_mul, ← hx']
  have hab : τ.lam (x * g * h) = τ.lam (x * g) * τ.lam (x' * h) := by rw [τ.lam_mul (x * g) h, hσ]
  have habc : τ.lam (x * g * (h * j)) = τ.lam (x * g) * τ.lam (x' * h * j) := by rw [τ.lam_mul (x * g) (h * j), hσ, mul_assoc]
  have hbc : τ.lam (x' * h * j) = τ.lam (x' * h) * τ.lam ((τ.σ (Transversal.qinv (H := H) (x' * h)))⁻¹ * j) := τ.lam_mul (x' * h) j
  have hgσ : A.ρ g * A.ρ (τ.σ (g⁻¹ • q)) = A.ρ (τ.σ q) * A.ρ ((τ.lam (x * g) : H) : G) := by
    rw [← map_mul, ← map_mul, hx]; exact congrArg _ (τ.mul_σ q g)
  rw [show x * (g * h) = x * g * h from (mul_assoc _ _ _).symm, show x * g * h * j = x * g * (h * j) from mul_assoc _ _ _,
    hab, habc, hbc, ← Module.End.mul_apply, hgσ, Module.End.mul_apply]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← map_add]
  congr 1
  have hu' := hu (τ.lam (x * g)) (τ.lam (x' * h)) (τ.lam ((τ.σ (Transversal.qinv (H := H) (x' * h)))⁻¹ * j))

  exact hu'

/--
@isnad1 id=eq.0h7v.s9.eda11fe2b119 from=translated src=- shape=5f933fef vocab=346c7afe
-/
lemma cor₂_add (u v : H × H → A) : cor₂ A τ (u + v) = cor₂ A τ u + cor₂ A τ v := by
  funext gh; obtain ⟨g₁, g₂⟩ := gh
  simp only [cor₂_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h7v.s10.44ff72f7ca06 from=translated src=- shape=216a167b vocab=adecf603
-/
lemma cor₂_smul (c : k) (u : H × H → A) : cor₂ A τ (c • u) = c • cor₂ A τ u := by
  funext gh; obtain ⟨g₁, g₂⟩ := gh
  simp only [cor₂_apply, Pi.smul_apply, map_smul, Finset.smul_sum]

noncomputable def corCocycles₂ : cocycles₂ (Rep.res H.subtype A) →ₗ[k] cocycles₂ A where
  toFun u := ⟨cor₂ A τ u, cor₂_mem_cocycles₂ A τ u.2⟩
  map_add' u v := Subtype.ext (cor₂_add A τ u v)
  map_smul' c u := Subtype.ext (cor₂_smul A τ c u)

end Cor
end Cores
end groupCohomology
