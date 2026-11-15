import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v

namespace LinearMap

variable {B : Type u} [CommRing B] {M : Type v} {N : Type v}
  [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] {r : ℕ}

def extPushoutRel (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) : Submodule B (N × (Fin r → B)) :=
  range (LinearMap.prod δ (-(ker p).subtype))

/--
@isnad1 id=iff.0h7v.s11.4852849f53ee from=translated src=- shape=bd11f97f vocab=15679d1a
-/
theorem mem_extPushoutRel_iff (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) (x : N × (Fin r → B)) :
    x ∈ extPushoutRel p δ ↔ ∃ s : ↥(ker p), δ s = x.1 ∧ -(s : Fin r → B) = x.2 := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (Prod.ext_iff.mp hs).1, (Prod.ext_iff.mp hs).2⟩
  · rintro ⟨s, h1, h2⟩
    exact ⟨s, Prod.ext h1 h2⟩

abbrev ExtPushout (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) : Type (max v u) :=
  (N × (Fin r → B)) ⧸ extPushoutRel p δ

namespace ExtPushout

variable (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N)

def mk : N × (Fin r → B) →ₗ[B] ExtPushout p δ := (extPushoutRel p δ).mkQ

/--
@isnad1 id=eq.0h7v.s10.934392a6ca22 from=translated src=- shape=d5311db8 vocab=2caede9d
-/
theorem mk_apply (x : N × (Fin r → B)) : mk p δ x = Submodule.Quotient.mk x := rfl

/--
@isnad1 id=surjecti.0h6v.s10.cf429a84ea1c from=translated src=- shape=fb484826 vocab=3871b62c
-/
theorem mk_surjective : Function.Surjective (mk p δ) := Submodule.Quotient.mk_surjective _

/--
@isnad1 id=iff.0h7v.s11.f2239c138508 from=translated src=- shape=5931d6e4 vocab=9e1e4da8
-/
theorem mk_eq_zero_iff (x : N × (Fin r → B)) :
    mk p δ x = 0 ↔ ∃ s : ↥(ker p), δ s = x.1 ∧ -(s : Fin r → B) = x.2 := by
  rw [mk_apply, Submodule.Quotient.mk_eq_zero (p := extPushoutRel p δ), mem_extPushoutRel_iff]

def inl : N →ₗ[B] ExtPushout p δ := mk p δ ∘ₗ LinearMap.inl B N (Fin r → B)

def inr : (Fin r → B) →ₗ[B] ExtPushout p δ := mk p δ ∘ₗ LinearMap.inr B N (Fin r → B)

/--
@isnad1 id=eq.0h7v.s10.6a62ad873dfc from=translated src=- shape=2b82ad73 vocab=6647612e
-/
theorem inl_apply (n : N) : inl p δ n = mk p δ (n, 0) := rfl

/--
@isnad1 id=eq.0h7v.s10.2728febb1508 from=translated src=- shape=e45f49da vocab=ce0ea406
-/
theorem inr_apply (v : Fin r → B) : inr p δ v = mk p δ (0, v) := rfl

/--
@isnad1 id=eq.0h8v.s11.15d2b54cfd11 from=translated src=- shape=80e6d060 vocab=be6e4283
-/
theorem mk_eq_inl_add_inr (n : N) (v : Fin r → B) : mk p δ (n, v) = inl p δ n + inr p δ v := by
  rw [inl_apply, inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/--
@isnad1 id=eq.0h7v.s11.c70586b99bcc from=translated src=- shape=87d7ef7c vocab=872ff709
-/
theorem inr_coe (s : ↥(ker p)) : inr p δ (s : Fin r → B) = inl p δ (δ s) := by
  rw [inr_apply, inl_apply, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  exact ⟨-s, by simp, by simp⟩

def proj : ExtPushout p δ →ₗ[B] M :=
  (extPushoutRel p δ).liftQ (p ∘ₗ LinearMap.snd B N (Fin r → B)) (by
    rintro x ⟨s, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    show p (-(s : Fin r → B)) = 0
    rw [map_neg, LinearMap.mem_ker.mp s.2, neg_zero])

/--
@isnad1 id=eq.0h8v.s10.48e2cb8d1e6d from=translated src=- shape=3a50deeb vocab=073b0208
-/
theorem proj_mk (n : N) (v : Fin r → B) : proj p δ (mk p δ (n, v)) = p v := rfl

/--
@isnad1 id=eq.0h7v.s10.a4cb5b31ed6f from=translated src=- shape=877fe37d vocab=7ebbfa29
-/
theorem proj_inl (n : N) : proj p δ (inl p δ n) = 0 := by
  rw [inl_apply, proj_mk, map_zero]

/--
@isnad1 id=eq.0h7v.s10.2b2d137cd0b1 from=translated src=- shape=f8aeb7c9 vocab=19d791f6
-/
theorem proj_inr (v : Fin r → B) : proj p δ (inr p δ v) = p v := rfl

/--
@isnad1 id=eq.0h6v.s10.51dd163481c8 from=translated src=- shape=598a4098 vocab=6d1e1784
-/
theorem proj_comp_inl : proj p δ ∘ₗ inl p δ = 0 := LinearMap.ext (proj_inl p δ)

/--
@isnad1 id=eq.0h6v.s10.8263fe7812ff from=translated src=- shape=853f1e17 vocab=7409d518
-/
theorem proj_comp_inr : proj p δ ∘ₗ inr p δ = p := LinearMap.ext (proj_inr p δ)

/--
@isnad1 id=injectiv.0h6v.s10.2f4232f4208c from=translated src=- shape=2f988950 vocab=341e9f69
-/
theorem inl_injective : Function.Injective (inl p δ) := by
  intro n n' h
  have h0 : inl p δ (n - n') = 0 := by rw [map_sub, h, sub_self]
  rw [inl_apply, mk_eq_zero_iff] at h0
  obtain ⟨s, h1, h2⟩ := h0
  have hs : s = 0 := by
    apply Subtype.ext
    have : -(s : Fin r → B) = 0 := h2
    simpa using this
  have h1' : δ s = n - n' := h1
  have h3 : n - n' = 0 := by rw [← h1', hs, map_zero]
  exact sub_eq_zero.mp h3

/--
@isnad1 id=surjecti.1h6v.s10.1f31d90fede2 from=translated src=- shape=f76d1330 vocab=58e4eddb
-/
theorem proj_surjective (hp : Function.Surjective p) : Function.Surjective (proj p δ) := by
  intro m
  obtain ⟨v, rfl⟩ := hp m
  exact ⟨inr p δ v, proj_inr p δ v⟩

/--
@isnad1 id=eq.0h6v.s10.8e149dfa0368 from=translated src=- shape=9ff91eff vocab=3172ad1b
-/
theorem range_inl_eq_ker_proj : range (inl p δ) = ker (proj p δ) := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact proj_inl p δ n
  · intro x hx
    obtain ⟨⟨n, v⟩, rfl⟩ := mk_surjective p δ x
    rw [LinearMap.mem_ker, proj_mk] at hx
    refine ⟨n + δ ⟨v, hx⟩, ?_⟩
    rw [map_add, ← inr_coe, mk_eq_inl_add_inr]

section lift

variable {Q : Type*} [AddCommGroup Q] [Module B Q]

def lift (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) : ExtPushout p δ →ₗ[B] Q :=
  (extPushoutRel p δ).liftQ (f.coprod g) (by
    rintro x ⟨s, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.coprod_apply]
    show f (δ s) + g (-(s : Fin r → B)) = 0
    rw [map_neg, h, add_neg_cancel])

/--
@isnad1 id=eq.1h11v.s12.73832e51d5a9 from=translated src=- shape=5d1764de vocab=8275e8c5
-/
theorem lift_mk (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) (v : Fin r → B) :
    lift p δ f g h (mk p δ (n, v)) = f n + g v := rfl

/--
@isnad1 id=eq.1h10v.s12.7f6cce210320 from=translated src=- shape=8a5cbeb9 vocab=fd093f4e
-/
theorem lift_inl (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) :
    lift p δ f g h (inl p δ n) = f n := by
  rw [inl_apply, lift_mk, map_zero, add_zero]

/--
@isnad1 id=eq.1h10v.s12.2ac4d6368852 from=translated src=- shape=4fccb952 vocab=32f0d943
-/
theorem lift_inr (f : N →ₗ[B] Q) (g : (Fin r → B) →ₗ[B] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (v : Fin r → B) :
    lift p δ f g h (inr p δ v) = g v := by
  rw [inr_apply, lift_mk, map_zero, zero_add]

/--
@isnad1 id=eq.2h9v.s12.eb89fa475618 from=translated src=- shape=efd83e2d vocab=4b8da071
-/
theorem hom_ext {φ ψ : ExtPushout p δ →ₗ[B] Q} (h₁ : ∀ n : N, φ (inl p δ n) = ψ (inl p δ n))
    (h₂ : ∀ v : Fin r → B, φ (inr p δ v) = ψ (inr p δ v)) : φ = ψ := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨n, v⟩, rfl⟩ := mk_surjective p δ x
  rw [mk_eq_inl_add_inr, map_add, map_add, h₁, h₂]

end lift

end ExtPushout

end LinearMap
