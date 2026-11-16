import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_EigenformIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section TateModule

variable (p : ℕ) {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

def TateModule : Submodule HeckeAlg (ℕ → J) where
  carrier := {x | x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp only [Pi.add_apply, smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => smul_zero p⟩
  smul_mem' := by
    rintro s x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp only [Pi.smul_apply]
    rw [smul_comm, hx n]

namespace TateModule

variable {p} {J}

/--
@isnad1 id=iff.0h3v.s8.eed3e12d151c from=translated src=- shape=137eddf4 vocab=163dd5ba
-/
lemma mem_iff {x : ℕ → J} :
    x ∈ TateModule p J ↔ x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n :=
  Iff.rfl

/--
@isnad1 id=eq.1h4v.s8.9c97ed113572 from=translated src=- shape=8d12c131 vocab=4b08273d
-/
lemma pow_smul_apply {x : ℕ → J} (hx : x ∈ TateModule p J) (n : ℕ) :
    p ^ n • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih =>
    have := hx.2 n
    calc p ^ (n + 1) • x (n + 1) = p ^ n • p • x (n + 1) := by
          rw [pow_succ, mul_smul]
      _ = p ^ n • x n := by rw [this]
      _ = 0 := ih

lemma eq_zero_of_pow_smul_eq_zero {x : ℕ → J} (hx : x ∈ TateModule p J) {k : ℕ}
    (h : p ^ k • x = 0) : x = 0 := by

  have key : ∀ m n, x n = p ^ m • x (n + m) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
      intro n
      calc x n = p ^ m • x (n + m) := ih n
        _ = p ^ m • (p • x (n + m + 1)) := by rw [hx.2 (n + m)]
        _ = (p ^ m * p) • x (n + m + 1) := by rw [mul_smul]
        _ = p ^ (m + 1) • x (n + (m + 1)) := by rw [← pow_succ, ← Nat.add_assoc]
  funext n
  have hk : p ^ k • x (n + k) = 0 := by
    have := congrFun h (n + k)
    simpa using this
  simp only [Pi.zero_apply]
  rw [key k n, hk]

omit [SMulCommClass G HeckeAlg J] in

/--
@isnad1 id=mem.1h5v.s8.c54e1f00db4c from=translated src=- shape=a835d995 vocab=75e474b5
-/
lemma smul_mem (g : G) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    g • x ∈ TateModule p J := by
  refine ⟨by simp [Pi.smul_apply, hx.1], fun n => ?_⟩
  simp only [Pi.smul_apply]
  rw [smul_comm, hx.2 n]

end TateModule

end TateModule

section FreeOfRankTwo

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

def FreeOfRankTwo : Prop :=
  ∃ e₁ e₂ : ℕ → J, e₁ ∈ TateModule p J ∧ e₂ ∈ TateModule p J ∧
    (∀ t ∈ TateModule p J, ∃ (k : ℕ) (s₁ s₂ : HeckeAlg), p ^ k • t = s₁ • e₁ + s₂ • e₂) ∧
    (∀ s₁ s₂ : HeckeAlg, s₁ • e₁ + s₂ • e₂ = 0 →
      (∀ t ∈ TateModule p J, s₁ • t = 0) ∧ (∀ t ∈ TateModule p J, s₂ • t = 0))

def CardinalityAJ (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card {x : J // p ^ n • x = 0} = p ^ (2 * g * n)

end FreeOfRankTwo

section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [NeZero N] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

structure EichlerShimuraData : Prop where

  freeOfRankTwo : FreeOfRankTwo p J

  unramifiedOutside : UnramifiedOutside (K := K) (L := L) N p J

  frobeniusQuadratic : FrobeniusQuadratic (K := K) (L := L) N p J

  eigenformSupport : EigenformSupport p J (IsEigenformIdeal N)

end Bundle

section Torsion

variable (p : ℕ) {J : Type*} [AddCommGroup J]

def IsPPowTorsion (x : J) : Prop := ∃ n : ℕ, p ^ n • x = 0

variable {p}

/--
@isnad1 id=isppowto.0h2v.s4.b8eb7dde993b from=translated src=- shape=2cef0bb0 vocab=24975732
-/
lemma IsPPowTorsion.zero : IsPPowTorsion p (0 : J) := ⟨0, smul_zero _⟩

/--
@isnad1 id=isppowto.2h4v.s5.e87d78e13577 from=translated src=- shape=1f678c8d vocab=05e01e8b
-/
lemma IsPPowTorsion.add {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  refine ⟨m + n, ?_⟩
  have hx' : p ^ (m + n) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hm, smul_zero]
  have hy' : p ^ (m + n) • y = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
  rw [smul_add, hx', hy', add_zero]

/--
@isnad1 id=isppowto.1h3v.s5.72a608a78cd4 from=translated src=- shape=10f3a74b vocab=06bc6747
-/
lemma IsPPowTorsion.neg {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (-x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [smul_neg, hn, neg_zero]

/--
@isnad1 id=isppowto.2h4v.s5.7fa81b58d525 from=translated src=- shape=1f678c8d vocab=dc114bbe
-/
lemma IsPPowTorsion.sub {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

private lemma nsmul_galois_smul {G : Type*} [Monoid G] [DistribMulAction G J] (σ : G)
    (m : ℕ) (x : J) : m • (σ • x) = σ • (m • x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

/--
@isnad1 id=isppowto.1h5v.s6.84bdabf70e57 from=translated src=- shape=01318b0d vocab=7f8920d3
-/
lemma IsPPowTorsion.galois_smul {G : Type*} [Group G] [DistribMulAction G J] (σ : G)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (σ • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [nsmul_galois_smul σ (p ^ n) x, hn, smul_zero]

/--
@isnad1 id=isppowto.1h4v.s7.80f2eb4139ac from=translated src=- shape=79a41201 vocab=061c4aa7
-/
lemma IsPPowTorsion.hecke_smul [Module HeckeAlg J] (t : HeckeAlg)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (t • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) (t • x), ← mul_smul, mul_comm, mul_smul,
    Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) x, hn, smul_zero]

/--
@isnad1 id=isppowto.1h4v.s5.bd19c9f9b1f7 from=translated src=- shape=16513b1f vocab=061c4aa7
-/
lemma IsPPowTorsion.nsmul [Module HeckeAlg J] (m : ℕ)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (m • x) := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x]
  exact hx.hecke_smul _

end Torsion

section Realization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsLambdaAdicRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, IsPPowTorsion p x → IsPPowTorsion p y → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), IsPPowTorsion p x → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), IsPPowTorsion p x → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | IsPPowTorsion p x}) = ⊤

namespace IsLambdaAdicRealization

variable {p J k φ V π ρ}
variable (h : IsLambdaAdicRealization p J k φ V π ρ)
include h

/--
@isnad1 id=eq.2h10v.s9.2420e8293176 from=translated src=- shape=91773e28 vocab=138a6dde
-/
lemma map_neg (x : J) (hx : IsPPowTorsion p x) : π (-x) = -π x := by
  have h0 : π (x + -x) = π x + π (-x) := h.map_add x (-x) hx hx.neg
  rw [add_neg_cancel, h.map_zero] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

/--
@isnad1 id=eq.3h11v.s9.4dc57023632f from=translated src=- shape=d9d512b7 vocab=9d7e76dc
-/
lemma map_sub (x y : J) (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    π (x - y) = π x - π y := by
  rw [sub_eq_add_neg, h.map_add x (-y) hx hy.neg, h.map_neg y hy, ← sub_eq_add_neg]

/--
@isnad1 id=eq.2h11v.s9.d621b9259a4a from=translated src=- shape=9da416f0 vocab=f472fdb0
-/
lemma map_nsmul (m : ℕ) (x : J) (hx : IsPPowTorsion p x) : π (m • x) = (m : k) • π x := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x, h.map_hecke _ x hx, map_natCast]

/--
@isnad1 id=eq.2h10v.s9.2837cbc90919 from=translated src=- shape=7b18b8b6 vocab=c5d8cd63
-/
lemma linearMap_eq_zero (T : V →ₗ[k] V)
    (hT : ∀ x : J, IsPPowTorsion p x → T (π x) = 0) : T = 0 := by
  rw [← LinearMap.ker_eq_top, ← top_le_iff, ← h.spanning, Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  exact hT x hx

/--
@isnad1 id=eq.2h11v.s9.046da241ba10 from=translated src=- shape=83a69943 vocab=c5d8cd63
-/
lemma linearMap_ext {T₁ T₂ : V →ₗ[k] V}
    (hT : ∀ x : J, IsPPowTorsion p x → T₁ (π x) = T₂ (π x)) : T₁ = T₂ := by
  have key := h.linearMap_eq_zero (T₁ - T₂) fun x hx => by
    rw [LinearMap.sub_apply, hT x hx, sub_self]
  rwa [sub_eq_zero] at key

end IsLambdaAdicRealization

end Realization

section AttachmentData

variable {k : Type*} [Field k]

def attachmentTraceData (φ : HeckeAlg →+* k) : ℕ → k := fun ℓ =>
  if h : ℓ.Prime then φ (heckeGen ⟨ℓ, h⟩) else 0

def attachmentDetData (k : Type*) [Field k] : ℕ → k := fun ℓ => (ℓ : k)

/--
@isnad1 id=eq.1h3v.s6.4b2b11295bc9 from=translated src=- shape=26ac052b vocab=bee79197
-/
@[simp] lemma attachmentTraceData_apply_prime (φ : HeckeAlg →+* k) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    attachmentTraceData φ ℓ = φ (heckeGen ⟨ℓ, hℓ⟩) := dite_eq_left hℓ

end AttachmentData

end ModularCurve
