import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi

set_option autoImplicit false

open NumberField

namespace R4H2F

open Matrix

section Defs

def SplitsIdem (R : Type*) [CommRing R] : Prop :=
  ∀ (N m n : ℕ), 0 < n → ∀ (ε : Matrix (Fin N) (Fin N) R)
    (A' : Matrix (Fin (m * n)) (Fin N × Fin n) R) (B' : Matrix (Fin N × Fin n) (Fin (m * n)) R),
    ε * ε = ε → A' * B' = 1 → B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε) →
    ∃ (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R), A * B = 1 ∧ B * A = ε

end Defs

section Local

variable {R : Type*} [CommRing R]

/--
@isnad1 id=ex.1h3v.s8.2c0b2f16372d from=translated src=- shape=d3f65e4d vocab=1fee9053
-/
theorem exists_splitting_of_isLocalRing [IsLocalRing R] {N : ℕ}
    (ε : Matrix (Fin N) (Fin N) R) (hε : ε * ε = ε) :
    ∃ (r : ℕ) (A : Matrix (Fin r) (Fin N) R) (B : Matrix (Fin N) (Fin r) R),
      A * B = 1 ∧ B * A = ε := by
  classical
  set e : (Fin N → R) →ₗ[R] (Fin N → R) := Matrix.toLin' ε with he_def
  have he : e ∘ₗ e = e := by rw [he_def, ← Matrix.toLin'_mul, hε]
  set M : Submodule R (Fin N → R) := LinearMap.range e with hM_def
  let p : (Fin N → R) →ₗ[R] M := e.rangeRestrict
  let s : M →ₗ[R] (Fin N → R) := M.subtype
  have hsp : s ∘ₗ p = e := by
    ext x i
    simp [s, p]
  have hps : p ∘ₗ s = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    apply Subtype.ext
    change e (e y) = e y
    exact congrArg (fun f : (Fin N → R) →ₗ[R] (Fin N → R) => f y) he
  haveI : Module.Finite R M := inferInstance
  haveI : Module.Projective R M := Module.Projective.of_split s p hps
  haveI : Module.Free R M := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank R M
  let b : Module.Basis (Fin r) R M := Module.finBasis R M
  refine ⟨r, LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ p),
    LinearMap.toMatrix' (s ∘ₗ b.equivFun.symm.toLinearMap), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ s p, hps, LinearMap.id_comp]
    ext x i
    simp
  · rw [← LinearMap.toMatrix'_comp]
    have hε' : LinearMap.toMatrix' e = ε := by rw [he_def, LinearMap.toMatrix'_toLin']
    rw [← hε']
    congr 1
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc p _ _]
    have : b.equivFun.symm.toLinearMap ∘ₗ b.equivFun.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [this, LinearMap.id_comp, hsp]

/--
@isnad1 id=eq.2h6v.s7.6973f947eaf0 from=translated src=- shape=86d0666a vocab=ffbb808f
-/
theorem trace_eq_of_splitting {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    {ε : Matrix ι ι R} {A : Matrix (Fin r) ι R} {B : Matrix ι (Fin r) R}
    (hAB : A * B = 1) (hBA : B * A = ε) : ε.trace = r := by
  rw [← hBA, Matrix.trace_mul_comm, hAB, Matrix.trace_one, Fintype.card_fin]

/--
@isnad1 id=splitsid.0h1v.s4.a994c84ee843 from=translated src=- shape=affebb5f vocab=670d0efc
-/
theorem splitsIdem_of_isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] [CharZero R] :
    SplitsIdem R := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  classical
  obtain ⟨r, A, B, hAB, hBA⟩ := exists_splitting_of_isLocalRing ε hε
  have h1 : ε.trace = r := trace_eq_of_splitting hAB hBA
  have h2 : (Matrix.blockDiagonal (fun _ : Fin n => ε)).trace = (m * n : ℕ) := by
    rw [← hB'A', Matrix.trace_mul_comm, hA'B', Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.trace_blockDiagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h1,
    nsmul_eq_mul] at h2
  have h3 : n * r = m * n := by exact_mod_cast h2
  have hr : r = m := by
    rw [mul_comm] at h3
    exact Nat.eq_of_mul_eq_mul_right hn h3
  subst hr
  exact ⟨A, B, hAB, hBA⟩

end Local

section Transfer

variable {R S : Type*} [CommRing R] [CommRing S]

/--
@isnad1 id=and.3h9v.s10.0cf09227ac21 from=translated src=- shape=c98f3e5d vocab=7c43e84b
-/
theorem hyps_map (φ : R →+* S) {N m n : ℕ} {ε : Matrix (Fin N) (Fin N) R}
    {A' : Matrix (Fin (m * n)) (Fin N × Fin n) R} {B' : Matrix (Fin N × Fin n) (Fin (m * n)) R}
    (hε : ε * ε = ε) (hA'B' : A' * B' = 1)
    (hB'A' : B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε)) :
    ε.map φ * ε.map φ = ε.map φ ∧ A'.map φ * B'.map φ = 1 ∧
      B'.map φ * A'.map φ = Matrix.blockDiagonal (fun _ : Fin n => ε.map φ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hε]
  · rw [← Matrix.map_mul, hA'B', Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [← Matrix.map_mul, hB'A', Matrix.blockDiagonal_map _ _ (map_zero φ)]

end Transfer

section Pi

/--
@isnad1 id=eq.1h6v.s8.445f75a872db from=translated src=- shape=4defc84f vocab=f16c73d6
-/
theorem matrix_eq_of_map_eval_eq {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    {α β : Type*} {M M' : Matrix α β (∀ i, R i)}
    (h : ∀ i, M.map (Pi.evalRingHom R i) = M'.map (Pi.evalRingHom R i)) : M = M' :=
  Matrix.ext fun a b => funext fun i => congrFun (congrFun (h i) a) b

/--
@isnad1 id=splitsid.1h2v.s5.8c9522b64985 from=translated src=- shape=277a5259 vocab=146b5794
-/
theorem splitsIdem_pi {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (h : ∀ i, SplitsIdem (R i)) : SplitsIdem (∀ i, R i) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  have H : ∀ i, ∃ (A : Matrix (Fin m) (Fin N) (R i)) (B : Matrix (Fin N) (Fin m) (R i)),
      A * B = 1 ∧ B * A = ε.map (Pi.evalRingHom R i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hyps_map (Pi.evalRingHom R i) hε hA'B' hB'A'
    exact h i N m n hn _ _ _ h1 h2 h3
  choose A B hAB hBA using H
  have hA : ∀ i, (Matrix.of fun a b i => A i a b).map (Pi.evalRingHom R i) = A i :=
    fun i => by ext a b; rfl
  have hB : ∀ i, (Matrix.of fun a b i => B i a b).map (Pi.evalRingHom R i) = B i :=
    fun i => by ext a b; rfl
  refine ⟨Matrix.of fun a b i => A i a b, Matrix.of fun a b i => B i a b, ?_, ?_⟩
  · refine matrix_eq_of_map_eval_eq fun i => ?_
    rw [Matrix.map_mul, hA, hB, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_eval_eq fun i => ?_
    rw [Matrix.map_mul, hA, hB, hBA]

/--
@isnad1 id=eq.2h6v.s8.87fe5eebc653 from=translated src=- shape=7e75764a vocab=61ffd54a
-/
theorem matrix_eq_of_map_fst_snd_eq {R S : Type*} [CommRing R] [CommRing S]
    {α β : Type*} {M M' : Matrix α β (R × S)}
    (h₁ : M.map (RingHom.fst R S) = M'.map (RingHom.fst R S))
    (h₂ : M.map (RingHom.snd R S) = M'.map (RingHom.snd R S)) : M = M' :=
  Matrix.ext fun a b => Prod.ext (congrFun (congrFun h₁ a) b) (congrFun (congrFun h₂ a) b)

/--
@isnad1 id=splitsid.2h2v.s4.11f8a67e9cdf from=translated src=- shape=ab93cd92 vocab=03e4b8f5
-/
theorem splitsIdem_prod (R S : Type*) [CommRing R] [CommRing S]
    (hR : SplitsIdem R) (hS : SplitsIdem S) : SplitsIdem (R × S) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  obtain ⟨h1, h2, h3⟩ := hyps_map (RingHom.fst R S) hε hA'B' hB'A'
  obtain ⟨A₁, B₁, hAB₁, hBA₁⟩ := hR N m n hn _ _ _ h1 h2 h3
  obtain ⟨k1, k2, k3⟩ := hyps_map (RingHom.snd R S) hε hA'B' hB'A'
  obtain ⟨A₂, B₂, hAB₂, hBA₂⟩ := hS N m n hn _ _ _ k1 k2 k3
  have hA1 : (Matrix.of fun a b => (A₁ a b, A₂ a b)).map (RingHom.fst R S) = A₁ := by
    ext a b; rfl
  have hA2 : (Matrix.of fun a b => (A₁ a b, A₂ a b)).map (RingHom.snd R S) = A₂ := by
    ext a b; rfl
  have hB1 : (Matrix.of fun a b => (B₁ a b, B₂ a b)).map (RingHom.fst R S) = B₁ := by
    ext a b; rfl
  have hB2 : (Matrix.of fun a b => (B₁ a b, B₂ a b)).map (RingHom.snd R S) = B₂ := by
    ext a b; rfl
  refine ⟨Matrix.of fun a b => (A₁ a b, A₂ a b), Matrix.of fun a b => (B₁ a b, B₂ a b), ?_, ?_⟩
  · refine matrix_eq_of_map_fst_snd_eq ?_ ?_
    · rw [Matrix.map_mul, hA1, hB1, hAB₁, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hA2, hB2, hAB₂, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_fst_snd_eq ?_ ?_
    · rw [Matrix.map_mul, hA1, hB1, hBA₁]
    · rw [Matrix.map_mul, hA2, hB2, hBA₂]

end Pi

section Restricted

open scoped RestrictedProduct
open Filter

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
variable {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : ∀ i, S i}

/--
@isnad1 id=ex.1h8v.s8.fdbdadc91c11 from=translated src=- shape=31707ac3 vocab=dbb369f7
-/
theorem exists_map_subtype_eq {α β : Type*} (i : ι) (M : Matrix α β (R i))
    (hM : ∀ a b, M a b ∈ B i) :
    ∃ M₀ : Matrix α β (B i), M₀.map (SubringClass.subtype (B i)) = M :=
  ⟨Matrix.of fun a b => ⟨M a b, hM a b⟩, by ext a b; rfl⟩

/--
@isnad1 id=eq.1h8v.s9.44f0f180c238 from=translated src=- shape=d9d7e912 vocab=6bfcb189
-/
theorem matrix_eq_of_map_evalRingHom_eq {α β : Type*} {M M' : Matrix α β (Πʳ i, [R i, B i])}
    (h : ∀ i, M.map (RestrictedProduct.evalRingHom R i) =
      M'.map (RestrictedProduct.evalRingHom R i)) : M = M' :=
  Matrix.ext fun a b => RestrictedProduct.ext _ _ fun i => congrFun (congrFun (h i) a) b

/--
@isnad1 id=splitsid.2h4v.s7.0cb4aaa827c1 from=translated src=- shape=5f9e36f5 vocab=7e0018a3
-/
theorem splitsIdem_restrictedProduct
    (hR : ∀ i, SplitsIdem (R i)) (hB : ∀ i, SplitsIdem (B i)) :
    SplitsIdem (Πʳ i, [R i, B i]) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  classical

  let good : ι → Prop := fun i =>
    (∀ a b, ε a b i ∈ B i) ∧ (∀ a b, A' a b i ∈ B i) ∧ (∀ a b, B' a b i ∈ B i)
  have hgood : ∀ᶠ i in cofinite, good i := by
    refine (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (ε a b).2).and
      ((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (A' a b).2).and
        (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (B' a b).2))
  let φ : ∀ i, (Πʳ i, [R i, B i]) →+* R i := fun i => RestrictedProduct.evalRingHom R i
  have H : ∀ i, ∃ (A : Matrix (Fin m) (Fin N) (R i)) (Bm : Matrix (Fin N) (Fin m) (R i)),
      A * Bm = 1 ∧ Bm * A = ε.map (φ i) ∧
        (good i → (∀ a b, A a b ∈ B i) ∧ (∀ a b, Bm a b ∈ B i)) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hyps_map (φ i) hε hA'B' hB'A'
    by_cases hg : good i
    · obtain ⟨hgε, hgA, hgB⟩ := hg
      obtain ⟨ε₀, hε₀⟩ := exists_map_subtype_eq (B := B) i (ε.map (φ i)) (fun a b => hgε a b)
      obtain ⟨A₀, hA₀⟩ := exists_map_subtype_eq (B := B) i (A'.map (φ i)) (fun a b => hgA a b)
      obtain ⟨B₀, hB₀⟩ := exists_map_subtype_eq (B := B) i (B'.map (φ i)) (fun a b => hgB a b)
      have hinj : Function.Injective
          (fun M : Matrix (Fin N) (Fin N) (B i) => M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have hinj₁ : Function.Injective
          (fun M : Matrix (Fin (m * n)) (Fin (m * n)) (B i) =>
            M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have hinj₂ : Function.Injective
          (fun M : Matrix (Fin N × Fin n) (Fin N × Fin n) (B i) =>
            M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have e1 : ε₀ * ε₀ = ε₀ := hinj (by simp only [Matrix.map_mul, hε₀, h1])
      have e2 : A₀ * B₀ = 1 := hinj₁ (by
        simp only [Matrix.map_mul, hA₀, hB₀, h2]
        rw [Matrix.map_one _ (map_zero _) (map_one _)])
      have e3 : B₀ * A₀ = Matrix.blockDiagonal (fun _ : Fin n => ε₀) := hinj₂ (by
        simp only [Matrix.map_mul, hA₀, hB₀, h3]
        rw [Matrix.blockDiagonal_map _ _ (map_zero _), hε₀])
      obtain ⟨A, Bm, hAB, hBA⟩ := hB i N m n hn ε₀ A₀ B₀ e1 e2 e3
      refine ⟨A.map (SubringClass.subtype (B i)), Bm.map (SubringClass.subtype (B i)), ?_, ?_,
        fun _ => ⟨fun a b => (A a b).2, fun a b => (Bm a b).2⟩⟩
      · rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
      · rw [← Matrix.map_mul, hBA, hε₀]
    · obtain ⟨A, Bm, hAB, hBA⟩ := hR i N m n hn _ _ _ h1 h2 h3
      exact ⟨A, Bm, hAB, hBA, fun hg' => absurd hg' hg⟩
  choose A Bm hAB hBA hint using H

  let Ag : Matrix (Fin m) (Fin N) (Πʳ i, [R i, B i]) := Matrix.of fun a b =>
    RestrictedProduct.mk (fun i => A i a b) (hgood.mono fun i hi => (hint i hi).1 a b)
  let Bg : Matrix (Fin N) (Fin m) (Πʳ i, [R i, B i]) := Matrix.of fun a b =>
    RestrictedProduct.mk (fun i => Bm i a b) (hgood.mono fun i hi => (hint i hi).2 a b)
  have hA : ∀ i, Ag.map (φ i) = A i := fun i => by ext a b; rfl
  have hBg : ∀ i, Bg.map (φ i) = Bm i := fun i => by ext a b; rfl
  refine ⟨Ag, Bg, ?_, ?_⟩
  · refine matrix_eq_of_map_evalRingHom_eq fun i => ?_
    change (Ag * Bg).map (φ i) = (1 : Matrix (Fin m) (Fin m) _).map (φ i)
    rw [Matrix.map_mul, hA, hBg, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_evalRingHom_eq fun i => ?_
    change (Bg * Ag).map (φ i) = ε.map (φ i)
    rw [Matrix.map_mul, hA, hBg, hBA]

end Restricted

section Reduction

variable {R : Type*} [CommRing R]

/--
@isnad1 id=free.2h5v.s7.92197c7f732a from=translated src=- shape=b8d815df vocab=68d95beb
-/
theorem free_of_splitsIdem (hR : SplitsIdem R) {m n : ℕ} (hn : 0 < n)
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : (Fin n → P) ≃ₗ[R] (Fin (m * n) → R)) : Module.Free R P := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let ι : P →ₗ[R] (Fin n → P) := LinearMap.single R (fun _ : Fin n => P) i0
  let π : (Fin n → P) →ₗ[R] P := LinearMap.proj i0
  let s : P →ₗ[R] (Fin (m * n) → R) := f.toLinearMap ∘ₗ ι
  let p : (Fin (m * n) → R) →ₗ[R] P := π ∘ₗ f.symm.toLinearMap
  have hps : ∀ x, p (s x) = x := fun x => by simp [p, s, π, ι, i0]
  let e : (Fin (m * n) → R) →ₗ[R] (Fin (m * n) → R) := s ∘ₗ p
  have he : ∀ y, e y = s (p y) := fun y => rfl
  let ε : Matrix (Fin (m * n)) (Fin (m * n)) R := LinearMap.toMatrix' e
  have hεe : Matrix.toLin' ε = e := Matrix.toLin'_toMatrix' e
  have hε : ε * ε = ε := by
    change LinearMap.toMatrix' e * LinearMap.toMatrix' e = LinearMap.toMatrix' e
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun y => by simp only [LinearMap.comp_apply, he, hps]

  let Ψ : (Fin n → P) →ₗ[R] (Fin (m * n) × Fin n → R) :=
    LinearMap.pi fun ki => (LinearMap.proj ki.1 ∘ₗ s) ∘ₗ LinearMap.proj ki.2
  let Φ : (Fin (m * n) × Fin n → R) →ₗ[R] (Fin n → P) :=
    LinearMap.pi fun i => p ∘ₗ LinearMap.pi fun k => LinearMap.proj (k, i)
  have hΨ : ∀ x ki, Ψ x ki = s (x ki.2) ki.1 := fun x ki => rfl
  have hΦ : ∀ y i, Φ y i = p (fun k => y (k, i)) := fun y i => rfl
  have hΦΨ : ∀ x, Φ (Ψ x) = x := fun x => by
    funext i
    rw [hΦ]
    exact hps (x i)
  let A' : Matrix (Fin (m * n)) (Fin (m * n) × Fin n) R :=
    LinearMap.toMatrix' (f.toLinearMap ∘ₗ Φ)
  let B' : Matrix (Fin (m * n) × Fin n) (Fin (m * n)) R :=
    LinearMap.toMatrix' (Ψ ∘ₗ f.symm.toLinearMap)
  have hA'B' : A' * B' = 1 := by
    change LinearMap.toMatrix' _ * LinearMap.toMatrix' _ = 1
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hΦΨ,
      LinearEquiv.apply_symm_apply]
  have hB'A' : B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε) := by
    change LinearMap.toMatrix' _ * LinearMap.toMatrix' _ = _
    rw [← LinearMap.toMatrix'_comp]
    ext ⟨k, i⟩ ⟨k', i'⟩
    rw [LinearMap.toMatrix'_apply, Matrix.blockDiagonal_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hΨ, hΦ]
    by_cases hii : i = i'
    · subst hii
      rw [ite_eq_left rfl]
      change _ = LinearMap.toMatrix' e k k'
      rw [LinearMap.toMatrix'_apply, he]
      have h1 : (fun k'' : Fin (m * n) => (Pi.single (k', i) (1 : R) :
          Fin (m * n) × Fin n → R) (k'', i)) = Pi.single k' 1 := by
        funext k''
        simp [Pi.single_apply]
      rw [h1]
    · rw [ite_eq_right hii]
      have h0 : (fun k'' : Fin (m * n) => (Pi.single (k', i') (1 : R) :
          Fin (m * n) × Fin n → R) (k'', i)) = 0 := by
        funext k''
        simp [hii]
      rw [h0, map_zero, map_zero, Pi.zero_apply]
  obtain ⟨A, B, hAB, hBA⟩ := hR (m * n) m n hn ε A' B' hε hA'B' hB'A'

  have hAεB : A * ε * B = 1 := by
    rw [← hBA, ← Matrix.mul_assoc, hAB, Matrix.one_mul, hAB]
  let u : P →ₗ[R] (Fin m → R) := Matrix.toLin' A ∘ₗ s
  let w : (Fin m → R) →ₗ[R] P := p ∘ₗ Matrix.toLin' B
  have hwu : w ∘ₗ u = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [u, w, LinearMap.comp_apply, LinearMap.id_apply]
    rw [← Matrix.toLin'_mul_apply, hBA, hεe, he, hps, hps]
  have huw : u ∘ₗ w = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [u, w, LinearMap.comp_apply, LinearMap.id_apply]
    rw [← he, ← hεe, ← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hAεB,
      Matrix.toLin'_one, LinearMap.id_apply]
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap u w huw hwu).symm

end Reduction

section Adelic

open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

/--
@isnad1 id=charzero.0h2v.s5.fa4c636d83bf from=translated src=- shape=d025193f vocab=1f41ca04
-/
theorem charZero_completion (v : InfinitePlace F) : CharZero v.Completion :=
  charZero_of_injective_algebraMap (algebraMap F v.Completion).injective

/--
@isnad1 id=charzero.0h2v.s6.b81a89437d1f from=translated src=- shape=082f7236 vocab=eca81c23
-/
theorem charZero_adicCompletion (v : HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

/--
@isnad1 id=charzero.0h2v.s9.2095a434080b from=translated src=- shape=700d3d0e vocab=bc0bbfaf
-/
theorem charZero_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletionIntegers F) :=
  haveI := charZero_adicCompletion F v
  (v.adicCompletionIntegers F).subtype.charZero

/--
@isnad1 id=splitsid.0h1v.s4.0abbe4b721a7 from=translated src=- shape=9499e9bc vocab=fed1c06d
-/
theorem splitsIdem_infiniteAdeleRing : SplitsIdem (InfiniteAdeleRing F) :=
  splitsIdem_pi (fun v : InfinitePlace F => v.Completion) fun v =>
    haveI := charZero_completion F v
    splitsIdem_of_isLocalRing _

/--
@isnad1 id=splitsid.0h1v.s5.29a448fe5b0f from=translated src=- shape=5a2b787c vocab=b0678067
-/
theorem splitsIdem_finiteAdeleRing : SplitsIdem (FiniteAdeleRing (𝓞 F) F) :=
  splitsIdem_restrictedProduct (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun v =>
      haveI := charZero_adicCompletion F v
      splitsIdem_of_isLocalRing _)
    (fun v =>
      haveI := charZero_adicCompletionIntegers F v
      splitsIdem_of_isLocalRing _)

/--
@isnad1 id=splitsid.0h1v.s5.383d8082f671 from=translated src=- shape=5a2b787c vocab=10a8611c
-/
theorem splitsIdem_adeleRing : SplitsIdem (AdeleRing (𝓞 F) F) :=
  splitsIdem_prod _ _ (splitsIdem_infiniteAdeleRing F) (splitsIdem_finiteAdeleRing F)

end Adelic

end R4H2F

/--
@isnad1 id=free.1h5v.s9.7c4967a160df from=translated src=- shape=da9d3fbd vocab=715cf0af
-/
theorem solution
    (F : Type) [Field F] [NumberField F] (m n : ℕ) (hn : 0 < n)
    (P : Type) [AddCommGroup P] [Module (AdeleRing (𝓞 F) F) P]
    (f : (Fin n → P) ≃ₗ[AdeleRing (𝓞 F) F] (Fin (m * n) → AdeleRing (𝓞 F) F)) :
    Module.Free (AdeleRing (𝓞 F) F) P :=
  R4H2F.free_of_splitsIdem (R4H2F.splitsIdem_adeleRing F) hn f
