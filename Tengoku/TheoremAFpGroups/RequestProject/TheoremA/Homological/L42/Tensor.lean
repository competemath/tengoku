module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Homological.Comparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma 4.2, part 1: the tensor square `Q = F ⊗_ℤ F` and an integral contraction of `F`

For a partial resolution `R` we form the bigraded groups `T p q = F_p ⊗_ℤ F_q` and the group
`Qm R = ∀ p q, T p q` of all bigraded families, with the total differential `D`
(`(D z)_{p,q} = (d ⊗ 1) z_{p+1,q} + (-1)^p (1 ⊗ d) z_{p,q+1}`) and the external action of
`B × B`.  We also construct an integral contraction `σ` of the augmented complex `F → ℤ`.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable (R : Res B k)

/-- The `p`-th term `F_p`.-/
abbrev F (p : ℕ) := FreeMod B (R.c p)

/-- `T p q = F_p ⊗_ℤ F_q`.-/
abbrev T (p q : ℕ) := F R p ⊗[ℤ] F R q

/-- Bigraded families in `F ⊗ F`.-/
abbrev Qm := ∀ p q, T R p q

/-- The differential as a `ℤ`-linear map.-/
noncomputable abbrev dZ (p : ℕ) : F R (p + 1) →ₗ[ℤ] F R p := (R.d p).restrictScalars ℤ

/-- `d ⊗ 1`.-/
noncomputable abbrev dL (p q : ℕ) : T R (p + 1) q →ₗ[ℤ] T R p q := map (dZ R p) LinearMap.id

/-- `1 ⊗ d`.-/
noncomputable abbrev dR (p q : ℕ) : T R p (q + 1) →ₗ[ℤ] T R p q := map LinearMap.id (dZ R q)

/-- The total differential on bigraded families.-/
noncomputable def D : Qm R →+ Qm R where
  toFun z p q := dL R p q (z (p + 1) q) + ((-1 : ℤ) ^ p) • dR R p q (z p (q + 1))
  map_zero' := by funext p q; simp
  map_add' z w := by funext p q; simp only [Pi.add_apply, map_add, smul_add]; abel

/--
@isnad1 id=eq.0h6v.s12.23680c241220 from=translated src=- shape=8b3060cc vocab=090d6ffa
-/
theorem D_apply (z : Qm R) (p q : ℕ) :
    D R z p q = dL R p q (z (p + 1) q) + ((-1 : ℤ) ^ p) • dR R p q (z p (q + 1)) := rfl

/-- Multiplication by a group element, as a `ℤ`-linear map.-/
noncomputable def gsm (p : ℕ) (g : B) : F R p →ₗ[ℤ] F R p where
  toFun x := MonoidAlgebra.of ℤ B g • x
  map_add' x y := smul_add _ x y
  map_smul' n x := smul_comm _ n x

/--
@isnad1 id=eq.0h6v.s9.ba0c94668e36 from=translated src=- shape=d8714597 vocab=313b784d
-/
@[simp] theorem gsm_apply (p : ℕ) (g : B) (x : F R p) :
    gsm R p g x = MonoidAlgebra.of ℤ B g • x := rfl

/-- The external action of `(b, c) ∈ B × B` on `T p q`.-/
noncomputable abbrev act (p q : ℕ) (b c : B) : T R p q →ₗ[ℤ] T R p q := map (gsm R p b) (gsm R q c)

/-- The external action on bigraded families.-/
noncomputable def actQ (b c : B) : Qm R →+ Qm R where
  toFun z p q := act R p q b c (z p q)
  map_zero' := by funext p q; simp
  map_add' z w := by funext p q; simp

/--
@isnad1 id=eq.0h8v.s11.17f75fe765ec from=translated src=- shape=b6734be3 vocab=9aa7ea8d
-/
@[simp] theorem actQ_apply (b c : B) (z : Qm R) (p q : ℕ) :
    actQ R b c z p q = act R p q b c (z p q) := rfl

/--
@isnad1 id=eq.0h6v.s11.1dbd5170a977 from=translated src=- shape=625df0ff vocab=f4f0399f
-/
theorem dZ_gsm (p : ℕ) (g : B) (x : F R (p + 1)) :
    dZ R p (gsm R (p + 1) g x) = gsm R p g (dZ R p x) := by
  simp

/-- The augmentation as a `ℤ`-linear map.-/
noncomputable abbrev εZ : F R 0 →ₗ[ℤ] ℤ := R.ε.toIntLinearMap

/--
@isnad1 id=eq.0h4v.s9.1fe8cc550579 from=translated src=- shape=42938381 vocab=9706012e
-/
theorem εZ_dZ (x : F R 1) : εZ R (dZ R 0 x) = 0 := R.ε_d x

/--
@isnad1 id=eq.0h5v.s10.c6dd7ed0cb92 from=translated src=- shape=5313d05f vocab=ec5b9d9a
-/
theorem εZ_gsm (g : B) (x : F R 0) : εZ R (gsm R 0 g x) = εZ R x := R.ε_inv g x

/-- An integral contraction of the augmented complex `F_{k+1} → ⋯ → F_0 → ℤ`.-/
structure Contr where
  x0 : F R 0
  hx0 : R.ε x0 = 1
  σ : ∀ p, F R p →ₗ[ℤ] F R (p + 1)
  σ_top : ∀ p, k < p → σ p = 0
  c0 : ∀ x, dZ R 0 (σ 0 x) + R.ε x • x0 = x
  ci : ∀ i, i < k → ∀ x : F R (i + 1), dZ R (i + 1) (σ (i + 1) x) + σ i (dZ R i x) = x

/--
@isnad1 id=nonempty.0h3v.s4.14dfdb282ec8 from=translated src=- shape=54d0cce0 vocab=4c9eda5f
-/
theorem exists_contr : Nonempty (Contr R) := by
  obtain ⟨x0, hx0⟩ := R.ε_surj 1
  -- partial contractions
  have key : ∀ n, n ≤ k + 1 → ∃ σ : ∀ p, F R p →ₗ[ℤ] F R (p + 1),
      (∀ p, n ≤ p → σ p = 0) ∧ (1 ≤ n → ∀ x, dZ R 0 (σ 0 x) + R.ε x • x0 = x) ∧
      (∀ i, i + 1 < n → ∀ x : F R (i + 1), dZ R (i + 1) (σ (i + 1) x) + σ i (dZ R i x) = x) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨fun _ => 0, fun _ _ => rfl, fun h => by omega, fun i hi => by omega⟩
    | succ n ih =>
      intro hn
      obtain ⟨σ, htop, h0, hi⟩ := ih (by omega)
      classical
      cases n with
      | zero =>
        -- construct `σ 0`
        have hmem : ∀ x : F R 0, x - R.ε x • x0 ∈ LinearMap.range (dZ R 0) := by
          intro x
          have : x - R.ε x • x0 ∈ R.ε.ker := by
            show R.ε _ = 0
            rw [map_sub, map_zsmul, hx0]; simp
          rw [R.exact0] at this
          obtain ⟨y, hy⟩ := this
          exact ⟨y, hy⟩
        let g : F R 0 →ₗ[ℤ] LinearMap.range (dZ R 0) :=
          LinearMap.codRestrict _ (LinearMap.id - (LinearMap.toSpanSingleton ℤ _ x0) ∘ₗ εZ R)
            (fun x => by simpa using hmem x)
        obtain ⟨h, hh⟩ := Module.projective_lifting_property (dZ R 0).rangeRestrict g
          (LinearMap.surjective_rangeRestrict _)
        refine ⟨Function.update (β := fun p => F R p →ₗ[ℤ] F R (p + 1)) σ 0 h, ?_, ?_, ?_⟩
        · intro p hp
          rw [Function.update_of_ne (by omega)]; exact htop p (by omega)
        · intro _ x
          rw [Function.update_self]
          have := congrArg (fun f => (f x : F R 0)) hh
          simp only [LinearMap.comp_apply, LinearMap.rangeRestrict, LinearMap.codRestrict_apply,
            g] at this
          rw [this]; simp
        · intro i hi; omega
      | succ n =>
        -- construct `σ (n+1)`
        have hmem : ∀ x : F R (n + 1), x - σ n (dZ R n x) ∈ LinearMap.range (dZ R (n + 1)) := by
          intro x
          have hker : x - σ n (dZ R n x) ∈ LinearMap.ker (R.d n) := by
            show R.d n _ = 0
            rw [map_sub]
            cases n with
            | zero =>
              have := h0 (by omega) (dZ R 0 x)
              have he : R.ε (dZ R 0 x) = 0 := R.ε_d x
              rw [he, zero_smul, add_zero] at this
              change R.d 0 x - dZ R 0 (σ 0 (dZ R 0 x)) = 0
              rw [this]; exact sub_self _
            | succ n' =>
              have := hi n' (by omega) (dZ R (n' + 1) x)
              have hdd : dZ R n' (dZ R (n' + 1) x) = 0 := R.d_d n' (by omega) x
              rw [hdd, map_zero, add_zero] at this
              change R.d (n' + 1) x - dZ R (n' + 1) (σ (n' + 1) (dZ R (n' + 1) x)) = 0
              rw [this]; exact sub_self _
          rw [R.exact n (by omega)] at hker
          obtain ⟨y, hy⟩ := hker
          exact ⟨y, hy⟩
        let g : F R (n + 1) →ₗ[ℤ] LinearMap.range (dZ R (n + 1)) :=
          LinearMap.codRestrict _ (LinearMap.id - σ n ∘ₗ dZ R n) (fun x => by simpa using hmem x)
        obtain ⟨h, hh⟩ := Module.projective_lifting_property (dZ R (n + 1)).rangeRestrict g
          (LinearMap.surjective_rangeRestrict _)
        refine ⟨Function.update (β := fun p => F R p →ₗ[ℤ] F R (p + 1)) σ (n + 1) h, ?_, ?_, ?_⟩
        · intro p hp
          rw [Function.update_of_ne (by omega)]; exact htop p (by omega)
        · intro _ x
          rw [Function.update_of_ne (by omega)]; exact h0 (by omega) x
        · intro i hi' x
          by_cases hin : i = n
          · subst hin
            rw [Function.update_self, Function.update_of_ne (by omega)]
            have := congrArg (fun f => (f x : F R (i + 1))) hh
            simp only [LinearMap.comp_apply, LinearMap.rangeRestrict, LinearMap.codRestrict_apply,
              g] at this
            rw [this]; simp
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hi i (by omega) x
  obtain ⟨σ, htop, h0, hi⟩ := key (k + 1) le_rfl
  exact ⟨⟨x0, hx0, σ, fun p hp => htop p hp, h0 (by omega), fun i hi' => hi i (by omega)⟩⟩

end L42

end TheoremA
