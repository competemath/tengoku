/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.ExactCategory
import Tengoku.Seed.CategoryTheory.Abelian.Projective.Dimension
import Tengoku.Seed.Algebra.Category.ModuleCat.Projective
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The resolution theorem for `K₀` of a noetherian ring

Let `R` be a noetherian ring such that every finitely generated `R`-module has projective
dimension `≤ d`. Then `K₀(R) → G₀(R)` is bijective (`k0ToG0_bijective_of_hasProjectiveDimensionLE`).
Here:
* `K₀(R)` is finitely generated projective modules modulo short exact sequences;
* `G₀(R)` is finitely generated modules modulo short exact sequences.

Both groups are `ExactGrothendieck.SubcategoryGroup`s in `ModuleCat R`.

## Construction

`chi n M` is the alternating class `[F₀] - [F₁] + ⋯ ± χ₀(Kₙ)` of a *chosen* free resolution of
`M`, truncated at the `n`-th syzygy. When `pd M ≤ n` it is independent of choices. By
simultaneous induction on `n` we prove:
* `res_level` (Schanuel). For *any* surjection `E ↠ M` from a finite projective module,
  `chi (n+1) M = [E] - chi n (ker)`. The two kernels are compared through the fibre product
  `E ×_M E₀`.
* `add_succ_level` (horseshoe). `chi n` is additive on short exact sequences of modules of
  `pd ≤ n`.
* `proj_succ_level`. `chi n P = [P]` for `P` finite projective.

Then `chi d` descends to `ψ : G₀(R) → K₀(R)`, and `ψ` is inverse to the comparison map
(`k0ToG0_chi`).
-/

noncomputable section

universe u

open CategoryTheory

namespace ModuleResolution

variable (R : Type u) [CommRing R]

/-- Finitely generated projective modules.-/
def IsFGProj (M : ModuleCat.{u} R) : Prop := Module.Finite R M ∧ Module.Projective R M

/-- Finitely generated modules.-/
def IsFG (M : ModuleCat.{u} R) : Prop := Module.Finite R M

/-- `K₀(R)`: finitely generated projective modules modulo short exact sequences.-/
abbrev K0 := ExactGrothendieck.SubcategoryGroup (ModuleCat.{u} R) (IsFGProj R)

/-- `G₀(R)`: finitely generated modules modulo short exact sequences.-/
abbrev G0 := ExactGrothendieck.SubcategoryGroup (ModuleCat.{u} R) (IsFG R)

/-- The forgetful comparison `K₀(R) → G₀(R)`.-/
def k0ToG0 : K0 R →+ G0 R :=
  ExactGrothendieck.map (fun E => ⟨E.1, E.2.1⟩) (fun _ _ _ h => h)

/-- Class of a finite projective module in `K₀(R)`.-/
def pcl (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    K0 R :=
  ExactGrothendieck.subcategoryClassOf _ (IsFGProj R) (ModuleCat.of R M) ⟨‹_›, ‹_›⟩

/-- Class of a finite module in `G₀(R)`.-/
def gcl (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : G0 R :=
  ExactGrothendieck.subcategoryClassOf _ (IsFG R) (ModuleCat.of R M) ‹_›

variable {R}

theorem shortExact_of_linear {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact hex.apply_apply_eq_zero x)).ShortExact :=
  ModuleCat.shortComplex_shortExact _ hex hf hg

theorem pcl_ses {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    pcl R B = pcl R A + pcl R C :=
  ExactGrothendieck.subcategoryClassOf_middle _ _ _ _ _ _ (shortExact_of_linear f g hf hex hg)

theorem gcl_ses {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [Module.Finite R A]
    [Module.Finite R B] [Module.Finite R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    gcl R B = gcl R A + gcl R C :=
  ExactGrothendieck.subcategoryClassOf_middle _ _ _ _ _ _ (shortExact_of_linear f g hf hex hg)

theorem k0ToG0_pcl (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : k0ToG0 R (pcl R M) = gcl R M :=
  ExactGrothendieck.map_classOf _ _ _

/-! ### Projective dimension bookkeeping -/

theorem hasPDLE_of_projective (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Projective R M] (n : ℕ) : HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  haveI : Projective (ModuleCat.of R M) := inferInstance
  exact hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)

theorem projective_of_hasPDLE_zero (M : Type u) [AddCommGroup M] [Module R M]
    (h : HasProjectiveDimensionLE (ModuleCat.of R M) 0) : Module.Projective R M := by
  rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h
  exact h

theorem hasPDLE_ker {F N : Type u} [AddCommGroup F] [Module R F] [AddCommGroup N]
    [Module R N] [Module.Projective R F] (f : F →ₗ[R] N) (hf : Function.Surjective f) (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : Projective (ModuleCat.of R F) := inferInstance
  exact hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance h

theorem hasPDLE_mid {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) (n : ℕ)
    (hA : HasProjectiveDimensionLE (ModuleCat.of R A) n)
    (hC : HasProjectiveDimensionLE (ModuleCat.of R C) n) :
    HasProjectiveDimensionLE (ModuleCat.of R B) n :=
  (shortExact_of_linear f g hf hex hg).hasProjectiveDimensionLT_X₂ (n + 1) hA hC

/-! ### The resolution Euler characteristic -/

/-- Chosen number of generators.-/
def cov (M : ModuleCat.{u} R) [Module.Finite R M] : ℕ :=
  (Module.Finite.exists_fin' R M).choose

/-- Chosen surjection from a finite free module.-/
def covMap (M : ModuleCat.{u} R) [Module.Finite R M] : (Fin (cov M) → R) →ₗ[R] M :=
  (Module.Finite.exists_fin' R M).choose_spec.choose

theorem covMap_surjective (M : ModuleCat.{u} R) [Module.Finite R M] :
    Function.Surjective (covMap M) :=
  (Module.Finite.exists_fin' R M).choose_spec.choose_spec

open Classical in
variable (R) in
/-- `chi n M = Σ (-1)^i [F_i]` along the chosen free resolution, truncated at stage `n` by the
class of the `n`-th syzygy (meaningful when `pd M ≤ n`).-/
def chi : ℕ → ModuleCat.{u} R → K0 R
  | 0, M => if h : Module.Finite R M ∧ Module.Projective R M then
      ExactGrothendieck.subcategoryClassOf _ (IsFGProj R) M h else 0
  | n + 1, M => if h : Module.Finite R M then
      haveI := h
      pcl R (Fin (cov M) → R) - chi n (ModuleCat.of R (LinearMap.ker (covMap M)))
    else 0

theorem chi_zero (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : chi R 0 (ModuleCat.of R M) = pcl R M := by
  rw [chi, dite_eq_left ⟨‹_›, ‹_›⟩]; rfl

theorem chi_succ (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M] :
    chi R (n + 1) M =
      pcl R (Fin (cov M) → R) - chi R n (ModuleCat.of R (LinearMap.ker (covMap M))) := by
  rw [chi, dite_eq_left ‹_›]

variable [IsNoetherianRing R]

variable (R) in
/-- Additivity at level `n`.-/
def Add (n : ℕ) : Prop :=
  ∀ (A B C : Type u) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C), Function.Injective f → Function.Exact f g →
    Function.Surjective g → HasProjectiveDimensionLE (ModuleCat.of R A) n →
    HasProjectiveDimensionLE (ModuleCat.of R B) n →
    HasProjectiveDimensionLE (ModuleCat.of R C) n →
    chi R n (ModuleCat.of R B) = chi R n (ModuleCat.of R A) + chi R n (ModuleCat.of R C)

variable (R) in
/-- Normalisation on projectives at level `n`.-/
def Proj (n : ℕ) : Prop :=
  ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P],
    chi R n (ModuleCat.of R P) = pcl R P

omit [IsNoetherianRing R] in
theorem add_zero_level : Add R 0 := by
  intro A B C _ _ _ _ _ _ _ _ _ f g hf hex hg hA hB hC
  haveI := projective_of_hasPDLE_zero A hA
  haveI := projective_of_hasPDLE_zero B hB
  haveI := projective_of_hasPDLE_zero C hC
  rw [chi_zero, chi_zero, chi_zero]
  exact pcl_ses f g hf hex hg

omit [IsNoetherianRing R] in
theorem proj_zero_level : Proj R 0 := fun P _ _ _ _ => chi_zero P

theorem chi_subsingleton {n : ℕ} (hAdd : Add R n) (Z : Type u) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] : chi R n (ModuleCat.of R Z) = 0 := by
  haveI : Module.Finite R Z := inferInstance
  haveI : HasProjectiveDimensionLT (ModuleCat.of R Z) 0 :=
    (ModuleCat.isZero_of_subsingleton _).hasProjectiveDimensionLT_zero
  have hZ : HasProjectiveDimensionLE (ModuleCat.of R Z) n :=
    hasProjectiveDimensionLT_of_ge _ 0 (n + 1) (by omega)
  have h := hAdd Z Z Z 0 0 (Function.injective_of_subsingleton _)
    (fun x => by simp [Subsingleton.elim x 0]) (Function.surjective_to_subsingleton _) hZ hZ hZ
  have h' := congrArg (fun z => z - chi R n (ModuleCat.of R Z)) h
  simpa using h'.symm

/-- **Independence of the cover** (generalised Schanuel).-/
theorem res_level {n : ℕ} (hAdd : Add R n) (hProj : Proj R n)
    (E M : Type u) [AddCommGroup E] [Module R E] [Module.Finite R E] [Module.Projective R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (π : E →ₗ[R] M)
    (hπ : Function.Surjective π) (hM : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)) :
    chi R (n + 1) (ModuleCat.of R M) = pcl R E - chi R n (ModuleCat.of R (LinearMap.ker π)) := by
  rw [chi_succ]
  set E₀ := Fin (cov (ModuleCat.of R M)) → R
  set π₀ : E₀ →ₗ[R] M := covMap (ModuleCat.of R M)
  have hπ₀ : Function.Surjective π₀ := covMap_surjective _
  let Φ : E × E₀ →ₗ[R] M := π.coprod π₀
  let L := LinearMap.ker Φ
  -- first sequence `0 → ker π → L → E₀ → 0`
  let i₁ : LinearMap.ker π →ₗ[R] L :=
    { toFun := fun k => ⟨(k.1, 0), LinearMap.mem_ker.mpr
        (show π k.1 + π₀ 0 = 0 by rw [map_zero, add_zero]; exact k.2)⟩
      map_add' := fun a b => Subtype.ext (Prod.ext rfl (add_zero 0).symm)
      map_smul' := fun r a => Subtype.ext (Prod.ext rfl (smul_zero r).symm) }
  let p₁ : L →ₗ[R] E₀ := (LinearMap.snd R E E₀).comp L.subtype
  let i₂ : LinearMap.ker π₀ →ₗ[R] L :=
    { toFun := fun k => ⟨(0, k.1), LinearMap.mem_ker.mpr
        (show π 0 + π₀ k.1 = 0 by rw [map_zero, zero_add]; exact k.2)⟩
      map_add' := fun a b => Subtype.ext (Prod.ext (add_zero 0).symm rfl)
      map_smul' := fun r a => Subtype.ext (Prod.ext (smul_zero r).symm rfl) }
  let p₂ : L →ₗ[R] E := (LinearMap.fst R E E₀).comp L.subtype
  have hmemL : ∀ ℓ : L, π ℓ.1.1 + π₀ ℓ.1.2 = 0 := fun ℓ => LinearMap.mem_ker.mp ℓ.2
  have hi₁ : Function.Injective i₁ := fun a b h => by
    have := congrArg (fun ℓ : L => ℓ.1.1) h; exact Subtype.ext this
  have hi₂ : Function.Injective i₂ := fun a b h => by
    have := congrArg (fun ℓ : L => ℓ.1.2) h; exact Subtype.ext this
  have hp₁ : Function.Surjective p₁ := fun e₀ => by
    obtain ⟨e, he⟩ := hπ (π₀ e₀)
    exact ⟨⟨(-e, e₀), LinearMap.mem_ker.mpr
      (show π (-e) + π₀ e₀ = 0 by rw [map_neg, he, neg_add_cancel])⟩, rfl⟩
  have hp₂ : Function.Surjective p₂ := fun e => by
    obtain ⟨e₀, he₀⟩ := hπ₀ (π e)
    exact ⟨⟨(e, -e₀), LinearMap.mem_ker.mpr
      (show π e + π₀ (-e₀) = 0 by rw [map_neg, he₀, add_neg_cancel])⟩, rfl⟩
  have hex₁ : Function.Exact i₁ p₁ := by
    intro ℓ
    constructor
    · intro h
      refine ⟨⟨ℓ.1.1, ?_⟩, ?_⟩
      · have := hmemL ℓ
        change ℓ.1.2 = 0 at h
        simpa [h] using this
      · change ℓ.1.2 = 0 at h
        exact Subtype.ext (Prod.ext rfl h.symm)
    · rintro ⟨k, rfl⟩; rfl
  have hex₂ : Function.Exact i₂ p₂ := by
    intro ℓ
    constructor
    · intro h
      refine ⟨⟨ℓ.1.2, ?_⟩, ?_⟩
      · have := hmemL ℓ
        change ℓ.1.1 = 0 at h
        simpa [h] using this
      · change ℓ.1.1 = 0 at h
        exact Subtype.ext (Prod.ext h.symm rfl)
    · rintro ⟨k, rfl⟩; rfl
  have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) n := hasPDLE_ker π hπ n hM
  have hK₀ : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π₀)) n :=
    hasPDLE_ker π₀ hπ₀ n hM
  have hL : HasProjectiveDimensionLE (ModuleCat.of R L) n :=
    hasPDLE_mid i₁ p₁ hi₁ hex₁ hp₁ n hK (hasPDLE_of_projective E₀ n)
  have h₁ := hAdd _ _ _ i₁ p₁ hi₁ hex₁ hp₁ hK hL (hasPDLE_of_projective E₀ n)
  have h₂ := hAdd _ _ _ i₂ p₂ hi₂ hex₂ hp₂ hK₀ hL (hasPDLE_of_projective E n)
  rw [hProj E₀] at h₁
  rw [hProj E] at h₂
  have : chi R n (ModuleCat.of R (LinearMap.ker π)) + pcl R E₀ =
      chi R n (ModuleCat.of R (LinearMap.ker π₀)) + pcl R E := h₁.symm.trans h₂
  change pcl R E₀ - chi R n (ModuleCat.of R (LinearMap.ker π₀)) = _
  rw [sub_eq_sub_iff_add_eq_add, add_comm (pcl R E₀), this, add_comm]

theorem proj_succ_level {n : ℕ} (hAdd : Add R n) (hProj : Proj R n) : Proj R (n + 1) := by
  intro P _ _ _ _
  rw [res_level hAdd hProj P P LinearMap.id Function.surjective_id (hasPDLE_of_projective P _)]
  haveI : Subsingleton (LinearMap.ker (LinearMap.id : P →ₗ[R] P)) := by
    rw [LinearMap.ker_id]; infer_instance
  rw [chi_subsingleton hAdd, sub_zero]

/-- **Horseshoe step.**-/
theorem add_succ_level {n : ℕ} (hAdd : Add R n) (hProj : Proj R n) : Add R (n + 1) := by
  intro A B C _ _ _ _ _ _ _ _ _ f g hf hex hg hA hB hC
  obtain ⟨ka, πA, hπA⟩ := Module.Finite.exists_fin' R A
  obtain ⟨kc, πC, hπC⟩ := Module.Finite.exists_fin' R C
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g πC hg
  let Φ : (Fin ka → R) × (Fin kc → R) →ₗ[R] B := (f ∘ₗ πA).coprod σ
  have hΦ : Function.Surjective Φ := by
    intro b
    obtain ⟨c, hc⟩ := hπC (g b)
    have : g (b - σ c) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hσ, hc, sub_self]
    obtain ⟨a', ha'⟩ := (hex (b - σ c)).mp this
    obtain ⟨a, rfl⟩ := hπA a'
    refine ⟨(a, c), ?_⟩
    change f (πA a) + σ c = b
    rw [ha', sub_add_cancel]
  let KA := LinearMap.ker πA
  let KC := LinearMap.ker πC
  let KB := LinearMap.ker Φ
  have hmem : ∀ ℓ : KB, f (πA ℓ.1.1) + σ ℓ.1.2 = 0 := fun ℓ => LinearMap.mem_ker.mp ℓ.2
  let i : KA →ₗ[R] KB :=
    { toFun := fun a => ⟨(a.1, 0), LinearMap.mem_ker.mpr
        (show f (πA a.1) + σ 0 = 0 by rw [map_zero, add_zero, LinearMap.mem_ker.mp a.2, map_zero])⟩
      map_add' := fun a b => Subtype.ext (Prod.ext rfl (add_zero 0).symm)
      map_smul' := fun r a => Subtype.ext (Prod.ext rfl (smul_zero r).symm) }
  have hpC : ∀ ℓ : KB, πC ℓ.1.2 = 0 := fun ℓ => by
    have := congrArg g (hmem ℓ)
    rw [map_add, map_zero, hex.apply_apply_eq_zero, zero_add, ← LinearMap.comp_apply, hσ] at this
    exact this
  let p : KB →ₗ[R] KC :=
    { toFun := fun ℓ => ⟨ℓ.1.2, LinearMap.mem_ker.mpr (hpC ℓ)⟩
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl }
  have hi : Function.Injective i := fun a b h => by
    have := congrArg (fun ℓ : KB => ℓ.1.1) h; exact Subtype.ext this
  have hp : Function.Surjective p := by
    intro c
    have : g (σ c.1) = 0 := by rw [← LinearMap.comp_apply, hσ]; exact c.2
    obtain ⟨a', ha'⟩ := (hex (σ c.1)).mp this
    obtain ⟨a, rfl⟩ := hπA a'
    refine ⟨⟨(-a, c.1), LinearMap.mem_ker.mpr ?_⟩, rfl⟩
    change f (πA (-a)) + σ c.1 = 0
    rw [map_neg, map_neg, ha', neg_add_cancel]
  have hip : Function.Exact i p := by
    intro ℓ
    constructor
    · intro h
      have h2 : ℓ.1.2 = 0 := congrArg Subtype.val h
      have h1 : πA ℓ.1.1 = 0 := by
        apply hf
        have := hmem ℓ
        rw [h2, map_zero, add_zero] at this
        rw [this, map_zero]
      exact ⟨⟨ℓ.1.1, h1⟩, Subtype.ext (Prod.ext rfl h2.symm)⟩
    · rintro ⟨a, rfl⟩; rfl
  have hKA := hasPDLE_ker πA hπA n hA
  have hKC := hasPDLE_ker πC hπC n hC
  have hKB := hasPDLE_ker Φ hΦ n hB
  have hK := hAdd KA KB KC i p hi hip hp hKA hKB hKC
  rw [res_level hAdd hProj _ _ Φ hΦ hB, res_level hAdd hProj _ _ πA hπA hA,
    res_level hAdd hProj _ _ πC hπC hC, hK]
  have hsum : pcl R ((Fin ka → R) × (Fin kc → R)) = pcl R (Fin ka → R) + pcl R (Fin kc → R) :=
    pcl_ses (LinearMap.inl R _ _) (LinearMap.snd R _ _) LinearMap.inl_injective
      (Function.Exact.inl_snd) LinearMap.snd_surjective
  rw [hsum]
  abel

theorem add_proj_all : ∀ n, Add R n ∧ Proj R n
  | 0 => ⟨add_zero_level, proj_zero_level⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := add_proj_all n
      exact ⟨add_succ_level h1 h2, proj_succ_level h1 h2⟩

/-- The Euler characteristic of the chosen resolution maps to the `G₀` class.-/
theorem k0ToG0_chi : ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
      k0ToG0 R (chi R n (ModuleCat.of R M)) = gcl R M
  | 0, M, _, _, _, hM => by
      haveI := projective_of_hasPDLE_zero M hM
      rw [chi_zero, k0ToG0_pcl]
  | n + 1, M, _, _, _, hM => by
      rw [chi_succ, map_sub, k0ToG0_pcl]
      have hπ := covMap_surjective (ModuleCat.of R M)
      rw [k0ToG0_chi n _ (hasPDLE_ker _ hπ n hM)]
      rw [gcl_ses (LinearMap.ker (covMap (ModuleCat.of R M))).subtype (covMap (ModuleCat.of R M))
        (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) hπ]
      change gcl R (LinearMap.ker (covMap (ModuleCat.of R M))) + gcl R M -
        gcl R (LinearMap.ker (covMap (ModuleCat.of R M))) = gcl R M
      abel

/-- **Resolution theorem for `K₀`.** If every finitely generated module over the noetherian
ring `R` has projective dimension `≤ d`, then `K₀(R) → G₀(R)` is bijective.-/
theorem k0ToG0_bijective_of_hasProjectiveDimensionLE (d : ℕ)
    (hd : ∀ M : ModuleCat.{u} R, Module.Finite R M → HasProjectiveDimensionLE M d) :
    Function.Bijective (k0ToG0 R) := by
  obtain ⟨hAdd, hProj⟩ := add_proj_all (R := R) d
  let ψ : G0 R →+ K0 R := ExactGrothendieck.lift (fun M => chi R d M.1) (by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨f, g, zero, hS⟩
    haveI : Module.Finite R A := hA
    haveI : Module.Finite R B := hB
    haveI : Module.Finite R C := hC
    exact hAdd A B C f.hom g.hom hS.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_surjective_g (hd _ hA) (hd _ hB) (hd _ hC))
  have h1 : ψ.comp (k0ToG0 R) = AddMonoidHom.id _ := by
    apply ExactGrothendieck.hom_ext
    rintro ⟨E, hE1, hE2⟩
    change ψ (k0ToG0 R (pcl R E)) = pcl R E
    rw [k0ToG0_pcl]
    exact (ExactGrothendieck.lift_classOf _ _ _).trans (hProj E)
  have h2 : (k0ToG0 R).comp ψ = AddMonoidHom.id _ := by
    apply ExactGrothendieck.hom_ext
    rintro ⟨M, hM⟩
    haveI : Module.Finite R M := hM
    change k0ToG0 R (ψ (gcl R M)) = gcl R M
    rw [show ψ (gcl R M) = chi R d (ModuleCat.of R M) from ExactGrothendieck.lift_classOf _ _ _]
    exact k0ToG0_chi d M (hd _ hM)
  refine ⟨fun x y hxy => ?_, fun y => ⟨ψ y, ?_⟩⟩
  · have := congrArg ψ hxy
    simpa [← AddMonoidHom.comp_apply, h1] using this
  · exact DFunLike.congr_fun h2 y

end ModuleResolution
