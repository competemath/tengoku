import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.Algebra.Homology.HomologicalComplex
import Tengoku.Seed.Algebra.Lie.IdealOperations
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.GroupTheory.Perm.Fin
import Tengoku.Seed.LinearAlgebra.Alternating.Curry
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.Multilinear.Curry
import Tengoku.Seed.LinearAlgebra.Quotient.Basic
import Tengoku.DgLean.DG.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Chevalley–Eilenberg complex

Let `𝔤` be a Lie algebra over a commutative ring `R` (an ordinary, ungraded Lie algebra, i.e. a
dg Lie algebra concentrated in degree `0`). This file constructs the Chevalley–Eilenberg cochain
complex of `𝔤` with trivial coefficients: the `n`-cochains are the alternating `R`-multilinear
maps `𝔤ⁿ → R` (`DG.ChevalleyEilenberg.CECochain R 𝔤 n`, Mathlib's `AlternatingMap`), with the
differential

  `(d ω)(x₀, …, xₙ) = ∑_{i < j} (-1)^(i + j) ω([xᵢ, xⱼ], x₀, …, x̂ᵢ, …, x̂ⱼ, …, xₙ)`

(`DG.ChevalleyEilenberg.ceD_apply_eq_sum`).

## Main definitions and results

* `DG.ChevalleyEilenberg.ceD R 𝔤 n : Cⁿ(𝔤) →ₗ[R] Cⁿ⁺¹(𝔤)`, with `d ∘ d = 0`
  (`DG.ChevalleyEilenberg.ceD_ceD`) and the standard formula above.
* `DG.ChevalleyEilenberg.ceComplex R 𝔤`: the complex as a `CochainComplex (ModuleCat R) ℕ`.
* `DG.ChevalleyEilenberg.CECohomology R 𝔤 n`: the Lie algebra cohomology `Hⁿ(𝔤, R)`, with
  `H⁰(𝔤, R) ≅ R` (`DG.ChevalleyEilenberg.ceCohomologyZeroEquiv`) and
  `H¹(𝔤, R) ≅ (𝔤 / [𝔤, 𝔤])^*` (`DG.ChevalleyEilenberg.ceCohomologyOneEquiv`).

The wedge product and the commutative dg algebra structure on `⨁ₙ Cⁿ(𝔤)` are in
`DG.Lie.ChevalleyEilenbergAlgebra`.

## Implementation notes

The differential is first defined on all multilinear cochains (`DG.ChevalleyEilenberg.ceDiff`)
by recursion on the degree, through the Cartan formula `ι_x (d f) = x • f - d (ι_x f)`, where
`ι_x` is contraction with `x` in the first argument and `x • f` is the coadjoint action
(`DG.ChevalleyEilenberg.lieAct`, itself defined by `ι_y (x • f) = x • ι_y f - ι_{[x, y]} f`).
With these definitions `d ∘ d = 0` follows by induction from the facts that the coadjoint action
is a representation (this is where the Jacobi identity enters) and that `d` is equivariant. The
differential preserves alternating cochains (`DG.ChevalleyEilenberg.IsAlt.ceDiff`), and on them it
is given by the standard formula.
-/

noncomputable section

namespace DG.ChevalleyEilenberg

variable (R 𝔤 : Type*) [CommRing R] [LieRing 𝔤] [LieAlgebra R 𝔤]

/-- Multilinear `n`-cochains `𝔤ⁿ → R`.-/
abbrev MCochain (n : ℕ) : Type _ := MultilinearMap R (fun _ : Fin n => 𝔤) R

/-- Currying in the first variable.-/
def curryEquiv (n : ℕ) : MCochain R 𝔤 (n + 1) ≃ₗ[R] (𝔤 →ₗ[R] MCochain R 𝔤 n) :=
  multilinearCurryLeftEquiv R (fun _ => 𝔤) R

variable {R 𝔤}

/--
@isnad1 id=eq.0h6v.s11.09c0282b202b from=translated src=- shape=6611362d vocab=44701e51
-/
@[simp]
theorem curryEquiv_apply {n : ℕ} (f : MCochain R 𝔤 (n + 1)) (x : 𝔤) (v : Fin n → 𝔤) :
    curryEquiv R 𝔤 n f x v = f (Fin.cons x v) := rfl

/--
@isnad1 id=eq.0h5v.s12.474a6f81e10a from=translated src=- shape=5f5e431e vocab=d8a8ca3c
-/
@[simp]
theorem curryEquiv_symm_apply {n : ℕ} (φ : 𝔤 →ₗ[R] MCochain R 𝔤 n) (v : Fin (n + 1) → 𝔤) :
    (curryEquiv R 𝔤 n).symm φ v = φ (v 0) (Fin.tail v) := rfl

/--
@isnad1 id=eq.1h5v.s12.524bfa90bdbf from=translated src=- shape=d45a660d vocab=47dcfbef
-/
theorem ext_curry {n : ℕ} {f g : MCochain R 𝔤 (n + 1)}
    (h : ∀ x, curryEquiv R 𝔤 n f x = curryEquiv R 𝔤 n g x) : f = g :=
  (curryEquiv R 𝔤 n).injective (LinearMap.ext h)

variable (R 𝔤)

/-- The coadjoint action of `x ∈ 𝔤` on multilinear cochains, defined recursively by
`ι_y (x • f) = x • ι_y f - ι_{[x, y]} f`.-/
def lieAct : (n : ℕ) → 𝔤 →ₗ[R] MCochain R 𝔤 n →ₗ[R] MCochain R 𝔤 n
  | 0 => 0
  | n + 1 => LinearMap.mk₂ R (fun x f => (curryEquiv R 𝔤 n).symm
      (lieAct n x ∘ₗ curryEquiv R 𝔤 n f - curryEquiv R 𝔤 n f ∘ₗ LieModule.toEnd R 𝔤 𝔤 x))
      (fun x x' f => by ext v; simp; ring)
      (fun r x f => by ext v; simp; ring)
      (fun x f f' => by ext v; simp; ring)
      (fun r x f => by ext v; simp; ring)

/-- The Chevalley–Eilenberg differential on multilinear cochains, defined recursively by the
Cartan formula `ι_x (d f) = x • f - d (ι_x f)`.-/
def ceDiff : (n : ℕ) → MCochain R 𝔤 n →ₗ[R] MCochain R 𝔤 (n + 1)
  | 0 => 0
  | n + 1 =>
    { toFun := fun f => (curryEquiv R 𝔤 (n + 1)).symm
        ((lieAct R 𝔤 (n + 1)).flip f - ceDiff n ∘ₗ curryEquiv R 𝔤 n f)
      map_add' := fun f g => by ext v; simp; ring
      map_smul' := fun r f => by ext v; simp; ring }

variable {R 𝔤}

/--
@isnad1 id=eq.0h6v.s13.7bc4207645c1 from=translated src=- shape=5acef19f vocab=38947f3e
-/
theorem curry_lieAct {n : ℕ} (x : 𝔤) (f : MCochain R 𝔤 (n + 1)) (y : 𝔤) :
    curryEquiv R 𝔤 n (lieAct R 𝔤 (n + 1) x f) y =
      lieAct R 𝔤 n x (curryEquiv R 𝔤 n f y) - curryEquiv R 𝔤 n f ⁅x, y⁆ := by
  ext v
  simp [lieAct]

/--
@isnad1 id=eq.0h5v.s13.c9bc2492189e from=translated src=- shape=efcbf1b0 vocab=2dee2d23
-/
theorem curry_ceDiff {n : ℕ} (f : MCochain R 𝔤 (n + 1)) (x : 𝔤) :
    curryEquiv R 𝔤 (n + 1) (ceDiff R 𝔤 (n + 1) f) x =
      lieAct R 𝔤 (n + 1) x f - ceDiff R 𝔤 n (curryEquiv R 𝔤 n f x) := by
  ext v
  simp [ceDiff]

/--
@isnad1 id=eq.0h4v.s11.36328c7c4abf from=translated src=- shape=923e809c vocab=6894fb9f
-/
@[simp] theorem lieAct_zero (x : 𝔤) (f : MCochain R 𝔤 0) : lieAct R 𝔤 0 x f = 0 := rfl

/--
@isnad1 id=eq.0h3v.s10.88b69bf7896f from=translated src=- shape=0b6ea87a vocab=687c3ee1
-/
@[simp] theorem ceDiff_zero (f : MCochain R 𝔤 0) : ceDiff R 𝔤 0 f = 0 := rfl

/-- The coadjoint action is a representation: `[x, y] • f = x • y • f - y • x • f`.
@isnad1 id=eq.0h6v.s13.9b09d714688f from=translated src=- shape=3b5f74eb vocab=2e79c535
-/
theorem lieAct_lie {n : ℕ} (x y : 𝔤) (f : MCochain R 𝔤 n) :
    lieAct R 𝔤 n ⁅x, y⁆ f =
      lieAct R 𝔤 n x (lieAct R 𝔤 n y f) - lieAct R 𝔤 n y (lieAct R 𝔤 n x f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine ext_curry fun z => ?_
    simp only [curry_lieAct, map_sub, LinearMap.sub_apply, ih]
    rw [leibniz_lie x y z]
    simp only [map_add]
    abel

/-- The differential commutes with the coadjoint action.
@isnad1 id=eq.0h5v.s13.70bb0d56d8c9 from=translated src=- shape=ebe04f09 vocab=7464f5dc
-/
theorem ceDiff_lieAct {n : ℕ} (x : 𝔤) (f : MCochain R 𝔤 n) :
    ceDiff R 𝔤 n (lieAct R 𝔤 n x f) = lieAct R 𝔤 (n + 1) x (ceDiff R 𝔤 n f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine ext_curry fun z => ?_
    simp only [curry_ceDiff, curry_lieAct, map_sub, ih, lieAct_lie]
    rw [← lie_skew x z]
    simp only [map_neg]
    abel

/-- `d ∘ d = 0` on multilinear cochains.
@isnad1 id=eq.0h4v.s11.704c812eb26c from=translated src=- shape=30b3f150 vocab=687c3ee1
-/
theorem ceDiff_ceDiff {n : ℕ} (f : MCochain R 𝔤 n) : ceDiff R 𝔤 (n + 1) (ceDiff R 𝔤 n f) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine ext_curry fun x => ?_
    simp only [curry_ceDiff, map_sub, ← ceDiff_lieAct, ih, map_zero]
    simp

/-- The coadjoint action on multilinear cochains:
`(x • f)(v₁, …, vₙ) = -∑ⱼ f (v₁, …, [x, vⱼ], …, vₙ)`.
@isnad1 id=eq.0h6v.s11.affd43779371 from=translated src=- shape=4f4ae731 vocab=20d0eb70
-/
theorem lieAct_apply {n : ℕ} (x : 𝔤) (f : MCochain R 𝔤 n) (v : Fin n → 𝔤) :
    lieAct R 𝔤 n x f v = -∑ j, f (Function.update v j ⁅x, v j⁆) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.cons_self_tail v]
    conv_lhs => rw [← curryEquiv_apply (lieAct R 𝔤 (n + 1) x f), curry_lieAct]
    rw [sub_apply, ih, Fin.sum_univ_succ]
    simp only [curryEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
      ← Fin.cons_update]
    abel

/-! ### Alternating cochains -/

/-- A multilinear cochain is alternating if it vanishes whenever two arguments coincide.-/
def IsAlt {n : ℕ} (f : MCochain R 𝔤 n) : Prop :=
  ∀ (v : Fin n → 𝔤) (i j : Fin n), v i = v j → i ≠ j → f v = 0

/--
@isnad1 id=isalt.0h3v.s6.66123e7897da from=translated src=- shape=acf24338 vocab=c68c034a
-/
theorem isAlt_zero {n : ℕ} : IsAlt (0 : MCochain R 𝔤 n) := fun _ _ _ _ _ => rfl

/--
@isnad1 id=isalt.2h5v.s7.be3a75915df2 from=translated src=- shape=8e100ce0 vocab=32db5128
-/
theorem IsAlt.sub {n : ℕ} {f g : MCochain R 𝔤 n} (hf : IsAlt f) (hg : IsAlt g) :
    IsAlt (f - g) := fun v i j h hij => by
  rw [sub_apply, hf v i j h hij, hg v i j h hij, sub_zero]

/--
@isnad1 id=isalt.0h4v.s6.b64dfefcd4fa from=translated src=- shape=a9ca6d61 vocab=c30bb591
-/
theorem isAlt_toMultilinearMap {n : ℕ} (ω : 𝔤 [⋀^Fin n]→ₗ[R] R) : IsAlt ω.toMultilinearMap :=
  fun v _ _ h hij => ω.map_eq_zero_of_eq v h hij

/--
@isnad1 id=isalt.1h5v.s11.ea5fd877c48d from=translated src=- shape=7f91e1d8 vocab=4e1012ed
-/
theorem IsAlt.curry {n : ℕ} {f : MCochain R 𝔤 (n + 1)} (hf : IsAlt f) (x : 𝔤) :
    IsAlt (curryEquiv R 𝔤 n f x) := fun v i j h hij => by
  rw [curryEquiv_apply]
  exact hf _ i.succ j.succ (by simpa using h) ((Fin.succ_injective _).ne hij)

/--
@isnad1 id=eq.1h5v.s12.09c7e49a7ad4 from=translated src=- shape=bd4a9e66 vocab=4e1012ed
-/
theorem IsAlt.curry_curry {n : ℕ} {f : MCochain R 𝔤 (n + 2)} (hf : IsAlt f) (x : 𝔤) :
    curryEquiv R 𝔤 n (curryEquiv R 𝔤 (n + 1) f x) x = 0 := by
  ext v
  exact hf _ 0 1 (by simp) Fin.zero_ne_one

/--
@isnad1 id=eq.2h7v.s7.8cded383ff7c from=translated src=- shape=15bec6b6 vocab=fa6779c7
-/
theorem IsAlt.map_swap {n : ℕ} {f : MCochain R 𝔤 n} (hf : IsAlt f) (v : Fin n → 𝔤) {i j : Fin n}
    (hij : i ≠ j) : f (v ∘ Equiv.swap i j) = -f v :=
  (⟨f, hf⟩ : 𝔤 [⋀^Fin n]→ₗ[R] R).map_swap v hij

/-- The coadjoint action preserves alternating cochains.
@isnad1 id=isalt.1h5v.s11.8b7ca03ae737 from=translated src=- shape=9fc44df9 vocab=1a678e2e
-/
theorem IsAlt.lieAct {n : ℕ} {f : MCochain R 𝔤 n} (hf : IsAlt f) (x : 𝔤) :
    IsAlt (lieAct R 𝔤 n x f) := fun v i j h hij => by
  rw [lieAct_apply, neg_eq_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [Finset.sum_eq_zero fun k hk => ?_, add_zero]
  · have key : f (Function.update v i ⁅x, v i⁆) = -f (Function.update v j ⁅x, v j⁆) := by
      rw [← hf.map_swap _ hij.symm]
      congr 1
      ext k
      rcases eq_or_ne k i with rfl | hki
      · simp [h]
      rcases eq_or_ne k j with rfl | hkj
      · simp [hij, hki, h]
      · simp [Equiv.swap_apply_of_ne_of_ne hkj hki, hki, hkj]
    rw [key, neg_add_cancel]
  · obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨hki, -⟩ := Finset.mem_erase.mp hk
    exact hf _ i j (by simp [hki.symm, hkj.symm, h]) hij

set_option backward.isDefEq.respectTransparency false in
/-- An alternating cochain vanishing whenever its first argument is `x` vanishes whenever any
argument is `x`.-/
theorem IsAlt.eq_zero_of_apply_eq {n : ℕ} {f : MCochain R 𝔤 (n + 1)} (hf : IsAlt f) {x : 𝔤}
    (hx : ∀ w : Fin n → 𝔤, f (Fin.cons x w) = 0) (v : Fin (n + 1) → 𝔤) (k : Fin (n + 1))
    (hk : v k = x) : f v = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [← Fin.cons_self_tail v, hk]
    exact hx _
  · rw [← neg_eq_zero, ← hf.map_swap v hk0.symm, ← Fin.cons_self_tail (v ∘ Equiv.swap 0 k)]
    convert hx (Fin.tail (v ∘ Equiv.swap 0 k))
    simp [hk]

/-- Uncurrying a family `φ` of alternating cochains with `φ x (…, x, …) = 0` gives an
alternating cochain.
@isnad1 id=isalt.2h4v.s12.0b17977b6b32 from=translated src=- shape=906b0e42 vocab=d2e3f588
-/
theorem isAlt_curryEquiv_symm {n : ℕ} (φ : 𝔤 →ₗ[R] MCochain R 𝔤 n) (h₁ : ∀ x, IsAlt (φ x))
    (h₂ : ∀ (x : 𝔤) (w : Fin n → 𝔤) (k : Fin n), w k = x → φ x w = 0) :
    IsAlt ((curryEquiv R 𝔤 n).symm φ) := fun v i j h hij => by
  rw [curryEquiv_symm_apply]
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ j => exact h₂ _ _ j (by simpa [Fin.tail] using h.symm)
  | succ i =>
    cases j using Fin.cases with
    | zero => exact h₂ _ _ i (by simpa [Fin.tail] using h)
    | succ j => exact h₁ _ _ i j (by simpa [Fin.tail] using h) (fun h' => hij (by rw [h']))

/-- The differential preserves alternating cochains.
@isnad1 id=isalt.1h4v.s9.3d23b2499951 from=translated src=- shape=68d452d0 vocab=680a6193
-/
theorem IsAlt.ceDiff {n : ℕ} {f : MCochain R 𝔤 n} (hf : IsAlt f) :
    IsAlt (ChevalleyEilenberg.ceDiff R 𝔤 n f) := by
  induction n with
  | zero => exact isAlt_zero
  | succ n ih =>
    change IsAlt ((curryEquiv R 𝔤 (n + 1)).symm _)
    refine isAlt_curryEquiv_symm _ (fun x => (hf.lieAct x).sub (ih (hf.curry x))) ?_
    intro x w k hk
    refine IsAlt.eq_zero_of_apply_eq ((hf.lieAct x).sub (ih (hf.curry x))) (fun u => ?_) w k hk
    rw [sub_apply, sub_eq_zero,
      ← curryEquiv_apply (ChevalleyEilenberg.lieAct R 𝔤 (n + 1) x f),
      curry_lieAct, lie_self, map_zero, sub_zero]
    cases n with
    | zero => simp
    | succ m =>
      rw [← curryEquiv_apply (ChevalleyEilenberg.ceDiff R 𝔤 (m + 1) _), curry_ceDiff,
        hf.curry_curry, map_zero,
        sub_zero]

/-! ### The Chevalley–Eilenberg complex -/

variable (R 𝔤)

/-- The Chevalley–Eilenberg `n`-cochains of `𝔤` with trivial coefficients: the alternating
`R`-multilinear maps `𝔤ⁿ → R`.-/
abbrev CECochain (n : ℕ) : Type _ := 𝔤 [⋀^Fin n]→ₗ[R] R

/-- The additive group structure of `CECochain R 𝔤 n`, registered for the abbreviation so that
instance search finds it when it arises by unification (e.g. for `⨁ n, CECochain R 𝔤 n`).-/
instance CECochain.instAddCommGroup (n : ℕ) : AddCommGroup (CECochain R 𝔤 n) :=
  AlternatingMap.instAddCommGroup

/-- The Chevalley–Eilenberg differential `Cⁿ(𝔤) → Cⁿ⁺¹(𝔤)`.-/
def ceD (n : ℕ) : CECochain R 𝔤 n →ₗ[R] CECochain R 𝔤 (n + 1) where
  toFun ω :=
    { toMultilinearMap := ceDiff R 𝔤 n ω.toMultilinearMap
      map_eq_zero_of_eq' := fun v i j h hij => (isAlt_toMultilinearMap ω).ceDiff v i j h hij }
  map_add' ω ω' := AlternatingMap.ext fun v => by simp [AlternatingMap.coe_add]
  map_smul' r ω := AlternatingMap.ext fun v => by simp [AlternatingMap.coe_smul]

variable {R 𝔤}

/--
@isnad1 id=eq.0h5v.s10.aac562e0e4dc from=translated src=- shape=bee2fe45 vocab=5089c43b
-/
theorem ceD_apply {n : ℕ} (ω : CECochain R 𝔤 n) (v : Fin (n + 1) → 𝔤) :
    ceD R 𝔤 n ω v = ceDiff R 𝔤 n ω.toMultilinearMap v := rfl

/-- `d ∘ d = 0` for the Chevalley–Eilenberg differential.
@isnad1 id=eq.0h4v.s10.e1e8ae01a774 from=translated src=- shape=30b3f150 vocab=7561d472
-/
theorem ceD_ceD {n : ℕ} (ω : CECochain R 𝔤 n) : ceD R 𝔤 (n + 1) (ceD R 𝔤 n ω) = 0 :=
  AlternatingMap.ext fun v => congrArg (fun f : MCochain R 𝔤 (n + 2) => f v) (ceDiff_ceDiff _)

/--
@isnad1 id=eq.0h3v.s9.faf97884784b from=translated src=- shape=0b6ea87a vocab=7561d472
-/
@[simp]
theorem ceD_zero (ω : CECochain R 𝔤 0) : ceD R 𝔤 0 ω = 0 := AlternatingMap.ext fun _ => rfl

/-- Moving the `i`-th argument of an alternating map to the front costs the sign `(-1)^i`.
@isnad1 id=eq.0h6v.s8.7ba5be708e64 from=translated src=- shape=b840adc0 vocab=daeca5ed
-/
theorem map_cons_removeNth {n : ℕ} (ω : CECochain R 𝔤 (n + 1)) (v : Fin (n + 1) → 𝔤)
    (i : Fin (n + 1)) :
    ω (Fin.cons (v i) (Fin.removeNth i v)) = koszulSign ((i : ℕ) : ℤ) • ω v := by
  have h : (Fin.cons (v i) (Fin.removeNth i v) : Fin (n + 1) → 𝔤) = v ∘ ⇑i.cycleRange.symm := by
    ext k
    cases k using Fin.cases with
    | zero => simp
    | succ k => simp [Fin.removeNth]
  rw [h, ω.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, koszulSign, Int.negOnePow_def,
    zpow_natCast]

/--
@isnad1 id=eq.0h7v.s8.d06db9406ecb from=translated src=- shape=7b9676c8 vocab=b90edb58
-/
theorem map_cons_cons_swap {n : ℕ} (ω : CECochain R 𝔤 (n + 2)) (a b : 𝔤) (w : Fin n → 𝔤) :
    ω (Fin.cons a (Fin.cons b w)) = -ω (Fin.cons b (Fin.cons a w)) := by
  rw [← ω.map_swap _ (i := 0) (j := 1) (by simp)]
  congr 1
  ext k
  cases k using Fin.cases with
  | zero => rfl
  | succ k =>
    cases k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
        rw [Ne, ← Fin.succ_zero_eq_one, Fin.succ_inj]; exact Fin.succ_ne_zero _)]
      simp only [Fin.cons_succ]

omit [LieRing 𝔤] in
/--
@isnad1 id=eq.0h5v.s7.51d843c7a975 from=translated src=- shape=ebcda25b vocab=ed6c37c2
-/
theorem removeNth_succ_cons {n : ℕ} (j : Fin (n + 1)) (a : 𝔤) (y : Fin (n + 1) → 𝔤) :
    Fin.removeNth j.succ (Fin.cons a y : Fin (n + 2) → 𝔤) = Fin.cons a (Fin.removeNth j y) := by
  ext k
  cases k using Fin.cases with
  | zero => simp [Fin.removeNth]
  | succ k => simp [Fin.removeNth, Fin.succ_succAbove_succ]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s11.33eed7adbcfc from=translated src=- shape=9f2dd161 vocab=bfccc34f
-/
theorem curryEquiv_toMultilinearMap {n : ℕ} (ω : CECochain R 𝔤 (n + 1)) (x : 𝔤) :
    curryEquiv R 𝔤 n ω.toMultilinearMap x = (ω.curryLeft x).toMultilinearMap := rfl

set_option backward.isDefEq.respectTransparency false in
/-- One step of the Chevalley–Eilenberg differential.
@isnad1 id=eq.0h6v.s11.b791e059cdc4 from=translated src=- shape=5e435410 vocab=4e6e92ed
-/
theorem ceD_cons {n : ℕ} (ω : CECochain R 𝔤 (n + 1)) (x₀ : 𝔤) (y : Fin (n + 1) → 𝔤) :
    ceD R 𝔤 (n + 1) ω (Fin.cons x₀ y) =
      -(∑ j : Fin (n + 1), koszulSign ((j : ℕ) : ℤ) • ω (Fin.cons ⁅x₀, y j⁆ (Fin.removeNth j y)))
        - ceD R 𝔤 n (ω.curryLeft x₀) y := by
  rw [ceD_apply, ← curryEquiv_apply, curry_ceDiff, sub_apply, lieAct_apply]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := map_cons_removeNth ω (Function.update y j ⁅x₀, y j⁆) j
  rw [Function.update_self, Fin.removeNth_update] at h
  rw [h, smul_smul, Int.units_mul_self, one_smul]
  rfl

private theorem ks_succ (k : ℕ) : koszulSign ((k + 1 : ℕ) : ℤ) = -koszulSign (k : ℤ) := by
  rw [Nat.cast_add, Nat.cast_one, koszulSign_add, koszulSign_odd odd_one, mul_neg_one]

set_option backward.isDefEq.respectTransparency false in
/-- The Chevalley–Eilenberg differential is given by the standard formula
`(d ω)(x₀, …, xₙ₊₁) = ∑_{i < j} (-1)^(i + j) ω([xᵢ, xⱼ], x₀, …, x̂ᵢ, …, x̂ⱼ, …, xₙ₊₁)`. Here
`Fin.removeNth i (Fin.removeNth j x)` is `x` with the entries `j` and then `i < j` removed.
@isnad1 id=eq.0h5v.s10.0bc24caafbe9 from=translated src=- shape=54b2cf72 vocab=15037085
-/
theorem ceD_apply_eq_sum {n : ℕ} (ω : CECochain R 𝔤 (n + 1)) (x : Fin (n + 2) → 𝔤) :
    ceD R 𝔤 (n + 1) ω x = ∑ j : Fin (n + 2), ∑ i : Fin (n + 1),
      if (i : ℕ) < j then koszulSign (((i : ℕ) + (j : ℕ) : ℕ) : ℤ) •
        ω (Fin.cons ⁅x i.castSucc, x j⁆ (Fin.removeNth i (Fin.removeNth j x))) else 0 := by
  induction n with
  | zero =>
    rw [← Fin.cons_self_tail x, ceD_cons, ceD_zero, AlternatingMap.zero_apply, sub_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, lt_irrefl,
      ite_false, zero_lt_one, ite_true, add_zero, zero_add, Fin.castSucc_zero, Fin.cons_zero,
      Fin.cons_succ, Nat.cast_zero, Nat.cast_one, koszulSign_zero, one_smul,
      koszulSign_odd odd_one, Units.neg_smul, Fin.tail]
    congr 3
  | succ m ih =>
    rw [← Fin.cons_self_tail x, ceD_cons, ih]
    generalize x 0 = x₀
    generalize Fin.tail x = y
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.not_lt_zero, ite_false, Finset.sum_const_zero, zero_add]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · rw [ite_eq_left (by simp), Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
        removeNth_succ_cons, Fin.removeNth_zero, Fin.tail_cons, Fin.val_zero, zero_add,
        Fin.val_succ, ks_succ, Units.neg_smul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show i.succ.castSucc = i.castSucc.succ from rfl, Fin.cons_succ, Fin.cons_succ,
        removeNth_succ_cons, removeNth_succ_cons, map_cons_cons_swap]
      simp only [Fin.val_succ, Nat.add_lt_add_iff_right]
      split_ifs
      · rw [show (i : ℕ) + 1 + ((j : ℕ) + 1) = (i + j + 1 : ℕ) + 1 by ring, ks_succ, ks_succ,
          neg_neg, smul_neg]
        rfl
      · rw [neg_zero]

/-! ### The complex and its cohomology -/

variable (R 𝔤)

/-- The Chevalley–Eilenberg complex of `𝔤` with trivial coefficients, as a cochain complex of
`R`-modules.-/
def ceComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (CECochain R 𝔤 n))
    (fun n => ModuleCat.ofHom (ceD R 𝔤 n)) fun n => by
      ext ω v
      exact congrArg (fun ω' : CECochain R 𝔤 (n + 2) => ω' v) (ceD_ceD ω)

/-- The Chevalley–Eilenberg cocycles `Zⁿ(𝔤)`.-/
def ceCocycles (n : ℕ) : Submodule R (CECochain R 𝔤 n) := LinearMap.ker (ceD R 𝔤 n)

/-- The Chevalley–Eilenberg coboundaries `Bⁿ(𝔤)` (zero for `n = 0`).-/
def ceCoboundaries : (n : ℕ) → Submodule R (CECochain R 𝔤 n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (ceD R 𝔤 n)

/--
@isnad1 id=le.0h3v.s8.b7307ed22a51 from=translated src=- shape=b888778f vocab=60d58954
-/
theorem ceCoboundaries_le_ceCocycles (n : ℕ) : ceCoboundaries R 𝔤 n ≤ ceCocycles R 𝔤 n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨ω, rfl⟩
    exact ceD_ceD ω

/- Instance search no longer finds `AddCommGroup (ceCocycles R 𝔤 n)` when it arises by
unification (the `Module R R` instances of the codomain do not unify), so the quotient below
needs it as an explicit local instance. -/
local instance (n : ℕ) : AddCommGroup (ceCocycles R 𝔤 n) := Submodule.addCommGroup _

set_option backward.isDefEq.respectTransparency false in
/-- The Lie algebra cohomology `Hⁿ(𝔤, R) = Zⁿ(𝔤) / Bⁿ(𝔤)` with trivial coefficients.-/
abbrev CECohomology (n : ℕ) : Type _ :=
  ceCocycles R 𝔤 n ⧸ (ceCoboundaries R 𝔤 n).comap (ceCocycles R 𝔤 n).subtype

/--
@isnad1 id=eq.0h2v.s11.c871174a3f39 from=translated src=- shape=f753fc77 vocab=eacf65ed
-/
theorem comap_ceCoboundaries_zero :
    (ceCoboundaries R 𝔤 0).comap (ceCocycles R 𝔤 0).subtype = ⊥ := by
  show Submodule.comap _ ⊥ = ⊥
  rw [Submodule.comap_bot, Submodule.ker_subtype]

/--
@isnad1 id=eq.0h2v.s11.1c9be7b6c273 from=translated src=- shape=f753fc77 vocab=eacf65ed
-/
theorem comap_ceCoboundaries_one :
    (ceCoboundaries R 𝔤 1).comap (ceCocycles R 𝔤 1).subtype = ⊥ := by
  have h : ceCoboundaries R 𝔤 1 = ⊥ := by
    show LinearMap.range (ceD R 𝔤 0) = ⊥
    rw [LinearMap.range_eq_bot]
    exact LinearMap.ext ceD_zero
  rw [h, Submodule.comap_bot, Submodule.ker_subtype]

set_option backward.isDefEq.respectTransparency false in
/-- `H⁰(𝔤, R) ≅ R`.-/
def ceCohomologyZeroEquiv : CECohomology R 𝔤 0 ≃ₗ[R] R :=
  (Submodule.quotEquivOfEqBot _ (comap_ceCoboundaries_zero R 𝔤)).trans <|
    (LinearEquiv.ofTop _ (LinearMap.ker_eq_top.mpr (LinearMap.ext ceD_zero))).trans
      (AlternatingMap.constLinearEquivOfIsEmpty (M'' := 𝔤) (ι := Fin 0)).symm

/-- `1`-cochains are linear forms.-/
def cochainOneEquiv : CECochain R 𝔤 1 ≃ₗ[R] Module.Dual R 𝔤 where
  toFun ω := ω.toMultilinearMap.toLinearMap (fun _ => 0) 0
  invFun φ := AlternatingMap.ofSubsingleton R 𝔤 R (0 : Fin 1) φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := AlternatingMap.ext fun v => by
    simp only [AlternatingMap.ofSubsingleton_apply_apply, MultilinearMap.toLinearMap_apply]
    exact congrArg ω (funext fun i => by fin_cases i; rfl)
  right_inv φ := LinearMap.ext fun x => by simp

variable {R 𝔤}

/--
@isnad1 id=eq.0h4v.s10.68266a77427c from=translated src=- shape=70aea4bd vocab=15b1f471
-/
@[simp]
theorem cochainOneEquiv_apply (ω : CECochain R 𝔤 1) (x : 𝔤) :
    cochainOneEquiv R 𝔤 ω x = ω ![x] := by
  simp only [cochainOneEquiv, LinearEquiv.coe_mk]
  exact congrArg ω (funext fun i => by fin_cases i; rfl)

/--
@isnad1 id=eq.0h4v.s10.a11633a808a9 from=translated src=- shape=f44d05cc vocab=a89322bd
-/
@[simp]
theorem cochainOneEquiv_symm_apply (φ : Module.Dual R 𝔤) (v : Fin 1 → 𝔤) :
    (cochainOneEquiv R 𝔤).symm φ v = φ (v 0) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s9.a94d3122caff from=translated src=- shape=d95e0787 vocab=dd72fa85
-/
theorem ceD_one_apply (ω : CECochain R 𝔤 1) (x y : 𝔤) :
    ceD R 𝔤 1 ω ![x, y] = -ω ![⁅x, y⁆] := by
  rw [show (![x, y] : Fin 2 → 𝔤) = Fin.cons x ![y] from rfl, ceD_cons, ceD_zero,
    AlternatingMap.zero_apply, sub_zero, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.cast_zero, koszulSign_zero, one_smul]
  congr 2

/-- A `1`-cochain is a cocycle if and only if it vanishes on brackets.
@isnad1 id=iff.0h3v.s9.f1934b5f8694 from=translated src=- shape=2a14f232 vocab=d9e58ab6
-/
theorem mem_ceCocycles_one {ω : CECochain R 𝔤 1} :
    ω ∈ ceCocycles R 𝔤 1 ↔ ∀ x y : 𝔤, ω ![⁅x, y⁆] = 0 := by
  constructor
  · intro h x y
    have := congrArg (fun ω' : CECochain R 𝔤 2 => ω' ![x, y]) (LinearMap.mem_ker.mp h)
    simpa [ceD_one_apply] using this
  · intro h
    refine LinearMap.mem_ker.mpr (AlternatingMap.ext fun v => ?_)
    rw [show v = ![v 0, v 1] from funext fun i => by fin_cases i <;> rfl, ceD_one_apply, h,
      neg_zero, AlternatingMap.zero_apply]

variable (R 𝔤) in
/-- The derived subalgebra `[𝔤, 𝔤]`, as a submodule.-/
abbrev derivedSubmodule : Submodule R 𝔤 :=
  LieSubmodule.toSubmodule (⁅(⊤ : LieIdeal R 𝔤), ⊤⁆ : LieIdeal R 𝔤)

/--
@isnad1 id=iff.0h3v.s9.86b345f953a9 from=translated src=- shape=f6527f9d vocab=0cf4350a
-/
theorem mem_dualAnnihilator_derivedSubmodule (φ : Module.Dual R 𝔤) :
    φ ∈ (derivedSubmodule R 𝔤).dualAnnihilator ↔ ∀ x y : 𝔤, φ ⁅x, y⁆ = 0 := by
  unfold derivedSubmodule
  rw [Submodule.mem_dualAnnihilator, LieSubmodule.lieIdeal_oper_eq_linear_span]
  constructor
  · intro h x y
    exact h _ (Submodule.subset_span ⟨⟨x, trivial⟩, ⟨y, trivial⟩, rfl⟩)
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, y, rfl⟩ := hw
      exact h x y
    | zero => exact map_zero φ
    | add w w' _ _ hw hw' => rw [map_add, hw, hw', add_zero]
    | smul r w _ hw => rw [map_smul, hw, smul_zero]

set_option backward.isDefEq.respectTransparency false in
variable (R 𝔤) in
/-- `H¹(𝔤, R) ≅ (𝔤 / [𝔤, 𝔤])^*`.-/
def ceCohomologyOneEquiv : CECohomology R 𝔤 1 ≃ₗ[R] Module.Dual R (𝔤 ⧸ derivedSubmodule R 𝔤) :=
  (Submodule.quotEquivOfEqBot _ (comap_ceCoboundaries_one R 𝔤)).trans <|
    (LinearEquiv.ofSubmodules (cochainOneEquiv R 𝔤) _ _ (by
      ext φ
      rw [mem_dualAnnihilator_derivedSubmodule, Submodule.mem_map_equiv, mem_ceCocycles_one]
      simp only [cochainOneEquiv_symm_apply, Matrix.cons_val_zero])).trans
      (Submodule.dualQuotEquivDualAnnihilator _).symm

end DG.ChevalleyEilenberg
