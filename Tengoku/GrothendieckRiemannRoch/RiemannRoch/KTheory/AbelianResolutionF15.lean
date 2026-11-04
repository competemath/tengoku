/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.CategoryTheory.Abelian.Basic
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.ExactCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Resolution theorem for `K₀` in an abstract abelian category (route F15)

A sheaf-friendly version of `KTheory/ModuleResolution.lean` which needs **no projective objects**
and no horseshoe lemma.  Let `C` be abelian, `Q ⊇ P` two full classes of objects ("coherent" and
"vector bundles") such that
* `P` is closed under extensions, kernels of epis between members, isomorphisms, contains zero,
* `Q` is closed under kernels and pullbacks and every `Q`-object is a quotient of a `P`-object.

Suppose every `Q`-object has "bundle dimension `≤ d`" (every `d`-th syzygy lies in `P`).  Then
`K₀(P) → K₀(Q)` is bijective (`AbelianResolutionF15.k0ToG0_bijective`).

The key point is that additivity of the resolution Euler characteristic is proved *only* from the
independence of the chosen cover (a Schanuel-type statement via the pullback of two covers)
by a two-step pullback / pullback trick (`add_succ`).  Everything is phrased with explicit short
exact sequences `SES i g`, so no kernel objects or comparison isomorphisms are needed.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AbelianResolutionF15

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Explicit short exact sequences -/

/-- `0 → K → E → M → 0` is short exact (explicit maps).-/
structure SES {K E M : C} (i : K ⟶ E) (g : E ⟶ M) : Prop where
  /-- composition vanishes-/
  zero : i ≫ g = 0
  /-- short exactness-/
  exact : (ShortComplex.mk i g zero).ShortExact

namespace SES

variable {K E M : C} {i : K ⟶ E} {g : E ⟶ M}

/--
@isnad1 id=mono.1h6v.s5.efce9f430070 from=translated src=- shape=c561e46e vocab=7bb3f261
-/
theorem mono (h : SES i g) : Mono i := h.exact.mono_f

/--
@isnad1 id=epi.1h6v.s5.8bf4cb4e9b0e from=translated src=- shape=b2e729ef vocab=9a40b0fb
-/
theorem epi (h : SES i g) : Epi g := h.exact.epi_g

/-- Morphisms killed by `g` factor through `i`.
@isnad1 id=ex.2h8v.s7.12664dbd562c from=translated src=- shape=a35f0762 vocab=7ec196fe
-/
theorem lift_exists (h : SES i g) {T : C} (k : T ⟶ E) (hk : k ≫ g = 0) :
    ∃ u : T ⟶ K, u ≫ i = k := by
  haveI := h.mono
  have hK := h.exact.exact.fIsKernel
  exact ⟨hK.lift (KernelFork.ofι k hk), hK.fac (KernelFork.ofι k hk) .zero⟩

/-- Chosen factorisation.-/
def liftSub (h : SES i g) {T : C} (k : T ⟶ E) (hk : k ≫ g = 0) : {u : T ⟶ K // u ≫ i = k} :=
  ⟨(h.lift_exists k hk).choose, (h.lift_exists k hk).choose_spec⟩

/-- Build a short exact sequence from a kernel fork that is a limit and an epi.
@isnad1 id=ses.1h7v.s7.58258953702e from=translated src=- shape=79c6d84c vocab=16388b02
-/
theorem ofKernel (zero : i ≫ g = 0) [Epi g] (hK : IsLimit (KernelFork.ofι i zero)) : SES i g :=
  ⟨zero, ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hK)
    (Limits.mono_of_isLimit_fork hK) inferInstance⟩

/-- Transport along an isomorphism of the third term.
@isnad1 id=ses.1h8v.s6.147387e373c7 from=translated src=- shape=e6e69286 vocab=1d5a0aa0
-/
theorem ofIsoRight (h : SES i g) {M' : C} (e : M ≅ M') : SES i (g ≫ e.hom) := by
  refine ⟨by rw [← Category.assoc, h.zero, zero_comp], ?_⟩
  have hiso : ShortComplex.mk i g h.zero ≅ ShortComplex.mk i (g ≫ e.hom)
      (by rw [← Category.assoc, h.zero, zero_comp]) :=
    ShortComplex.isoMk (Iso.refl K) (Iso.refl E) e (by simp) (by simp)
  exact ShortComplex.shortExact_of_iso hiso h.exact

/-- The kernel of an epimorphism.
@isnad1 id=ses.0h4v.s6.3e9eb085c531 from=translated src=- shape=f04f793e vocab=7c1b4cfb
-/
theorem kernel_of_epi (g : E ⟶ M) [Epi g] : SES (kernel.ι g) g :=
  ⟨kernel.condition g, ⟨ShortComplex.exact_kernel g⟩⟩

/-- Pullback of a short exact sequence along `f : X ⟶ M` (right-hand copy).
@isnad1 id=ses.1h8v.s6.a63ff9e065ba from=translated src=- shape=d2ea294a vocab=0ae0a5c8
-/
theorem pullbackR (h : SES i g) {X : C} (f : X ⟶ M) :
    SES (pullback.lift (0 : K ⟶ X) i (by rw [zero_comp, h.zero])) (pullback.fst f g) := by
  haveI := h.mono
  haveI := h.epi
  haveI : Mono (pullback.lift (f := f) (g := g) (0 : K ⟶ X) i (by rw [zero_comp, h.zero])) :=
    mono_of_mono_fac (pullback.lift_snd (f := f) (g := g) _ _ _)
  have hz : pullback.lift (f := f) (g := g) (0 : K ⟶ X) i (by rw [zero_comp, h.zero]) ≫
      pullback.fst f g = 0 :=
    pullback.lift_fst _ _ _
  refine ofKernel hz (KernelFork.IsLimit.ofι' _ hz ?_)
  intro T k hk
  have hk' : (k ≫ pullback.snd f g) ≫ g = 0 := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk, zero_comp]
  refine ⟨(h.liftSub _ hk').1, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, comp_zero, hk]
  · rw [Category.assoc, pullback.lift_snd]
    exact (h.liftSub _ hk').2

/-- Pullback of a short exact sequence along `f : X ⟶ M` (left-hand copy).
@isnad1 id=ses.1h8v.s6.61bc85de069f from=translated src=- shape=abe1257e vocab=f22e6b2e
-/
theorem pullbackL (h : SES i g) {X : C} (f : X ⟶ M) :
    SES (pullback.lift i (0 : K ⟶ X) (by rw [zero_comp, h.zero])) (pullback.snd g f) := by
  haveI := h.mono
  haveI := h.epi
  haveI : Mono (pullback.lift (f := g) (g := f) i (0 : K ⟶ X) (by rw [zero_comp, h.zero])) :=
    mono_of_mono_fac (pullback.lift_fst (f := g) (g := f) _ _ _)
  have hz : pullback.lift (f := g) (g := f) i (0 : K ⟶ X) (by rw [zero_comp, h.zero]) ≫
      pullback.snd g f = 0 :=
    pullback.lift_snd _ _ _
  refine ofKernel hz (KernelFork.IsLimit.ofι' _ hz ?_)
  intro T k hk
  have hk' : (k ≫ pullback.fst g f) ≫ g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
  refine ⟨(h.liftSub _ hk').1, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact (h.liftSub _ hk').2
  · rw [Category.assoc, pullback.lift_snd, comp_zero, hk]

/-- Pull back the first term along an epimorphism `a : X ⟶ E`: the kernel of `a ≫ g`.
@isnad1 id=ses.1h8v.s6.4dad17e7deed from=translated src=- shape=bfbf9900 vocab=532f601b
-/
theorem comp (h : SES i g) {X : C} (a : X ⟶ E) [Epi a] :
    SES (pullback.snd i a) (a ≫ g) := by
  haveI := h.mono
  haveI := h.epi
  have hz : pullback.snd i a ≫ a ≫ g = 0 := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, h.zero, comp_zero]
  refine ofKernel hz (KernelFork.IsLimit.ofι' _ hz ?_)
  intro T k hk
  have hk' : (k ≫ a) ≫ g = 0 := by rw [Category.assoc, hk]
  exact ⟨pullback.lift (h.liftSub _ hk').1 k (h.liftSub _ hk').2, pullback.lift_snd _ _ _⟩

/-- A short exact sequence with zero left term and identity right map.
@isnad1 id=ses.1h3v.s6.65ffad7a9885 from=translated src=- shape=4877fd59 vocab=c21ffe54
-/
theorem zeroId {K : C} (hK : IsZero K) (E : C) : SES (0 : K ⟶ E) (𝟙 E) := by
  haveI : Mono (0 : K ⟶ E) := hK.mono _
  refine ⟨by simp, ?_⟩
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_mono (ShortComplex.mk (0 : K ⟶ E) (𝟙 E) (by simp)) rfl).2
      (inferInstance : Mono (𝟙 E))) inferInstance inferInstance

end SES

/-! ## The abstract setup -/

/-- Axioms: `P ⊆ Q` full classes of objects with the closure properties used below.-/
structure Setup (C : Type u) [Category.{v} C] [Abelian C] where
  /-- vector bundles-/
  P : C → Prop
  /-- coherent sheaves-/
  Q : C → Prop
  P_iso : ∀ {A B : C}, (A ≅ B) → P A → P B
  P_Q : ∀ {A : C}, P A → Q A
  P_zero : ∀ {Z : C}, IsZero Z → P Z
  P_ext : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → P A → P D → Q B → P B
  P_ker : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → P B → P D → Q A → P A
  Q_kernel : ∀ {A B : C} (f : A ⟶ B), Q A → Q B → Q (kernel f)
  Q_pullback : ∀ {A B D : C} (f : A ⟶ D) (g : B ⟶ D), Q A → Q B → Q D → Q (pullback f g)
  cover : ∀ {M : C}, Q M → ∃ (E : C) (g : E ⟶ M), P E ∧ Epi g

variable (S : Setup C)

/-- `K₀` of the class `P`.-/
abbrev K0 := ExactGrothendieck.SubcategoryGroup C S.P

/-- `G₀` of the class `Q`.-/
abbrev G0 := ExactGrothendieck.SubcategoryGroup C S.Q

/-- Class in `K₀`.-/
def cls (E : C) (h : S.P E) : K0 S := ExactGrothendieck.subcategoryClassOf C S.P E h

/-- Class in `G₀`.-/
def gcl (E : C) (h : S.Q E) : G0 S := ExactGrothendieck.subcategoryClassOf C S.Q E h

/-- `Syz S n Z M`: `Z` is an `n`-th syzygy of `M` along `P`-covers with `Q` kernels.-/
def Syz : ℕ → C → C → Prop
  | 0, Z, M => Nonempty (Z ≅ M)
  | n + 1, Z, M => ∃ (K E : C) (i : K ⟶ E) (g : E ⟶ M), SES i g ∧ S.P E ∧ S.Q K ∧ Syz n Z K

/-- Every `n`-th syzygy of `M` is in `P`.-/
def PdLE (n : ℕ) (M : C) : Prop := ∀ Z, Syz S n Z M → S.P Z

/-- `x ∈ K₀` is the Euler class of an `n`-step `P`-resolution of `M` truncated at a `P`-syzygy.-/
def Rep : ℕ → C → K0 S → Prop
  | 0, M, x => ∃ h : S.P M, x = cls S M h
  | n + 1, M, x => ∃ (K E : C) (i : K ⟶ E) (g : E ⟶ M) (y : K0 S), SES i g ∧
      ∃ h : S.P E, S.Q K ∧ Rep n K y ∧ x = cls S E h - y

/--
@isnad1 id=syz.1h7v.s5.c3ace9b6c0bf from=translated src=- shape=53502305 vocab=ed7c6b9b
-/
theorem Syz.ofIsoRight {n : ℕ} {Z M M' : C} (h : Syz S n Z M) (e : M ≅ M') : Syz S n Z M' := by
  cases n with
  | zero => obtain ⟨e1⟩ := h; exact ⟨e1 ≪≫ e⟩
  | succ n =>
    obtain ⟨K, E, i, g, hs, hE, hK, hZ⟩ := h
    exact ⟨K, E, i, g ≫ e.hom, hs.ofIsoRight e, hE, hK, hZ⟩

/--
@isnad1 id=pdle.1h6v.s5.03105e086d98 from=translated src=- shape=3b438db6 vocab=94053b69
-/
theorem PdLE.iso {n : ℕ} {M M' : C} (h : PdLE S n M) (e : M ≅ M') : PdLE S n M' :=
  fun Z hZ => h Z (hZ.ofIsoRight S e.symm)

/--
@isnad1 id=iff.0h3v.s5.7635fe1cc53c from=translated src=- shape=9075c4aa vocab=7465f47f
-/
theorem pdLE_zero_iff {M : C} : PdLE S 0 M ↔ S.P M := by
  constructor
  · intro h; exact h M ⟨Iso.refl M⟩
  · rintro h Z ⟨e⟩; exact S.P_iso e.symm h

/--
@isnad1 id=pdle.4h8v.s6.aa0eb17948aa from=translated src=- shape=016126d3 vocab=ca1d6764
-/
theorem PdLE.ker {n : ℕ} {M K E : C} {i : K ⟶ E} {g : E ⟶ M} (h : PdLE S (n + 1) M)
    (hs : SES i g) (hE : S.P E) (hK : S.Q K) : PdLE S n K :=
  fun Z hZ => h Z ⟨K, E, i, g, hs, hE, hK, hZ⟩

/--
@isnad1 id=pdle.1h4v.s5.939b1a4e3c6a from=translated src=- shape=e8d64e03 vocab=7465f47f
-/
theorem pdLE_of_P : ∀ (n : ℕ) (E : C), S.P E → PdLE S n E := by
  intro n
  induction n with
  | zero => intro E hE; exact (pdLE_zero_iff S).2 hE
  | succ n ih =>
    intro E hE Z hZ
    obtain ⟨K, E1, i, g, hs, hE1, hK, hZ⟩ := hZ
    exact ih K (S.P_ker hs hE1 hE hK) Z hZ

/-- An extension of a bundle by an object of bundle dimension `≤ n` has bundle dimension `≤ n`.
@isnad1 id=pdle.5h8v.s6.e342056ec0b3 from=translated src=- shape=6cb89e97 vocab=b7426f15
-/
theorem pdLE_ext {n : ℕ} {K P0 E : C} {i : K ⟶ P0} {g : P0 ⟶ E} (hs : SES i g) (hE : S.P E)
    (hK : S.Q K) (hP0 : S.Q P0) (hpd : PdLE S n K) : PdLE S n P0 := by
  cases n with
  | zero =>
    rw [pdLE_zero_iff] at hpd ⊢
    exact S.P_ext hs hpd hE hP0
  | succ m =>
    intro Z hZ
    obtain ⟨K1, H, i1, a, hs1, hH, hK1, hZ1⟩ := hZ
    haveI := hs1.epi
    have hQH := S.P_Q hH
    have hQV : S.Q (pullback i a) := S.Q_pullback i a hK hQH hP0
    have sV1 := hs1.pullbackR i
    have sV2 := hs.comp a
    have hV : S.P (pullback i a) := S.P_ker sV2 hH hE hQV
    exact hpd Z ⟨K1, pullback i a, _, _, sV1, hV, hK1, hZ1⟩

/--
@isnad1 id=ex.2h4v.s5.00e01461d1be from=translated src=- shape=93608042 vocab=7821fd16
-/
theorem exists_rep : ∀ (n : ℕ) (M : C), S.Q M → PdLE S n M → ∃ x, Rep S n M x := by
  intro n
  induction n with
  | zero =>
    intro M _ hpd
    have hP := (pdLE_zero_iff S).1 hpd
    exact ⟨cls S M hP, hP, rfl⟩
  | succ n ih =>
    intro M hQ hpd
    obtain ⟨E, g, hE, hepi⟩ := S.cover hQ
    haveI := hepi
    have hs := SES.kernel_of_epi g
    have hQK := S.Q_kernel g (S.P_Q hE) hQ
    obtain ⟨y, hy⟩ := ih (kernel g) hQK (hpd.ker S hs hE hQK)
    exact ⟨cls S E hE - y, kernel g, E, kernel.ι g, g, y, hs, hE, hQK, hy, rfl⟩

/--
@isnad1 id=rep.1h4v.s7.7b987f4778e8 from=translated src=- shape=020528fb vocab=181badd5
-/
theorem rep_zero : ∀ (n : ℕ) (Z : C), IsZero Z → Rep S n Z 0 := by
  intro n
  induction n with
  | zero =>
    intro Z hZ
    exact ⟨S.P_zero hZ, (ExactGrothendieck.subcategoryClassOf_isZero C S.P (S.P_zero hZ) hZ).symm⟩
  | succ n ih =>
    intro Z hZ
    refine ⟨Z, Z, 0, 𝟙 Z, 0, SES.zeroId hZ Z, S.P_zero hZ, S.P_Q (S.P_zero hZ), ih Z hZ, ?_⟩
    rw [sub_zero]
    exact (ExactGrothendieck.subcategoryClassOf_isZero C S.P (S.P_zero hZ) hZ).symm

/--
@isnad1 id=rep.1h4v.s5.e9151d347e76 from=translated src=- shape=f4d7ca8f vocab=73ace78e
-/
theorem rep_bundle : ∀ (n : ℕ) (E : C) (hE : S.P E), Rep S n E (cls S E hE) := by
  intro n
  induction n with
  | zero => intro E hE; exact ⟨hE, rfl⟩
  | succ n ih =>
    intro E hE
    have h0 : IsZero (0 : C) := isZero_zero C
    exact ⟨0, E, 0, 𝟙 E, 0, SES.zeroId h0 E, hE, S.P_Q (S.P_zero h0), rep_zero S n 0 h0,
      (sub_zero _).symm⟩

/-- Uniqueness of the Euler class at level `n`.-/
def Uniq (n : ℕ) : Prop :=
  ∀ M : C, S.Q M → PdLE S n M → ∀ x y, Rep S n M x → Rep S n M y → x = y

/-- Additivity at level `n`.-/
def Add (n : ℕ) : Prop :=
  ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → S.Q A → S.Q B → S.Q D →
    PdLE S n A → PdLE S n B → PdLE S n D → ∀ {x y z : K0 S},
      Rep S n A x → Rep S n B y → Rep S n D z → y = x + z

/--
@isnad1 id=uniq.0h2v.s4.0afe845ced93 from=translated src=- shape=59365f29 vocab=705409b0
-/
theorem uniq_zero : Uniq S 0 := by
  rintro M _ _ x y ⟨h1, rfl⟩ ⟨h2, rfl⟩
  rfl

/--
@isnad1 id=add.0h2v.s4.32271725b103 from=translated src=- shape=59365f29 vocab=2f62813d
-/
theorem add_zero_level : Add S 0 := by
  rintro A B D i g hs _ _ _ _ _ _ x y z ⟨hA, rfl⟩ ⟨hB, rfl⟩ ⟨hD, rfl⟩
  exact ExactGrothendieck.subcategoryClassOf_middle C S.P hA hB hD hs.zero hs.exact

/--
@isnad1 id=uniq.1h3v.s5.f8ef29ea8195 from=translated src=- shape=a23a0ce8 vocab=6ab9f162
-/
theorem uniq_succ {n : ℕ} (hA : Add S n) : Uniq S (n + 1) := by
  rintro M hQM hM x x' ⟨K, E, i, g, y, hs, hE, hK, hy, rfl⟩ ⟨K', E', i', g', y', hs', hE', hK', hy', rfl⟩
  haveI := hs.epi
  haveI := hs'.epi
  have hQE := S.P_Q hE
  have hQE' := S.P_Q hE'
  have hQP : S.Q (pullback g' g) := S.Q_pullback g' g hQE' hQE hQM
  have ses1 := hs.pullbackR g'
  have ses2 := hs'.pullbackL g
  have hpdP : PdLE S n (pullback g' g) := pdLE_ext S ses1 hE' hK hQP (hM.ker S hs hE hK)
  obtain ⟨yP, hyP⟩ := exists_rep S n _ hQP hpdP
  have h1 := hA ses1 hK hQP hQE' (hM.ker S hs hE hK) hpdP (pdLE_of_P S n _ hE') hy hyP
    (rep_bundle S n E' hE')
  have h2 := hA ses2 hK' hQP hQE (hM.ker S hs' hE' hK') hpdP (pdLE_of_P S n _ hE) hy' hyP
    (rep_bundle S n E hE)
  have h3 : y + cls S E' hE' = y' + cls S E hE := h1.symm.trans h2
  calc cls S E hE - y = (y' + cls S E hE) - (y' + y) := by abel
    _ = (y + cls S E' hE') - (y' + y) := by rw [h3]
    _ = cls S E' hE' - y' := by abel

/--
@isnad1 id=add.2h3v.s5.7c8cd4938034 from=translated src=- shape=5a1e8d5e vocab=6ab9f162
-/
theorem add_succ {n : ℕ} (hA : Add S n) (hU : Uniq S (n + 1)) : Add S (n + 1) := by
  intro A B D i g hs hQA hQB hQD hpA hpB hpD xA xB xD hxA hxB hxD
  -- a cover of `D`
  obtain ⟨EC, ρ, hEC, hρ⟩ := S.cover hQD
  haveI := hρ
  have sC := SES.kernel_of_epi ρ
  have hQKC := S.Q_kernel ρ (S.P_Q hEC) hQD
  -- the pullback `B' = EC ×_D B`
  have s1 := hs.pullbackR ρ
  have s2 := sC.pullbackL g
  have hQB' : S.Q (pullback ρ g) := S.Q_pullback ρ g (S.P_Q hEC) hQB hQD
  obtain ⟨H, a, hH, ha⟩ := S.cover hQB'
  haveI := ha
  have sa := SES.kernel_of_epi a
  have hQK' := S.Q_kernel a (S.P_Q hH) hQB'
  -- `V = A ×_{B'} H`
  have sV1 := sa.pullbackR (pullback.lift (0 : A ⟶ EC) i (by rw [zero_comp, hs.zero]))
  have sV2 := s1.comp a
  have hV : S.P (pullback (pullback.lift (0 : A ⟶ EC) i (by rw [zero_comp, hs.zero])) a) :=
    S.P_ker sV2 hH hEC (S.Q_pullback _ a hQA (S.P_Q hH) hQB')
  -- `W = K_C ×_{B'} H`
  have sW1 := sa.pullbackR (pullback.lift (kernel.ι ρ) (0 : kernel ρ ⟶ B) (by
    rw [zero_comp, sC.zero]))
  have sW2 := s2.comp a
  have hQW : S.Q (pullback (pullback.lift (kernel.ι ρ) (0 : kernel ρ ⟶ B) (by
      rw [zero_comp, sC.zero])) a) :=
    S.Q_pullback _ a hQKC (S.P_Q hH) hQB'
  -- `n`-step data
  have hpK' : PdLE S n (kernel a) := by
    intro Z hZ
    exact hpA Z ⟨kernel a, _, _, _, sV1, hV, hQK', hZ⟩
  have hpW := hpB.ker S sW2 hH hQW
  have hpKC := hpD.ker S sC hEC hQKC
  obtain ⟨yK, hyK⟩ := exists_rep S n _ hQK' hpK'
  obtain ⟨yW, hyW⟩ := exists_rep S n _ hQW hpW
  obtain ⟨yC, hyC⟩ := exists_rep S n _ hQKC hpKC
  have hadd := hA sW1 hQK' hQW hQKC hpK' hpW hpKC hyK hyW hyC
  have RA : Rep S (n + 1) A (cls S _ hV - yK) := ⟨kernel a, _, _, _, yK, sV1, hV, hQK', hyK, rfl⟩
  have RB : Rep S (n + 1) B (cls S H hH - yW) := ⟨_, H, _, _, yW, sW2, hH, hQW, hyW, rfl⟩
  have RC : Rep S (n + 1) D (cls S EC hEC - yC) := ⟨_, EC, _, ρ, yC, sC, hEC, hQKC, hyC, rfl⟩
  have eA := hU A hQA hpA _ _ hxA RA
  have eB := hU B hQB hpB _ _ hxB RB
  have eD := hU D hQD hpD _ _ hxD RC
  have hrel := ExactGrothendieck.subcategoryClassOf_middle C S.P hV hH hEC sV2.zero sV2.exact
  change cls S H hH = cls S _ hV + cls S EC hEC at hrel
  rw [eA, eB, eD, hadd, hrel]
  abel

/--
@isnad1 id=and.0h3v.s4.a1b37a9509f1 from=translated src=- shape=c5b54d44 vocab=5b657865
-/
theorem add_uniq_all : ∀ n, Add S n ∧ Uniq S n
  | 0 => ⟨add_zero_level S, uniq_zero S⟩
  | n + 1 => by
      obtain ⟨h1, -⟩ := add_uniq_all n
      have hU := uniq_succ S h1
      exact ⟨add_succ S h1 hU, hU⟩

/-! ## The comparison map and the resolution theorem -/

/-- Forget that a `P`-object is in `P`.-/
def toQ (E : {E : C // S.P E}) : {E : C // S.Q E} := ⟨E.1, S.P_Q E.2⟩

/-- The forgetful comparison `K₀ → G₀`.-/
def k0ToG0 : K0 S →+ G0 S :=
  ExactGrothendieck.map (toQ S) (fun _ _ _ h => h)

/--
@isnad1 id=eq.1h3v.s8.b81035dd3b52 from=translated src=- shape=04d63165 vocab=cfa672c6
-/
theorem k0ToG0_cls (E : C) (h : S.P E) : k0ToG0 S (cls S E h) = gcl S E (S.P_Q h) :=
  ExactGrothendieck.map_classOf (toQ S) (fun _ _ _ h => h) ⟨E, h⟩

/--
@isnad1 id=eq.2h5v.s8.12171c0b85de from=translated src=- shape=039c8f62 vocab=0675b09c
-/
theorem rep_map : ∀ (n : ℕ) (M : C) (x : K0 S) (hQ : S.Q M), Rep S n M x →
    k0ToG0 S x = gcl S M hQ := by
  intro n
  induction n with
  | zero =>
    rintro M x hQ ⟨h, rfl⟩
    exact k0ToG0_cls S M h
  | succ n ih =>
    rintro M x hQ ⟨K, E, i, g, y, hs, hE, hK, hy, rfl⟩
    have hrel := ExactGrothendieck.subcategoryClassOf_middle C S.Q hK (S.P_Q hE) hQ hs.zero
      hs.exact
    change gcl S E (S.P_Q hE) = gcl S K hK + gcl S M hQ at hrel
    rw [map_sub, k0ToG0_cls, ih K y hK hy, hrel]
    abel

/-- **Resolution theorem** in an abstract abelian category: if every `Q`-object has bundle
dimension `≤ d` then `K₀(P) → K₀(Q)` is bijective.
@isnad1 id=bijectiv.1h3v.s8.d7fb9b598e31 from=translated src=- shape=33e813de vocab=2257ac6b
-/
theorem k0ToG0_bijective (d : ℕ) (hd : ∀ M : C, S.Q M → PdLE S d M) :
    Function.Bijective (k0ToG0 S) := by
  obtain ⟨hAdd, hUniq⟩ := add_uniq_all S d
  let f : {M : C // S.Q M} → K0 S := fun M =>
    Classical.choose (exists_rep S d M.1 M.2 (hd M.1 M.2))
  have hf : ∀ M : {M : C // S.Q M}, Rep S d M.1 (f M) := fun M =>
    Classical.choose_spec (exists_rep S d M.1 M.2 (hd M.1 M.2))
  let ψ : G0 S →+ K0 S := ExactGrothendieck.lift f (by
    rintro A B D ⟨i, g, zero, hS⟩
    exact hAdd ⟨zero, hS⟩ A.2 B.2 D.2 (hd _ A.2) (hd _ B.2) (hd _ D.2) (hf A) (hf B) (hf D))
  have h1 : ψ.comp (k0ToG0 S) = AddMonoidHom.id _ := by
    apply ExactGrothendieck.hom_ext
    rintro ⟨E, hE⟩
    change ψ (k0ToG0 S (cls S E hE)) = cls S E hE
    rw [k0ToG0_cls]
    exact (ExactGrothendieck.lift_classOf _ _ _).trans
      (hUniq E (S.P_Q hE) (pdLE_of_P S d E hE) _ _ (hf ⟨E, S.P_Q hE⟩) (rep_bundle S d E hE))
  have h2 : (k0ToG0 S).comp ψ = AddMonoidHom.id _ := by
    apply ExactGrothendieck.hom_ext
    rintro ⟨M, hM⟩
    change k0ToG0 S (ψ (gcl S M hM)) = gcl S M hM
    rw [show ψ (gcl S M hM) = f ⟨M, hM⟩ from ExactGrothendieck.lift_classOf _ _ _]
    exact rep_map S d M _ hM (hf ⟨M, hM⟩)
  refine ⟨fun x y hxy => ?_, fun y => ⟨ψ y, ?_⟩⟩
  · have := congrArg ψ hxy
    simpa [← AddMonoidHom.comp_apply, h1] using this
  · exact DFunLike.congr_fun h2 y

end AbelianResolutionF15
