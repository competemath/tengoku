/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.IsProjPrime
import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.Ips.Basic

/-!

# rank one operators

This defines the rank one operator $| x \rangle\langle y |$ for continuous linear maps
  (see `rank_one`) and linear maps (see `rank_one_lm`).

-/

@[expose] public section

section rankOne

/-- The bra map sending a vector to the corresponding inner-product functional. -/
@[simps!]
noncomputable abbrev bra (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    E →L⋆[𝕜] (E →L[𝕜] 𝕜) :=
innerSL 𝕜
/-- The ket map sending a vector to scalar multiplication by that vector. -/
@[simps!]
noncomputable def ket (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    E →L[𝕜] (𝕜 →L[𝕜] E) where
  toFun x :=
  { toFun := fun α => α • x
    map_add' := fun _ _ => by simp only [add_smul]
    map_smul' := fun _ _ => by simp only [smul_smul, smul_eq_mul]; rfl }
  map_add' := fun _ _ => by simp only [smul_add]; rfl
  map_smul' := fun α _ => by simp_rw [smul_smul, mul_comm _ α, ← smul_smul]; rfl
  cont := by
    refine continuous_clm_apply.mpr ?_
    intro
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    exact continuous_const_smul _
/--
@isnad1 id=eq.0h3v.s10.2e3e295894a1 from=translated src=- shape=b9ba0933 vocab=b2ff11ee
-/
@[simp high]
lemma ket_one_apply
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (x : E) :
  ket 𝕜 x 1 = x :=
by simp only [ket_apply_apply, one_smul]

/--
@isnad1 id=eq.0h2v.s12.c937c6b267c5 from=translated src=- shape=81e706e2 vocab=247d60c5
-/
theorem ket_RCLike {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
  ket 𝕜 x = ContinuousLinearMap.mul 𝕜 𝕜 x := by
  ext
  simp only [ket_one_apply, ContinuousLinearMap.mul_apply', mul_one]

/--
@isnad1 id=eq.0h2v.s10.e57a59ff1837 from=translated src=- shape=bea18866 vocab=50e69c7e
-/
lemma ContinuousLinearMap.mul_one_apply {𝕜 𝕜' : Type*}
  [NontriviallyNormedField 𝕜] [SeminormedRing 𝕜']
  [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] :
  mul 𝕜 𝕜' 1 = 1 :=
by ext; rw [mul_apply', one_mul]; rfl

/--
@isnad1 id=eq.0h1v.s11.7b4c369dd8ec from=translated src=- shape=d592003b vocab=8c791998
-/
theorem ket_RCLike_one {𝕜 : Type*} [RCLike 𝕜] :
  ket 𝕜 (1 : 𝕜) = 1 :=
by rw [ket_RCLike, ContinuousLinearMap.mul_one_apply]

/--
@isnad1 id=eq.0h2v.s12.2a7fc68ab2fd from=translated src=- shape=21d235d0 vocab=9950d779
-/
theorem bra_RCLike {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
  bra 𝕜 x = ContinuousLinearMap.mul 𝕜 𝕜 ((starRingEnd 𝕜) x) := by
  ext
  simp_all

/--
@isnad1 id=eq.0h1v.s11.19f79e502d6a from=translated src=- shape=4ef6ffff vocab=0b26c3ef
-/
theorem bra_RCLike_one {𝕜 : Type*} [RCLike 𝕜] :
  bra 𝕜 (1 : 𝕜) = 1 :=
by rw [bra_RCLike, map_one, ContinuousLinearMap.mul_one_apply]

/--
@isnad1 id=eq.0h3v.s12.e85709e79ed8 from=translated src=- shape=c339c85c vocab=de56918f
-/
lemma bra_adjoint_eq_ket {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (x : E) :
  ContinuousLinearMap.adjoint (bra 𝕜 x : E →L[𝕜] 𝕜) = (ket 𝕜 x) := by
  ext
  apply ext_inner_left 𝕜
  intro y
  simp only [ket_apply_apply, one_smul, ContinuousLinearMap.adjoint_inner_right,
    bra_apply_apply, RCLike.inner_apply, inner_conj_symm, one_mul]

lemma _root_.ket_adjoint_eq_bra {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (x : E) :
  ContinuousLinearMap.adjoint (ket 𝕜 x) = bra 𝕜 x := by
  rw [← bra_adjoint_eq_ket, ContinuousLinearMap.adjoint_adjoint]

open scoped InnerProductSpace

/--
@isnad1 id=eq.0h4v.s12.e3e5b98f1cc5 from=translated src=- shape=25dcc225 vocab=347aba66
-/
lemma bra_ket_apply {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
  (bra 𝕜 x) ∘L (ket 𝕜 y) = ket 𝕜 ⟪x, y⟫_𝕜 := by
  ext
  simp_all

/--
@isnad1 id=eq.0h4v.s11.c991933f5202 from=translated src=- shape=29594122 vocab=347aba66
-/
lemma bra_ket_one_eq_inner {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
  ((bra 𝕜 x) ∘L (ket 𝕜 y)) 1 = ⟪x, y⟫_𝕜 := by
  rw [bra_ket_apply, ket_one_apply]

/--
@isnad1 id=eq.0h5v.s11.5ada1cb3984c from=translated src=- shape=1b1507c7 vocab=e1cbc458
-/
lemma continuousLinearMap_comp_ket {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  (f : E₁ →L[𝕜] E₂) (x : E₁) :
  f ∘L ket 𝕜 x = ket 𝕜 (f x) := by
  ext
  simp only [ContinuousLinearMap.comp_apply, ket_one_apply]

/--
@isnad1 id=eq.0h5v.s12.134138bd2f93 from=translated src=- shape=be9d4d47 vocab=8e4765fe
-/
lemma bra_comp_continuousLinearMap {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [CompleteSpace E₁] [CompleteSpace E₂]
  (x : E₂) (f : E₁ →L[𝕜] E₂) :
  bra 𝕜 x ∘L f = bra 𝕜 (ContinuousLinearMap.adjoint f x) := by
  ext
  simp only [ContinuousLinearMap.comp_apply, bra_apply_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- we define the rank one operator $| x \rangle\langle y |$ by
  $x \mapsto \langle y,z\rangle x$ -/
@[simps]
def rankOne (𝕜 : Type*) {E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₁ →ₗ[𝕜] (E₂ →ₗ⋆[𝕜] (E₂ →L[𝕜] E₁)) where
  toFun x :=
  { toFun := fun y =>
    { toFun := fun z => ⟪y,z⟫_𝕜 • x
      map_add' := fun _ _ => by simp_rw [inner_add_right, add_smul]
      map_smul' := fun _ _ => by simp_rw [inner_smul_right, RingHom.id_apply, smul_smul]
      cont := Continuous.smul (Continuous.inner continuous_const continuous_id') continuous_const }
    map_add' := fun a b => by simp only [inner_add_left, add_smul]; rfl
    map_smul' := fun r x => by simp only [inner_smul_left, ← smul_smul]; rfl }
  map_add' a b := by simp only [smul_add]; rfl
  map_smul' r a := by
    simp only [smul_smul, RingHom.id_apply, mul_comm _ r]
    simp only [← smul_smul]; rfl

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

/--
@isnad1 id=eq.0h6v.s12.168608273222 from=translated src=- shape=c94cc495 vocab=11ad51b1
-/
@[simp]
theorem rankOne_apply {x : E₁} {y : E₂} (z : E₂) : rankOne 𝕜 x y z = ⟪y,z⟫_𝕜 • x :=
rfl

/--
@isnad1 id=eq.0h5v.s12.a4e7761e5e74 from=translated src=- shape=707dbdaf vocab=a8e2ee56
-/
theorem ket_bra_eq_rankOne {x : E₁} {y : E₂} :
  ket 𝕜 x ∘L bra 𝕜 y = rankOne 𝕜 x y :=
rfl

open ContinuousLinearMap

/--
$| x \rangle\langle y | | z \rangle\langle w | =
\langle y, z \rangle \cdot  | x \rangle\langle w |$
@isnad1 id=eq.0h8v.s13.7a8895c39705 from=translated src=- shape=16662a0a vocab=44765da1
-/
@[simp]
theorem rankOne.apply_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y z : E₂) (w : E₃) :
    (rankOne 𝕜 x y) ∘L rankOne 𝕜 z w = ⟪y,z⟫_𝕜 • rankOne 𝕜 x w := by
  ext r
  simp_rw [smul_apply, comp_apply, rankOne_apply,
    inner_smul_right, mul_comm, smul_smul]

/-- $u \circ | x \rangle\langle y | = | u(x) \rangle\langle y |$
@isnad1 id=eq.0h7v.s13.4609f7218932 from=translated src=- shape=def3c5ca vocab=56f55a5d
-/
theorem ContinuousLinearMap.comp_rankOne {E₃ : Type*} [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y : E₂) (u : E₁ →L[𝕜] E₃) :
    u ∘L rankOne 𝕜 x y = rankOne 𝕜 (u x) y := by
  ext r
  simp_rw [comp_apply, rankOne_apply, map_smul]

/-- $| x \rangle\langle y | \circ u  = | x \rangle\langle u^*(y) |$
@isnad1 id=eq.0h7v.s13.dd3b529fdbad from=translated src=- shape=466c51fc vocab=b383b00b
-/
theorem ContinuousLinearMap.rankOne_comp {E₃ : Type*} [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₃]
  [CompleteSpace E₂] [CompleteSpace E₃] (x : E₁) (y : E₂) (u : E₃ →L[𝕜] E₂) :
    rankOne 𝕜 x y ∘L u = rankOne 𝕜 x (adjoint u y) := by
  ext r
  simp_rw [comp_apply, rankOne_apply, adjoint_inner_left]

/--
@isnad1 id=issymmet.0h3v.s12.3e2d09ac11b5 from=translated src=- shape=9adc8765 vocab=40a1181a
-/
theorem rankOne_self_isSymmetric {x : E₁} :
  LinearMap.IsSymmetric ((rankOne 𝕜 x x) : E₁ →ₗ[𝕜] E₁) := by
  simp_rw [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff]

/-- rank one operators are automatically self-adjoint
@isnad1 id=isselfad.0h3v.s12.10925b42aab2 from=translated src=- shape=15d316ab vocab=ad74f0df
-/
@[simp]
theorem rankOne_self_isSelfAdjoint [CompleteSpace E₁] {x : E₁} :
  IsSelfAdjoint (rankOne 𝕜 x x) :=
isSelfAdjoint_iff_isSymmetric.mpr rankOne_self_isSymmetric

/-- $| x \rangle\langle y |^* = | y \rangle\langle x |$
@isnad1 id=eq.0h5v.s13.8eab4b63b3c4 from=translated src=- shape=6c80f73d vocab=625018cd
-/
theorem rankOne_adjoint [CompleteSpace E₁] [CompleteSpace E₂] (x : E₁) (y : E₂) :
  adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  rw [← ket_bra_eq_rankOne, adjoint_comp, bra_adjoint_eq_ket, ket_adjoint_eq_bra]
  rfl

/--
@isnad1 id=eq.0h7v.s12.09e1aeffdad1 from=translated src=- shape=3e4ec84a vocab=ca23fe1e
-/
theorem rankOne_inner_left (x w : E₁) (y z : E₂) :
  ⟪rankOne 𝕜 x y z,w⟫_𝕜 = ⟪z,y⟫_𝕜 * ⟪x,w⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_left, inner_conj_symm]

/--
@isnad1 id=iff.0h3v.s10.2ad217a4ffa2 from=translated src=- shape=4ffb8c08 vocab=a9431d64
-/
theorem ContinuousLinearMap.commutes_with_all_iff [CompleteSpace E₁] {T : E₁ →L[𝕜] E₁} :
    (∀ S, Commute S T) ↔ ∃ α : 𝕜, T = α • 1 := by
  constructor
  · intro h
    have h' : ∀ x y : E₁, rankOne 𝕜 x y ∘L T = T ∘L rankOne 𝕜 x y := fun x y => h _
    simp_rw [ContinuousLinearMap.rankOne_comp, ContinuousLinearMap.comp_rankOne] at h'
    have h'' : ∀ x y : E₁, rankOne 𝕜 (adjoint T y) x = rankOne 𝕜 y (T x) := by
      intro x y
      nth_rw 1 [← rankOne_adjoint]
      rw [h', rankOne_adjoint]
    simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at h' h''
    by_cases H : ∀ x : E₁, x = 0
    · use 0
      simp_rw [ContinuousLinearMap.ext_iff]
      simp_all
    push Not at H
    obtain ⟨x, hx⟩ := H
    use (⟪x,x⟫_𝕜)⁻¹ * ⟪adjoint T x, x⟫_𝕜
    simp_rw [ContinuousLinearMap.ext_iff, smul_apply,
      one_apply_eq_self, mul_smul, h', smul_smul]
    simp_all
  · rintro ⟨α, hα⟩ S
    simp_rw [Commute, SemiconjBy, mul_def, hα, comp_smul, smul_comp, one_def, comp_id, id_comp]

/--
@isnad1 id=eq.0h2v.s10.1f6c6790fdd8 from=translated src=- shape=aa43be69 vocab=41140f00
-/
theorem ContinuousLinearMap.centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer = { x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1 } := by
  simp_rw [Set.centralizer, Set.mem_univ, true_imp_iff, ← ContinuousLinearMap.commutes_with_all_iff]
  rfl

/--
@isnad1 id=eq.0h2v.s10.932d88963ba5 from=translated src=- shape=18353512 vocab=b45b9409
-/
theorem ContinuousLinearMap.scalar_centralizer :
    {x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1}.centralizer = @Set.univ (E₁ →L[𝕜] E₁) := by
  simp_rw [Set.centralizer, Set.ext_iff, Set.mem_ofPred, Set.mem_univ, iff_true]
  simp_all

/--
@isnad1 id=eq.0h2v.s9.1b7a8d6961df from=translated src=- shape=d73fa181 vocab=773b00a0
-/
theorem ContinuousLinearMap.centralizer_centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer.centralizer = Set.univ := by
  rw [ContinuousLinearMap.centralizer, ContinuousLinearMap.scalar_centralizer]

/--
@isnad1 id=iff.0h4v.s11.df7d27fe01b4 from=translated src=- shape=6e99b4b4 vocab=b2ff11ee
-/
theorem ket_eq_ket_iff {x y : E₁} :
  ket 𝕜 x = ket 𝕜 y ↔ x = y := by
  simp only [ContinuousLinearMap.ext_iff, ket_apply_apply,
    ← @sub_eq_zero _ _ (_ • _), ← @sub_eq_zero _ _ x]
  simp only [← smul_sub, smul_eq_zero, forall_or_right,
    or_iff_right_iff_imp]
  intro h
  specialize h 1
  simp only [one_ne_zero] at h

/--
@isnad1 id=iff.0h4v.s11.e7f2de18a322 from=translated src=- shape=e17bd034 vocab=446b2eac
-/
theorem bra_eq_bra_iff {x y : E₁} :
  bra 𝕜 x = bra 𝕜 y ↔ x = y := by
  simp_all

/--
@isnad1 id=iff.0h5v.s9.4f15e99cf148 from=translated src=- shape=e6272026 vocab=b5089b93
-/
theorem ContinuousLinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →L[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 := by
  simp only [ContinuousLinearMap.ext_iff]
  exact ⟨fun h x _ => by rw [h], fun h x => ext_inner_right 𝕜 (h x)⟩
/--
@isnad1 id=iff.0h5v.s9.36dfb294e908 from=translated src=- shape=e6272026 vocab=c8e903b2
-/
theorem LinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →ₗ[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 := by
  simp only [LinearMap.ext_iff]
  exact ⟨fun h x _ => by rw [h], fun h x => ext_inner_right 𝕜 (h x)⟩

open scoped BigOperators

/--
@isnad1 id=ex.0h4v.s12.b34cf78f3270 from=translated src=- shape=c7d2986c vocab=0f397073
-/
theorem ContinuousLinearMap.exists_sum_rankOne
  [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →L[𝕜] E₂) :
    ∃ (x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂)
      (y : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁),
      T = ∑ i, rankOne 𝕜 (x i) (y i) := by
  let := FiniteDimensional.complete 𝕜 E₁
  let := FiniteDimensional.complete 𝕜 E₂
  let e₁ := stdOrthonormalBasis 𝕜 E₁
  let e₂ := stdOrthonormalBasis 𝕜 E₂
  let b : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁ := fun ij =>
    e₁ ij.1
  let a : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂ := fun ij =>
    e₂.repr (T (e₁ ij.1)) ij.2 • e₂ ij.2
  refine ⟨a, b, ?_⟩
  simp only [a, b]
  simp only [ContinuousLinearMap.ext_inner_map, sum_apply, sum_inner, rankOne_inner_left,
    inner_smul_left, OrthonormalBasis.repr_apply_apply, inner_conj_symm]
  intro u v
  symm
  calc
    ∑ x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂),
          ⟪u,e₁ x.fst⟫_𝕜 * (⟪T (e₁ x.fst),e₂ x.snd⟫_𝕜 * ⟪e₂ x.snd,v⟫_𝕜) =
        ∑ x_1, ∑ x_2,
          ⟪u,e₁ x_1⟫_𝕜 * (⟪T (e₁ x_1),e₂ x_2⟫_𝕜 * ⟪e₂ x_2,v⟫_𝕜) :=
      by simp_rw [← Finset.sum_product', Finset.univ_product_univ]
    _ = ∑ x_1, ⟪u,e₁ x_1⟫_𝕜 * ⟪T (e₁ x_1),v⟫_𝕜 := by
      simp_rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner]
    _ = ⟪T u,v⟫_𝕜 := by simp_rw [← adjoint_inner_right T, OrthonormalBasis.sum_inner_mul_inner]

/--
@isnad1 id=ex.0h4v.s12.285b86f81238 from=translated src=- shape=67714cfe vocab=9ecc5855
-/
theorem LinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    (T : E₁ →ₗ[𝕜] E₂) :
    ∃ (x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂)
      (y : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁),
      T = ∑ i, ↑(rankOne 𝕜 (x i) (y i)) := by
  obtain ⟨a, b, h⟩ := ContinuousLinearMap.exists_sum_rankOne (toContinuousLinearMap T)
  refine ⟨a, b, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap h

end rankOne

section rankOneLm

/-- Same as `rankOne`, but as a linear map. -/
abbrev rankOneLm {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) : E₂ →ₗ[𝕜] E₁ :=
  (rankOne 𝕜 x y).toLinearMap

variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped BigOperators

open scoped BigOperators

/--
@isnad1 id=iff.0h4v.s10.9eb5488ed3be from=translated src=- shape=a94416e8 vocab=1961e3e5
-/
theorem ContinuousLinearMap.coe_eq_zero {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] (f : E₁ →L[𝕜] E₂) :
    (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 := by norm_cast

/--
@isnad1 id=eq.0h6v.s13.6de3664dabcb from=translated src=- shape=0e178f14 vocab=d282b8c7
-/
theorem rankOne.left_sub {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x y : E₁) (z : E₂) :
    rankOne 𝕜 (x - y) z = rankOne 𝕜 x z - rankOne 𝕜 y z := by
  simp_all

/--
@isnad1 id=eq.0h5v.s12.df03e1624530 from=translated src=- shape=bdd0a305 vocab=a8f86e69
-/
theorem OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne {ι 𝕜 : Type _} [RCLike 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection' U = ∑ i : ι, rankOne 𝕜 (b i : E) (b i : E) := by
  ext
  simp_rw [orthogonalProjection'_apply, OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum b,
    sum_apply, rankOne_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]

/--
@isnad1 id=eq.0h4v.s12.9078d32e3f01 from=translated src=- shape=ec0ae2de vocab=e99e9640
-/
theorem ContinuousLinearMap.linearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B →L[𝕜] C) :
    LinearMap.adjoint (x : B →ₗ[𝕜] C) =
      @ContinuousLinearMap.adjoint 𝕜 _ _ _ _ _ _ _ (FiniteDimensional.complete 𝕜 B)
        (FiniteDimensional.complete 𝕜 C) x :=
  rfl

open scoped InnerProductSpace

/--
@isnad1 id=eq.0h4v.s13.8fa92a95e8de from=translated src=- shape=37483207 vocab=b6c61c9e
-/
theorem OrthonormalBasis.repr_adjoint {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
  letI := Module.Basis.finiteDimensional_of_finite b.toBasis
  letI := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.adjoint b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    = b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  simp_all

/--
@isnad1 id=eq.0h4v.s12.fe1981f95414 from=translated src=- shape=c026fa98 vocab=cc21e41b
-/
theorem OrthonormalBasis.repr_adjoint'
  {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
  haveI := Module.Basis.finiteDimensional_of_finite b.toBasis
  haveI := FiniteDimensional.complete 𝕜 E
  LinearMap.adjoint b.repr.toLinearMap
    = b.repr.symm.toLinearMap :=
haveI := Module.Basis.finiteDimensional_of_finite b.toBasis
haveI := FiniteDimensional.complete 𝕜 E
calc LinearMap.adjoint b.repr.toLinearMap
    =  ContinuousLinearMap.adjoint b.repr.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  _ = b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by rw [b.repr_adjoint]

open scoped Matrix

end rankOneLm
