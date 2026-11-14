/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldDegree
import Tengoku.Seed.FieldTheory.SplittingField.Construction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/FieldSplitting.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 多项式的分裂域

本模块在 A3.5 的显式域嵌入与生成中间域、A3.6 的有限扩张接口之上，
建立分裂域的完整教材链。多项式根集通过显式求值刻画；分裂表示映入
目标域后的多项式可写成有限个一次因子的乘积；分裂域还要求全部根生成
整个目标域。

零多项式在 Mathlib `Polynomial.Splits` 的边界约定下分裂，但本模块只把
非零多项式纳入 `SplittingFieldFor`，并把零多项式的教材根集定义为空。
公开 API 使用 `FieldEmbedding`、集合谓词及正式 `Polynomial`，不要求调用者
提供 Mathlib 的 `Algebra`、`IntermediateField`、`AlgEquiv` 或分裂域类。
这些高级对象仅作为私有证明后端，用于验证存在性、有限性和
唯一到同构。

> **Entry**: abstract-algebra.field.splitting
-/

namespace SandronesLibrary.AbstractAlgebra.FieldSplitting

open Polynomial
open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree


universe u

/-! ## 公开教材定义 -/

/-- 多项式在显式扩域中的教材根集。成员必须同时满足原多项式非零，且经
`evaluateOver` 在该点的显式求值为零；因此零多项式的根集按约定为空。

> **Entry**: abstract-algebra.field.splitting-/
def PolynomialRootSetIn {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) : Set L :=
  {a | p ≠ 0 ∧ evaluateOver e p a = 0}

/-- 多项式在显式扩域中分裂：先沿 `e.toRingHom` 映射全部系数，再要求所得
正式多项式分裂为一次因子。Mathlib 的边界约定令零多项式也满足此谓词。

> **Entry**: abstract-algebra.field.splitting-/
def PolynomialSplitsIn {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) : Prop :=
  (p.map e.toRingHom).Splits

/-- `L/K` 是非零多项式 `p` 的分裂域，当且仅当 `p` 在 `L` 中分裂，并且
其全部根相对于嵌入 `e` 生成整个目标域。
这是教材的“分裂且由根生成”定义。

> **Entry**: abstract-algebra.field.splitting-/
def SplittingFieldFor {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) : Prop :=
  p ≠ 0 ∧ PolynomialSplitsIn e p ∧
    generatedIntermediateFieldSet e (PolynomialRootSetIn e p) = Set.univ

/-- `g : L → M` 延拓两个选定的基域嵌入，意即对每个 `x : K` 都有
`g (e x) = j x`。该谓词显式记录同态固定基域的交换三角形。

> **Entry**: abstract-algebra.field.splitting-/
def ExtendsFieldEmbedding {K L M : Type*} [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (j : FieldEmbedding K M)
    (g : FieldEmbedding L M) : Prop :=
  ∀ x : K, g (e x) = j x

/-- 两个显式扩域在基域上的教材同构。结构显式记录正向与逆向域嵌入、
左右互逆关系，以及正向嵌入延拓同一个基域映射的条件。

> **Entry**: abstract-algebra.field.splitting-/
structure FieldIsomorphismOver {K L M : Type*} [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) where
  forward : FieldEmbedding L M
  inverse : FieldEmbedding M L
  left_inverse : Function.LeftInverse inverse forward
  right_inverse : Function.RightInverse inverse forward
  fixes_base : ExtendsFieldEmbedding eL eM forward

/-- 基域上的恒等同构。正向和逆向均取目标域的恒等嵌入，互逆与固定基域
性质都由定义直接成立。

> **Entry**: abstract-algebra.field.splitting-/
def FieldIsomorphismOver.refl {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : FieldIsomorphismOver e e where
  forward := FieldEmbedding.id L
  inverse := FieldEmbedding.id L
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  fixes_base := fun _ => rfl

/-- 基域上同构的对称同构。交换正逆嵌入和左右逆证明；逆向固定基域由原
正向嵌入的单射性与互逆关系推出。

> **Entry**: abstract-algebra.field.splitting-/
def FieldIsomorphismOver.symm {K L M : Type*} [Field K] [Field L] [Field M]
    {eL : FieldEmbedding K L} {eM : FieldEmbedding K M}
    (h : FieldIsomorphismOver eL eM) : FieldIsomorphismOver eM eL where
  forward := h.inverse
  inverse := h.forward
  left_inverse := h.right_inverse
  right_inverse := h.left_inverse
  fixes_base := fun x => by
    apply h.forward.injective
    rw [h.right_inverse, h.fixes_base]

/-- 基域上同构的传递复合。正向嵌入按路径复合，逆向嵌入按反序复合，
左右逆和固定基域条件逐层消去。

> **Entry**: abstract-algebra.field.splitting-/
def FieldIsomorphismOver.trans {K L M N : Type*}
    [Field K] [Field L] [Field M] [Field N]
    {eL : FieldEmbedding K L} {eM : FieldEmbedding K M} {eN : FieldEmbedding K N}
    (hLM : FieldIsomorphismOver eL eM) (hMN : FieldIsomorphismOver eM eN) :
    FieldIsomorphismOver eL eN where
  forward := hMN.forward.comp hLM.forward
  inverse := hLM.inverse.comp hMN.inverse
  left_inverse := fun x => by
    change hLM.inverse (hMN.inverse (hMN.forward (hLM.forward x))) = x
    rw [hMN.left_inverse, hLM.left_inverse]
  right_inverse := fun x => by
    change hMN.forward (hLM.forward (hLM.inverse (hMN.inverse x))) = x
    rw [hLM.right_inverse, hMN.right_inverse]
  fixes_base := fun x => by
    change hMN.forward (hLM.forward (eL x)) = eN x
    rw [hLM.fixes_base, hMN.fixes_base]

/-- 非零多项式分裂域的依赖见证。结构把载体类型、域结构、基域嵌入和
`SplittingFieldFor` 性质打包，供存在性定理在同一 universe 中返回。

> **Entry**: abstract-algebra.field.splitting-/
structure SplittingFieldWitness (K : Type u) [Field K] (p : Polynomial K) where
  Carrier : Type u
  fieldInstance : Field Carrier
  embedding : @FieldEmbedding K Carrier _ fieldInstance
  isSplittingField : @SplittingFieldFor K Carrier _ fieldInstance embedding p

/-- 把分裂域见证中保存的域结构注册为其载体的实例，使见证的嵌入和
分裂域性质可直接用于后续教材定理。

> **Entry**: abstract-algebra.field.splitting-/
instance {K : Type u} [Field K] {p : Polynomial K}
    (w : SplittingFieldWitness K p) : Field w.Carrier :=
  w.fieldInstance

/-! ## 私有 Mathlib 证明后端

以下私有桥局部安装由显式嵌入诱导的代数结构，并将教材根集、
生成中间域、有限扩张和基域上同构与 Mathlib 的成熟接口对齐。
高级结构不会进入公开签名。
-/

-- A3.7S-01：显式嵌入诱导的代数映射就是其环同态桥。
private theorem algebraMap_eq_embedding {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    @algebraMap K L _ _ e.toRingHom.toAlgebra = e.toRingHom := by
  exact RingHom.algebraMap_toAlgebra e.toRingHom

-- A3.7S-02：Mathlib 的多项式代数求值与本库显式求值一致。
private theorem aeval_eq_evaluateOver {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (a : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    Polynomial.aeval a p = evaluateOver e p a := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rw [Polynomial.aeval_def, algebraMap_eq_embedding]
  rfl

-- A3.7S-03：教材根集与 Mathlib 的 `rootSet` 对齐。
private theorem rootSet_eq_mathlib {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    PolynomialRootSetIn e p = p.rootSet L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  ext a
  rw [Polynomial.mem_rootSet]
  simp only [PolynomialRootSetIn, Set.mem_ofPred_eq, aeval_eq_evaluateOver]

-- A3.7S-04：集合交定义的生成中间域与 Mathlib 中间域生成的底层集合对齐。
private theorem generated_eq_adjoin {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (S : Set L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    generatedIntermediateFieldSet e S =
      ((IntermediateField.adjoin K S : IntermediateField K L) : Set L) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  ext x
  constructor
  · intro hx
    apply hx (IntermediateField.adjoin K S : Set L)
    · refine ⟨⟨⟨IntermediateField.zero_mem _, IntermediateField.one_mem _,
          ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · exact fun _ _ ha hb => IntermediateField.add_mem _ ha hb
      · exact fun _ _ ha hb => IntermediateField.mul_mem _ ha hb
      · exact fun _ ha => IntermediateField.neg_mem _ ha
      · exact fun _ hx _ => IntermediateField.inv_mem _ hx
      · rintro _ ⟨a, rfl⟩
        change algebraMap K L a ∈ (IntermediateField.adjoin K S)
        exact IntermediateField.algebraMap_mem _ a
    · exact IntermediateField.subset_adjoin K S
  · intro hx T hT hST
    let U : IntermediateField K L :=
      { carrier := T
        mul_mem' := fun {a b} ha hb => hT.1.1.2.2.2.1 ha hb
        add_mem' := fun {a b} ha hb => hT.1.1.2.2.1 ha hb
        algebraMap_mem' := fun a => by
          rw [algebraMap_eq_embedding e]
          exact hT.2 ⟨a, rfl⟩
        inv_mem' := fun x hx => by
          by_cases hzero : x = 0
          · simpa [hzero] using hT.1.1.1
          · exact hT.1.2 hx hzero }
    have hSU : S ⊆ (U : Set L) := by
      intro y hy
      exact hST hy
    exact (IntermediateField.adjoin_le_iff.mpr hSU :
      IntermediateField.adjoin K S ≤ U) hx

-- A3.7S-05：本库分裂域谓词与 Mathlib 正式谓词对齐，显式保留非零边界。
private theorem splittingFieldFor_iff_mathlib {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    SplittingFieldFor e p ↔ p ≠ 0 ∧ Polynomial.IsSplittingField K L p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨hp, hsplits, hgen⟩
    refine ⟨hp, isSplittingField_iff_intermediateField.mpr ⟨?_, ?_⟩⟩
    · simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using hsplits
    · rw [← rootSet_eq_mathlib e p]
      apply SetLike.coe_injective
      rw [← generated_eq_adjoin e]
      exact hgen
  · rintro ⟨hp, hsf⟩
    obtain ⟨hsplits, hadjoin⟩ :=
      isSplittingField_iff_intermediateField.mp hsf
    refine ⟨hp, ?_, ?_⟩
    · simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using hsplits
    · rw [rootSet_eq_mathlib e p, generated_eq_adjoin e]
      exact congrArg (fun F : IntermediateField K L => (F : Set L)) hadjoin

-- A3.7S-06：分裂等价于首项系数乘全部线性因子的有限多重集乘积。
private theorem splits_multiset_bridge {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) :
    PolynomialSplitsIn e p ↔
      ∃ roots : Multiset L,
        p.map e.toRingHom = Polynomial.C (p.map e.toRingHom).leadingCoeff *
          (roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
  exact Polynomial.splits_iff_exists_multiset

-- A3.7S-07：零、常数、一次以及非零乘积的基础分裂规则。
private theorem elementary_splits_bridge {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    PolynomialSplitsIn e (0 : Polynomial K) ∧
      (∀ c : K, PolynomialSplitsIn e (Polynomial.C c)) ∧
      (∀ p : Polynomial K, p.degree = 1 → PolynomialSplitsIn e p) ∧
      (∀ p q : Polynomial K, p ≠ 0 → q ≠ 0 →
        (PolynomialSplitsIn e (p * q) ↔
          PolynomialSplitsIn e p ∧ PolynomialSplitsIn e q)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [PolynomialSplitsIn]
  · intro c
    simp [PolynomialSplitsIn]
  · intro p hp
    unfold PolynomialSplitsIn
    apply Polynomial.Splits.of_degree_eq_one
    rw [Polynomial.degree_map_eq_of_injective e.injective]
    exact hp
  · intro p q hp hq
    unfold PolynomialSplitsIn
    rw [Polynomial.map_mul]
    exact Polynomial.splits_mul
      ((Polynomial.map_ne_zero_iff e.injective).mpr hp)
      ((Polynomial.map_ne_zero_iff e.injective).mpr hq)

-- A3.7S-08：Mathlib 基域代数同态转为本库显式延拓嵌入。
private theorem algHom_to_embedding_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) :
    letI : Algebra K L := eL.toRingHom.toAlgebra
    letI : Algebra K M := eM.toRingHom.toAlgebra
    ∀ φ : L →ₐ[K] M,
      ∃ g : FieldEmbedding L M,
        g.toFun = φ ∧ ExtendsFieldEmbedding eL eM g := by
  letI : Algebra K L := eL.toRingHom.toAlgebra
  letI : Algebra K M := eM.toRingHom.toAlgebra
  intro φ
  let g : FieldEmbedding L M :=
    { toFun := φ
      map_isRingHomomorphism :=
        ⟨φ.map_zero, φ.map_one, φ.map_add, φ.map_mul, φ.map_neg⟩
      injective := φ.injective }
  refine ⟨g, rfl, ?_⟩
  intro x
  change φ (eL x) = eM x
  have hL : eL x = algebraMap K L x := by
    change eL.toRingHom x = algebraMap K L x
    rw [algebraMap_eq_embedding eL]
  have hM : algebraMap K M x = eM x := by
    change algebraMap K M x = eM.toRingHom x
    rw [algebraMap_eq_embedding eM]
  exact (congrArg φ hL).trans ((φ.commutes x).trans hM)

-- A3.7S-09：Mathlib 基域代数同构转为本库显式基域上同构。
private theorem algEquiv_to_isomorphism_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) :
    letI : Algebra K L := eL.toRingHom.toAlgebra
    letI : Algebra K M := eM.toRingHom.toAlgebra
    ∀ φ : L ≃ₐ[K] M,
      ∃ h : FieldIsomorphismOver eL eM, h.forward.toFun = φ := by
  letI : Algebra K L := eL.toRingHom.toAlgebra
  letI : Algebra K M := eM.toRingHom.toAlgebra
  intro φ
  obtain ⟨forward, hforward, hfix⟩ :=
    algHom_to_embedding_bridge eL eM φ.toAlgHom
  obtain ⟨inverse, hinverse, hinverseFix⟩ :=
    algHom_to_embedding_bridge eM eL φ.symm.toAlgHom
  refine ⟨{
    forward := forward
    inverse := inverse
    left_inverse := ?_
    right_inverse := ?_
    fixes_base := hfix }, ?_⟩
  · intro x
    rw [hforward, hinverse]
    exact φ.symm_apply_apply x
  · intro x
    rw [hforward, hinverse]
    exact φ.apply_symm_apply x
  · exact hforward

-- A3.7S-10：Mathlib 有限维性转为 A3.6 的显式有限扩张见证。
private theorem finiteDimensional_to_finiteFieldExtension {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FiniteDimensional K L → FiniteFieldExtension e := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  intro hfinite
  letI : FiniteDimensional K L := hfinite
  let b : Module.Basis (Fin (Module.finrank K L)) K L := Module.finBasis K L
  have hcomb (c : Fin (Module.finrank K L) → K) :
      fieldLinearCombination e Finset.univ c b = ∑ i, c i • b i := by
    simp [fieldLinearCombination, Algebra.smul_def, algebraMap_eq_embedding e]
    rfl
  refine ⟨Module.finrank K L, ⟨b, ?_⟩⟩
  constructor
  · intro c hc i
    apply Fintype.linearIndependent_iff.mp b.linearIndependent c
    rw [← hcomb]
    exact hc
  · intro x
    refine ⟨fun i => b.repr x i, ?_⟩
    rw [hcomb]
    exact b.sum_repr x

-- A3.7S-11：本库分裂域由 Mathlib 有限维定理得到有限扩张。
private theorem splittingField_finite_bridge {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K)
    (h : SplittingFieldFor e p) : FiniteFieldExtension e := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hsf : Polynomial.IsSplittingField K L p :=
    (splittingFieldFor_iff_mathlib e p).mp h |>.2
  letI : Polynomial.IsSplittingField K L p := hsf
  exact finiteDimensional_to_finiteFieldExtension e
    (Polynomial.IsSplittingField.finiteDimensional L p)

-- A3.7S-12：分裂域向任意分裂扩域的 Mathlib `lift` 转为显式嵌入。
private theorem splittingField_embedding_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) (p : Polynomial K)
    (hL : SplittingFieldFor eL p) (hM : PolynomialSplitsIn eM p) :
    ∃ g : FieldEmbedding L M, ExtendsFieldEmbedding eL eM g := by
  letI : Algebra K L := eL.toRingHom.toAlgebra
  letI : Algebra K M := eM.toRingHom.toAlgebra
  have hsf : Polynomial.IsSplittingField K L p :=
    (splittingFieldFor_iff_mathlib eL p).mp hL |>.2
  letI : Polynomial.IsSplittingField K L p := hsf
  have hsplits : (p.map (algebraMap K M)).Splits := by
    simpa [PolynomialSplitsIn, algebraMap_eq_embedding eM] using hM
  let φ : L →ₐ[K] M := Polynomial.IsSplittingField.lift L p hsplits
  obtain ⟨g, hfun, hextends⟩ := algHom_to_embedding_bridge eL eM φ
  exact ⟨g, hextends⟩

-- A3.7S-13：Mathlib 标准分裂域类型打包为本库依赖见证。
private noncomputable def mathlib_splittingFieldWitness
    (K : Type u) [Field K] (p : Polynomial K) (hp : p ≠ 0) :
    SplittingFieldWitness K p := by
  let E := Polynomial.SplittingField p
  let canonicalAlgebra : Algebra K E := inferInstance
  let e : FieldEmbedding K E :=
    { toFun := @algebraMap K E _ _ canonicalAlgebra
      map_isRingHomomorphism := by
        let f : K →+* E := @algebraMap K E _ _ canonicalAlgebra
        exact ⟨f.map_zero, f.map_one, f.map_add, f.map_mul, f.map_neg⟩
      injective := (@algebraMap K E _ _ canonicalAlgebra).injective }
  have heRing : e.toRingHom = @algebraMap K E _ _ canonicalAlgebra := by
    ext x
    rfl
  have halgebra : e.toRingHom.toAlgebra = canonicalAlgebra := by
    apply Algebra.algebra_ext
    intro x
    change e.toRingHom x = (@algebraMap K E _ _ canonicalAlgebra) x
    exact DFunLike.congr_fun heRing x
  have hcanonical :
      @Polynomial.IsSplittingField K E _ _ canonicalAlgebra p := inferInstance
  have hexplicit :
      @Polynomial.IsSplittingField K E _ _ e.toRingHom.toAlgebra p := by
    rw [halgebra]
    exact hcanonical
  refine {
    Carrier := E
    fieldInstance := inferInstance
    embedding := e
    isSplittingField := ?_ }
  exact (splittingFieldFor_iff_mathlib e p).mpr ⟨hp, hexplicit⟩

-- A3.7S-14：Mathlib 分裂域唯一性同构转为显式基域上同构。
private theorem splittingFields_isomorphic_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) (p : Polynomial K)
    (hL : SplittingFieldFor eL p) (hM : SplittingFieldFor eM p) :
    Nonempty (FieldIsomorphismOver eL eM) := by
  letI : Algebra K L := eL.toRingHom.toAlgebra
  letI : Algebra K M := eM.toRingHom.toAlgebra
  have hsfL : Polynomial.IsSplittingField K L p :=
    (splittingFieldFor_iff_mathlib eL p).mp hL |>.2
  have hsfM : Polynomial.IsSplittingField K M p :=
    (splittingFieldFor_iff_mathlib eM p).mp hM |>.2
  letI : Polynomial.IsSplittingField K L p := hsfL
  letI : Polynomial.IsSplittingField K M p := hsfM
  let φ : L ≃ₐ[K] M :=
    (Polynomial.IsSplittingField.algEquiv L p).trans
      (Polynomial.IsSplittingField.algEquiv M p).symm
  obtain ⟨h, hforward⟩ := algEquiv_to_isomorphism_bridge eL eM φ
  exact ⟨h⟩

/-! ## 根集与分裂 -/

/-- 展开根集定义的成员判据：`a` 属于根集，当且仅当 `p` 非零且
`evaluateOver e p a = 0`。该定理固定零多项式边界。

> **Entry**: abstract-algebra.field.splitting-/
theorem mem_polynomialRootSetIn_iff {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (a : L) :
    a ∈ PolynomialRootSetIn e p ↔ p ≠ 0 ∧ evaluateOver e p a = 0 := by
  rfl

/-- 零多项式的教材根集为空。虽然零多项式在 Mathlib 边界下满足分裂谓词，
根集定义中的非零条件排除了所有元素。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialRootSetIn_zero {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    PolynomialRootSetIn e (0 : Polynomial K) = ∅ := by
  ext a
  simp [PolynomialRootSetIn]

/-- 分裂的有限线性因子多重集刻画：映射后的多项式等于首项系数对应常数
多项式，乘以由根的多重集给出的全部 `X - C a` 因子之积。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialSplitsIn_iff_exists_multiset {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K) :
    PolynomialSplitsIn e p ↔
      ∃ roots : Multiset L,
        p.map e.toRingHom = Polynomial.C (p.map e.toRingHom).leadingCoeff *
          (roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
  exact splits_multiset_bridge e p

/-- 零多项式在 Mathlib 的 `Splits` 边界约定下分裂。该结果只描述
`PolynomialSplitsIn`，并不使零多项式满足 `SplittingFieldFor`。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialSplitsIn_zero {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : PolynomialSplitsIn e (0 : Polynomial K) := by
  exact (elementary_splits_bridge e).1

/-- 任意常数多项式在任意显式扩域中分裂，包括零常数。其一次因子多重集
为空，剩余因子就是映射后的常数多项式。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialSplitsIn_C {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (c : K) : PolynomialSplitsIn e (Polynomial.C c) := by
  exact (elementary_splits_bridge e).2.1 c

/-- 次数恰为一的多项式在任意域扩张中分裂。域嵌入的单射性保证系数映射
保持次数，再应用一次多项式的正式分裂定理。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialSplitsIn_of_degree_eq_one {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K)
    (hp : p.degree = 1) : PolynomialSplitsIn e p := by
  exact (elementary_splits_bridge e).2.2.1 p hp

/-- 两个非零多项式之积分裂，当且仅当两个因子分别分裂。非零假设排除
乘积退化为零时 Mathlib `Splits` 边界约定造成的逆向例外。

> **Entry**: abstract-algebra.field.splitting-/
theorem polynomialSplitsIn_mul_iff {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
    PolynomialSplitsIn e (p * q) ↔
      PolynomialSplitsIn e p ∧ PolynomialSplitsIn e q := by
  exact (elementary_splits_bridge e).2.2.2 p q hp hq

/-! ## 分裂域性质与存在唯一性 -/

/-- 从 `SplittingFieldFor` 投影原多项式非零条件。该投影明确区分分裂谓词
允许的零多项式边界与教材分裂域的定义域。

> **Entry**: abstract-algebra.field.splitting-/
theorem SplittingFieldFor.nonzero {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} {p : Polynomial K} (h : SplittingFieldFor e p) : p ≠ 0 :=
  h.1

/-- 从 `SplittingFieldFor` 投影多项式在目标域中分裂的条件，即映射后的
正式多项式满足 `Polynomial.Splits`。

> **Entry**: abstract-algebra.field.splitting-/
theorem SplittingFieldFor.splits {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} {p : Polynomial K} (h : SplittingFieldFor e p) :
    PolynomialSplitsIn e p :=
  h.2.1

/-- 从 `SplittingFieldFor` 投影根生成条件：原多项式在目标域中的全部教材
根所生成的中间域集合恰为目标域全集。

> **Entry**: abstract-algebra.field.splitting-/
theorem SplittingFieldFor.generated {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} {p : Polynomial K} (h : SplittingFieldFor e p) :
    generatedIntermediateFieldSet e (PolynomialRootSetIn e p) = Set.univ :=
  h.2.2

/-- 非零多项式的分裂域是 A3.6 意义下的有限域扩张。证明后端使用 Mathlib
分裂域有限维性，再构造显式有限域基见证。

> **Entry**: abstract-algebra.field.splitting-/
theorem splittingFieldFor_finite {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (h : SplittingFieldFor e p) :
    FiniteFieldExtension e := by
  exact splittingField_finite_bridge e p h

/-- 分裂域是 A3.6 意义下的代数扩张。该结论先取得有限扩张见证，再直接
复用“有限域扩张必为代数扩张”的公开定理。

> **Entry**: abstract-algebra.field.splitting-/
theorem splittingFieldFor_algebraic {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (h : SplittingFieldFor e p) :
    AlgebraicExtension e := by
  exact finiteFieldExtension_isAlgebraic e (splittingFieldFor_finite e p h)

/-- 一个分裂域可在基域上嵌入任意使原多项式分裂的扩域。所得显式域嵌入
满足 `ExtendsFieldEmbedding`，所以固定给定的基域嵌入。

> **Entry**: abstract-algebra.field.splitting-/
theorem splittingField_embeds_into_splitting_extension {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) (p : Polynomial K)
    (hL : SplittingFieldFor eL p) (hM : PolynomialSplitsIn eM p) :
    ∃ g : FieldEmbedding L M, ExtendsFieldEmbedding eL eM g := by
  exact splittingField_embedding_bridge eL eM p hL hM

/-- 每个非零多项式都存在一个打包后的分裂域见证。证明后端采用 Mathlib
标准分裂域类型，并把其基域映射与本库显式嵌入精确对齐。

> **Entry**: abstract-algebra.field.splitting-/
theorem nonempty_splittingFieldWitness (K : Type u) [Field K]
    (p : Polynomial K) (hp : p ≠ 0) : Nonempty (SplittingFieldWitness K p) := by
  exact ⟨mathlib_splittingFieldWitness K p hp⟩

/-- 同一非零多项式的任意两个分裂域在所选基域嵌入上同构。证明把两者
分别同构到标准分裂域，再复合得到显式 `FieldIsomorphismOver`。

> **Entry**: abstract-algebra.field.splitting-/
theorem splittingFields_isomorphic_over {K L M : Type*}
    [Field K] [Field L] [Field M]
    (eL : FieldEmbedding K L) (eM : FieldEmbedding K M) (p : Polynomial K)
    (hL : SplittingFieldFor eL p) (hM : SplittingFieldFor eM p) :
    Nonempty (FieldIsomorphismOver eL eM) := by
  exact splittingFields_isomorphic_bridge eL eM p hL hM

end SandronesLibrary.AbstractAlgebra.FieldSplitting
