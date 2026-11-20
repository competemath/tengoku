/-
# `T(x₁ … xₙ)` 里的典范 walk(step 4 辅助文件)

`TreePaths.lean` 的两档分类需要两种显式 walk:

* **上行路径**:从子树结点 `treeV i s l` 沿父边一路走到 `vᵢ`,长度 `|l| + 1`;
* **主路径段**:从 `vᵢ` 沿主路径走到 `vⱼ`,长度 `|i − j|`。

同块档只需要把两条上行路径接起来,**不必证拼出来的东西是路径** —— 无圈图里真正的
路径只会更短(`path_length_le_walk`)。

异块档需要等号,所以拼出来的 `上行 ++ 主路径段 ++ 下行` 必须证 `IsPath`。
支撑集无重复的理由是三段互不相交:

| 段 | `tIdx` | `tHeight` |
|---|---|---|
| A = 上行段(含末端 `vᵢ`) | 恒为 `i` | —— |
| B = 主路径段去掉首点 `vᵢ` | 恒 `≠ i` | 恒为 `0`(全是主路径点) |
| C = 下行段去掉首点 `vⱼ` | 恒为 `j ≠ i` | 恒 `≥ 1` |

A 与 B、A 与 C 靠 `tIdx` 分开,B 与 C 靠 `tHeight` 分开;三段各自的 `Nodup` 来自
各自的 `IsPath`。

注意 B 段「`tIdx ≠ i`」不需要主路径的下标单调性:主路径段的支撑集全是主路径点,
若某个非首点也有 `tIdx = i`,那它就等于首点 `vᵢ`,与该段自身的 `Nodup` 矛盾。
这一步省掉了一整套下标单调性的样板。同理 C 段的「`tHeight ≥ 1`」来自上行段性质里的
「要么是端点 `vⱼ`,要么深度 ≥ 1」,而端点已被 `.tail` 去掉。

**一律用存在量词形式**(`∃ p, …`)而不是先 `def` 出 walk 再逐条证性质:
walk 的构造带着依赖类型的合法性证明项,`def` 出来之后每条性质引理都要重新面对
同一堆 `TValid` 参数;存在形式把构造与性质一次性打包,后面只 `obtain` 一次。

⚠ 本文件全程**不对 `TVtx` 的元素做 `obtain ⟨uv, huv⟩`**:`TVtx` 是 `def` 包的
`Subtype`,拆开之后 Lean 会把它显示成 `{v // TValid x n v}`,与 `TTree x n` 的顶点类型
不再语法相同,`Walk` 上的引理立刻全部失配。一律走「`rcases hv : u.val` + `TVtx_ext`」。
-/
import Tengoku.Erdos815Lean.Erdos815.TreeBasic
import Tengoku.Erdos815Lean.Erdos815.TreeStruct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos815

open SimpleGraph

variable {n : ℕ} {x : ℕ → ℕ}

/-! ## 0. 小工具 -/

/-- 子树结点的父亲仍然合法(深度减一)。
@isnad1 id=tvalid.1h6v.s5.db4d5e424df7 from=translated src=- shape=806987e1 vocab=c3173b60
-/
lemma TValid_tail {i : Fin n} {s b : Bool} {m : List Bool}
    (h : TValid x n (.treeV i s (b :: m))) : TValid x n (.treeV i s m) := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  simp only [List.length_cons] at h2 ⊢
  omega

/-- 高度为 0 恰好刻画主路径点。
@isnad1 id=iff.0h2v.s4.0e592adcf7a6 from=translated src=- shape=6bc0bd2d vocab=a0c09496
-/
lemma tHeight_eq_zero_iff {v : TV n} : tHeight v = 0 ↔ ∃ k : Fin n, v = TV.pathV k := by
  cases v with
  | pathV k => exact ⟨fun _ => ⟨k, rfl⟩, fun _ => rfl⟩
  | treeV k s l => simp [tHeight]

/-! ## 1. 上行路径:子树结点 ⇝ `vᵢ` -/

/-- **上行路径(按子树内深度归纳的版本)**。长度 `|l| + 1`。

支撑集的三条性质分别为下游服务:
* `tIdx w.val = i` —— 异块档里把这一段与别的块分开;
* `tHeight w.val ≤ l.length + 1` —— 归纳里证 `IsPath` 用(新头结点比整段都深);
* `w = tP x i ∨ 1 ≤ tHeight w.val` —— 去掉端点后整段都在子树内部。
@isnad1 id=ex.1h5v.s7.950db03a2ffc from=translated src=- shape=12706f12 vocab=0d349a86
-/
lemma exists_upPath_aux {i : Fin n} {s : Bool} :
    ∀ (l : List Bool) (h : TValid x n (.treeV i s l)),
      ∃ p : (TTree x n).Walk (tT x i s l h) (tP x i),
        p.length = l.length + 1 ∧ p.IsPath ∧
        ∀ w ∈ p.support, tIdx w.val = i ∧ tHeight w.val ≤ l.length + 1 ∧
          (w = tP x i ∨ 1 ≤ tHeight w.val) := by
  intro l
  induction l with
  | nil =>
      intro h
      have hadj : (TTree x n).Adj (tT x i s [] h) (tP x i) := ⟨rfl, rfl⟩
      have hne : tT x i s [] h ≠ tP x i := fun hc => by
        have hcv : TV.treeV i s ([] : List Bool) = TV.pathV i := congrArg Subtype.val hc
        simp at hcv
      refine ⟨Walk.cons hadj Walk.nil, by simp, by simp [hne], ?_⟩
      intro w hw
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨rfl, by simp, Or.inr (by simp)⟩
      · exact ⟨rfl, by simp, Or.inl rfl⟩
  | cons b m ih =>
      intro h
      obtain ⟨p, hlen, hpath, hsupp⟩ := ih (TValid_tail h)
      have hadj : (TTree x n).Adj (tT x i s (b :: m) h) (tT x i s m (TValid_tail h)) :=
        Or.inl ⟨rfl, rfl, b, rfl⟩
      refine ⟨Walk.cons hadj p, by simp [hlen], ?_, ?_⟩
      · -- 新头结点深度 `|m| + 2`,严格大于整段的上界 `|m| + 1`,故不在段内
        rw [Walk.cons_isPath_iff]
        refine ⟨hpath, fun hmem => ?_⟩
        have hb := (hsupp _ hmem).2.1
        simp only [tT_val, tHeight_treeV, List.length_cons] at hb
        omega
      · intro w hw
        simp only [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨rfl, by simp, Or.inr (by simp)⟩
        · obtain ⟨h1, h2, h3⟩ := hsupp w hw
          exact ⟨h1, by simp only [List.length_cons]; omega, h3⟩

/-- **上行路径(叶子版本)**:从第 `i` 块的一片叶子走到 `vᵢ`,长度恰为 `xᵢ`。

这是下游真正使用的形态 —— 把子树的侧 `s` 与位置 `l` 都藏了起来。
@isnad1 id=ex.2h4v.s7.f2e094d6e280 from=translated src=- shape=4651af98 vocab=68cecf3b
-/
lemma exists_upPath (i : Fin n) (u : TVtx x n) (hi : tIdx u.val = i)
    (hu : IsTLeafRaw x n u.val) :
    ∃ p : (TTree x n).Walk u (tP x i), p.length = x (i : ℕ) ∧ p.IsPath ∧
      ∀ w ∈ p.support, tIdx w.val = i ∧ (w = tP x i ∨ 1 ≤ tHeight w.val) := by
  rcases hv : u.val with k | ⟨k, s, l⟩
  · rw [hv] at hu; exact absurd hu (by simp [IsTLeafRaw])
  · have hval : TValid x n (.treeV k s l) := hv ▸ u.2
    have hki : k = i := by rw [← hi, hv]; rfl
    subst hki
    have hlx : l.length + 1 = x (k : ℕ) := by rw [hv] at hu; exact hu
    have hueq : u = tT x k s l hval := TVtx_ext (by rw [hv]; rfl)
    subst hueq
    obtain ⟨p, hlen, hpath, hsupp⟩ := exists_upPath_aux (x := x) (i := k) (s := s) l hval
    exact ⟨p, by rw [hlen, hlx], hpath, fun w hw => ⟨(hsupp w hw).1, (hsupp w hw).2.2⟩⟩

/-! ## 2. 主路径段:`vᵢ ⇝ vⱼ` -/

/-! ## 3. 两片叶子之间的典范 walk -/

/-- **同块档的见证 walk**:两片同属第 `i` 块的叶子之间有一条长 `2xᵢ` 的 walk。

见证:上行到 `vᵢ`(长 `xᵢ`),再沿另一条上行路径的反向下到目标(长 `xᵢ`)。
**不需要**它是路径 —— 无圈图里真正的路径只会更短。
@isnad1 id=ex.3h4v.s7.aa33c2e53c96 from=translated src=- shape=a1f4ea56 vocab=c94f3ee8
-/
lemma exists_leafWalk_of_idx_eq {u v : TVtx x n}
    (hu : IsTLeafRaw x n u.val) (hv : IsTLeafRaw x n v.val)
    (heq : tIdx u.val = tIdx v.val) :
    ∃ p : (TTree x n).Walk u v, p.length = 2 * x ((tIdx u.val : ℕ)) := by
  obtain ⟨pu, hlenu, -, -⟩ := exists_upPath (tIdx u.val) u rfl hu
  obtain ⟨pv, hlenv, -, -⟩ := exists_upPath (tIdx u.val) v heq.symm hv
  refine ⟨pu.append pv.reverse, ?_⟩
  rw [Walk.length_append, Walk.length_reverse, hlenu, hlenv]
  omega

end Erdos815
