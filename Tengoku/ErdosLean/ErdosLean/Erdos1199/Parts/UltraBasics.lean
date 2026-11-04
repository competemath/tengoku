import Tengoku.ErdosLean.ErdosLean.Erdos1199.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #1199 — Part 1: basic facts about `βℕ`

Paper: arXiv:2607.17333, §2.4 (eq. (2.1), (2.4), Lemma 2.7(ii)) and Lemma 2.8.
-/

namespace Erdos1199

open Filter

/-- Membership in a sum of ultrafilters (paper eq. (2.1)).
@isnad1 id=iff.0h3v.s6.e0a1f9d75183 from=translated src=- shape=6b2b3a60 vocab=18568009
-/
theorem mem_add_iff (A : Set ℕ) (p q : Ultrafilter ℕ) :
    A ∈ p + q ↔ {m : ℕ | {m' : ℕ | m + m' ∈ A} ∈ q} ∈ p := by
  exact Iff.rfl

/-- Membership in `D p` (paper eq. (2.4)).
@isnad1 id=iff.0h2v.s5.c83065b05191 from=translated src=- shape=0d2b6d4e vocab=e82a2ad0
-/
theorem mem_dbl_iff (A : Set ℕ) (p : Ultrafilter ℕ) :
    A ∈ dbl p ↔ {n : ℕ | 2 * n ∈ A} ∈ p := by
  exact Iff.rfl

/-- `βℕ` is a right-topological semigroup: `p ↦ p + q` is continuous.
@isnad1 id=continuo.0h1v.s4.aa5570ea0846 from=translated src=- shape=2730dcd8 vocab=cf8b8b6d
-/
theorem continuous_add_const (q : Ultrafilter ℕ) :
    Continuous (fun p : Ultrafilter ℕ => p + q) := by
  exact Ultrafilter.continuous_add_left q

/-- Lemma 2.7(ii), first half: `p + q ∈ ℕ*` whenever `q ∈ ℕ*`.
@isnad1 id=nonprinc.1h2v.s4.6e2d97ba45d0 from=translated src=- shape=9dbbc820 vocab=4a2a6dd6
-/
theorem nonprincipal_add {p q : Ultrafilter ℕ} (hq : Nonprincipal q) :
    Nonprincipal (p + q) := by
  intro S hS
  have hS' : Sᶜ.Finite := hS
  show S ∈ (p + q)
  rw [mem_add_iff]
  refine Filter.mem_of_superset Filter.univ_mem fun m _ => ?_
  apply hq
  show {m' : ℕ | m + m' ∈ S}ᶜ.Finite
  refine (hS'.preimage (f := fun m' => m + m') (fun a _ b _ h => by simpa using h)).subset ?_
  intro m' hm'
  exact hm'

/-- Lemma 2.7(ii), second half: `D p ∈ ℕ*` whenever `p ∈ ℕ*`.
@isnad1 id=nonprinc.1h1v.s3.6b0f7eff6aa2 from=translated src=- shape=354f35de vocab=34ddb134
-/
theorem nonprincipal_dbl {p : Ultrafilter ℕ} (hp : Nonprincipal p) :
    Nonprincipal (dbl p) := by
  unfold Nonprincipal dbl
  rw [Ultrafilter.coe_map]
  exact (Filter.map_mono hp).trans
    (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h))

/-- `ℕ*` is closed in `βℕ`.
@isnad1 id=isclosed.0h0v.s3.37dd13f4eb88 from=translated src=- shape=a4527796 vocab=7d9c317a
-/
theorem isClosed_nonprincipal : IsClosed {p : Ultrafilter ℕ | Nonprincipal p} := by
  have : {p : Ultrafilter ℕ | Nonprincipal p} = ⋂ x : ℕ, {p : Ultrafilter ℕ | {x}ᶜ ∈ p} := by
    ext p
    simp only [Set.mem_iInter]
    exact Filter.le_cofinite_iff_compl_singleton_mem
  rw [this]
  exact isClosed_iInter fun x => ultrafilter_isClosed_basic _

/-- Every infinite set belongs to some nonprincipal ultrafilter.
@isnad1 id=ex.1h1v.s4.abaabf08d195 from=translated src=- shape=747d616e vocab=62813556
-/
theorem exists_nonprincipal_mem {B : Set ℕ} (hB : B.Infinite) :
    ∃ p : Ultrafilter ℕ, Nonprincipal p ∧ B ∈ p := by
  have : (Filter.cofinite ⊓ Filter.principal B).NeBot :=
    Filter.frequently_mem_iff_neBot.mp hB.frequently_cofinite
  refine ⟨Ultrafilter.of (Filter.cofinite ⊓ Filter.principal B), ?_, ?_⟩
  · exact (Ultrafilter.of_le _).trans inf_le_left
  · exact Ultrafilter.of_le _ (Filter.mem_inf_of_right (Filter.mem_principal_self B))

/-- A set in a nonprincipal ultrafilter has elements beyond every bound.
@isnad1 id=ex.2h3v.s5.1051e4ea7266 from=translated src=- shape=29fc19c1 vocab=538ba40c
-/
theorem Nonprincipal.exists_ge {p : Ultrafilter ℕ} (hp : Nonprincipal p) {S : Set ℕ}
    (hS : S ∈ p) (N : ℕ) : ∃ n ∈ S, N ≤ n := by
  have hN : {n : ℕ | N ≤ n} ∈ p := hp (by
    show {n : ℕ | N ≤ n}ᶜ.Finite
    exact (Set.finite_lt_nat N).subset fun n hn => by simpa using hn)
  obtain ⟨n, hnS, hnN⟩ := Ultrafilter.nonempty_of_mem (p.inter_mem hS hN)
  exact ⟨n, hnS, hnN⟩

end Erdos1199
