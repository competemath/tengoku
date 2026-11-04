import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CompactRootCovering
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.Topology.Homotopy.Lifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Monomial root counts and preservation of fiber cardinality by covering transport. -/

open Polynomial
namespace DuistermaatVanDerKallen
/--
@isnad1 id=eq.2h2v.s5.43a3a1608668 from=translated src=- shape=9489753d vocab=7e7380a8
-/
theorem complex_nth_root_card (n : ℕ) (hn : 0 < n) (a : ℂ) (ha : a ≠ 0) :
    Nat.card {z : ℂ // z ^ n = a} = n := by
  classical
  let p : ℂ[X] := X ^ n - C a
  have hp : p ≠ 0 := X_pow_sub_C_ne_zero hn a
  have he : {z : ℂ | z ^ n = a} = p.rootSet ℂ := by
    ext z
    simp [mem_rootSet_of_ne hp, p, sub_eq_zero]
  change Nat.card ↥({z : ℂ | z ^ n = a}) = n
  rw [he, Nat.card_eq_fintype_card]
  rw [card_rootSet_eq_natDegree (separable_X_pow_sub_C a (by exact_mod_cast hn.ne') ha)
    (IsAlgClosed.splits _)]
  exact natDegree_X_pow_sub_C

/--
@isnad1 id=eq.5h4v.s6.7dcfee28d377 from=translated src=- shape=0d8988eb vocab=9f50aae6
-/
theorem complex_monomial_root_card_in_disc (n : ℕ) (hn : 0 < n) (A a : ℂ) (hA : A ≠ 0) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hbound : ‖a‖ < ‖A‖ * ε ^ n) :
    Nat.card {z : ℂ // ‖z‖ ≤ ε ∧ A * z ^ n = a} = n := by
  have hinside (z : ℂ) (hz : z ^ n = a / A) : ‖z‖ ≤ ε := by
    have hpow : ‖z‖ ^ n = ‖a‖ / ‖A‖ := by rw [← norm_pow, hz, norm_div]
    apply (lt_of_pow_lt_pow_left₀ n hε.le _).le
    rw [hpow]
    exact (div_lt_iff₀ (norm_pos_iff.mpr hA)).mpr (by simpa [mul_comm] using hbound)
  let e : {z : ℂ // ‖z‖ ≤ ε ∧ A * z ^ n = a} ≃ {z : ℂ // z ^ n = a / A} :=
    { toFun := fun z => ⟨z.val, (eq_div_iff hA).mpr (by simpa [mul_comm] using z.property.2)⟩
      invFun := fun z => ⟨z.val, hinside z.val z.property,
        by simpa [mul_comm] using (eq_div_iff hA).mp z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact complex_nth_root_card n hn (a / A) (div_ne_zero ha hA)

/--
@isnad1 id=eq.1h6v.s5.5e2d1b58c8a9 from=translated src=- shape=0a9e6790 vocab=85c7be40
-/
theorem covering_fiber_card_eq_along_path {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsCoveringMap p) {a b : Y} (γ : Path a b) :
    Nat.card (p ⁻¹' {a}) = Nat.card (p ⁻¹' {b}) := by
  exact Nat.card_congr (Equiv.ofBijective
    (hp.monodromy (Path.Homotopic.Quotient.mk γ))
    (hp.monodromy_bijective (Path.Homotopic.Quotient.mk γ)))

/-- A fiber of the compact root projection is exactly the set of roots in its
selected closed disc; no multiplicity or extra base coordinate is counted.-/
noncomputable def compactRootFiberEquiv {E : Type*} [TopologicalSpace E]
    (P : E × ℂ → ℂ) (B : Set E) (ε : ℝ) (b : B) :
    (compactRootProjection P B ε ⁻¹' {b}) ≃ {z : ℂ // ‖z‖ ≤ ε ∧ P (b.val, z) = 0} where
  toFun q := ⟨q.val.val.2, q.val.property.2.1, by
    have hb : q.val.val.1 = b.val := congrArg Subtype.val q.property
    rw [← hb]
    exact q.val.property.2.2⟩
  invFun z := ⟨⟨(b.val, z.val), b.property, z.property⟩, rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val q.property).symm
    · rfl
  right_inv _ := rfl

end DuistermaatVanDerKallen
