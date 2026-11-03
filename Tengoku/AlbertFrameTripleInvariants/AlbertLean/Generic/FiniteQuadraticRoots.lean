import Tengoku.Seed.Algebra.QuadraticAlgebra.Basic
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms oneRootField_nonempty` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rootField_nonempty` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rootField_nonempty_of_fintype` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms charZero_of_embedding` (it only prints; the queue checks the axioms of every declaration). -/

/-! A common extension containing finitely many requested square roots.
No algebraic closure or square-root-surjectivity premise is assumed. -/

noncomputable section
namespace AlbertLean.Generic.FiniteQuadraticRoots

universe u v

structure OneRootField (K : Type u) [Field K] (c : K) where
  Carrier : Type u
  [instField : Field Carrier]
  embedding : K →+* Carrier
  root : Carrier
  root_sq : root ^ 2 = embedding c

attribute [instance] OneRootField.instField

/--
@isnad1 id=nonempty.0h2v.s3.fccc1ccf8aba from=translated src=- shape=3883d05c vocab=eb04f339
-/
theorem oneRootField_nonempty (K : Type u) [Field K] (c : K) :
    Nonempty (OneRootField K c) := by
  classical
  by_cases hc : IsSquare c
  · obtain ⟨r, hr⟩ := hc
    exact ⟨{
      Carrier := K
      embedding := RingHom.id K
      root := r
      root_sq := by simpa only [pow_two, RingHom.id_apply] using hr.symm }⟩
  · letI : Fact (¬ IsSquare c) := ⟨hc⟩
    refine ⟨{
      Carrier := QuadraticAlgebra K c 0
      embedding := algebraMap K (QuadraticAlgebra K c 0)
      root := QuadraticAlgebra.omega
      root_sq := ?_ }⟩
    simpa only [pow_two, map_zero, zero_mul, add_zero] using
      (QuadraticAlgebra.omega_mul_omega_eq_algebraMap
        (R := K) (a := c) (b := 0))

structure RootField (K : Type u) [Field K] {ι : Type v} (c : ι → K) where
  Carrier : Type u
  [instField : Field Carrier]
  embedding : K →+* Carrier
  roots : ι → Carrier
  roots_sq : ∀ i, roots i ^ 2 = embedding (c i)

attribute [instance] RootField.instField

/-- All requested roots lie in one common field, even when successive
quadratics start splitting after earlier adjunctions.
@isnad1 id=nonempty.0h3v.s4.826e9c13d308 from=translated src=- shape=85bb825c vocab=abdc7039
-/
theorem rootField_nonempty : ∀ n : ℕ, ∀ (K : Type u) [Field K]
    (c : Fin n → K), Nonempty (RootField K c) := by
  intro n
  induction n with
  | zero =>
      intro K _ c
      exact ⟨{
        Carrier := K
        embedding := RingHom.id K
        roots := Fin.elim0
        roots_sq := fun i => Fin.elim0 i }⟩
  | succ n ih =>
      intro K _ c
      obtain ⟨E⟩ := oneRootField_nonempty K (c 0)
      obtain ⟨F⟩ := ih E.Carrier (fun i => E.embedding (c i.succ))
      refine ⟨{
        Carrier := F.Carrier
        embedding := F.embedding.comp E.embedding
        roots := Fin.cases (F.embedding E.root) F.roots
        roots_sq := ?_ }⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cases_zero, RingHom.comp_apply, map_pow] using
          congrArg F.embedding E.root_sq
      · simpa only [Fin.cases_succ, RingHom.comp_apply] using F.roots_sq j

/-- The same common-extension result for any finite indexing type.
@isnad1 id=nonempty.0h3v.s4.0537bad6ee00 from=translated src=- shape=5ad5fac5 vocab=adfc2388
-/
theorem rootField_nonempty_of_fintype (K : Type u) [Field K]
    {ι : Type v} [Fintype ι] (c : ι → K) : Nonempty (RootField K c) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨F⟩ := rootField_nonempty (Fintype.card ι) K (fun i => c (e.symm i))
  refine ⟨{
    Carrier := F.Carrier
    embedding := F.embedding
    roots := fun i => F.roots (e i)
    roots_sq := ?_ }⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using F.roots_sq (e i)

/-- Characteristic zero survives the supplied field embedding.
@isnad1 id=charzero.0h3v.s5.7f1571d535de from=translated src=- shape=8157dbee vocab=2adec685
-/
theorem charZero_of_embedding {K L : Type u} [Field K] [Field L] [CharZero K]
    (f : K →+* L) : CharZero L where
  cast_injective m n h := Nat.cast_injective (R := K) (f.injective (by
    simpa only [map_natCast] using h))

end AlbertLean.Generic.FiniteQuadraticRoots
