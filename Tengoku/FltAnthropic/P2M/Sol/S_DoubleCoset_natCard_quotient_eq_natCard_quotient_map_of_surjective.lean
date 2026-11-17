import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective

set_option autoImplicit false

/--
@isnad1 id=eq.2h5v.s7.2515ba6c1fff from=translated src=- shape=66b0ee2d vocab=df80257e
-/
theorem solution
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (H K : Subgroup G) (hH : f.ker ≤ H) :
    Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (H.map f : Set Q) (K.map f : Set Q)) := by

  let φ : DoubleCoset.Quotient (H : Set G) (K : Set G) → DoubleCoset.Quotient (H.map f : Set Q) (K.map f : Set Q) :=
    Quotient.map' f (fun x y hxy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
      exact DoubleCoset.rel_iff.mpr ⟨f a, Subgroup.mem_map_of_mem f ha, f b, Subgroup.mem_map_of_mem f hb,
        by rw [map_mul, map_mul]⟩)
  have hφ : ∀ x : G, φ (DoubleCoset.mk H K x) = DoubleCoset.mk (H.map f) (K.map f) (f x) := fun _ => rfl
  refine Nat.card_congr (Equiv.ofBijective φ ⟨?_, ?_⟩)
  ·
    intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn' with | h x => ?_
    induction q₂ using Quotient.inductionOn' with | h y => ?_
    change φ (DoubleCoset.mk H K x) = φ (DoubleCoset.mk H K y) at h
    rw [hφ, hφ, DoubleCoset.eq] at h
    obtain ⟨a', ha', b', hb', hy⟩ := h
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    change DoubleCoset.mk H K x = DoubleCoset.mk H K y
    rw [DoubleCoset.eq]
    have hn : y * (a * x * b)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, ← hy, mul_inv_cancel]
    refine ⟨y * (a * x * b)⁻¹ * a, H.mul_mem (hH hn) ha, b, hb, ?_⟩
    group
  ·
    intro q
    induction q using Quotient.inductionOn' with | h z => ?_
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨DoubleCoset.mk H K x, hφ x⟩

