import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsPrimitiveRoot_existsUnique_eq_pow_val.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsPrimitiveRoot_existsUnique_eq_pow_val

set_option autoImplicit false
open scoped IntermediateField Pointwise

theorem solution
    {R ι : Type*} [CommRing R] [IsDomain R] {ζ : Rˣ} {p : ℕ} [NeZero p] (hζ : IsPrimitiveRoot ζ p) (f : ι → Rˣ) (hf : ∀ i, f i ^ p = 1) :
    ∃! c : ι → ZMod p, ∀ i, f i = ζ ^ (c i).val := by
  have hex : ∀ i, ∃ k : ℕ, k < p ∧ ζ ^ k = f i := fun i =>
    hζ.eq_pow_of_mem_rootsOfUnity (by rw [mem_rootsOfUnity]; exact hf i)
  choose k hk hkf using hex
  refine ⟨fun i => (k i : ZMod p), fun i => ?_, fun c' hc' => ?_⟩
  · rw [ZMod.val_natCast_of_lt (hk i), hkf]
  · funext i
    have h := hc' i
    rw [← hkf i] at h
    have hv : (c' i).val = k i :=
      (hζ.pow_inj (ZMod.val_lt _) (hk i) h.symm)
    rw [← hv, ZMod.natCast_zmod_val]
