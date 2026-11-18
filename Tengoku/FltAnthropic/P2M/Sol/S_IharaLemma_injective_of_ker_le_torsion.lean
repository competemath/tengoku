import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_injective_of_ker_le_torsion.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_injective_of_ker_le_torsion

set_option autoImplicit false

/--
@isnad1 id=injectiv.3h11v.s9.2098e50edcdd from=translated src=- shape=933c68ed vocab=f709314d
-/
theorem solution {R : Type*} [CommRing R] (S : Submonoid R)
    {V W V' W' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
    (g : V →ₗ[R] V') [IsLocalizedModule S g] (h : W →ₗ[R] W') [IsLocalizedModule S h]
    (f : V →ₗ[R] W) (F : V' →ₗ[R] W') (hcomm : ∀ v, F (g v) = h (f v))
    (E : Submodule R V) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0) (hker : ∀ v, f v = 0 → v ∈ E) :
    Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨v, s⟩, hv⟩ := IsLocalizedModule.surj S g x

  have hv' : (s : R) • x = g v := hv
  have hfv : h (f v) = 0 := by
    rw [← hcomm, ← hv', map_smul, hx, smul_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S h).mp hfv

  have hc' : (c : R) • f v = 0 := hc
  have hcv : f ((c : R) • v) = 0 := by rw [map_smul]; exact hc'
  obtain ⟨s', hs'⟩ := hE _ (hker _ hcv)

  apply IsLocalizedModule.smul_injective g (s' * c * s)
  show ((s' * c * s : S) : R) • x = ((s' * c * s : S) : R) • 0
  rw [smul_zero, Submonoid.coe_mul, Submonoid.coe_mul, mul_smul, mul_smul]
  rw [hv', ← map_smul, ← map_smul, hs', map_zero]

