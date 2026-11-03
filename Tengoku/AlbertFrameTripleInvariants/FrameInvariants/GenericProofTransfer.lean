import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Transport a quadratic generator and its unique coefficient representation
along a field isomorphism. This lemma makes no assertion about individual fibers. -/
noncomputable section
namespace FrameInvariants.GenericTransfer

variable {M N : Type*} [Field M] [Field N]

theorem quadratic_basis (e : M ≃+* N) (H B : Subfield M) (H' B' : Subfield N)
    (d : M) (d' : N) (hd : e d = d')
    (hH : ∀ x, x ∈ H ↔ e x ∈ H') (hB : ∀ x, x ∈ B ↔ e x ∈ B')
    (hne : d' ∉ H')
    (hquad : ∃ s p : H', d' ^ 2 - (s : N) * d' + (p : N) = 0)
    (hbasis : ∀ x : B', ∃! ab : H' × H',
      (ab.1 : N) + (ab.2 : N) * d' = (x : N)) :
    d ∉ H ∧
    (∃ s p : H, d ^ 2 - (s : M) * d + (p : M) = 0) ∧
    (∀ x : B, ∃! ab : H × H,
      (ab.1 : M) + (ab.2 : M) * d = (x : M)) := by
  have back_mem (a : H') : e.symm (a : N) ∈ H := by
    apply (hH _).mpr
    simpa using a.property
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    simpa [hd] using (hH d).mp h
  · obtain ⟨s, p, hp⟩ := hquad
    refine ⟨⟨e.symm s, back_mem s⟩, ⟨e.symm p, back_mem p⟩, ?_⟩
    apply e.injective
    simpa only [map_add, map_sub, map_mul, map_pow, map_zero,
      RingEquiv.apply_symm_apply, hd] using hp
  · intro x
    obtain ⟨ab, hab, huniq⟩ := hbasis ⟨e x, (hB x).mp x.property⟩
    let cd : H × H := (⟨e.symm ab.1, back_mem ab.1⟩,
      ⟨e.symm ab.2, back_mem ab.2⟩)
    have hcd : (cd.1 : M) + (cd.2 : M) * d = (x : M) := by
      apply e.injective
      simpa only [cd, map_add, map_mul, RingEquiv.apply_symm_apply, hd] using hab
    refine ⟨cd, hcd, ?_⟩
    intro yz hyz
    let old : H' × H' := (⟨e yz.1, (hH yz.1).mp yz.1.property⟩,
      ⟨e yz.2, (hH yz.2).mp yz.2.property⟩)
    have hold : (old.1 : N) + (old.2 : N) * d' = e x := by
      simpa only [old, map_add, map_mul, hd] using congrArg e hyz
    have heq : old = ab := huniq old hold
    apply Prod.ext
    · apply Subtype.ext
      apply e.injective
      have h := congrArg (fun z : H' × H' => (z.1 : N)) heq
      simpa only [old, cd, RingEquiv.apply_symm_apply] using h
    · apply Subtype.ext
      apply e.injective
      have h := congrArg (fun z : H' × H' => (z.2 : N)) heq
      simpa only [old, cd, RingEquiv.apply_symm_apply] using h

end FrameInvariants.GenericTransfer
