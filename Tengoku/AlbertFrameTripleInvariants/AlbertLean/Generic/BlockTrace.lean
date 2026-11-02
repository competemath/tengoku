import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms trace_prod_blocks` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trace_prod_three_blocks` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.BlockTrace

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup N] [Module K N] [FiniteDimensional K N]

/-- The trace of an arbitrary endomorphism of a product is the sum of the
traces of its two diagonal blocks.-/
theorem trace_prod_blocks (L : M × N →ₗ[K] M × N) :
    LinearMap.trace K (M × N) L =
      LinearMap.trace K M
          ((LinearMap.fst K M N).comp (L.comp (LinearMap.inl K M N))) +
        LinearMap.trace K N
          ((LinearMap.snd K M N).comp (L.comp (LinearMap.inr K M N))) := by
  have hid :
      (LinearMap.inl K M N).comp (LinearMap.fst K M N) +
          (LinearMap.inr K M N).comp (LinearMap.snd K M N) =
        LinearMap.id := by
    ext x <;> simp [LinearMap.inl_apply, LinearMap.inr_apply]
  calc
    LinearMap.trace K (M × N) L =
        LinearMap.trace K (M × N) (LinearMap.id.comp L) := by rfl
    _ = LinearMap.trace K (M × N)
          (((LinearMap.inl K M N).comp (LinearMap.fst K M N) +
            (LinearMap.inr K M N).comp (LinearMap.snd K M N)).comp L) := by
          rw [hid]
    _ = LinearMap.trace K (M × N)
          ((LinearMap.inl K M N).comp
            ((LinearMap.fst K M N).comp L)) +
        LinearMap.trace K (M × N)
          ((LinearMap.inr K M N).comp
            ((LinearMap.snd K M N).comp L)) := by
          rw [LinearMap.add_comp, map_add]
          simp only [LinearMap.comp_assoc]
    _ = _ := by
      rw [LinearMap.trace_comp_comm'
            ((LinearMap.fst K M N).comp L) (LinearMap.inl K M N),
          LinearMap.trace_comp_comm'
            ((LinearMap.snd K M N).comp L) (LinearMap.inr K M N)]
      simp only [LinearMap.comp_assoc]

/-- Three diagonal blocks for the right-associated carrier `M × (N × P)`.-/
theorem trace_prod_three_blocks
    {P : Type*} [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    (L : M × (N × P) →ₗ[K] M × (N × P)) :
    LinearMap.trace K (M × (N × P)) L =
      LinearMap.trace K M
          ((LinearMap.fst K M (N × P)).comp
            (L.comp (LinearMap.inl K M (N × P)))) +
        LinearMap.trace K N
          ((LinearMap.fst K N P).comp
            ((LinearMap.snd K M (N × P)).comp
              (L.comp ((LinearMap.inr K M (N × P)).comp
                (LinearMap.inl K N P))))) +
        LinearMap.trace K P
          ((LinearMap.snd K N P).comp
            ((LinearMap.snd K M (N × P)).comp
              (L.comp ((LinearMap.inr K M (N × P)).comp
                (LinearMap.inr K N P))))) := by
  rw [trace_prod_blocks L]
  let L₂ : N × P →ₗ[K] N × P :=
    (LinearMap.snd K M (N × P)).comp
      (L.comp (LinearMap.inr K M (N × P)))
  rw [trace_prod_blocks L₂]
  simp only [L₂, LinearMap.comp_assoc, add_assoc]

end AlbertLean.Generic.BlockTrace
