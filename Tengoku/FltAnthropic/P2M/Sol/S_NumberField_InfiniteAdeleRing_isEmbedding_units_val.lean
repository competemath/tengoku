import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfiniteAdeleRing_isEmbedding_units_val.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfiniteAdeleRing_isEmbedding_units_val

set_option autoImplicit false

open NumberField

/--
@isnad1 id=isembedd.0h1v.s6.8a91586f5032 from=translated src=- shape=1e799a07 vocab=a0e3b115
-/
theorem solution
    (K : Type) [Field K] [NumberField K] :
    Topology.IsEmbedding (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K)  := by

  refine Units.isEmbedding_val_mk' (f := fun x : InfiniteAdeleRing K => fun w : InfinitePlace K => (x w)⁻¹) ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    have hc : ContinuousOn (fun x : InfiniteAdeleRing K => x w) {x : InfiniteAdeleRing K | IsUnit x} := (continuous_apply w).continuousOn
    refine ContinuousOn.inv₀ hc fun x hx => ?_
    obtain ⟨u, rfl⟩ := hx
    exact (u.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).toMonoidHom).ne_zero
  · intro u
    funext w
    have h := congrFun u.inv_mul w

    have h' : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w * ((u : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 := h
    exact (eq_inv_of_mul_eq_one_left h').symm
