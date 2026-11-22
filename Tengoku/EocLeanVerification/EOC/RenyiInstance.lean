import Tengoku.EocLeanVerification.EOC.RenyiBarrier
import Tengoku.EocLeanVerification.EOC.PsiSieve
import Tengoku.EocLeanVerification.EOC.PsiShellBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Rényi / prefix-sharing barrier for the (C3) split of `Ψ`

Instantiates `RenyiBarrier` with `PsiSieve.Fpre` / `PsiSieve.Gsuf` (split of the `Ψ` path product
at step `N`, `psi_split`).  With `g_S := #shellV b j0 N S (σ − S)` (so `‖Gsuf‖ ≤ g_S`,
`PsiSieve.norm_Gsuf_le`):

* `sum_sq_split_le_aligned` — for every interval `a + range H`,
  `∑_k ‖∑_S Fpre·Gsuf‖² ≤ ∑_k (∑_S g_S ‖Fpre(S, a+k)‖)²`;
* `aligned_split_attains` — there are unimodular phases `c λ S` such that replacing `Gsuf` by
  `g_S · c λ S` gives **equality**.  Hence *no argument that uses only `‖Gsuf‖ ≤ g_S` can beat
  `∑_k (∑_S g_S ‖Fpre‖)²`* — the continuation must be used through genuine cancellation;
* `path_sq_le_aligned` — the same bound for the `Ψ` path product itself (via `psi_split`);
* `sq_card_shellP_le_prefix_sharing` — prefix-sharing collisions:
  `|P_σ|² ≤ #(N-prefixes) · #{(P,Q) ∈ P_σ² : pre N P = pre N Q}`, and the exact count
  `card_prefix_sharing` `= ∑_c #fibre(c)²` (Rényi-2 collisions of the prefix law).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace RenyiInstance

open Finset PrefixCollision PsiSieve RenyiBarrier

variable (b : ℕ → ℕ)

/-- Continuation sizes `g_S = #shellV b j0 N S (σ − S)`.-/
noncomputable def gS (j0 N σ S : ℕ) : ℝ := ((shellV b j0 N S (σ - S)).card : ℝ)

/--
@isnad1 id=le.0h5v.s4.2a37858a65e2 from=translated src=- shape=55700d45 vocab=1224d742
-/
theorem gS_nonneg (j0 N σ S : ℕ) : 0 ≤ gS b j0 N σ S := Nat.cast_nonneg _

/--
@isnad1 id=le.0h7v.s5.365f8a6e859a from=translated src=- shape=365009d9 vocab=82e568c4
-/
theorem norm_Gsuf_le_gS (m j0 N σ S lam : ℕ) : ‖Gsuf b m j0 N σ S lam‖ ≤ gS b j0 N σ S :=
  norm_Gsuf_le b m j0 N σ S lam

/-- **Upper bound (Minkowski form is all that `‖Gsuf‖ ≤ g_S` gives)**: on every interval
`a + range H`, `∑_k ‖∑_S Fpre·Gsuf‖² ≤ ∑_k (∑_S g_S ‖Fpre(S, a+k)‖)²`.
@isnad1 id=le.0h7v.s7.f62a075d2fbd from=translated src=- shape=1aa406d6 vocab=b01732a8
-/
theorem sum_sq_split_le_aligned (m j0 N σ a H : ℕ) :
    ∑ k ∈ range H, ‖∑ S ∈ range (σ + 1), Fpre b m N S (a + k) * Gsuf b m j0 N σ S (a + k)‖ ^ 2 ≤
      ∑ k ∈ range H, (∑ S ∈ range (σ + 1), gS b j0 N σ S * ‖Fpre b m N S (a + k)‖) ^ 2 :=
  sum_sq_le_aligned (range H) (range (σ + 1)) (fun k S => Fpre b m N S (a + k))
    (fun k S => Gsuf b m j0 N σ S (a + k)) (gS b j0 N σ)
    (fun k _ S _ => norm_Gsuf_le_gS b m j0 N σ S (a + k))

/-- **Sharpness (the barrier)**: there exist unimodular phase families `c k S` such that the
admissible continuations `G k S := g_S · c k S` (which satisfy `‖G‖ = g_S`, exactly the only
information used about `Gsuf`) attain the bound of `sum_sq_split_le_aligned` with equality.
Therefore no argument that uses only `‖Gsuf‖ ≤ g_S` can beat
`∑_k (∑_S g_S ‖Fpre(S, a+k)‖)²`.
@isnad1 id=ex.0h7v.s7.5fb544034744 from=translated src=- shape=f7313bc7 vocab=fcb74ee4
-/
theorem aligned_split_attains (m j0 N σ a H : ℕ) :
    ∃ c : ℕ → ℕ → ℂ, (∀ k S, ‖c k S‖ = 1) ∧
      ∑ k ∈ range H, ‖∑ S ∈ range (σ + 1),
          Fpre b m N S (a + k) * ((gS b j0 N σ S : ℂ) * c k S)‖ ^ 2 =
        ∑ k ∈ range H, (∑ S ∈ range (σ + 1), gS b j0 N σ S * ‖Fpre b m N S (a + k)‖) ^ 2 :=
  aligned_attains (range H) (range (σ + 1)) (fun k S => Fpre b m N S (a + k)) (gS b j0 N σ)
    (fun S _ => gS_nonneg b j0 N σ S)

/-- Admissible phase-aligned continuations are admissible: `‖g_S · c‖ = g_S`.
@isnad1 id=eq.1h6v.s5.3f6942bb3a8d from=translated src=- shape=8aeecd4f vocab=cb0d2f42
-/
theorem norm_aligned_eq (j0 N σ S : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(gS b j0 N σ S : ℂ) * z‖ = gS b j0 N σ S := by
  rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gS_nonneg b j0 N σ S)]

/-- Combined barrier: some admissible continuations force the split energy to be at least
`(1/H)(∑_k ∑_S g_S ‖Fpre‖)²`.
@isnad1 id=ex.0h7v.s7.a89cfc3888e5 from=translated src=- shape=946f7254 vocab=f92d58ce
-/
theorem split_barrier (m j0 N σ a H : ℕ) :
    ∃ c : ℕ → ℕ → ℂ, (∀ k S, ‖c k S‖ = 1) ∧
      (∑ k ∈ range H, ∑ S ∈ range (σ + 1), gS b j0 N σ S * ‖Fpre b m N S (a + k)‖) ^ 2 ≤
        (range H).card * ∑ k ∈ range H, ‖∑ S ∈ range (σ + 1),
          Fpre b m N S (a + k) * ((gS b j0 N σ S : ℂ) * c k S)‖ ^ 2 :=
  barrier (range H) (range (σ + 1)) (fun k S => Fpre b m N S (a + k)) (gS b j0 N σ)
    (fun S _ => gS_nonneg b j0 N σ S)

/-- The same upper bound for the `Ψ` path product itself (via `psi_split`).
@isnad1 id=le.2h7v.s7.daccc4265296 from=translated src=- shape=3c39bf0a vocab=8dd9ba1e
-/
theorem path_sq_le_aligned (m j0 N σ a H : ℕ) (hN1 : 1 ≤ N) (hNj : N < j0) :
    ∑ k ∈ range H, ‖∑ P ∈ shellP b j0 σ,
        ∏ i ∈ range j0, SwapBound.ee (cp (a + k) m i (P.prefixSum i))‖ ^ 2 ≤
      ∑ k ∈ range H, (∑ S ∈ range (σ + 1), gS b j0 N σ S * ‖Fpre b m N S (a + k)‖) ^ 2 := by
  have h : ∀ k, ∑ P ∈ shellP b j0 σ,
      ∏ i ∈ range j0, SwapBound.ee (cp (a + k) m i (P.prefixSum i)) =
      ∑ S ∈ range (σ + 1), Fpre b m N S (a + k) * Gsuf b m j0 N σ S (a + k) :=
    fun k => psi_split b m j0 N σ (a + k) hN1 hNj
  simp_rw [h]
  exact sum_sq_split_le_aligned b m j0 N σ a H

/-! ## Prefix-sharing collisions on `P_σ` -/

/-- Exact prefix-sharing collision count: `#{(P,Q) : pre N P = pre N Q} = ∑_c #fibre(c)²`.
@isnad1 id=eq.0h4v.s7.434c3f985269 from=translated src=- shape=51188ef2 vocab=ec1c2962
-/
theorem card_prefix_sharing (j0 σ N : ℕ) :
    (sharePairs (shellP b j0 σ) (fun P => pre N P)).card =
      ∑ c ∈ (shellP b j0 σ).image (fun P => pre N P),
        (fibre (shellP b j0 σ) (fun P => pre N P) c).card ^ 2 :=
  card_sharePairs _ _

/-- **Rényi / Cauchy–Schwarz lower bound on prefix sharing**:
`|P_σ|² ≤ #(N-prefixes) · #{(P,Q) ∈ P_σ² : pre N P = pre N Q}`.
@isnad1 id=le.0h4v.s6.1329e2fba32b from=translated src=- shape=3e6425f6 vocab=0965d2d3
-/
theorem sq_card_shellP_le_prefix_sharing (j0 σ N : ℕ) :
    (shellP b j0 σ).card ^ 2 ≤
      ((shellP b j0 σ).image (fun P => pre N P)).card *
        (sharePairs (shellP b j0 σ) (fun P => pre N P)).card :=
  sq_card_le_image_mul_sharePairs _ _

end RenyiInstance
end EOC
