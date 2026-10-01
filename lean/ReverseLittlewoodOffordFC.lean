import FormalConjecturesUtil
import ReverseLittlewoodOfford.Rate

/-!
# The odd-`n` exponential rate of the reverse Littlewood–Offord problem at radius one

This file states the fully inlined Formal Conjectures target and derives it from
`rootSeq_tendsto`. The final axiom audit is at the end of this file.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Filter Topology

/-- The inlined Formal Conjectures statement is `rootSeq_tendsto` with every definition
unfolded. -/
theorem inline_statement_iff_helper :
    Tendsto
      (fun k : ℕ =>
        (⨅ v : {v : Fin (2 * k + 1) → ℂ // ∀ i, ‖v i‖ = 1},
          ((Finset.univ.filter fun ε : Fin (2 * k + 1) → Bool =>
              ‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1).card : ℝ) / 2 ^ (2 * k + 1))
          ^ (1 / (2 * k + 1 : ℝ)))
      atTop (𝓝 (1 / Real.sqrt 2)) ↔
    Tendsto rootSeq atTop (𝓝 (1 / Real.sqrt 2)) :=
  Iff.rfl

/-- The Formal Conjectures target with the answer filled in. -/
theorem reverse_littlewood_offord_rate :
    Tendsto
      (fun k : ℕ =>
        (⨅ v : {v : Fin (2 * k + 1) → ℂ // ∀ i, ‖v i‖ = 1},
          ((Finset.univ.filter fun ε : Fin (2 * k + 1) → Bool =>
              ‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1).card : ℝ) / 2 ^ (2 * k + 1))
          ^ (1 / (2 * k + 1 : ℝ)))
      atTop (𝓝 (answer(1 / Real.sqrt 2) : ℝ)) :=
  inline_statement_iff_helper.mpr rootSeq_tendsto

#print axioms inline_statement_iff_helper
#print axioms reverse_littlewood_offord_rate

end ReverseLittlewoodOfford
