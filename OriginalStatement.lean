import Mathlib

/-!
# The original square-root supersaturation question

Erdős problem 60 asks for a positive absolute constant in a square-root
lower bound for ordinary four-cycle copies above the actual extremal number.
The asymptotic quantifier is expressed by `Filter.atTop` on the natural numbers.
-/

open Filter SimpleGraph

namespace Erdos60Statement

/-- The original proposed uniform square-root lower bound. -/
def squareRootSupersaturation : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
          c * Real.sqrt (n : ℝ) ≤
            ({H : G.Subgraph | Nonempty (H.coe ≃g cycleGraph 4)}.ncard : ℝ)

end Erdos60Statement
