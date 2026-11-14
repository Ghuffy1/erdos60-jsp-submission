import Erdos60Proof
import OriginalStatement

/-! # Complete negative resolution of the square-root claim in Erdős problem 60 -/

open Filter SimpleGraph

namespace JSP79

/-- The independently stated problem agrees with the proposition used by the proof. -/
theorem formalizations_agree :
    Erdos60Statement.squareRootSupersaturation ↔ Bounty.Erdos60Private.ClaimedBound := by
  rfl

/-- No positive absolute square-root lower bound exists above the extremal number. -/
theorem disproof : ¬ Erdos60Statement.squareRootSupersaturation := by
  intro h
  exact Bounty.Erdos60Private.not_claimedBound (formalizations_agree.mp h)

/-- Every positive proposed constant fails at some arbitrarily large order. -/
theorem arbitrarily_large_failures (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ¬ (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
          c * Real.sqrt (n : ℝ) ≤
            ({H : G.Subgraph | Nonempty (H.coe ≃g cycleGraph 4)}.ncard : ℝ)) := by
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply disproof
  exact ⟨c, hc, Filter.eventually_atTop.2 ⟨N, h⟩⟩

end JSP79
