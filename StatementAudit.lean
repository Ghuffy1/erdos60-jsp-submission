import JSP79

/-! # Direct statement-to-proof checks for the original mathematical question -/

namespace StatementAudit

/-- The complete original assertion is refuted with all quantifiers expanded. -/
theorem original_problem_false :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) < G.edgeFinset.card →
            c * Real.sqrt (n : ℝ) ≤
              ({H : G.Subgraph |
                Nonempty (H.coe ≃g SimpleGraph.cycleGraph 4)}.ncard : ℝ)) := by
  exact JSP79.disproof

end StatementAudit
