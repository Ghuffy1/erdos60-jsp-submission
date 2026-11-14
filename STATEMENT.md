# Correspondence with the original problem

## Original question

The full question in Thomas Bloom's Erdős Problem 60 record asks whether every
graph on n vertices with more than ex(n,C4) edges contains at least a positive
absolute constant times sqrt(n) ordinary copies of C4. The record attributes the
conjecture to Erdős and Simonovits and cites Er90 and Er93, page 335. The full page
and its mathematical context were read on 14 November 2026.
[Original problem record](https://www.erdosproblems.com/60)

The JSP entry is the quadrilateral supersaturation question JSP-000079.
[JSP catalog](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/problems/catalog-0001-0100.md#jsp-000079--how-many-quadrilaterals-are-forced-when-a-graphs-edge-count-exceeds-the-threshold-for-containing-one)

The notation for an absolute asymptotic lower bound means that there are constants
c > 0 and N such that the bound holds for every n >= N and every admissible graph.
The formal statement uses the equivalent `Filter.atTop` quantifier. Refuting this
eventual bound also refutes a bound asserted at every graph order.

## Formal statement

```lean
def squareRootSupersaturation : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) < G.edgeFinset.card →
          c * Real.sqrt (n : ℝ) ≤
            ({H : G.Subgraph |
              Nonempty (H.coe ≃g SimpleGraph.cycleGraph 4)}.ncard : ℝ)
```

The submitted theorem is `JSP79.disproof`, whose type is the negation of this
proposition. Its hypotheses contain no added mathematical assumptions.

## Coverage matrix

| Original requirement | Formal representation | Correspondence and evidence |
| --- | --- | --- |
| Arbitrary finite graph order | `n : ℕ` tending to `Filter.atTop` | Every sufficiently large natural order is included. |
| A constant independent of order and graph | `∃ c : ℝ, 0 < c ∧ ...` outside all later quantifiers | The same positive constant must serve every size and graph. |
| Finite simple graphs | `G : SimpleGraph (Fin n)` | Every n-vertex finite simple graph admits such a relabelling. The graph structure has symmetric, loopless adjacency. |
| No extra computability restriction | `[DecidableRel G.Adj]` | Classical decidability supplies an instance for every finite graph. No decision algorithm is a mathematical premise. |
| Actual extremal threshold | `SimpleGraph.extremalNumber n (cycleGraph 4)` | Mathlib's maximum edge count among n-vertex graphs avoiding C4, used directly by the statement and proof. |
| Strictly more edges | `extremalNumber ... < G.edgeFinset.card` | The strict inequality matches the question. The threshold is an integer. |
| Ordinary, unlabelled four-cycles | `{H : G.Subgraph | Nonempty (H.coe ≃g cycleGraph 4)}.ncard` | Each selected cycle subgraph is counted once. Extra ambient edges are allowed. Isomorphisms are witnesses, not the objects being counted. |
| Square-root scale | `c * Real.sqrt (n : ℝ)` | The real square root of the graph order is the scale in the original question. |
| Complete negative answer | `¬ squareRootSupersaturation` | No positive uniform constant works eventually. |
| Arbitrarily large failures | `JSP79.arbitrarily_large_failures` | For each c > 0 and each N, a size n >= N violates the required universal graph bound. |
| Internal statement fidelity | `JSP79.formalizations_agree` | Definitional equality connects the independently written statement with the proposition used by the proof. |
| Fully expanded audit target | `StatementAudit.original_problem_false` | The full original proposition is repeated without the named statement abbreviation. |

The extremal number, graph model, cycle count and square root retain their
Mathlib meanings throughout the public interface. The count is of cycle
subgraphs and permits chords in the ambient graph. It counts three cycle
subgraphs in a complete graph on four vertices. No induced-cycle condition or
labelled-isomorphism multiplier is introduced.

The original page's two-copy remark is historical context about an additional
lower bound. Its plane-order result for n = q^2 + q + 1 is a known restricted
case. Neither changes the quantifiers of the main question. A failure along an
unbounded sequence fully refutes the main uniform assertion.

## Proof chain

`JSP79.disproof` applies `Bounty.Erdos60Private.not_claimedBound` through
`JSP79.formalizations_agree`. The internal contradiction argument chooses its
parameters and extremizing graph from the assumed uniform bound. The apparent
assumptions inside that contradiction are discharged in the final theorem.
The verification report includes the declaration checks and transitive axiom
closures, plus an independently prepared challenge and kernel checks.

The formal endpoint is the complete negative resolution of the original
square-root question. The accompanying paper also discusses a structured
sequence of graph orders. The scope of each formally checked declaration is
given by its displayed type.
