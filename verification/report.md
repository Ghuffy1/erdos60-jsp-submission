# Verification passed

The full original square-root assertion in Erdős problem 60 is false, as proved
by `JSP79.disproof` at proof commit `62aa60b23089cbd4729f1fc4cc850620228c9038`.
This report records a final submission audit completed on
2026-11-14T17:43:50.455668+00:00.

| Question | Judgment | Evidence |
| --- | --- | --- |
| Does the proof address the original problem? | Yes | The original graph model, strict extremal threshold, ordinary cycle count and uniform asymptotic quantifiers agree with the independently specified challenge. |
| Did the exact selected commit pass? | Yes | A clean checkout of `62aa60b23089cbd4729f1fc4cc850620228c9038` passed all listed checks. |
| Does it fully solve the original problem? | Yes, by disproof | The parameter-free main theorem refutes every eventual uniform positive square-root bound. |
| Does it meet the Lean completeness requirements? | Meets | Every target has only the three standard classical axioms in its dependency closure. |

## Original statement and scope

The source asks whether every n-vertex graph with more than ex(n,C4) edges has
at least a positive absolute constant times sqrt(n) copies of C4.
The constant is uniform over graph orders and graphs. Ordinary cycle subgraphs
are counted, including cycles in graphs with additional edges among their vertices.
The formal statement retains these objects and quantifiers.
[Original problem](https://www.erdosproblems.com/60)

`OriginalStatement.lean` gives the proposed original statement.
`JSP79.formalizations_agree` connects it to the proposition used internally by
the proof. `StatementAudit.original_problem_false` repeats the full negated
statement directly. `JSP79.arbitrarily_large_failures` states failure beyond
each proposed order threshold. The coverage matrix is in
[STATEMENT.md](https://github.com/Ghuffy1/erdos60-jsp-submission/blob/62aa60b23089cbd4729f1fc4cc850620228c9038/STATEMENT.md).

The audit-only challenge was specified independently using Mathlib. It imports
the original graph definitions and states the same three public conclusions.
The comparator checked their full types and transitive definitions against the
submitted export. It checked standard primitives and allowed axioms, then
replayed the proof export in a fresh kernel environment.

## Reproduction and checks

The toolchain is `leanprover/lean4:v4.35.0-rc2`, release commit
`11acb17ec6b07a8f9e9173e6845197929540936b`. Mathlib is pinned at
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. All nine dependency source revisions
matched `lake-manifest.json`, with clean tracked dependency trees before and after.
The proof sources were rebuilt from a fresh Git checkout.

Execution used a Windows AppContainer with zero capabilities, an explicit
environment whitelist, copied dependencies, a 32 GiB job memory limit and
bounded CPU and wall time. Negative controls confirmed that an outside canary
file was inaccessible for reading and writing and that a parent-accessible
loopback service was inaccessible from the proof process.

```sh
git clone https://github.com/Ghuffy1/erdos60-jsp-submission
cd erdos60-jsp-submission
git checkout --detach 62aa60b23089cbd4729f1fc4cc850620228c9038
lake exe cache get
lake --wfail build Erdos60Proof
lake --wfail build
lake build +JSP79 +StatementAudit
lake env lean JSP79.lean
lake env lean StatementAudit.lean
lake env lean AxiomAudit.lean
```

The clean build passed with warnings treated as errors. Informational suggestions
from speculative tactic branches are present in the full log. The official JSP
audit script passed all four target source, type and axiom checks with stable
inputs and mechanical status `standard_axioms_only`.

| Check | Exit code | Seconds |
| --- | --- | --- |
| `isolation-negative-controls` | 0 | 1.188 |
| `lean-version` | 0 | 0.063 |
| `lake-version` | 0 | 0.062 |
| `clean-core-build` | 0 | 236.875 |
| `clean-default-build` | 0 | 57.703 |
| `full-axiom-audit` | 0 | 20.562 |
| `official-target-audit` | 0 | 182.266 |
| `export-proof` | 0 | 23.641 |
| `separate-kernel-replay` | 0 | 56.593 |
| `build-independent-challenge` | 0 | 20.906 |
| `export-independent-challenge` | 0 | 11.500 |
| `independent-statement-comparator` | 0 | 114.313 |
| `independent-nanoda-kernel` | 0 | 14.015 |

| Target or bridge | Complete transitive axiom list |
| --- | --- |
| `JSP79.disproof` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP79.formalizations_agree` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP79.arbitrarily_large_failures` | `propext`, `Classical.choice`, `Quot.sound` |
| `StatementAudit.original_problem_false` | `propext`, `Classical.choice`, `Quot.sound` |

No target depends on an admission, a new unproved axiom or native-evaluation
trust. The standalone Lean checker accepted the proof export. The comparator
accepted the independent original-problem challenge. Nanoda 0.4.17 independently
checked 43,076 declarations with no errors and printed only the three allowed
axioms. The exported proof's SHA-256 is
`21aefbfc953f2b41fcf173159b450eaa632b64167a7682ae5d3f9d051d66122b`.

The exporter is pinned at `6cea97789dc088ea47fcea15692db85685aedac5` and the
comparator at `32bd61da1d68fbaa310234964e9b820b03a0f82f`. An earlier optional
lean4lean probe was incompatible with the pinned standard-library object format.
The final verification used the successful standalone checker, comparator and
Nanoda checks listed above. Full execution evidence is retained locally.

## Submission review and attribution

The catalog patch applies to awards revision
`10e0ab6e7503b6db769029d7d68cc4ca42c011d7`. JSP's catalog validation and all 54
repository tests passed. The patch changes only the relevant status, proof,
attribution and publication fields for JSP-000079. The current complete-solution
requirements and original statement were reviewed again before publication.
[Submission requirements](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/CONTRIBUTING.md)

Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and
Liam Kruer (lkruer) receive equal contribution credit. Ghuffy1 owns the original
repository and is the primary submitter. AI assistance and reused geometric
foundations are disclosed in [AUTHORS.md](https://github.com/Ghuffy1/erdos60-jsp-submission/blob/62aa60b23089cbd4729f1fc4cc850620228c9038/AUTHORS.md) and
[THIRD_PARTY.md](https://github.com/Ghuffy1/erdos60-jsp-submission/blob/62aa60b23089cbd4729f1fc4cc850620228c9038/THIRD_PARTY.md).

The 15-page mathematical paper was checked for author order and readable layout.
It states the complete negative result and credits the prior literature.
The 2019 vertex-splitting construction and the stronger 2021 announcement are
documented in [PRIOR_WORK.md](https://github.com/Ghuffy1/erdos60-jsp-submission/blob/62aa60b23089cbd4729f1fc4cc850620228c9038/PRIOR_WORK.md). Mathematical priority remains
unresolved. This submission requests JSP review of correctness, contribution
attribution and priority. The report is an AI-assisted pre-submission audit.
JSP's independent review and award decisions remain pending.

This evidence is added after the selected proof commit. It certifies the proof
revision named above. The subsequent publication commit adds documentation and
verification evidence while retaining every proof and configuration file byte
for byte.
