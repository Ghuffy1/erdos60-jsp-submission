# A formal disproof of the square-root bound in Erdős problem 60

This project proves that no positive absolute constant gives a square-root lower
bound for the number of ordinary four-cycle copies in every sufficiently large
finite simple graph with more edges than the actual four-cycle extremal number.
The corresponding Justin Sun Prize catalog entry is JSP-000079.

## Main theorem

`JSP79.disproof` refutes `Erdos60Statement.squareRootSupersaturation`.
`OriginalStatement.lean` states the original asymptotic assertion explicitly using
Mathlib definitions. `StatementAudit.original_problem_false` spells out the full
proposition directly. `JSP79.arbitrarily_large_failures` states that every proposed
positive constant fails at arbitrarily large graph orders.

The full mathematical proof is in `Erdos60Proof.lean`. The project imports Mathlib
directly. The mathematical interface and its equivalence to the proof's internal
statement are described in [STATEMENT.md](STATEMENT.md).

## Authors

Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and
Liam Kruer (lkruer) receive equal contribution credit. Names are ordered by surname.
Ghuffy1 is the designated owner and primary submitting account. The work was
developed with assistance from OpenAI's AI systems. [AUTHORS.md](AUTHORS.md)

## Reproduction

Use the exact commit named in the submission record. The toolchain is
`leanprover/lean4:v4.35.0-rc2`. Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and `lake-manifest.json` records all
dependency revisions.

```sh
lake exe cache get
lake --wfail build Erdos60Proof
lake --wfail build
lake build +JSP79 +StatementAudit
lake env lean AxiomAudit.lean
```

The default build includes `JSP79` and `StatementAudit`, which import the complete
proof. The axiom audit prints the target declarations and their complete transitive
axiom lists. The expected axioms are contained in `propext`, `Classical.choice`, and
`Quot.sound`. The release verification report records the exact checks performed
on the selected proof commit.

## Mathematical exposition and prior work

The paper is [paper/erdos-60-proof.pdf](paper/erdos-60-proof.pdf), with its source
alongside it. It develops the extremal-graph and matrix argument behind the
negative resolution. [PRIOR_WORK.md](PRIOR_WORK.md) records the public 2019
vertex-splitting construction, the 2021 announcement reported by Ning and Zhai,
and related JSP submissions. First-discovery priority is unresolved.

## Submission and verification

The original repository for this contribution is
https://github.com/Ghuffy1/erdos60-jsp-submission, on branch `main`.
Ghuffy1 is the primary submitting account.

The selected proof revision and the results of its final review appear in
[verification/report.md](verification/report.md). The report covers the full
original-problem statement, clean compilation, axiom dependencies, independent
statement comparison and separate kernel checks. The verification evidence is
added after the selected proof revision, which remains the version submitted
for review.

The mathematical solution and formalization are submitted for independent JSP
review. JSP assesses acceptance, attribution, priority and awards.
