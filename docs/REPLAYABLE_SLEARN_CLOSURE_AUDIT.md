# Replayable Slearn closure audit

This module derives the auditability requirement for a Slearn closure version:
the invariant is neither fixed axioms, fixed geometry, nor a fixed verifier.
It is a published record from which a lawful successor can be replayed.

[`ReplayableSlearnClosureAudit.lean`](../Slearn/ReplayableSlearnClosureAudit.lean)
separates two conditions that must not be collapsed:

\[
\operatorname{TruthAgreement}(A,G)
\quad\neq\quad
\operatorname{LawfulSuccession}.
\]

`TruthAgreement` means the predecessor and successor each close their local
perspective and goal in their declared witness relation. `Lawful` additionally
checks that the published record reconstructs all of the actual bridges:

```text
returned perspective → successor perspective
derived verifier → successor current verifier
derived axiometry frame → successor current frame
further relation → successor observed material
successor fresh held-out relation ≠ re-entered material
```

`auditStep auditor record` holds only when the record is lawful and the
modeled auditor identity differs from the publisher identity. `TrueClosure`
requires both the truth relation and that replayable audit step. Under the
stated identity separation, Lean proves:

\[
\operatorname{TrueClosure}(r)
\iff
\operatorname{Lawful}(r).
\]

It also proves that an author cannot independently audit their own record and
that a truth-agreeing finite forged record does not certify succession. The
finite example confirms the intended timing: the first relation re-enters as
observed material; a distinct successor relation remains held out and OPEN.

## Scope boundary

The identity test `auditor ≠ publisher` is only a formal separation of names.
It does not prove actual independence, reproduce an external experiment,
validate a new mathematical foundation, or establish broad language/axiometry
invariance. The current source and experiment records remain `PATH` and
`DESIGN_READY`; the module defines what a future published record must carry
before it can be called an audited true closure in this bounded model.
