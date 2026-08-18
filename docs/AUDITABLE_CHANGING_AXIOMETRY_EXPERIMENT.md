# Auditable changing-axiometry experiment

This is a bounded, falsifiable experiment protocol derived from the current
grant-oriented source. It does not claim that Slearn has built ASI, that it
works for all mathematics, or that a declared external outcome is actually
independent. It instead makes every required claim and failure point explicit.

## The completion condition

At stage `t`, axiom and geometry are different presentations:

\[
A_t \neq G_t
\quad\text{as presentations.}
\]

Completion is **not** their literal syntactic identity. It is equality in the
admitted translation's declared witness relation:

\[
[A_t]_{\mathcal C}=[G_t]_{\mathcal C},
\qquad
\Delta_t\ \text{retained}.
\]

The code calls this `closureTruth`. That name has a deliberately narrow scope:
it is a proved equality of the supplied witness values, not an unconditional
claim of mathematical, physical, or metaphysical truth.

The next frame and verifier receive both the completed relation and its
residue:

\[
(A_{t+1},G_{t+1})=\Phi(C_t,\Delta_t),
\qquad
M_{t+1}=\Psi(C_t,\Delta_t).
\]

The protocol additionally requires that each derived object differs from its
predecessor in the stated model. That blocks a run from calling a frozen replay
“development,” though it does not by itself demonstrate useful novelty.

## Required run and failure points

```text
independent frame generation and freeze
  → native translation discovered after freeze
  → identity-independent validation
  → independent return
  → axiom–geometry closure truth + retained residue
  → derived, changed next axiometry
  → derived, changed next verifier
  → held-out relation: old verifier cannot evaluate; new verifier can
  → prediction before independently supplied outcome
```

Each arrow can fail. The corresponding negative results are: no native
translation, failed validation or return, no relative closure witness, a frozen
next axiometry/verifier, no held-out capability gain, or a mismatched external
outcome. A passing run supports only the bounded hypothesis that these supplied
relations were auditable under the stated conditions.

## Machine-checked contract

[`AuditableChangingAxiometryProtocol.lean`](../Slearn/AuditableChangingAxiometryProtocol.lean)
defines:

- `CompletedRelation`: frozen-frame native-translation, validation, return,
  closure witness, and residue;
- `AuditRun`: derivation and change of next axiometry/verifier, a single
  held-out relation interface, old non-evaluation, new evaluation, and
  externally evidenced prediction/outcome comparison.

The checked receipt establishes only the implications of this supplied record:
relative closure truth, changed next structures, old/new held-out distinction,
and matching outcome tokens. It cannot create an independent return, prove an
evidence source external, or infer a mathematical result from prose.

## Current execution state

[`framework/changing-axiometry-experiment.json`](../framework/changing-axiometry-experiment.json)
contains the source-derived protocol with every execution evidence field open.
Run:

```sh
node scripts/run-changing-axiometry-protocol.mjs
```

It must report `DESIGN_READY`, not a passing experiment. That means the grant
question has been converted into an auditable protocol, but no generated frame,
native translation, held-out result, or independent consequence has been
claimed.
