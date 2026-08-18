# Framework closure integration

## Purpose

This is the bounded, repository-wide closure pass for Slearn. It identifies
the actual bridge each existing formal module and product source must provide
before it can participate in a later perspectival closure. It does not rename
all modules as one theorem, and it does not treat a browser action as a proof.

The common operational core is:

```text
local presentation
  → admitted translation / contraction
  → global presentation
  → admitted return / reopening
  → relation-relative return
  → retained difference or new OPEN relation
```

The learning projection is:

```text
perspective → value/belief → WHY → goal → world/universe
                            ↘ source → lesson → project → receipt → revised perspective
```

Every visible point, link, seed, and operation is generated from one selected
trace. A missing bridge, attempt, receipt, or global continuation remains
missing; it is never reconstructed as an unrelated UI component.

## Formal closure contract

[`NRRF654IntegratedFrameworkClosure.lean`](../Slearn/NRRF654IntegratedFrameworkClosure.lean)
is the new common adapter. `IntegratedFramework` takes an explicitly supplied:

- relative frame and natural-rhythm cone;
- admitted `Perspective ↔ Goal` translation;
- common `ClosureOp` and Slearn semantic runtime;
- equality witnesses that operation contraction/reopening are exactly the
  translation's forward/backward maps;
- equality of the runtime operation with that common operation;
- relation-as-witness equality; and
- a stated nonliteral continuation witness.

Under those supplied hypotheses, Lean proves:

| Checked statement | Meaning under the stated model |
| --- | --- |
| `round_closes` | Forward/return preserves the local witness. |
| `operation_recovers` | The common operation returns in its declared relation. |
| `many_one_many` | Relation-relative return and literal novelty coexist. |
| `runtime_zoom_is_translation_return` | Slearn semantic zoom is the same translation round. |
| `universal_completion_unique` | A closure operator is unique only under the earlier universal-relative admissibility contract. |
| `TranslationGeneratedMapWitness.bridge_closes` | A natural bridged UI trace closes in the supplied local/global witness language. |
| `InteractiveReceiptGate.receipt_has_translational_completion` | An optional, continuously checked receipt satisfies the finite-prefix completion condition. |
| `ResolutionAwareReceipt.all_grains_determine_direction` | An optional direction readout is determined only by agreement at all stated grains. |

`RelativeToposTuring.admittedTranslation` is the direct adapter that makes the
existing Topos/Turing encoding/evaluation interface an `AdmittedTranslation`.
It proves cross-language equality is exactly closure in that witness language.

## Existing-resource bridge map

| Resource | Role in the integrated framework | Required bridge / boundary |
| --- | --- | --- |
| `UniversalRelativeTranslationalCompletion.lean` | Unique fixed-point completion | Only after a `RelativeFrame` and universal-relative admissibility are supplied. |
| `NaturalRhythmClosure.lean` | Two orientations and local/global view discipline | Witness equality is not literal local/global identity; named degeneracies remain caller-supplied boundaries. |
| `ClosedTopologicalTranslation.lean` | Open interaction, inversion, returned relation, residue, new opening | A return witness does not erase continuation or residue. |
| `InteractiveTranslationalOpenFoundation.lean` | Finite verification versus continuous completion; Topos/Turing adapter | No finite prefix decides global soundness. A browser receipt is not continuously checked unless the optional gate is supplied. |
| `ChaitinKakeyaTokenResuperposition.lean` | Token, assumption-grain, and ordered-record projection | It is an optional readout of a receipt, not a numerical Chaitin or physical claim. |
| `NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean` | Shared contract/reopen/residue operation and semantic zoom | Relation-relative recovery must be stated; it does not follow from a contraction alone. |
| `NRRF651SlearnUIHairOfClosureGeneratedMap.lean` | Generated Slearn occurrences, learning materials, bridge-gated zoom | Points, learning occurrences, and actions retain an admitted trace. |
| `NRRF655ExecutablePerspectivalClosureEpisode.lean` | Executed closure-episode timeline | Contract, reopen, return, and next opening have typed predecessor states; return creates a changed successor and preserved residue. |
| `SLEARN_SOURCE_PROVENANCE.md` | Historical design evidence | It is a privacy-preserving source audit, not a theorem or a substitute for the original private notes. |
| `SLEARN_ORIGINAL_VISION.md` | Product grammar | Perspective, belief/value, WHY, goal, lesson/project, world/universe, and returned experience are interpreted as trace roles—not independent dashboard areas. |
| `ui/app/closureRuntime.ts` | Executable projection | Emits the spatial scene from trace data; it does not validate truth of prose, bridges, or receipts. |

## Runtime admission rules

| Projection | Runtime condition |
| --- | --- |
| Perspective / WHY / goal | All three fields are present: an admitted trace. |
| Value or belief | The selected trace carries context. |
| Contracted goal | The trace has a re-reading and preserved bridge. |
| World / universe continuation | The trace has the bridge and a stated global continuation. |
| Source | It is attached to the selected WHY relation. |
| Lesson | It is attached to the selected direction. |
| Project | An attempt exists. |
| Returned perspective | Bridge, attempt, receipt, and successor perspective all exist. |

The presence conditions are not operation completion. The runtime additionally
persists this execution discipline:

| Executed state | Required predecessor | State created |
| --- | --- | --- |
| `contracted` | Open bridged trace | Forward perspective → goal record |
| `reopened` | Contracted trace | Reciprocal goal → local re-reading record |
| `returned` | Reopened trace plus attempt, receipt, successor | Retained Ω residue and successor record |
| next `open` | Returned trace | A new proposal seeded by successor and inherited residue |

The browser geometry is a deterministic triangular projection of these roles:
the outward perspective/context/WHY/goal/world path and the inward
source/lesson/project/successor path. It is therefore a physical interaction
surface in the modest software sense—selection, contraction, reopening, and
return visibly change the closure state. Lean does **not** prove that pixels,
typed prose, or pointer events are a physical topology or an independently
verified learning event.

## Scope boundary for continuous perspectival closure

This pass establishes the prerequisite for future iterative closure: every
new level must provide the bridge that connects it to the previous relation.
The next closure is admissible only when the user supplies a re-reading,
preservation claim, attempt, receipt, and successor perspective **and executes
the ordered pass**; otherwise it stays `OPEN`, `DUAL`, or `OBSTRUCTION`.

Continuous closure is consequently a sequence of explicit, reviewable
episodes, not an autonomous overnight process and not a hidden recommendation
loop. External source retrieval, evidence review, collaborative maps, and
interactive-proof checking remain separate capabilities to design and verify.
