# Trading–Network–Interface–Proof Closure (NRRF656)

The Supernet runtime now treats trading, network coordination, interface
projection, and proof as four presentations of one interaction rather than as
four products joined after the fact:

\[
T \xrightarrow{\tau_{TN}} N
  \xrightarrow{\tau_{NI}} I
  \xrightarrow{\tau_{IP}} P
  \xrightarrow{\tau_{PT}} T'.
\]

Each presentation has a reading in one witness language `W`. The four supplied
coherence conditions say that an adjacent translation preserves this witness.
Consequently:

\[
w_T(T') = w_P(P) = w_I(I) = w_N(N) = w_T(T).
\]

The return is therefore `T′ ~ T` relative to `W`. It is deliberately not a
claim that `T′ = T`. A completed interaction may retain a residue and become a
new trading opening while remaining in the same admitted closure class.

## Machine-checked contract

[`../Slearn/NRRF656TradingNetworkInterfaceProofClosure.lean`](../Slearn/NRRF656TradingNetworkInterfaceProofClosure.lean)
defines:

- `Closure`, the four maps, four witness projections, and adjacent coherence;
- `networkOf`, `interfaceOf`, `proofOf`, and `complete`, the actual composite
  translation;
- `Receipt`, which retains all four intermediate presentations and the returned
  trading state;
- `complete_closes`, proving the whole orbit returns in the trading witness
  relation;
- `complete_relationally_idempotent`, proving a second completion closes with
  the first without asserting literal fixed-point equality;
- `receipt_witnesses_close`, proving every retained surface has the same
  witness; and
- `interact_translate_complete_close`, joining the four executed maps and the
  returned closure relation in one theorem.

The file uses no market-price assumptions, consensus assumptions, browser
claims, or external evidence axioms. A caller must supply the translation maps
and their coherence proofs.

## Runtime projection

The browser's existing predecessor-typed phases mirror the four surfaces:

| Executable phase | Active surface | Meaning |
| --- | --- | --- |
| `open` | Trading | a local source-grounded transaction or attempted action |
| `contracted` | Network | the relation has been admitted into a shared network presentation |
| `reopened` | Interface | the network relation has been reciprocally projected into a local view |
| reviewed return gate | Proof | source, attempt, counter-reading, method, review, receipt, and successor are present |
| `returned` | Closed orbit | all four runtime surfaces share one recorded receipt and reopen trading |

`ui/app/closureRuntime.ts` derives this circuit from the same `ClosureField`
that generates the map. The interface cannot independently advance a surface:
only `CONTRACT`, `REOPEN`, `RETURN`, and `CONTINUE` change the underlying
episode.

## Proof and truth boundary

“Proof” has two intentionally separate readings:

1. Lean checks the abstract theorem: any supplied four-surface system satisfying
   the coherence fields returns to the same witness class.
2. The runtime checks that the declared episode fields required for a return
   are present and that the predecessor operations were executed.

Neither check proves a trading strategy profitable, a transaction authentic, a
network adversary absent, or a source claim empirically true. Those require
external adapters, authenticated data, independent review, and domain-specific
proof obligations. Until those are supplied, the external realization remains
`OPEN` even when the internal translation orbit is closed.
