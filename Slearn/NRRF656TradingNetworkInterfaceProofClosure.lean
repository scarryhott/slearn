import Slearn.NRRF655ExecutablePerspectivalClosureEpisode

/-
Trading–Network–Interface–Proof closure for Slearn / Supernet.

The four named surfaces are not independent products.  A `Closure` supplies
one directed translation orbit and one witness language shared by every
surface:

  Trading → Network → Interface → Proof → Trading′.

The certified return is relational: `Trading′` and the input trading state
have the same witness.  Literal equality is neither assumed nor derived.  The
module proves only the typed closure contract supplied by a caller.  It does
not prove a market strategy profitable, a network consensus honest, a browser
display accurate, or an external proof/evidence claim true.
-/

universe u v w x y

namespace Slearn
namespace TradingNetworkInterfaceProof

/-- One four-surface translation orbit with a common comparison language. -/
structure Closure
    (Trading : Type u) (Network : Type v) (Interface : Type w)
    (Proof : Type x) (Witness : Type y) where
  tradingToNetwork : Trading → Network
  networkToInterface : Network → Interface
  interfaceToProof : Interface → Proof
  proofToTrading : Proof → Trading
  tradingWitness : Trading → Witness
  networkWitness : Network → Witness
  interfaceWitness : Interface → Witness
  proofWitness : Proof → Witness
  trading_network_coherent : ∀ trading,
    networkWitness (tradingToNetwork trading) = tradingWitness trading
  network_interface_coherent : ∀ network,
    interfaceWitness (networkToInterface network) = networkWitness network
  interface_proof_coherent : ∀ interface,
    proofWitness (interfaceToProof interface) = interfaceWitness interface
  proof_trading_coherent : ∀ proof,
    tradingWitness (proofToTrading proof) = proofWitness proof

namespace Closure

variable {Trading : Type u} {Network : Type v} {Interface : Type w}
variable {Proof : Type x} {Witness : Type y}
variable (C : Closure Trading Network Interface Proof Witness)

/-- The network presentation translated from one trading opening. -/
def networkOf (trading : Trading) : Network :=
  C.tradingToNetwork trading

/-- The interface presentation of the same translated relation. -/
def interfaceOf (trading : Trading) : Interface :=
  C.networkToInterface (C.networkOf trading)

/-- The proof presentation reached through the network and interface. -/
def proofOf (trading : Trading) : Proof :=
  C.interfaceToProof (C.interfaceOf trading)

/-- The whole translation orbit returned to a new trading presentation. -/
def complete (trading : Trading) : Trading :=
  C.proofToTrading (C.proofOf trading)

/-- Relative identity for trading presentations in the shared witness language. -/
def Closes (first second : Trading) : Prop :=
  C.tradingWitness first = C.tradingWitness second

/-- A receipt retains every presentation of one completed four-surface orbit. -/
structure Receipt (trading : Trading) where
  network : Network
  interface : Interface
  proof : Proof
  returnedTrading : Trading
  network_is_translation : network = C.networkOf trading
  interface_is_translation : interface = C.networkToInterface network
  proof_is_translation : proof = C.interfaceToProof interface
  return_is_translation : returnedTrading = C.proofToTrading proof

/-- Construct the canonical receipt by executing all four translations. -/
def receipt (trading : Trading) : C.Receipt trading where
  network := C.networkOf trading
  interface := C.interfaceOf trading
  proof := C.proofOf trading
  returnedTrading := C.complete trading
  network_is_translation := rfl
  interface_is_translation := rfl
  proof_is_translation := rfl
  return_is_translation := rfl

/-- Trading and its translated network view have one witness. -/
theorem trading_network_closes (trading : Trading) :
    C.networkWitness (C.networkOf trading) = C.tradingWitness trading :=
  C.trading_network_coherent trading

/-- Network and interface are two presentations of the same witness. -/
theorem network_interface_closes (trading : Trading) :
    C.interfaceWitness (C.interfaceOf trading) =
      C.networkWitness (C.networkOf trading) :=
  C.network_interface_coherent (C.networkOf trading)

/-- Interface and proof are two presentations of the same witness. -/
theorem interface_proof_closes (trading : Trading) :
    C.proofWitness (C.proofOf trading) =
      C.interfaceWitness (C.interfaceOf trading) :=
  C.interface_proof_coherent (C.interfaceOf trading)

/-- The proof-to-trading return preserves the proof witness. -/
theorem proof_trading_closes (trading : Trading) :
    C.tradingWitness (C.complete trading) =
      C.proofWitness (C.proofOf trading) :=
  C.proof_trading_coherent (C.proofOf trading)

/-- The complete orbit returns to the input trading closure class. -/
theorem complete_closes (trading : Trading) :
    C.Closes (C.complete trading) trading := by
  calc
    C.tradingWitness (C.complete trading) = C.proofWitness (C.proofOf trading) :=
      C.proof_trading_closes trading
    _ = C.interfaceWitness (C.interfaceOf trading) := C.interface_proof_closes trading
    _ = C.networkWitness (C.networkOf trading) := C.network_interface_closes trading
    _ = C.tradingWitness trading := C.trading_network_closes trading

/-- Reapplying completion is idempotent in closure, not necessarily literally. -/
theorem complete_relationally_idempotent (trading : Trading) :
    C.Closes (C.complete (C.complete trading)) (C.complete trading) :=
  C.complete_closes (C.complete trading)

/-- Every surface of the canonical receipt carries the trading witness. -/
theorem receipt_witnesses_close (trading : Trading) :
    let receipt := C.receipt trading
    C.networkWitness receipt.network = C.tradingWitness trading ∧
      C.interfaceWitness receipt.interface = C.tradingWitness trading ∧
      C.proofWitness receipt.proof = C.tradingWitness trading ∧
      C.tradingWitness receipt.returnedTrading = C.tradingWitness trading := by
  dsimp [receipt]
  exact ⟨C.trading_network_closes trading,
    C.network_interface_closes trading |>.trans (C.trading_network_closes trading),
    C.interface_proof_closes trading |>.trans
      ((C.network_interface_closes trading).trans (C.trading_network_closes trading)),
    C.complete_closes trading⟩

/--
The requested interaction/translation/completion/closure theorem: the receipt
records each actual map in order and its returned trading state closes with the
opening state in the one shared witness language.
-/
theorem interact_translate_complete_close (trading : Trading) :
    let receipt := C.receipt trading
    receipt.network = C.tradingToNetwork trading ∧
      receipt.interface = C.networkToInterface receipt.network ∧
      receipt.proof = C.interfaceToProof receipt.interface ∧
      receipt.returnedTrading = C.proofToTrading receipt.proof ∧
      C.Closes receipt.returnedTrading trading := by
  dsimp [receipt, networkOf, interfaceOf, proofOf, complete]
  exact ⟨rfl, rfl, rfl, rfl, C.complete_closes trading⟩

end Closure
end TradingNetworkInterfaceProof
end Slearn

#print axioms Slearn.TradingNetworkInterfaceProof.Closure.complete_closes
#print axioms Slearn.TradingNetworkInterfaceProof.Closure.complete_relationally_idempotent
#print axioms Slearn.TradingNetworkInterfaceProof.Closure.receipt_witnesses_close
#print axioms Slearn.TradingNetworkInterfaceProof.Closure.interact_translate_complete_close
