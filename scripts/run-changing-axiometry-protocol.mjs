import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { text } from "./closure-packet-kernel.mjs";

const root = resolve(import.meta.dirname, "..");
const requestedProtocol = process.argv.slice(2).find((argument) => !argument.startsWith("--"));
const protocolPath = requestedProtocol
  ? resolve(process.cwd(), requestedProtocol)
  : resolve(root, "framework/changing-axiometry-experiment.json");
const protocol = JSON.parse(await readFile(protocolPath, "utf8"));

const requiredStages = [
  "frameGeneration", "nativeTranslation", "identityIndependentValidation", "independentReturn",
  "closureTruth", "nextAxiometry", "nextVerifier", "heldOutTransfer", "externalConsequence"
];
const executionOrder = [
  "frameGenerated", "frameFrozen", "nativeTranslation", "identityIndependentValidation",
  "independentReturn", "closureTruth", "residue", "nextAxiometry", "nextAxiometryChanged",
  "nextVerifier", "nextVerifierChanged", "heldOutRelation", "oldCannotEvaluate",
  "newCanEvaluate", "predictionPrecedesOutcome", "externalEvidence", "outcomeMatchesPrediction"
];
const missingDesign = requiredStages.filter((stage) => !text(protocol.stages?.[stage]));
if (!text(protocol.id) || !text(protocol.sourceAnchor) || !text(protocol.question) || missingDesign.length > 0) {
  throw new Error(`Incomplete changing-axiometry protocol: ${missingDesign.join(", ") || "identifier, source anchor, or question"}.`);
}

const recorded = executionOrder.filter((stage) => text(protocol.execution?.[stage]));
const missingEvidence = executionOrder.filter((stage) => !text(protocol.execution?.[stage]));
let status = "DESIGN_READY";
let next = "Begin independent frame generation; the protocol has no executed run yet.";
if (recorded.length > 0 && missingEvidence.length > 0) {
  status = "RUN_OPEN";
  next = `Supply auditable evidence for ${missingEvidence[0]}; no later stage may substitute for it.`;
}
if (missingEvidence.length === 0) {
  status = "DECLARED_EVIDENCE_COMPLETE";
  next = "Audit the supplied evidence externally; this runner does not establish its independence or truth.";
}
if (protocol.expectedStatus && protocol.expectedStatus !== status) {
  throw new Error(`Expected ${protocol.expectedStatus}, received ${status} for ${protocol.id}.`);
}

console.log(`changing-axiometry protocol: ${protocol.id}`);
console.log(`source anchor: ${protocol.sourceAnchor}`);
console.log(`status: ${status}`);
console.log(`design stages: ${requiredStages.length} specified`);
console.log(`recorded evidence: ${recorded.length}/${executionOrder.length}`);
console.log(`OPEN evidence: ${missingEvidence.length === 0 ? "none" : missingEvidence.join(", ")}`);
console.log(`next: ${next}`);
