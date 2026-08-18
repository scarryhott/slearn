export const text = (value) => typeof value === "string" && value.trim().length > 0;

export const at = (object, path) => path.reduce((value, key) => value?.[key], object);

export const requiredForPath = [
  ["source", "anchor"], ["source", "claim"], ["observation"], ["perspective"],
  ["beliefLimit"], ["goalLimit"], ["why"], ["explanations", "semantic"],
  ["explanations", "operative"], ["definition"], ["paths", "forward"],
  ["paths", "counter"], ["translation", "forwardBridge"],
  ["translation", "inverseBridge"], ["translation", "witnessLanguage"]
];

export const requiredForRecordedReturn = [
  ["verification", "material"], ["verification", "attempt"],
  ["verification", "counterReading"], ["verification", "comparisonMethod"],
  ["verification", "review"], ["admission", "condition"],
  ["admission", "receipt"], ["admission", "successor"],
  ["admission", "returnedBasis"], ["admission", "nextRelation"]
];

const missing = (packet, requirements) => requirements
  .filter((path) => !text(at(packet, path)))
  .map((path) => path.join("."));

/**
 * The repository's deterministic information-state classifier.  It reports
 * what a packet has supplied; it never validates a source or a human review.
 */
export function classifyClosurePacket(packet) {
  const pathGaps = missing(packet, requiredForPath);
  const returnGaps = missing(packet, requiredForRecordedReturn);
  const contracted = packet.execution?.contracted === true;
  const reopened = packet.execution?.reopened === true;
  let status = "OPEN";
  let admission = "BLOCKED";
  let next = "State the source primitives and their single translation bridge.";

  if (pathGaps.length === 0) {
    status = "PATH";
    next = "Execute the declared forward and reciprocal translations against source-grounded material.";
    if (contracted && reopened) {
      status = "REOPENED";
      next = "Compare the returned reading with its counter-reading and record a review.";
      if (returnGaps.length === 0) {
        status = "RETURNED (RECORDED)";
        admission = "CONTINUED";
        next = "Open the supplied successor relation with the retained receipt; do not treat it as terminal truth.";
      }
    }
  }

  return { status, admission, pathGaps, returnGaps, contracted, reopened, next };
}

export function assertExpectedStatus(packet, result) {
  if (packet.expectedStatus && packet.expectedStatus !== result.status) {
    throw new Error(`Expected ${packet.expectedStatus}, received ${result.status} for ${packet.id ?? "unnamed packet"}.`);
  }
}
