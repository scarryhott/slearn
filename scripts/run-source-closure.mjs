import { readFile } from "node:fs/promises";
import { resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const defaultPacket = resolve(root, "framework/source-closure-primitives.json");
const packetPath = process.argv[2] ? resolve(process.cwd(), process.argv[2]) : defaultPacket;
const packet = JSON.parse(await readFile(packetPath, "utf8"));

const text = (value) => typeof value === "string" && value.trim().length > 0;
const at = (object, path) => path.reduce((value, key) => value?.[key], object);
const requiredForPath = [
  ["source", "anchor"], ["source", "claim"], ["observation"], ["perspective"],
  ["beliefLimit"], ["goalLimit"], ["why"], ["explanations", "semantic"],
  ["explanations", "operative"], ["definition"], ["paths", "forward"],
  ["paths", "counter"], ["translation", "forwardBridge"],
  ["translation", "inverseBridge"], ["translation", "witnessLanguage"]
];
const requiredForRecordedReturn = [
  ["verification", "material"], ["verification", "attempt"],
  ["verification", "counterReading"], ["verification", "comparisonMethod"],
  ["verification", "review"], ["admission", "condition"],
  ["admission", "receipt"], ["admission", "successor"], ["admission", "nextRelation"]
];
const missing = (requirements) => requirements
  .filter((path) => !text(at(packet, path)))
  .map((path) => path.join("."));

const pathGaps = missing(requiredForPath);
const returnGaps = missing(requiredForRecordedReturn);
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

if (packet.expectedStatus && packet.expectedStatus !== status) {
  throw new Error(`Expected ${packet.expectedStatus}, received ${status} for ${packet.id ?? "unnamed packet"}.`);
}

console.log(`closure packet: ${packet.id ?? "unnamed"}`);
console.log(`source anchor: ${packet.source?.anchor ?? "MISSING"}`);
console.log(`status: ${status}`);
console.log(`admission: ${admission}`);
console.log(`path primitives: ${pathGaps.length === 0 ? "complete" : `missing ${pathGaps.join(", ")}`}`);
console.log(`execution: forward=${contracted ? "recorded" : "OPEN"}; reciprocal=${reopened ? "recorded" : "OPEN"}`);
console.log(`return conditions: ${returnGaps.length === 0 ? "complete" : `OPEN at ${returnGaps.join(", ")}`}`);
console.log(`next: ${next}`);
