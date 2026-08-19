import { access, readFile } from "node:fs/promises";
import { resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const notologyPath = resolve(root, "framework/notology.json");
const registryPath = resolve(root, "framework/registry.json");
const notology = JSON.parse(await readFile(notologyPath, "utf8"));
const registry = JSON.parse(await readFile(registryPath, "utf8"));

const requiredRules = [
  "each_notology_address_is_relative",
  "source_is_not_proof",
  "translation_is_not_literal_identity",
  "finite_resolution_is_not_all_stated_depths",
  "machine_checked_is_not_empirical",
  "projection_is_not_authority",
  "return_requires_reviewed_receipt",
  "each_return_retains_a_next_opening",
  "metaphysical_hypothesis_remains_open"
];
const requiredFields = [
  "id",
  "name",
  "resource",
  "frame",
  "claimKind",
  "depth",
  "verification",
  "closureState",
  "translation",
  "boundary",
  "nextOpening"
];

if (notology.unit !== "relative closure address") {
  throw new Error("Notology must use the relative closure address as its unit.");
}

for (const rule of requiredRules) {
  if (notology.rules?.[rule] !== true) throw new Error(`Missing notology rule: ${rule}`);
}

if (JSON.stringify(notology.addressFields) !== JSON.stringify(requiredFields)) {
  throw new Error("Notology address fields must retain the canonical ordered address.");
}

const frameResources = new Map(registry.frames.map((frame) => [frame.id, new Set(frame.resources)]));
const claimKinds = new Set(notology.claimKinds.map((kind) => kind.id));
const depths = new Set(notology.depths.map((depth) => depth.id));
const verificationKinds = new Set(notology.verificationKinds);
const closureStates = new Set(notology.closureStates.map((state) => state.id));
const addressIds = new Set();

for (const address of notology.addresses) {
  for (const field of requiredFields) {
    if (typeof address[field] !== "string" || address[field].trim() === "") {
      throw new Error(`Incomplete notology address ${address.id ?? "unknown"}: ${field}`);
    }
  }
  if (addressIds.has(address.id)) throw new Error(`Duplicate notology address: ${address.id}`);
  addressIds.add(address.id);

  if (!frameResources.has(address.frame)) throw new Error(`Unknown notology frame: ${address.frame}`);
  if (!claimKinds.has(address.claimKind)) throw new Error(`Unknown claim kind: ${address.claimKind}`);
  if (!depths.has(address.depth)) throw new Error(`Unknown depth: ${address.depth}`);
  if (!verificationKinds.has(address.verification)) throw new Error(`Unknown verification kind: ${address.verification}`);
  if (!closureStates.has(address.closureState)) throw new Error(`Unknown closure state: ${address.closureState}`);
  if (!frameResources.get(address.frame).has(address.resource)) {
    throw new Error(`Notology address resource is not registered in ${address.frame}: ${address.resource}`);
  }
  await access(resolve(root, address.resource));

  if (address.claimKind === "DIRECT_SOURCE" && !["OPEN", "PATH"].includes(address.closureState)) {
    throw new Error(`Direct source must remain OPEN or PATH: ${address.id}`);
  }
  if (address.claimKind === "METAPHYSICAL_HYPOTHESIS" && address.closureState !== "OPEN") {
    throw new Error(`Metaphysical hypothesis must remain OPEN: ${address.id}`);
  }
  if (address.claimKind === "PROVED_THEOREM" && (address.verification !== "MACHINE_CHECKED" || address.closureState !== "NOT_APPLICABLE")) {
    throw new Error(`Proved theorem must be machine-checked and not a learner-state: ${address.id}`);
  }
  if (address.claimKind === "RUNTIME_RECORD" && !["PATH", "REOPENED", "RETURNED_RECORDED"].includes(address.closureState)) {
    throw new Error(`Runtime record must name a packet state: ${address.id}`);
  }
}

if (addressIds.size < 8) throw new Error("Notology must register the core source, product, formal, runtime, interpretation, and boundary addresses.");

console.log(`notology valid: ${addressIds.size} relative closure addresses`);
