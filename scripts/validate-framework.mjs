import { access, readFile } from "node:fs/promises";
import { resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const registryPath = resolve(root, "framework/registry.json");
const registry = JSON.parse(await readFile(registryPath, "utf8"));
const frameIds = new Set(registry.frames.map((frame) => frame.id));
const requiredRules = [
  "source_is_not_proof",
  "projection_is_not_authority",
  "return_requires_counter_reading",
  "finite_interaction_is_not_global_completion",
  "unresolved_remainder_is_preserved"
];

if (registry.unit !== "source-grounded closure packet") {
  throw new Error("Framework registry must name the source-grounded closure packet as its unit.");
}

for (const rule of requiredRules) {
  if (registry.rules[rule] !== true) throw new Error(`Missing framework rule: ${rule}`);
}

for (const frame of registry.frames) {
  if (!frame.id || !frame.purpose || !Array.isArray(frame.resources) || frame.resources.length === 0) {
    throw new Error(`Incomplete frame: ${frame.id ?? "unknown"}`);
  }
  for (const resource of frame.resources) {
    await access(resolve(root, resource));
  }
}

for (const route of registry.routes) {
  if (!Array.isArray(route) || route.length !== 2 || !frameIds.has(route[0]) || !frameIds.has(route[1])) {
    throw new Error(`Invalid frame route: ${JSON.stringify(route)}`);
  }
}

const requiredCycle = ["OPEN", "PERSPECTIVE", "TRANSLATION", "INTERACTION", "VERIFICATION", "RETURN", "OPEN"];
for (let index = 0; index < requiredCycle.length - 1; index += 1) {
  const edge = [requiredCycle[index], requiredCycle[index + 1]];
  if (!registry.routes.some(([from, to]) => from === edge[0] && to === edge[1])) {
    throw new Error(`Missing closure-frame route: ${edge.join(" → ")}`);
  }
}

console.log(`framework registry valid: ${registry.frames.length} frames, ${registry.routes.length} routes`);
