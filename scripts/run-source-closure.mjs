import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { assertExpectedStatus, classifyClosurePacket } from "./closure-packet-kernel.mjs";

const root = resolve(import.meta.dirname, "..");
const defaultPacket = resolve(root, "framework/source-closure-primitives.json");
const packetPath = process.argv[2] ? resolve(process.cwd(), process.argv[2]) : defaultPacket;
const packet = JSON.parse(await readFile(packetPath, "utf8"));

const result = classifyClosurePacket(packet);
assertExpectedStatus(packet, result);

console.log(`closure packet: ${packet.id ?? "unnamed"}`);
console.log(`source anchor: ${packet.source?.anchor ?? "MISSING"}`);
console.log(`status: ${result.status}`);
console.log(`admission: ${result.admission}`);
console.log(`path primitives: ${result.pathGaps.length === 0 ? "complete" : `missing ${result.pathGaps.join(", ")}`}`);
console.log(`execution: forward=${result.contracted ? "recorded" : "OPEN"}; reciprocal=${result.reopened ? "recorded" : "OPEN"}`);
console.log(`return conditions: ${result.returnGaps.length === 0 ? "complete" : `OPEN at ${result.returnGaps.join(", ")}`}`);
console.log(`next: ${result.next}`);
