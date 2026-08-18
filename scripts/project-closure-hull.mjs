import { readFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { assertExpectedStatus, classifyClosurePacket, text } from "./closure-packet-kernel.mjs";

const root = resolve(import.meta.dirname, "..");
const defaultLedger = resolve(root, "framework/closure-ledger.json");
const requestedLedger = process.argv.slice(2).find((argument) => !argument.startsWith("--"));
const ledgerPath = requestedLedger
  ? resolve(process.cwd(), requestedLedger)
  : defaultLedger;
const summaryOnly = process.argv.includes("--summary");
const ledger = JSON.parse(await readFile(ledgerPath, "utf8"));
const ledgerDirectory = dirname(ledgerPath);

const idPart = (value) => String(value).trim().toLocaleLowerCase()
  .replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "").slice(0, 72) || "unnamed";
const countBy = (values) => values.reduce((counts, value) => {
  counts[value] = (counts[value] ?? 0) + 1;
  return counts;
}, {});
const node = (packet, role, content, id = `${packet.id}:${role}`) => ({ id, packetId: packet.id, role, content });
const link = (packet, from, to, kind) => ({ id: `${packet.id}:${kind}:${from}:${to}`, packetId: packet.id, from, to, kind });

function projectPacket(packet, result) {
  const ids = {
    source: `${packet.id}:source`, observation: `${packet.id}:observation`,
    perspective: `${packet.id}:perspective`, belief: `${packet.id}:belief-limit`,
    why: `${packet.id}:why`, semantic: `${packet.id}:semantic-explanation`,
    operative: `${packet.id}:operative-explanation`, definition: `${packet.id}:definition`,
    lesson: `${packet.id}:prospective-lesson`, forward: `${packet.id}:forward-path`,
    counter: `${packet.id}:counter-path`, goal: `${packet.id}:goal`, open: `${packet.id}:open`
  };
  const nodes = [
    node(packet, "source", packet.source.claim, ids.source),
    node(packet, "observation", packet.observation, ids.observation),
    node(packet, "perspective", packet.perspective, ids.perspective),
    node(packet, "beliefLimit", packet.beliefLimit, ids.belief),
    node(packet, "why", packet.why, ids.why),
    node(packet, "semanticExplanation", packet.explanations.semantic, ids.semantic),
    node(packet, "operativeExplanation", packet.explanations.operative, ids.operative),
    node(packet, "definition", packet.definition, ids.definition),
    node(packet, "prospectiveLesson", { why: packet.why, definition: packet.definition }, ids.lesson),
    node(packet, "forwardPath", packet.paths.forward, ids.forward),
    node(packet, "counterPath", packet.paths.counter, ids.counter),
    node(packet, "goal", packet.goalLimit, ids.goal)
  ];
  const links = [
    link(packet, ids.source, ids.observation, "sourceToObservation"),
    link(packet, ids.observation, ids.perspective, "situatesPerspective"),
    link(packet, ids.perspective, ids.belief, "situatesPerspective"),
    link(packet, ids.belief, ids.why, "beliefConstrainsWhy"),
    link(packet, ids.why, ids.semantic, "semanticExplains"),
    link(packet, ids.why, ids.operative, "operativeExplains"),
    link(packet, ids.semantic, ids.definition, "semanticExplains"),
    link(packet, ids.operative, ids.definition, "operativeExplains"),
    link(packet, ids.definition, ids.lesson, "definitionMakesLesson"),
    link(packet, ids.why, ids.lesson, "whyMakesLesson"),
    link(packet, ids.perspective, ids.forward, "translationForward"),
    link(packet, ids.forward, ids.goal, "forwardPathToGoal"),
    link(packet, ids.goal, ids.counter, "translationReturn"),
    link(packet, ids.counter, ids.perspective, "counterPathToPerspective")
  ];
  const zoom = {
    out: [ids.perspective, ids.belief, ids.why, ids.lesson, ids.forward, ids.goal],
    in: [ids.goal, ids.counter, ids.operative, ids.definition, ids.why, ids.belief, ids.perspective]
  };
  const openConditions = [
    ...(result.contracted ? [] : ["execution.contracted"]),
    ...(result.reopened ? [] : ["execution.reopened"]),
    ...result.returnGaps
  ];

  if (result.status !== "RETURNED (RECORDED)") {
    nodes.push(node(packet, "openRemainder", openConditions, ids.open));
    links.push(link(packet, ids.counter, ids.open, "prospectiveOpen"));
    return { packet, result, nodes, links, zoom, openRegions: [{ id: ids.open, conditions: openConditions }], experienceFibres: [], perspectiveUpdates: [] };
  }

  const basisId = `basis:${idPart(packet.admission.returnedBasis)}`;
  const projectId = `${packet.id}:project`;
  const experienceId = `${packet.id}:experience`;
  const successorId = `${packet.id}:successor`;
  const continuationId = `${packet.id}:world-continuation`;
  nodes.push(
    node(packet, "returnedBasis", packet.admission.returnedBasis, basisId),
    node(packet, "project", packet.verification.attempt, projectId),
    node(packet, "experience", packet.admission.receipt, experienceId),
    node(packet, "successorPerspective", packet.admission.successor, successorId),
    node(packet, "worldContinuation", packet.admission.nextRelation, continuationId),
    node(packet, "openRemainder", ["next relation is the next packet's OPEN"], ids.open)
  );
  links.push(
    link(packet, ids.goal, basisId, "returnedBasis"),
    link(packet, ids.lesson, projectId, "lessonToProject"),
    link(packet, projectId, experienceId, "projectExperience"),
    link(packet, basisId, experienceId, "experienceFibre"),
    link(packet, experienceId, successorId, "experienceFibre"),
    link(packet, successorId, continuationId, "successorContinuation"),
    link(packet, continuationId, ids.open, "continuedOpen")
  );
  return {
    packet, result, nodes, links, zoom,
    openRegions: [{ id: ids.open, conditions: ["next relation is the next packet's OPEN"] }],
    experienceFibres: [{ id: experienceId, project: packet.verification.attempt, receipt: packet.admission.receipt, successor: packet.admission.successor, basis: packet.admission.returnedBasis, nextRelation: packet.admission.nextRelation }],
    perspectiveUpdates: [packet.admission.successor]
  };
}

const packets = await Promise.all((ledger.packets ?? []).map(async (entry) => {
  const path = resolve(ledgerDirectory, entry);
  return JSON.parse(await readFile(path, "utf8"));
}));
if (packets.length === 0) throw new Error("A closure ledger must contain at least one packet.");

const projected = packets.map((packet) => {
  const result = classifyClosurePacket(packet);
  assertExpectedStatus(packet, result);
  return projectPacket(packet, result);
});
const deduplicateNodes = new Map();
for (const item of projected) for (const itemNode of item.nodes) {
  if (!deduplicateNodes.has(itemNode.id)) deduplicateNodes.set(itemNode.id, itemNode);
}
const nodes = [...deduplicateNodes.values()];
const links = projected.flatMap((item) => item.links);
const statusCounts = countBy(projected.map((item) => item.result.status));
const hull = {
  ledger: ledger.id ?? "unnamed",
  packets: projected.map((item) => ({
    id: item.packet.id,
    sourceAnchor: item.packet.source.anchor,
    status: item.result.status,
    admission: item.result.admission,
    zoom: item.zoom
  })),
  nodes,
  links,
  openRegions: projected.flatMap((item) => item.openRegions),
  experienceFibres: projected.flatMap((item) => item.experienceFibres),
  perspectiveUpdates: projected.flatMap((item) => item.perspectiveUpdates),
  summary: {
    packetCount: packets.length,
    statusCounts,
    prospectiveBranches: projected.filter((item) => item.result.status !== "OPEN").length,
    experienceFibres: projected.flatMap((item) => item.experienceFibres).length,
    openRegions: projected.flatMap((item) => item.openRegions).length,
    nodeCount: nodes.length,
    linkCount: links.length
  }
};

for (const [key, expected] of Object.entries(ledger.expected ?? {})) {
  const actual = hull.summary[key];
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    throw new Error(`Expected hull ${key} to be ${JSON.stringify(expected)}, received ${JSON.stringify(actual)}.`);
  }
}

if (summaryOnly) {
  console.log(`closure hull: ${hull.ledger}`);
  console.log(`packets: ${hull.summary.packetCount}; statuses: ${JSON.stringify(hull.summary.statusCounts)}`);
  console.log(`prospective branches: ${hull.summary.prospectiveBranches}; experience fibres: ${hull.summary.experienceFibres}; OPEN regions: ${hull.summary.openRegions}`);
  console.log(`derived nodes: ${hull.summary.nodeCount}; derived links: ${hull.summary.linkCount}`);
} else {
  console.log(JSON.stringify(hull, null, 2));
}
