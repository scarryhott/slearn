/**
 * Slearn closure machine.
 *
 * This file is the whole authored product contract. It takes only closure
 * state and deterministically emits the interaction scene: topology, spatial
 * coordinates, words, visual tokens, editable seeds, and enabled operations.
 * React and CSS are deliberately generic interpreters of this contract.
 */

export type Lens = "contracted" | "expanded" | "returned";
export type RelativePosition = "natural" | "dual" | "obstructed";
export type ClosureStatus = "OPEN" | "PATH" | "RETURNED" | "DUAL" | "OBSTRUCTION";
export type SurfaceTone = "open" | "path" | "returned" | "dual" | "obstructed" | "presentation" | "context" | "translation" | "closure" | "world" | "source" | "lesson" | "project";
export type PointRole = "presentation" | "context" | "translation" | "closure" | "world" | "source" | "lesson" | "project" | "successor";
export type ClosureAppearance = { signal: string; pattern: "solid" | "dashed"; glow: boolean };

export type Interaction = {
  id: string;
  perspective: string;
  belief: string;
  why: string;
  goal: string;
  redefinition: string;
  bridge: string;
  world: string;
  source: string;
  lesson: string;
  attempt: string;
  receipt: string;
  returnedPerspective: string;
  position: RelativePosition;
};

export type InteractionFieldKey = Exclude<keyof Interaction, "id">;

export type ClosureField = {
  lens: Lens;
  selected: string | null;
  nextId: number;
  interactions: Interaction[];
  proposal: Omit<Interaction, "id">;
};

export type ScenePoint = {
  id: string;
  traceIds: string[];
  role: PointRole;
  tone: SurfaceTone;
  appearance: ClosureAppearance;
  label: string;
  detail: string;
  x: number;
  y: number;
  selected: boolean;
};

export type SceneLink = {
  id: string;
  from: string;
  to: string;
  tone: SurfaceTone;
  appearance: ClosureAppearance;
  traceIds: string[];
};

export type InputSeed = {
  id: string;
  target: "proposal" | "selected";
  key: InteractionFieldKey;
  label: string;
  placeholder: string;
  detail: string;
  value: string;
  required: boolean;
  x: number;
  y: number;
  tone: SurfaceTone;
  appearance: ClosureAppearance;
  kind: "text" | "position";
};

export type ClosureOperation = {
  id: string;
  label: string;
  detail: string;
  lens?: Lens;
  type: "LENS" | "ADMIT_PROPOSAL" | "CLEAR";
  enabled: boolean;
  tone: SurfaceTone;
  appearance: ClosureAppearance;
};

export type ClosureScene = {
  status: ClosureStatus;
  statusAppearance: ClosureAppearance;
  lens: Lens;
  statusText: string;
  focusText: string;
  points: ScenePoint[];
  links: SceneLink[];
  inputs: InputSeed[];
  operations: ClosureOperation[];
};

const seedRelation: Interaction = {
  id: "r1",
  perspective: "A learner's place and time",
  belief: "Curiosity",
  why: "A connective question can change what is relevant",
  goal: "A chosen learning direction",
  redefinition: "Treat the same question as a project relation",
  bridge: "The question still connects the learner's place to the chosen direction",
  world: "A world relation where curiosity can be practiced with others",
  source: "A source, conversation, or observation worth returning to",
  lesson: "Two explanations and questions to think through",
  attempt: "Practice the relation in a project",
  receipt: "The attempted path changes the next reading",
  returnedPerspective: "A revised perspective",
  position: "natural",
};

export function emptyInteraction(): Omit<Interaction, "id"> {
  return {
    perspective: "",
    belief: "",
    why: "",
    goal: "",
    redefinition: "",
    bridge: "",
    world: "",
    source: "",
    lesson: "",
    attempt: "",
    receipt: "",
    returnedPerspective: "",
    position: "natural",
  };
}

export const initialClosureField: ClosureField = {
  lens: "expanded",
  selected: seedRelation.id,
  nextId: 2,
  interactions: [seedRelation],
  proposal: emptyInteraction(),
};

const clean = (value: string) => value.trim();
const present = (value: string) => clean(value).length > 0;
const key = (value: string) => clean(value).toLocaleLowerCase();

export function isAdmitted(interaction: Omit<Interaction, "id"> | Interaction) {
  return present(interaction.perspective) && present(interaction.why) && present(interaction.goal);
}

export function hasBridge(interaction: Omit<Interaction, "id"> | Interaction) {
  return isAdmitted(interaction) && present(interaction.redefinition) && present(interaction.bridge);
}

export function hasReturn(interaction: Omit<Interaction, "id"> | Interaction) {
  return hasBridge(interaction) && present(interaction.attempt) && present(interaction.receipt) && present(interaction.returnedPerspective);
}

/** A world/universe view is a bridged global continuation, not decoration. */
function hasWorldContinuation(interaction: Omit<Interaction, "id"> | Interaction) {
  return hasBridge(interaction) && present(interaction.world);
}

function traceStatus(interaction: Interaction): ClosureStatus {
  if (interaction.position === "obstructed") return "OBSTRUCTION";
  if (interaction.position === "dual") return "DUAL";
  if (hasReturn(interaction)) return "RETURNED";
  if (hasBridge(interaction)) return "PATH";
  return "OPEN";
}

function toneFor(status: ClosureStatus): SurfaceTone {
  if (status === "RETURNED") return "returned";
  if (status === "PATH") return "path";
  if (status === "DUAL") return "dual";
  if (status === "OBSTRUCTION") return "obstructed";
  return "open";
}

/** The scene's physical rendering token is derived with the closure verdict. */
function appearanceFor(tone: SurfaceTone): ClosureAppearance {
  const signal = tone === "path" || tone === "translation" ? "#d5fb73"
    : tone === "returned" || tone === "closure" ? "#a7d6ff"
      : tone === "dual" ? "#efacff"
        : tone === "obstructed" ? "#ff9a8f"
          : tone === "presentation" ? "#9de9d1"
            : tone === "context" ? "#79d8df"
              : tone === "world" ? "#bcb5ff"
                : tone === "source" ? "#ffd285"
                  : tone === "lesson" ? "#d5fb73"
                    : tone === "project" ? "#ffabcf" : "#a5b2ac";
  return { signal, pattern: tone === "dual" || tone === "obstructed" ? "dashed" : "solid", glow: tone === "returned" };
}

function idFor(role: string, value: string) {
  return `${role}:${key(value)}`;
}

type RawPoint = Omit<ScenePoint, "x" | "y" | "selected">;

/** The spatial projection of the closure field; no stored coordinates exist. */
function projectedTopology(field: ClosureField) {
  const admitted = field.interactions.filter(isAdmitted);
  const points = new Map<string, RawPoint>();
  const links: SceneLink[] = [];
  const add = (id: string, trace: Interaction, role: PointRole, label: string, detail: string, tone: SurfaceTone) => {
    const current = points.get(id);
    if (current) {
      current.traceIds.push(trace.id);
      return;
    }
    points.set(id, { id, traceIds: [trace.id], role, tone, appearance: appearanceFor(tone), label, detail });
  };

  if (field.lens === "contracted") {
    admitted.filter(hasBridge).forEach((trace) => {
      add(idFor("closure", trace.goal), trace, "closure", clean(trace.goal), `Recomposed by the preserved relation: ${clean(trace.bridge)}`, toneFor(traceStatus(trace)));
    });
  } else {
    admitted.forEach((trace) => {
      const source = idFor("presentation", trace.perspective);
      const context = `context:${trace.id}`;
      const relation = `translation:${trace.id}`;
      const target = idFor("closure", trace.goal);
      const tone = toneFor(traceStatus(trace));
      add(source, trace, "presentation", clean(trace.perspective), "Local reading of the selected translation.", "presentation");
      if (present(trace.belief)) {
        add(context, trace, "context", clean(trace.belief), "A value or belief carried by this relation, not a free category.", "context");
        links.push({ id: `context-start:${trace.id}`, from: source, to: context, tone: "context", appearance: appearanceFor("context"), traceIds: [trace.id] });
        links.push({ id: `context-why:${trace.id}`, from: context, to: relation, tone, appearance: appearanceFor(tone), traceIds: [trace.id] });
      }
      add(relation, trace, "translation", clean(trace.why), "WHY relation carrying this trace.", "translation");
      add(target, trace, "closure", clean(trace.goal), hasBridge(trace) ? `Re-read as: ${clean(trace.redefinition)}. Preserves: ${clean(trace.bridge)}.` : "OPEN: a re-reading and preserved relation are absent.", "closure");
      if (!present(trace.belief)) links.push({ id: `forward:${trace.id}`, from: source, to: relation, tone, appearance: appearanceFor(tone), traceIds: [trace.id] });
      links.push({ id: `close:${trace.id}`, from: relation, to: target, tone, appearance: appearanceFor(tone), traceIds: [trace.id] });
      if (hasWorldContinuation(trace)) {
        const world = `world:${trace.id}`;
        add(world, trace, "world", clean(trace.world), "A bridged global continuation of this goal; it is not independent scenery.", "world");
        links.push({ id: `world:${trace.id}`, from: target, to: world, tone: "world", appearance: appearanceFor("world"), traceIds: [trace.id] });
      }
      if (present(trace.source)) {
        const material = `source:${trace.id}`;
        add(material, trace, "source", clean(trace.source), "A source, observation, or conversation positioned through this relation.", "source");
        links.push({ id: `source:${trace.id}`, from: material, to: relation, tone: "source", appearance: appearanceFor("source"), traceIds: [trace.id] });
      }
      if (present(trace.lesson)) {
        const lesson = `lesson:${trace.id}`;
        add(lesson, trace, "lesson", clean(trace.lesson), "A lesson generated as a traversable reading of this relation.", "lesson");
        links.push({ id: `lesson:${trace.id}`, from: target, to: lesson, tone: "lesson", appearance: appearanceFor("lesson"), traceIds: [trace.id] });
      }
      if (present(trace.attempt)) {
        const project = `project:${trace.id}`;
        add(project, trace, "project", clean(trace.attempt), "A project or practice. Its attempt is required before a return can be recorded.", "project");
        links.push({ id: `project:${trace.id}`, from: present(trace.lesson) ? `lesson:${trace.id}` : target, to: project, tone: "project", appearance: appearanceFor("project"), traceIds: [trace.id] });
      }
      if (field.lens === "returned" && hasReturn(trace)) {
        const successor = idFor("successor", trace.returnedPerspective);
        add(successor, trace, "successor", clean(trace.returnedPerspective), `Returned through: ${clean(trace.receipt)}`, "returned");
        links.push({ id: `return:${trace.id}`, from: target, to: successor, tone: "returned", appearance: appearanceFor("returned"), traceIds: [trace.id] });
      }
    });
  }

  return { rawPoints: [...points.values()], links };
}

/**
 * The physical plane is a recenterable triangle field, not a force-directed
 * decoration. Every coordinate comes from the occurrence's closure role and
 * witnessed trace order: local/context/WHY/goal/world is the outward fold;
 * source/lesson/project/successor is the inward and returned fold.
 */
function arrange(rawPoints: RawPoint[], selected: string | null): ScenePoint[] {
  const traceOrder = [...new Set(rawPoints.flatMap((point) => point.traceIds))];
  const laneOf = (point: RawPoint) => {
    const index = traceOrder.indexOf(point.traceIds[0]);
    return traceOrder.length <= 1 ? 0 : (index / (traceOrder.length - 1) - 0.5) * 16;
  };
  const coordinate = (point: RawPoint) => {
    const lane = laneOf(point);
    if (point.role === "presentation") return { x: 10, y: 50 + lane };
    if (point.role === "context") return { x: 27, y: 22 + lane / 2 };
    if (point.role === "translation") return { x: 46, y: 50 + lane };
    if (point.role === "closure") return { x: 65, y: 22 + lane / 2 };
    if (point.role === "world") return { x: 89, y: 50 + lane };
    if (point.role === "source") return { x: 39, y: 82 + lane / 3 };
    if (point.role === "lesson") return { x: 64, y: 72 + lane / 3 };
    if (point.role === "project") return { x: 83, y: 84 + lane / 3 };
    return { x: 38, y: 86 + lane / 3 };
  };
  return rawPoints.map((point) => ({ ...point, selected: point.traceIds.includes(selected ?? ""), ...coordinate(point) }));
}

const seedSchema: Array<Pick<InputSeed, "key" | "label" | "placeholder" | "detail" | "required" | "kind">> = [
  { key: "perspective", label: "perspective", placeholder: "a local place and time", detail: "The local presentation of a possible relation.", required: true, kind: "text" },
  { key: "belief", label: "belief / context", placeholder: "what currently matters", detail: "Context carried by the relation, not an independent map object.", required: false, kind: "text" },
  { key: "why", label: "WHY relation", placeholder: "why this changes what is relevant", detail: "Translation from the local reading toward a direction.", required: true, kind: "text" },
  { key: "goal", label: "direction", placeholder: "a chosen direction", detail: "Closure orientation made available by the relation.", required: true, kind: "text" },
  { key: "redefinition", label: "re-reading", placeholder: "read the same relation as…", detail: "Relative language/definition at the next closure level.", required: false, kind: "text" },
  { key: "bridge", label: "what persists", placeholder: "the relation maintained through the re-reading", detail: "Required bridge. Without it, zoom is OPEN rather than a new view.", required: false, kind: "text" },
  { key: "world", label: "world / universe continuation", placeholder: "where this direction becomes shareable or practical", detail: "A global continuation appears only through a bridged relation.", required: false, kind: "text" },
  { key: "position", label: "relative position", placeholder: "", detail: "Natural, dual, or obstructed are readings of this same trace.", required: true, kind: "position" },
];

const returnSchema: Array<Pick<InputSeed, "key" | "label" | "placeholder" | "detail" | "required" | "kind">> = [
  { key: "source", label: "source / observation", placeholder: "a source, conversation, or observation", detail: "Material becomes part of a path only through this selected relation.", required: false, kind: "text" },
  { key: "lesson", label: "lesson / question", placeholder: "a traversable learning relation", detail: "A local lesson reading of the selected trace.", required: false, kind: "text" },
  { key: "attempt", label: "attempt", placeholder: "what was actually tried", detail: "An attempted trace is required for return.", required: false, kind: "text" },
  { key: "receipt", label: "return receipt", placeholder: "what was returned or compared", detail: "The stated grounding evidence for return.", required: false, kind: "text" },
  { key: "returnedPerspective", label: "successor perspective", placeholder: "the next reading", detail: "A successor is a continuation, not literal repetition.", required: false, kind: "text" },
];

/** Input positions are an open closure trace, not a surrounding control panel. */
function seedGeometry(index: number, total: number, target: "proposal" | "selected") {
  const start = target === "proposal" ? 12 : 14;
  const end = target === "proposal" ? 88 : 86;
  const row = target === "proposal" ? 82 : 14;
  return { x: total === 1 ? 50 : start + (index / (total - 1)) * (end - start), y: row + (index % 2) * 9 };
}

function inputSeeds(target: "proposal" | "selected", value: Omit<Interaction, "id"> | Interaction, schema: typeof seedSchema | typeof returnSchema): InputSeed[] {
  return schema.map((field, index) => ({
    ...field,
    id: `${target}:${field.key}`,
    target,
    value: value[field.key] as string,
    tone: target === "proposal" ? "open" : hasReturn(value) ? "returned" : hasBridge(value) ? "path" : "open",
    appearance: appearanceFor(target === "proposal" ? "open" : hasReturn(value) ? "returned" : hasBridge(value) ? "path" : "open"),
    ...seedGeometry(index, schema.length, target),
  }));
}

function operations(field: ClosureField, selected: Interaction | null): ClosureOperation[] {
  const bridged = Boolean(selected && hasBridge(selected));
  const returned = Boolean(selected && hasReturn(selected));
  return [
    { id: "contract", type: "LENS", lens: "contracted", label: "contract", detail: "Recompose the selected bridged relation into its shared closure.", enabled: bridged, tone: bridged ? "path" : "open", appearance: appearanceFor(bridged ? "path" : "open") },
    { id: "reopen", type: "LENS", lens: "expanded", label: "reopen", detail: "Restore the selected relation as local presentation, WHY translation, and direction.", enabled: bridged, tone: bridged ? "path" : "open", appearance: appearanceFor(bridged ? "path" : "open") },
    { id: "return", type: "LENS", lens: "returned", label: "return", detail: "Create a successor presentation only through a bridged attempted receipt.", enabled: returned, tone: returned ? "returned" : "open", appearance: appearanceFor(returned ? "returned" : "open") },
    { id: "admit", type: "ADMIT_PROPOSAL", label: "admit open trace", detail: "Make the proposal a spatial relation only when perspective, WHY, and direction are present.", enabled: isAdmitted(field.proposal), tone: isAdmitted(field.proposal) ? "path" : "open", appearance: appearanceFor(isAdmitted(field.proposal) ? "path" : "open") },
    { id: "clear", type: "CLEAR", label: "clear field", detail: "Remove the current traces and leave an OPEN proposal field.", enabled: field.interactions.length > 0, tone: "open", appearance: appearanceFor("open") },
  ];
}

export function closureScene(field: ClosureField): ClosureScene {
  const selected = field.interactions.find((interaction) => interaction.id === field.selected) ?? field.interactions[0] ?? null;
  const selectedStatus = selected ? traceStatus(selected) : "OPEN";
  const topology = projectedTopology(field);
  const points = arrange(topology.rawPoints, selected?.id ?? null);
  const inputs = [
    ...inputSeeds("proposal", field.proposal, seedSchema),
    ...(selected ? inputSeeds("selected", selected, returnSchema) : []),
  ];
  const statusText = selected
    ? selectedStatus === "OPEN" ? "OPEN: the selected trace has not recorded a relative re-reading and preserved bridge."
      : selectedStatus === "PATH" ? "PATH: bridge recorded; contraction and reopening are available."
      : selectedStatus === "RETURNED" ? "RETURNED: the attempted trace has produced a successor perspective."
      : selectedStatus === "DUAL" ? "DUAL: the selected trace remains a relative dual reading."
      : "OBSTRUCTION: the selected trace records an unresolved relative obstruction."
    : "OPEN: no interaction has been admitted; only an open candidate trace is available.";
  const focusText = selected
    ? `${selected.why} — ${hasBridge(selected) ? selected.bridge : "bridge absent"}${hasWorldContinuation(selected) ? ` — ${selected.world}` : ""}`
    : "Build an interaction trace; the map has no independent topic or navigation state.";
  return { status: selectedStatus, statusAppearance: appearanceFor(toneFor(selectedStatus)), lens: field.lens, statusText, focusText, points, links: topology.links, inputs, operations: operations(field, selected) };
}

export type ClosureEvent =
  | { type: "SELECT"; relationId: string }
  | { type: "LENS"; lens: Lens }
  | { type: "SET"; target: "proposal" | "selected"; key: InteractionFieldKey; value: string }
  | { type: "ADMIT_PROPOSAL" }
  | { type: "CLEAR" };

/** The only state transitions in the browser are closure events. */
export function transition(field: ClosureField, event: ClosureEvent): ClosureField {
  if (event.type === "SELECT") return { ...field, selected: event.relationId };
  if (event.type === "SET") {
    if (event.target === "proposal") return { ...field, proposal: { ...field.proposal, [event.key]: event.value } };
    if (!field.selected) return field;
    return { ...field, interactions: field.interactions.map((interaction) => interaction.id === field.selected ? { ...interaction, [event.key]: event.value } : interaction) };
  }
  if (event.type === "LENS") {
    const selected = field.interactions.find((interaction) => interaction.id === field.selected);
    const allowed = event.lens === "returned" ? Boolean(selected && hasReturn(selected)) : Boolean(selected && hasBridge(selected));
    return allowed ? { ...field, lens: event.lens } : field;
  }
  if (event.type === "ADMIT_PROPOSAL") {
    if (!isAdmitted(field.proposal)) return field;
    const id = `r${field.nextId}`;
    return { ...field, lens: "expanded", selected: id, nextId: field.nextId + 1, interactions: [...field.interactions, { ...field.proposal, id }], proposal: emptyInteraction() };
  }
  return { ...field, lens: "expanded", selected: null, interactions: [], proposal: emptyInteraction() };
}
