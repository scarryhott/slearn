/**
 * Privacy-preserving source anchors for the Slearn closure ledger.
 *
 * These are deliberately short provenance handles rather than copies of
 * private notes.  Their longer chronology and classification live in
 * docs/SLEARN_SOURCE_PROVENANCE.md.  A closure episode must identify one of
 * these anchors (or an explicitly recorded observation/external source)
 * before it can be admitted to the map.
 */
export const closureSources = [
  {
    id: "SRC-2023-WHY",
    label: "2023 WHY-first learning note",
    class: "direct project note",
    contribution: "Questions, projects, failure, and learner-directed assistance.",
  },
  {
    id: "SRC-2024-MAP",
    label: "2024 perspective-map interface note",
    class: "direct interface specification",
    contribution: "Perspective, belief/value, goal, lesson, project, world, zoom, and lived return.",
  },
  {
    id: "SRC-2024-ADAPTIVE",
    label: "2024 adaptive path note",
    class: "direct project note",
    contribution: "AI may offer paths relative to learner choice; it does not replace the learner's map.",
  },
  {
    id: "SRC-2025-TRIANGLE",
    label: "2025 natural-rhythm triangle note",
    class: "direct project note",
    contribution: "Downward decomposition, upward return, revised goal/depth, and multiple WHY paths.",
  },
  {
    id: "SRC-2026-WHY-TREE",
    label: "2026 WHY-tree note",
    class: "direct project note",
    contribution: "Insights are organized beneath perspective maps through inspectable WHY branches.",
  },
  {
    id: "SRC-2026-MAZE",
    label: "2026 perspectival maze-map note",
    class: "direct project note",
    contribution: "Learning/goal/perspective/WHY/lesson trees are read through a perspectival maze-map.",
  },
  {
    id: "CHAT-EDUCATION-MAP",
    label: "education-model design conversation",
    class: "direct conversational design material",
    contribution: "Draw relations among perspectives, reasons, and goals; sources and other maps remain revisable.",
  },
  {
    id: "OBSERVED-INTERACTION",
    label: "recorded learner interaction",
    class: "runtime observation",
    contribution: "A concrete observation, conversation, or practice supplied for this one episode.",
  },
  {
    id: "EXTERNAL-SOURCE",
    label: "external source supplied by learner",
    class: "runtime reference",
    contribution: "A citation, artifact, or primary material supplied for this one episode.",
  },
] as const;

export type ClosureSourceId = typeof closureSources[number]["id"];
export type ClosureSource = typeof closureSources[number];

export function sourceById(id: string): ClosureSource | undefined {
  return closureSources.find((source) => source.id === id);
}
