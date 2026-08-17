export type Orientation = "perspective" | "goal";
export type HairId = "why" | "lesson" | "goal";
export type ClosureStatus = "OPEN_LOCAL" | "LOCALLY_COMPATIBLE" | "RETURNED_COMPLETE";

export type Hair = {
  id: HairId;
  label: string;
  translation: string;
  status: ClosureStatus;
  witness: string;
};

export type ClosureReceipt = {
  sequence: number;
  sourceOrientation: Orientation;
  translation: string;
  returnWitness: string;
  status: ClosureStatus;
};

export type ClosureState = {
  ball: string;
  orientation: Orientation;
  hairs: Hair[];
  receipt: ClosureReceipt | null;
  sequence: number;
};

const perspectiveHairs: Hair[] = [
  { id: "why", label: "WHY", translation: "perspective → WHY", status: "LOCALLY_COMPATIBLE", witness: "relation preserved across the selected view" },
  { id: "lesson", label: "LESSON", translation: "WHY → lesson", status: "OPEN_LOCAL", witness: "finite opening; continuation remains available" },
  { id: "goal", label: "GOAL", translation: "lesson → goal", status: "RETURNED_COMPLETE", witness: "goal closes with the active perspective" },
];

const goalHairs: Hair[] = [
  { id: "why", label: "WHY⁻¹", translation: "goal → WHY", status: "LOCALLY_COMPATIBLE", witness: "goal relation translated into the active view" },
  { id: "lesson", label: "REQUIREMENT", translation: "WHY → lesson", status: "OPEN_LOCAL", witness: "selected prerequisite remains locally open" },
  { id: "goal", label: "PERSPECTIVE", translation: "lesson → perspective", status: "RETURNED_COMPLETE", witness: "perspective closes with the active goal" },
];

export const initialClosureState: ClosureState = {
  ball: "PERSPECTIVE",
  orientation: "perspective",
  hairs: perspectiveHairs,
  receipt: null,
  sequence: 0,
};

export type ClosureEvent = { type: "FOLLOW_HAIR"; hair: HairId } | { type: "FLIP_ORIENTATION" };

/** Finite executable mirror of the ContinualInversion receipt contract. */
export function transition(state: ClosureState, event: ClosureEvent): ClosureState {
  if (event.type === "FLIP_ORIENTATION") {
    const orientation = state.orientation === "perspective" ? "goal" : "perspective";
    return {
      ...state,
      orientation,
      ball: orientation === "perspective" ? "PERSPECTIVE" : "GOAL",
      hairs: orientation === "perspective" ? perspectiveHairs : goalHairs,
    };
  }

  const hair = state.hairs.find((candidate) => candidate.id === event.hair);
  if (!hair) return state;
  const orientation = hair.id === "goal" ? (state.orientation === "perspective" ? "goal" : "perspective") : state.orientation;
  const sequence = state.sequence + 1;

  return {
    ball: hair.label,
    orientation,
    hairs: orientation === "perspective" ? perspectiveHairs : goalHairs,
    sequence,
    receipt: {
      sequence,
      sourceOrientation: state.orientation,
      translation: hair.translation,
      returnWitness: hair.witness,
      status: hair.status,
    },
  };
}
