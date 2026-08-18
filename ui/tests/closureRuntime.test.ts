import assert from "node:assert/strict";
import { closureScene, initialClosureField, transition, type ClosureField } from "../app/closureRuntime";

const setProposal = (field: ClosureField, key: "why" | "goal" | "redefinition" | "bridge" | "world", value: string) =>
  transition(field, { type: "SET", target: "proposal", key, value });

const setSelected = (field: ClosureField, key: "attempt" | "receipt" | "returnedPerspective", value: string) =>
  transition(field, { type: "SET", target: "selected", key, value });

let field = initialClosureField;
assert.equal(field.interactions[0].machine.phase, "returned");

field = transition(field, { type: "CONTINUE" });
assert.equal(field.continuation?.changedPerspective, "A revised perspective");
assert.equal(field.proposal.perspective, "A revised perspective");

field = setProposal(field, "why", "Why this returned perspective now matters");
field = setProposal(field, "goal", "A next learning direction");
field = setProposal(field, "redefinition", "Read the direction as a new local practice");
field = setProposal(field, "bridge", "The returned question still joins perspective and direction");
field = setProposal(field, "world", "A practical relation to a shared world");
field = transition(field, { type: "ADMIT_PROPOSAL" });
assert.equal(field.interactions.at(-1)?.machine.phase, "open");
assert.equal(field.interactions.at(-1)?.machine.inheritedResidue?.changedPerspective, "A revised perspective");

field = transition(field, { type: "CONTRACT" });
assert.equal(field.interactions.at(-1)?.machine.phase, "contracted");
assert.equal(field.lens, "contracted");

field = transition(field, { type: "REOPEN" });
assert.equal(field.interactions.at(-1)?.machine.phase, "reopened");
assert.equal(field.lens, "expanded");

field = setSelected(field, "attempt", "Test the new direction in practice");
field = setSelected(field, "receipt", "The practice exposed a changed relation");
field = setSelected(field, "returnedPerspective", "A second revised perspective");
field = transition(field, { type: "RETURN" });
assert.equal(field.interactions.at(-1)?.machine.phase, "returned");
assert.equal(field.lens, "returned");

const scene = closureScene(field);
assert.ok(scene.points.some((point) => point.role === "residue"));
assert.ok(scene.points.some((point) => point.role === "successor"));

field = transition(field, { type: "CONTINUE" });
assert.equal(field.proposal.perspective, "A second revised perspective");
assert.equal(field.continuation?.receipt, "The practice exposed a changed relation");

console.log("closure runtime episode passed");
