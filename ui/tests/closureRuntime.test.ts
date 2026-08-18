import assert from "node:assert/strict";
import { closureScene, initialClosureField, transition, type ClosureField } from "../app/closureRuntime";

const setProposal = (field: ClosureField, key: "why" | "goal" | "redefinition" | "bridge" | "world" | "sourceClaim", value: string) =>
  transition(field, { type: "SET", target: "proposal", key, value });

const setSelected = (field: ClosureField, key: "source" | "attempt" | "counterReading" | "verificationMethod" | "review" | "receipt" | "returnedPerspective", value: string) =>
  transition(field, { type: "SET", target: "selected", key, value });

let field = initialClosureField;
assert.equal(field.interactions[0].machine.phase, "open");
assert.equal(closureScene(field).status, "PATH");

field = transition(field, { type: "SELECT", relationId: "r1" });
field = transition(field, { type: "CONTRACT" });
assert.equal(field.interactions[0].machine.phase, "contracted");
field = transition(field, { type: "REOPEN" });
assert.equal(field.interactions[0].machine.phase, "reopened");

// A receipt alone cannot manufacture an interactive verification or a return.
field = setSelected(field, "attempt", "Practice the relation in a project");
field = setSelected(field, "receipt", "The attempt changes the next reading");
field = setSelected(field, "returnedPerspective", "A revised perspective");
field = transition(field, { type: "RETURN" });
assert.equal(field.interactions[0].machine.phase, "reopened");

field = setSelected(field, "source", "A cited passage and a record of the practice");
field = setSelected(field, "counterReading", "The same goal may not follow if the relation is an assumed limitation");
field = setSelected(field, "verificationMethod", "Compare the cited passage, the practical attempt, and the counter-reading");
field = setSelected(field, "review", "The bridge remains useful, but the counter-reading keeps a further question open");
field = transition(field, { type: "RETURN" });
assert.equal(field.interactions[0].machine.phase, "returned");
assert.equal(field.interactions[0].machine.residue?.counterReading, "The same goal may not follow if the relation is an assumed limitation");
assert.equal(field.interactions[0].machine.residue?.sourceRef, "SRC-2024-MAP");

field = transition(field, { type: "CONTINUE" });
assert.equal(field.continuation?.changedPerspective, "A revised perspective");
assert.equal(field.proposal.perspective, "A revised perspective");

field = setProposal(field, "sourceClaim", "A returned relation may be reconsidered as the opening of another question");
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
field = setSelected(field, "source", "A comparison note and the practice record");
field = setSelected(field, "counterReading", "The new direction could still preserve the original limiting assumption");
field = setSelected(field, "verificationMethod", "Compare a source reading, practical result, and alternative interpretation");
field = setSelected(field, "review", "The attempt changes the perspective while leaving the competing interpretation explicitly OPEN");
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
