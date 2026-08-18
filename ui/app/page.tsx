"use client";

import { useMemo, useReducer } from "react";
import type { CSSProperties } from "react";
import {
  closureScene,
  initialClosureField,
  transition,
  type ClosureEvent,
  type ClosureAppearance,
  type ClosureOperation,
  type InputSeed,
  type SceneLink,
  type ScenePoint,
} from "./closureRuntime";

/**
 * Generic interpreter only. It has no Slearn labels, topology, coordinates,
 * styling decisions, or enabled mechanics: all are supplied by closureScene.
 */
export default function Home() {
  const [field, dispatch] = useReducer(transition, initialClosureField);
  const scene = useMemo(() => closureScene(field), [field]);
  return (
    <main className="closure-machine" data-status={scene.status} data-lens={scene.lens}>
      <section className="closure-plane" aria-label={scene.statusText}>
        <div className="machine-verdict" data-pattern={scene.statusAppearance.pattern} data-glow={scene.statusAppearance.glow} style={appearanceStyle(scene.statusAppearance)}>
          <span>{scene.status}</span>
          <small>{scene.statusText}</small>
        </div>
        {scene.links.map((link) => <GenericLink key={link.id} link={link} points={scene.points} />)}
        {scene.points.map((point) => <GenericPoint key={point.id} point={point} dispatch={dispatch} />)}
        {scene.inputs.map((input) => <GenericSeed key={input.id} input={input} dispatch={dispatch} />)}
        <div className="machine-focus" data-pattern={scene.statusAppearance.pattern} style={appearanceStyle(scene.statusAppearance)}>{scene.focusText}</div>
        <nav className="machine-operations" aria-label="Available closure operations">
          {scene.operations.map((operation) => <GenericOperation key={operation.id} operation={operation} dispatch={dispatch} />)}
        </nav>
      </section>
    </main>
  );
}

function GenericPoint({ point, dispatch }: { point: ScenePoint; dispatch: (event: ClosureEvent) => void }) {
  const style = { left: `${point.x}%`, top: `${point.y}%`, ...appearanceStyle(point.appearance) } as CSSProperties;
  return (
    <button className={`machine-point ${point.selected ? "selected" : ""}`} data-pattern={point.appearance.pattern} data-glow={point.appearance.glow} style={style} type="button" title={point.detail} onClick={() => dispatch({ type: "SELECT", relationId: point.traceIds[0] })}>
      <span>{point.role}</span>
      <strong>{point.label}</strong>
      <small>{point.traceIds.length === 1 ? "one trace" : `${point.traceIds.length} traces`}</small>
    </button>
  );
}

function GenericLink({ link, points }: { link: SceneLink; points: ScenePoint[] }) {
  const source = points.find((point) => point.id === link.from);
  const target = points.find((point) => point.id === link.to);
  if (!source || !target) return null;
  const dx = target.x - source.x;
  const dy = target.y - source.y;
  const style = { left: `${source.x}%`, top: `${source.y}%`, width: `${Math.hypot(dx, dy)}%`, transform: `rotate(${Math.atan2(dy, dx) * (180 / Math.PI)}deg)`, ...appearanceStyle(link.appearance) } as CSSProperties;
  return <i className="machine-link" data-pattern={link.appearance.pattern} data-glow={link.appearance.glow} style={style} aria-hidden="true" />;
}

function GenericSeed({ input, dispatch }: { input: InputSeed; dispatch: (event: ClosureEvent) => void }) {
  const style = { left: `${input.x}%`, top: `${input.y}%`, ...appearanceStyle(input.appearance) } as CSSProperties;
  return (
    <label className="machine-seed" data-pattern={input.appearance.pattern} data-glow={input.appearance.glow} style={style} title={input.detail}>
      <span>{input.label}{input.required && <b> required</b>}</span>
      {input.kind === "position" ? (
        <select value={input.value} onChange={(event) => dispatch({ type: "SET", target: input.target, key: input.key, value: event.target.value })}>
          <option value="natural">natural</option>
          <option value="dual">relative dual</option>
          <option value="obstructed">relative obstruction</option>
        </select>
      ) : (
        <textarea rows={2} value={input.value} placeholder={input.placeholder} onChange={(event) => dispatch({ type: "SET", target: input.target, key: input.key, value: event.target.value })} />
      )}
    </label>
  );
}

function GenericOperation({ operation, dispatch }: { operation: ClosureOperation; dispatch: (event: ClosureEvent) => void }) {
  const event: ClosureEvent = operation.type === "LENS"
    ? { type: "LENS", lens: operation.lens! }
    : operation.type === "ADMIT_PROPOSAL" ? { type: "ADMIT_PROPOSAL" }
      : { type: "CLEAR" };
  return <button className="machine-operation" data-pattern={operation.appearance.pattern} data-glow={operation.appearance.glow} style={appearanceStyle(operation.appearance)} type="button" disabled={!operation.enabled} title={operation.detail} onClick={() => dispatch(event)}>{operation.label}</button>;
}

function appearanceStyle(appearance: ClosureAppearance) {
  return { "--signal": appearance.signal } as CSSProperties;
}
