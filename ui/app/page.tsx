"use client";

import { useReducer } from "react";
import { initialClosureState, transition, type Hair } from "./closureRuntime";

const positions = ["north", "southwest", "southeast"];

export default function Home() {
  const [state, dispatch] = useReducer(transition, initialClosureState);

  return (
    <main className={`closure ${state.orientation === "goal" ? "goal-oriented" : ""}`}>
      <p className="runtime-mark">SLEARN / CONTINUAL INVERSION / {state.orientation.toUpperCase()}</p>

      <section className="field" aria-label="Perspectival closure hair">
        <button
          className="ball"
          onClick={() => dispatch({ type: "FLIP_ORIENTATION" })}
          aria-label="Flip the active closure orientation"
        >
          <span className="ball-title">{state.ball}</span>
          <span className="ball-subtitle">formal ball · invert orientation</span>
        </button>

        {state.hairs.map((hair, index) => (
          <HairBranch
            key={hair.id}
            hair={hair}
            position={positions[index]}
            onFollow={() => dispatch({ type: "FOLLOW_HAIR", hair: hair.id })}
          />
        ))}

        {state.receipt && (
          <div className="receipt" aria-live="polite">
            <b>ρ{state.receipt.sequence}</b>
            <span>{state.receipt.translation}</span>
            <span>{state.receipt.returnWitness}</span>
            <em>{state.receipt.status}</em>
          </div>
        )}
      </section>

      <p className="closure-note">
        A hair is an admissible translation from the active ball. Following one records its witness-relative return.
      </p>
    </main>
  );
}

function HairBranch({ hair, position, onFollow }: { hair: Hair; position: string; onFollow: () => void }) {
  return (
    <button className={`hair ${position}`} onClick={onFollow} aria-label={`Follow ${hair.label} hair`}>
      <span className="thread" />
      <span className="hair-node">
        <b>{hair.label}</b>
        <small>{hair.translation}</small>
        <i>{hair.status}</i>
      </span>
    </button>
  );
}
