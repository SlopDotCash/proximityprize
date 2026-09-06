"use client";

import { useMemo, useState } from "react";
import { example, MESSAGE, ORIGINAL } from "@/lib/rs-example";

function Symbols({ values, changed = 0 }: { values: number[]; changed?: number }) {
  return <div className="symbols">{values.map((v, i) => <span key={i}
    className={i < changed ? "symbol changed" : "symbol"}
    aria-label={`${v}${i < changed ? ", changed" : ""}`}>
    {v}{i < changed && <small aria-hidden="true">×</small>}
  </span>)}</div>;
}

export function ProblemVisual() {
  const [errors, setErrors] = useState(2);
  const result = useMemo(() => example(errors), [errors]);
  return <figure className="problem-visual" aria-labelledby="visual-title">
    <figcaption id="visual-title">Try a small Reed–Solomon code</figcaption>
    <div className="visual-step">
      <p><b>1. Add redundancy</b><span>Four message symbols become eight encoded symbols.</span></p>
      <div className="encoding"><Symbols values={MESSAGE} /><span aria-hidden="true">→</span><Symbols values={ORIGINAL} /></div>
    </div>
    <div className="visual-step">
      <label htmlFor="errors"><b>2. Change some symbols</b><span>{errors} of 8 changed · {errors * 12.5}% errors</span></label>
      <input id="errors" type="range" min="0" max="4" step="1" value={errors}
        aria-valuetext={`${errors} of 8 symbols changed`}
        onChange={(e) => setErrors(Number(e.target.value))} />
      <Symbols values={result.received} changed={errors} />
      <p className="visual-key">× marks a changed symbol. Move the slider to add or remove errors.</p>
    </div>
    <div className="visual-step" aria-live="polite" aria-atomic="true">
      <p><b>3. Find the possible messages</b><span>Keep every valid codeword at most {errors} symbol {errors === 1 ? "change" : "changes"} away.</span></p>
      <p className="candidate-count"><strong>{result.count}</strong> possible {result.count === 1 ? "message" : "messages"}</p>
      <p className="visual-key">{result.count === 1 ? "Here the original message is the only candidate." : "Here several messages fit. List decoding returns the candidate list."}</p>
    </div>
    <p className="visual-note">Exact enumeration of all 17⁴ messages for this eight-symbol code, using arithmetic modulo 17.
      This illustrates ordinary list decoding; the prize adds interleaving, smooth-domain, and much smaller failure-budget requirements.</p>
  </figure>;
}
