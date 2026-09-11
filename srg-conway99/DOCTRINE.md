# Doctrine — read this in full before writing any code

## The one rule that matters

**Every edge you claim must be independently verified by real computation on both sides, or it does not go
in.** This is a graph other tools will trust and traverse without re-checking. A false edge doesn't just
give one wrong answer — it silently poisons every future query that walks through it.

## This is a $0, zero-LLM system

The graph, the blades, and the verification are all real deterministic computation: SQL queries, SAT/exact
solvers, Lean-checked theorems, direct arithmetic. There is no LLM step at runtime anywhere in this
pipeline. You (Codex) may use every ounce of your own intelligence to *author* the code and to *propose*
candidate transports (pattern-matching known mathematical equivalences is exactly the right use of your
reasoning). The code you ship must not call an LLM to decide whether an edge is real — that decision must
be made by re-computing both sides and checking they agree.

## Why this matters — a real incident from this project's history

On 2026-07-23 the operator proposed a transport from memory: `Hadamard(4t) <-> SRG(4t-1, 2t-1, t-1, t-1)`.
It is impossible for every single t — `v*k = (4t-1)(2t-1)` is odd*odd, so the strongly-regular-graph degree
sum is odd, which cannot happen in any real graph. The verifier caught it immediately because it recomputed
both sides instead of trusting the claim. That is the entire point of the PROPOSE/VERIFY split used
throughout `oracle/kbk/engine/design_transports.py`: a human or a model proposing a plausible-sounding
parameter map is the *weakest* part of the chain, and the code must never let that proposal stand without
independent re-derivation.

## The PROPOSE / VERIFY split (the pattern to follow exactly)

Look at `reference/design_transports.py`. Every transport candidate has this shape:

```python
{
    "name": "...",
    "receipt": "<citation or derivation, human-readable>",
    "type": "EQUIVALENCE" | "IMPLICATION",
    "range": range(...),          # the parameter space to test over
    "left": lambda n: (family, params),   # left side of the claimed relation
    "right": lambda n: (family, params),  # right side
}
```

`verify()` then computes the REAL status of both sides independently (via `computed_truth.py`'s
`*_status()` functions — actual lookups against Brouwer's tables / actual solver calls, never guessed) over
every value in `range`, and only accepts the transport if there is real overlap (`MIN_OVERLAP`, currently 5)
and **zero disagreements**. `EQUIVALENCE` requires both directions to agree in both directions;
`IMPLICATION` only requires the one failure mode (`left EXISTS, right NONE`) to never occur.

**Any transport you submit must go through this exact discipline** — propose the parameter map, then call
the real `computed_truth` functions (or write new ones with the same "real lookup, never guessed" property)
to check it, and report the disagreement count honestly even if it's not zero.

## One-sided results are weaker than they look

A real correction already made in this codebase: two design-theory transports were verified "16/16 agree,"
but all 16 test points were EXISTS cases — the verifier never once saw the transport correctly predict an
*impossibility* (a NONE/NONE agreement). `verify()` was changed to always report the EXISTS/NONE balance
and stamp one-sided results `[ONE-SIDED]`. If everything you test happens to exist, you have not actually
tested whether the transport is correct — you've only tested whether it's consistent on the easy half. Test
against known-impossible parameter combinations too, and report the balance explicitly.

## What "verified" does NOT mean

- It does not mean "the code ran without crashing."
- It does not mean "it matched on the first few values I happened to try."
- It does not mean "it's citing a real theorem" (citing something real is necessary, not sufficient — the
  citation must actually apply to the exact parameter range you're claiming, checked point by point).

## Ground truth sources already in this repo (use them, don't invent new ones)

- Brouwer's strongly-regular-graph parameter table (`ns='brouwer'` nodes) — the authoritative existence/
  non-existence source for SRGs. `computed_truth.py`'s lookups against this are ground truth.
- OEIS (`ns='oeis'`) — published, citable sequences.
- Mathlib Lean declarations (`ns='mathlib'`) — kernel-checked, the strongest possible tier (`kernel-verified`
  in the `tier` column).
- La Jolla covering/design repository conventions, referenced throughout `oracle/kbk/engine/covering_*.py`.

If a claim can't be checked against one of these (or an equally rigorous independent source you name
explicitly), it doesn't belong in this graph yet — flag it as a gap instead of forcing it in.
