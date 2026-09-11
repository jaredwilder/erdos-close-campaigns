# PENDING / UNPROVED — erdos142-close-2026-09-05

Items **2, 3 and 4** below are **UNPROVED** — no claim in them is receipted, and
each names the exact command that would settle it. Item 1 was pending when this
file was first written and was **sealed later in the same session**; it is kept
here, marked RESOLVED, so the record shows what actually happened rather than
only the outcome.

## Status of the rented box at report time (2026-09-05 ~17:40Z)

The box `51.158.234.15` went into memory thrash and stopped answering SSH.
Measured, not inferred, from the last successful connection at 17:37:30Z:

```
Mem:  total 125  used 120  free 1  available 5   (GB)
PID    ELAPSED   RSS(kB)     COMMAND
93510    55:54   87,259,004  lean   <- ANOTHER USER'S JOB (/root/peer/erdos1-attack-2026-09-05/Probe02.lean)
121553   12:43   22,022,212  lean   <- THIS CAMPAIGN'S Attack07
96565    39:47    1,987,640  lean   <- another user's msl-eg411 build
```

`Attack07` was projected (from Close03's measured 0.86 MB per slice member) to
need roughly 28 GB peak against 5 GB of headroom. Continuing it risked the OOM
killer selecting the 87 GB job — another user's 56-minute run — because that is
the highest-badness target, not mine.

**Decision: kill this campaign's own job rather than gamble with someone else's.**
`pkill -f Attack07.lean` was issued repeatedly; SSH stopped responding before an
acknowledgement was received, so **whether the kill landed is UNKNOWN**. The job
carries `timeout 5400`, so it self-terminates by 18:55Z at the latest.

No further jobs were launched after this was observed. `run142d.sh` and
`run142f.sh` (the queued runners) were killed; `Close07_BehrendSeed` was started
and killed within ~2 seconds when the memory state was seen.

## Unproved items, with exact launch lines

Items 2 and 3 remain UNPROVED. Run them only when `free -g` shows real headroom (≥ 40 GB available) and no
other user's large `lean` process is live. One value per process — the kernel
holds the whole cardinality slice in memory.

### 1. `Close07_BehrendSeed.lean` — RESOLVED: SEALED at 17:41Z (exit 0, 5.31 s, 6.76 GB)

**No longer pending.** After the box recovered (17:40:55Z, 21 GB available) this
file was compiled clean: exit 0, every axiom line
`[propext, Classical.choice, Quot.sound]` or a subset, no `sorryAx`.
Receipts: `receipts/Close07_BehrendSeed.log`, `.time`. Now SEALED:

- `behrend_seed : 8*10^18 ≤ rothNumberNat (199^12)` (from `Behrend.bound_aux' 12 100`)
- `behrend_power_law`, `behrend_size`
- `exponent_strictly_above_classical : 2^20 < 3^13 ∧ (2*199^12-1)^13 < (8*10^18)^20`

The claim "this campaign's dial can be turned past the classical base-3
exponent log 2/log 3" rested entirely on this file and is now **PROVED**.

Every numeral in the file was independently pre-checked in exact integer /
rational arithmetic (`receipts/close07-arithmetic-precheck.log`): the Behrend
seed is legitimate (`8×10^18 ≤ 100^12/(12·100^2) = 25000000000000000000/3`),
both natural-subtraction rewrites hold, `2^20 < 3^13`, and
`(2·199^12−1)^13 < (8×10^18)^20` — giving θ = 0.67784 against the classical
0.63093, a margin of +0.04691. That pre-check is Python and was never a proof —
it only established that the file should not fail for arithmetic reasons. The
Lean kernel has since confirmed all of it independently.

One earlier attempt aborted with `EXIT=134` — a `ulimit -v` of 20 GB, too small
for Lean's virtual-address reservation. That was an operator error, not a
mathematical failure; at 48 GB the file compiled in 5.31 s using 6.76 GB RSS.
**Do not set `ulimit -v` below ~48 GB for any Lean job on this toolchain.**

```bash
ssh root@51.158.234.15 'cd /root/formalizer/proofs && export PATH=/root/.elan/bin:$PATH && \
  D=/root/peer/sub-142-close && ( ulimit -v 50331648; \
  /usr/bin/time -v timeout 1800 nice -n 19 lake env lean $D/Close07_BehrendSeed.lean \
  > $D/Close07_BehrendSeed.log 2> $D/Close07_BehrendSeed.time ); \
  grep -E "error|depends on axioms" $D/Close07_BehrendSeed.log'
```
Expect: ~10 s, ~7 GB. Pass = exit 0, every axiom line `[propext, Classical.choice, Quot.sound]`.

### 2. `Close05_Exact16.lean` — `rothNumberNat 16 = 8`

C(16,9) = 11,440 slice members. Projected ~10 GB above the ~7 GB baseline,
~3 min, extrapolated from Close03's measured 1:58.88 / 12.87 GB for 7,007.

```bash
ssh root@51.158.234.15 'cd /root/formalizer/proofs && export PATH=/root/.elan/bin:$PATH && \
  D=/root/peer/sub-142-close && ( ulimit -v 50331648; \
  /usr/bin/time -v timeout 5400 nice -n 19 lake env lean $D/Close05_Exact16.lean \
  > $D/Close05_Exact16.log 2> $D/Close05_Exact16.time ); \
  grep -E "error|depends on axioms" $D/Close05_Exact16.log'
```

### 3. `Close06_Exact17.lean` — `rothNumberNat 17 = 8`

C(17,9) = 24,310. Projected ~28 GB peak, ~7 min. **This is the file that needs
real headroom.** It supersedes Attack07 (same computation, but stated for
Mathlib's `rothNumberNat` instead of the predecessor campaign's private `r3`),
so Attack07 does not need to be re-run at all.

```bash
ssh root@51.158.234.15 'cd /root/formalizer/proofs && export PATH=/root/.elan/bin:$PATH && \
  D=/root/peer/sub-142-close && ( ulimit -v 50331648; \
  /usr/bin/time -v timeout 5400 nice -n 19 lake env lean $D/Close06_Exact17.lean \
  > $D/Close06_Exact17.log 2> $D/Close06_Exact17.time ); \
  grep -E "error|depends on axioms" $D/Close06_Exact17.log'
```

### 4. Attack07 (predecessor campaign) — DO NOT RE-RUN

Superseded by item 3. Its target `r3 17 ≤ 8` transports to `rothNumberNat` only
through `Close01_Bridge.r3_eq_rothNumberNat`; proving it natively (item 3) is
the same cost and a better statement.

## Cost model for whoever picks this up

Measured, from `Close03_Exact.time` (the only clean data point):
7,007 slice members → 1:58.88 wall, 12,865,976 kB peak RSS, against a
~6,870,000 kB baseline for `import Mathlib` alone.
⇒ **≈ 0.86 MB and ≈ 16 ms per slice member.** Slice size is C(n, k+1):

| n  | C(n,9)  | projected peak RSS | projected wall |
|----|---------|--------------------|----------------|
| 16 |  11,440 | ~17 GB             | ~3 min         |
| 17 |  24,310 | ~28 GB             | ~7 min         |
| 18 |  48,620 | ~49 GB             | ~13 min        |
| 19 |  92,378 | ~86 GB             | ~25 min        |
| 20 | 184,756 (C(20,10)) | ~166 GB | ~50 min      |

n = 19 and n = 20 do not fit this box (125 GB total, shared). They are not
"hard", they are out of budget — and per finding F3 in `TERMINAL.json` they buy
nothing for the exponent anyway.
