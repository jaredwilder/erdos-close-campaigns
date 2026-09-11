# Acceptance Contract — how your submission gets checked

This package was written after finding real, checkable damage from prior external submissions to this
project: fabricated pointers to files/anchors that don't exist, and bulk-generated "technique" filler with
the topic name swapped in and nothing else distinct. Both were caught by direct inspection, not by trusting
the submission's own claims. Your submission will be checked the same way.

## What happens to your submission

1. **File existence check.** Every path, anchor, or citation you reference (a Mathlib declaration name, an
   `ARMORY.md` entry, an OEIS sequence ID, a Brouwer table entry) must resolve to something that actually
   exists. A citation to a file or anchor that isn't real is an instant reject of that specific claim, not
   just a note.
2. **Re-run your `selftest()`.** It must actually execute and actually pass, not just be present. If it
   imports anything, those imports must resolve against the real files in `reference/` (or standard-library/
   commonly-available packages you name explicitly — don't assume an unstated dependency is installed).
3. **Independent re-verification of at least one claimed edge.** For any transport you claim is verified,
   at least one data point will be independently recomputed by a human or a separate checking process
   against Brouwer's table (or the equivalent ground-truth source you cited). If it disagrees with your
   claimed result, the whole submission is treated as unverified, not partially credited.
4. **Overlap/disagreement honesty check.** If you report "N verified, 0 disagreements," the actual overlap
   count N will be checked against how many parameter values you actually tested — a transport "verified"
   over only 2-3 points where `MIN_OVERLAP` in this codebase is 5 does not meet the bar (see
   `design_transports.py`'s `MIN_OVERLAP` constant).
5. **Template/filler check.** If multiple "transports" or "techniques" you submit differ only in a
   substituted family name or parameter, with no distinct verification logic or mathematical content behind
   each, they will be treated as a single submission, not N.

## What "accepted" gets you

An accepted transport gets merged into the live `oracle-math.db` graph as a real `EQUIVALENCE`/
`IMPLICATION` edge, with `tier` set honestly based on its verification strength (`kernel-verified` only if
it's Lean-checked; `published-proof` if literature-cited and machine-verified on overlap;
`curated-database` if checked only against a curated table like Brouwer's). It will then be load-bearing —
other tools will traverse it without re-checking. That is why the bar above is strict.

## What gets flagged, not silently dropped

If your submission includes an honest "I could not find a real bridging transport, here is specifically
what's missing" section, that gets kept and surfaced — it's real information about where the gap actually
is, and this project's own doctrine treats an honest documented gap as more valuable than a fabricated fix.
