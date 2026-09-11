# Recent SRG construction audit

Date: 2026-07-24

The current target component was checked against recent public SRG construction results.

- Brady's 2025 partial-difference-set search reports first constructions for `(144,52,16,20)` and
  `(147,66,25,33)`.
- Brouwer's 2024 follow-up derives `(148,77,36,44)` by switching from the `(147,66,25,33)` graph with
  an isolated vertex.
- The target island contains `(148,63,22,30)` and its complement `(148,84,50,44)`, not `(148,77,36,44)`.
  Same vertex count is not a transport, and the cited switching construction does not establish either
  target parameter set.

The new known graphs are already in a different decided component. No valid target bridge was emitted.

Sources:

- https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i1p24
- https://aeb.win.tue.nl/preprints/srg148.pdf
