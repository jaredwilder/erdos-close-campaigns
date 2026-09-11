# SRG frontier search

This is the next search record after completing the conference structural transport.

## Checked lanes

The repository’s explicit SRG constructors were used as source graphs, and every switched graph was
rechecked by the independent SRG checker before it could become an edge.

| source order | explicit sources checked | target parameters | verified target hits |
|---:|---|---|---:|
| 100 | lattice(10), complete multipartite | `(100,33,8,12)` | 0 |
| 121 | lattice(11), cyclic Latin-square ladder `g=3..12` | `(121,36,7,12)`, `(121,48,17,20)` | 0 |
| 169 | lattice(13) | `(169,42,5,12)`, `(169,56,15,20)`, `(169,70,27,30)` | 0 |

No edge was emitted. The live database is unchanged by this search.

## Current implication

Component `135224` is not missing an existing constructor endpoint. It contains open SRG parameter
sets whose known explicit source families do not reach them by the tested switching operation. The
next productive lane is a new construction family (for example a verified partial-geometry or linked-
design construction), not another conference-range expansion.
