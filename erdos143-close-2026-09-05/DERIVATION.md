# Erdos 143 — the in-record derivation (MSL s.42.1 D1 provenance)

**Campaign** `erdos143-close-2026-09-05` · **MSL_DIALECT v2.0 · MSL_MODE CLOSE**

## 0. Frozen target

Source: `oracle/evidence/targets/erdos-statements.json`, key `erdos:143`,
fetched `2026-08-10T09:18:02` from `erdosproblems.com/latex/143`. Prize `$500`,
tags `["primitive sets"]` (`oracle/evidence/targets/erdos-enriched.json`).

> Let \(A\subset(1,\infty)\) be a countably infinite set such that for all
> \(x\neq y\in A\) and integers \(k\geq 1\) we have \(\lvert kx-y\rvert\geq 1\).
> Does this imply that \(A\) is sparse? In particular, does this imply that
> \(\sum_{x\in A}\frac{1}{x\log x}<\infty\) or
> \(\sum_{x<n,\,x\in A}\frac1x=o(\log n)\)?

Lean freeze: `oracle/evidence/targets/lean-sources/FormalConjectures__ErdosProblems__143.lean`
(`Erdos143.WellSeparatedSet`, `erdos_143.parts.i`, `erdos_143.parts.ii`; both
carry `sorry` and `@[category research open]`).

**Symbol binding.** "\(k\)" ranges over the natural numbers \(\ge 1\), not over
reals and not over integers of either sign. The condition is stated for the
*ordered* pair, so both \(\lvert kx-y\rvert\ge1\) and \(\lvert ky-x\rvert\ge1\)
hold. \(k=1\) therefore gives \(\lvert x-y\rvert\ge 1\): **A is 1-separated.**

## 1. The dilation-packing theorem

**Theorem T1.** Let \(A\subseteq(1,\infty)\) satisfy the separation predicate.
Then for every \(X>0\),
\[ \#\bigl(A\cap(1,2X)\bigr)\ \le\ \lceil X\rceil, \qquad\text{hence}\qquad
   \#\bigl(A\cap(1,Y)\bigr)\ \le\ \tfrac{Y}{2}+1 \ \ \text{for all } Y>0. \]

*Derivation.* Fix \(X>0\). For \(a\in A\) with \(a<2X\) put
\[ m(a) \;=\; \min\{\,m\in\mathbb N : 2^{m}a\ \ge\ X\,\}, \qquad
   \varphi(a) \;=\; 2^{m(a)}a . \]
The minimum exists because \(a>1\) forces \(2^{m}a\ge 2^{m}\to\infty\).

**(1a) The image lies in \([X,2X)\).** \(X\le\varphi(a)\) is the defining
property. For the upper bound: if \(m(a)=0\) then \(\varphi(a)=a<2X\) by
hypothesis; if \(m(a)=n+1\) then minimality gives \(2^{n}a<X\), so
\(\varphi(a)=2\cdot 2^{n}a<2X\).

**(1b) The image is 1-separated.** Let \(a\ne b\) in \(A\cap(1,2X)\) and assume
without loss of generality \(m(b)\le m(a)\); write \(d=m(a)-m(b)\ge 0\). Then
\[ \varphi(a)-\varphi(b)\;=\;2^{m(b)}\bigl(2^{d}a-b\bigr), \]
and \(2^{d}\) is an integer \(\ge 1\), so the defining property of \(A\) applied
with \(x=a,\;y=b,\;k=2^{d}\) gives \(\lvert 2^{d}a-b\rvert\ge1\). Since
\(2^{m(b)}\ge1\),
\[ \lvert\varphi(a)-\varphi(b)\rvert \;=\; 2^{m(b)}\,\lvert 2^{d}a-b\rvert \;\ge\; 1 . \]
In particular \(\varphi\) is injective on \(A\cap(1,2X)\).

**(1c) Counting.** \(\varphi\) maps \(A\cap(1,2X)\) injectively onto a
1-separated subset of the half-open interval \([X,2X)\) of length \(X\). The map
\(t\mapsto\lfloor t-X\rfloor\) sends that image injectively into
\(\{0,1,\dots,\lceil X\rceil-1\}\): two points with the same floor differ by less
than 1, contradicting (1b). Hence \(\#(A\cap(1,2X))\le\lceil X\rceil\). Putting
\(X=Y/2\) and using \(\lceil Y/2\rceil< Y/2+1\) gives the second form. \(\square\)

**Why the multipliers must be powers of two — the method's own ceiling.**
Step (1b) works because the two multipliers used, \(2^{m(a)}\) and \(2^{m(b)}\),
are *comparable under divisibility*: only then does \(\varphi(a)-\varphi(b)\)
factor as (integer multiplier) × (an instance of the defining inequality). For
an arbitrary assignment \(a\mapsto k(a)\cdot a\) the same computation needs
\(k(a)\mid k(b)\) or \(k(b)\mid k(a)\) for **every** pair, i.e. the multiplier set
must be a chain in the divisibility order. A chain \(k_1\mid k_2\mid\cdots\)
whose dilates of \((1,X)\) cover the window \([X,\lambda X)\) needs consecutive
ratios \(\le\lambda\) and \(\ge2\); for \(\lambda=2\) that pins the chain to
\(\{2^{m}\}\) exactly, and \(\lambda>2\) gives a strictly weaker constant
(\(\lambda=3\) yields \(\tfrac23\) in place of \(\tfrac12\)). **The packing
method is saturated at \(1/2\).**

## 2. Corollaries

**C1 (upper density).** \(\limsup_{x\to\infty}\#(A\cap[1,x])/x\le \tfrac12\).

**C2 (harmonic sum).** Abel summation against \(N(t)=\#(A\cap(1,t))\le t/2+1\):
\[ \sum_{\substack{x\in A\\ x<n}}\frac1x \;=\; \frac{N(n)}{n}+\int_{2}^{n}\frac{N(t)}{t^{2}}\,dt
   \;\le\; \tfrac12\log n + O(1). \]
This is a factor-2 improvement on the trivial \(\log n + O(1)\) that
1-separation alone gives — and it is **not** the \(o(\log n)\) the problem asks
for. **UNPROVED here; analytic, not receipted** — only the input \(N(t)\le t/2+1\)
is kernel-checked. C1 is likewise stated but not formalized.

## 3. Elements are at least 2

**Theorem T2.** If \(A\) is well-separated **and infinite**, every \(a\in A\)
satisfies \(a\ge2\).

*Derivation.* Suppose \(1<x<2\), \(x\in A\). Infinitude gives \(y\in A\),
\(y\ne x\), \(y>1\). If \(y<x\) then \(0<x-y<2-1=1\), contradicting
1-separation. If \(y>x\), set \(k=\lfloor y/x\rfloor\ge1\) and \(r=y-kx\in[0,x)\).
If \(r<1\) then \(\lvert kx-y\rvert=r<1\), contradiction. If \(r\ge1\) then
\(\lvert (k+1)x-y\rvert=x-r\le x-1<1\), contradiction. \(\square\)

(The infinitude hypothesis is load-bearing: the singleton \(\{3/2\}\) is
vacuously well-separated. T1 needs no such hypothesis.)

## 4. Sharpness

For every \(N\ge2\), \(A_N=\{N,N+1,\dots,2N-1\}\) satisfies the separation
predicate: the entries are integers, so \(\lvert kx-y\rvert\ge1\) unless
\(kx=y\); \(k=1\) forces \(x=y\), and \(k\ge2\) forces \(kx\ge2N>y\). And
\(\#(A_N\cap(1,2N))=N=\tfrac{2N}{2}\). **The constant \(1/2\) in T1 cannot be
lowered.** Verified exhaustively for \(2\le N\le120\) — receipt
`receipts/falsifier-2026-09-05.json`, arm `SHARPNESS`, `max_count_over_2N = 1/2`.

\(A_N\) is finite; that the supremum \(1/2\) is also approached by *infinite*
primitive integer sequences is Besicovitch (1934). **CITED,
VERIFICATION_DEPTH EXISTS, adjudicates nothing here** — the finite family alone
already proves T1 optimal.

## 5. What this does NOT do

Neither `erdos_143.parts.i` nor `erdos_143.parts.ii` is touched.

* Part (i) asks for \(\liminf\); T1 bounds the \(\limsup\). A set whose block
  densities hover near \(1/2\) is compatible with everything proved here.
* Part (ii) needs \(\sum 1/(x\log x)<\infty\); T1 gives
  \(\sum 1/(x\log x)\le\tfrac12\sum 1/(x\log x)\)-type bounds that **diverge**
  (\(\int dt/(t\log t)=\log\log t\)). T1 is not even the right order of
  strength for part (ii).

## 6. External audit (MSL s.42.8 D8 — obtained BEFORE banking)

Receipt: `oracle/evidence/ask-gemini/20260905T184040-202da298.json`
(model `google/gemini-3.7-flash`, temperature 0.3, 2026-09-05T18:40:40).
Its English report is a **foreign RENDER**, read-only; only the items below
re-enter state, and each is marked with what it is.

| # | Finding | Status here |
|---|---|---|
| Q1 | Proof of T1 correct as stated; all three steps re-derived independently | **agrees** with the kernel receipt |
| Q2 | \(A_N\) is well-separated, \(1/2\) optimal, no \(cY+O(1)\) with \(c<1/2\) can hold | **agrees** with the exhaustive receipt |
| Q3 | "T1 is a known elementary observation … the exact continuous analogue of the classical dyadic pigeonhole proof for discrete primitive sets (Behrend 1935, Erdős 1935)"; and Erdős "noted that local density ≤ 1/2 follows trivially from the dyadic scaling" | **CONTRADICTS any novelty claim. UNVERIFIED LEAD** — no such Erdős remark was located from this session; treat as prior-art suspicion, not as a located citation |
| Q4 | T1 implies neither Erdős question; gives \(\le\frac12\log n+O(1)\) and only \(\frac12\log\log n+O(1)\) for the \(1/(x\log x)\) sum, divergent | **agrees**, and supplies the explicit divergent bound |
| Q5 | Sharpened generalization: a base-\(b\) chain sends \((1,X)\) into \([X,bX)\), giving upper density \(\frac{b-1}{b}\), minimized at \(b=2\) | **adopted** — a cleaner statement of §1's saturation argument. Its \(b=3\) value \(2/3\) matches the value derived here independently |

The audit's own closing steer: *"one must exploit multiscale interference
between coprime multipliers (e.g. \(2^a3^b\)) rather than a single 1D chain."*
That is the same gap named in §5 below, reached from the other side.

**NOVELTY_STATUS: PRIOR_ART_COLLISION_SUSPECTED, UNVERIFIED.** No prior-art
search was executed in this campaign. Nothing here is claimed as new; the value
banked is the kernel receipt and the named obstruction, not priority.

**The exact obstruction.** Every element \(a\in A\) forbids the union
\(\bigcup_{k\ge1}(ka-1,ka+1)\), of density \(2/a\); if these were independent,
\(\sum_{a\in A}1/a=\infty\) would already force density \(0\), which is the whole
problem. They are not independent, and the *only* tool proved here for making
several \(a\)'s block simultaneously — the divisibility-chain factorization of
step (1b) — handles a chain and nothing wider. A second, incomparable multiplier
pair \((k,k')\) with \(k\nmid k'\) and \(k'\nmid k\) has **no** controlled lower
bound on \(\lvert ka-k'b\rvert\) in this hypothesis, and the integer case shows
such collisions genuinely occur (\(a=3t,\,b=2t\) gives \(2a=3b\) with both
\(a,b\) admissible). **A method that bounds \(\lvert ka-k'b\rvert\) from below
for incomparable \(k,k'\), or a second-moment estimate controlling the overlaps
of the forbidden unions, is what is missing.**
