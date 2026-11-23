# Products of two primes in residue classes: an AI-orchestrated study of the Erdős–Odlyzko–Sárközy conjecture under GRH

*Research report, November 2026. Not refereed.*

> **Read this first.**
> - **Provenance.** This is AI-orchestrated work. Most of the mathematics below was produced by AI agents. Other AI agents
>   checked it, and part of it was checked by the Lean 4 proof assistant. **No human has refereed any of it.** Treat every
>   statement that is not formalized in Lean as a research note. A Lean proof certifies only the deduction from the
>   named hypotheses. Whether those hypotheses are true rests on paper arguments and citations that were checked by
>   agents.
> - **GRH.** A proof of the Generalized Riemann Hypothesis was recently announced [Remark]. We have not checked it, and
>   nothing here depends on it. Every GRH result below is stated as **conditional** on GRH.
> - **Status tags.** Claims carry the tags used in the project notes: *proved* (complete argument written out),
>   *sketched* (some steps only indicated), *heuristic* (not a proof), *computed* (output of a script), and
>   *[UNVERIFIED]*. "Lean" means machine-checked from the named hypotheses.
> - **Scope.** The conjecture is **not** proved here, not even under GRH.

---

## 1. Abstract

The Erdős–Odlyzko–Sárközy (EOS) conjecture asserts that for every sufficiently large $m$ and every $a$ coprime to $m$
there are primes $p, q \le m$ with $pq \equiv a \pmod m$. The conjecture is open, even under GRH. We report on a short
(two-day) AI-orchestrated study of it. The study had four parts: a literature review, several research routes with
adversarial referees, numerics, and a Lean 4 / Mathlib formalization.

The main findings are these.

1. **GRH-conditional approximations, all formalized in Lean.** GRH enters only through a named, standard consequence
   of GRH. For all large $m$ and every unit $a$:
   - $a \equiv pq$ with $p, q \le K m \log^2 m$;
   - $a \equiv pq$ with $p \le m$ and $q \le K m \log^3 m$;
   - $a \equiv pqs$ with $p, q \le m$ and a third prime $s \ll (\log m)^2 (\log\log m)^2$.

   The first two are new statements with routine proofs. The third improves the $(\log m)^4$ of Banks–Shparlinski
   [BS26, Thm 1.3] by a standard moment refinement. It is an easy refinement, not a new technique.
2. **A precise description of the obstruction (the "Parseval wall").** At range exactly $m$, Parseval's identity is
   exact. Any argument that uses only the sizes $\lvert S(\chi)\rvert$ of the character sums over primes loses exactly
   one logarithm. The conjecture is decided by the phases of $\bar\chi(a) S(\chi)^2$.
3. **Barriers.** These include an unconditional *conjugation barrier* (Theorem G), with a one-line proof. The primes
   and their inverses have identical character-sum data, yet $-1 \notin P \cdot P^{-1}$ for every odd $m$ with $m-2$
   composite. A numerical "phase lab" finds no localized phase pattern that separates the primes from barrier objects.
4. **A Lean-checked conditional reduction.** EOS follows from cited unconditional sieve inputs together with an
   explicit fourth-moment hypothesis H4 over residue classes. **H4 is stronger than EOS and is not known to follow from
   GRH.** The reduction isolates the gap; it does not close it.
5. **Numerics.** EOS holds for every $m$ with $401 < m \le 10^6$. Exactly 48 moduli $m \le 10^6$ fail, the largest
   being $m = 401$.

---

## 2. Introduction

### 2.1 The conjecture

Let $m \ge 3$ and $G = (\mathbb Z/m\mathbb Z)^\times$.

**Conjecture (Erdős–Odlyzko–Sárközy [EOS87]).** For all sufficiently large $m$ and every $a$ with $\gcd(a, m) = 1$
there are primes $p, q \le m$ with $pq \equiv a \pmod m$.

For a unit $a$, a representation $pq \equiv a$ forces $p, q \nmid m$, so $p, q < m$. Two reformulations are useful.

- **Primes in a Kloosterman-type sequence.** Write $\bar p$ for the inverse of $p$ mod $m$. Since $q < m$ is determined
  by $q \equiv a\bar p$, EOS for $a$ is equivalent to the statement that the set
  $A_a = \lbrace a\bar p \bmod m : p \le m \text{ prime},\ p \nmid m\rbrace \subset [1, m)$ contains a prime.
- **A binary problem.** $pq \equiv a$ is a multiplicative analogue of $p + q = N$. Section 4 makes this precise.

### 2.2 History

The following summary is taken from the project's literature notes (`notes/lit/01-eos-direct.md`). Statements tagged
there as read in the source are given as such. The conjecture is described as open, explicitly including under GRH,
in [FKS08], [Wal16], [Shp17], [Sza24], [MT24], [Ban26] and [BS26].

- **Erdős–Odlyzko–Sárközy (1987)** [EOS87], for $m$ prime. Under GRH:
  - every $a$ is $p_1p_2$ with $p_i \le C m (\log m)^4$ (Cor. 3);
  - all but $O((\log m)^5)$ classes are $p_1p_2$ with $p_i \le m$;
  - every $a$ is $p_1p_2p_3$ with $p_i \le m$. This needs only a zero-free strip of width $\asymp \log\log m/\log m$.
- **Friedlander–Kurlberg–Shparlinski** [FKS08] treat averages over moduli, and **Garaev** [Gar12] treats ternary and
  shifted variants.
- **Walker** [Wal16] ($m$ prime):
  - a positive proportion ($\ge 1/64 + o(1)$) of classes are $p_1p_2$ with $p_i \le m$;
  - every class is a product of at most 6 primes below $m^{15/16+\varepsilon}$.
- **Ramaré–Walker** [RW18]: every class mod $q$ contains a product of three primes, each below $q^{16/3}$. They call
  this "a footnote in parity breaking".
- **Shparlinski** [Shp13, Shp17] obtains products of primes and almost-primes. He uses bounds for Kloosterman-type
  sums over primes, which go back to Fouvry–Shparlinski [FS11]. **Zhao** [Zha22] shows that every
  $a \equiv p_1p_2n$ with $p_1, p_2, n \le m$ and $\Omega(n) \le 2$.
- **Szabó** [Sza24]:
  - $\lvert E_2(m)\rvert \ge (3/8 + o(1))\varphi(m)$ for cube-free $m$;
  - every class is a product of 6 primes for large prime $m$;
  - every class is a product of three primes $\le m^{6/5+\varepsilon}$.
- **Matomäki–Teräväinen** [MT24] give the current unconditional state of the art:
  - every class is a product of three primes $\le m$ for large cube-free $m$;
  - every class is a product of three primes $\le m^{1+\varepsilon}$ for all large $m$;
  - $\lvert E_2(m)\rvert \ge (2/3 - \varepsilon)\varphi(m)$.

  Here $E_2(m)$ is the set of classes that are $p_1p_2$ with $p_i \le m$.
- **Banks–Shparlinski** [BS26] (arXiv, October 2026), for arbitrary moduli under GRH:
  - all but $O((\log m)^3)$ classes are $p_1p_2$ with $p_i \le m$ (Thm 1.4);
  - every $a$ is $\ell_1\ell_2\ell_3$ with $\ell_1, \ell_2 \le m$ and $\ell_3 \ll (\log m)^4$ (Thm 1.3).

  They also prove unconditional results for prime-power moduli. **Banks** [Ban26] proves the analogue of EOS in
  Granville's random model, and states the barrier precisely: the loss "comes from the sum over the characters, not
  from any single character".

### 2.3 The function-field analogue

Over $\mathbb F_q[t]$ the analogue of EOS is a theorem in two regimes (`notes/routes/B-function-field.md`).

- **Xie** [Xie26]: for fixed degree $n$ and $q \ge Q(n)$ (one may take $Q(n) = n^{23n}$), every unit modulo a squarefree
  $f$ of degree $n$ is a product of two monic irreducibles of degree $\le n$.
- **Sawin** [Saw24]: square-root cancellation for factorization functions in squarefree progressions. As Xie observes,
  this gives the analogue for fixed $q > 1024e^2$ and $n \to \infty$.

In both proofs the cancellation across characters does **not** come from the Riemann hypothesis for the individual
$L(s,\chi)$. It comes from a second, Deligne-type spectral expansion: the twisted family sum is itself a Frobenius
trace on a geometric object of small complexity. No integer analogue of this object is known. The small fixed-$q$
regime ($q = 2, 3$, $n \to \infty$) appears to be open *[UNVERIFIED]*, and it is the faithful analogue of the integer
problem.

### 2.4 What this report contains

- **Section 3:** a table of results.
- **Section 4:** the obstruction.
- **Section 5:** the GRH results, with proofs.
- **Section 6:** barriers.
- **Section 7:** the H4 reduction and other conditional reductions.
- **Section 8:** numerics.
- **Section 9:** the Lean development.
- **Section 10:** how the work was done.
- **Section 11:** limitations and open problems.

File paths refer to the repository.

---

## 3. Summary of results

### 3.1 Lean theorems

Everything below is in `EOS/EOS/*.lean`. Every theorem is proved with **no `sorry`**. The only `sorry` in the
development is the deliberate statement of the open problem, `eos_of_grhBounds`. The constants $K, m_0$ are existential
in all statements. "Unit $a$" means $a \in (\mathbb Z/m\mathbb Z)^\times$, and conclusions hold for every $m \ge m_0$
unless stated otherwise.

| Lean theorem (file) | Hypotheses | Conclusion | Source / status |
|---|---|---|---|
| `coveredBy_of_grhBounds` (LogFour) | `GRHBounds` (GRH consequence) | $a \equiv pq$, $p, q \le K m \log^4 m$ | [EOS87, Cor. 3] (prime $m$), extended to all $m$. Known. |
| `coveredBy_log_sq` (LogSquare) | `GRHSmoothBound` (GRH consequence) | $a \equiv pq$, $p, q \le K m \log^2 m$ | Theorem S. New statement, routine proof. |
| `coveredByAsym_m_log_cube` (LogSquare) | `GRHSmoothBound` | $a \equiv pq$, $p \le m$, $q \le K m \log^3 m$ | Corollary A1. New statement, routine proof. |
| `coveredBy_three_primes` (ThreePrimes) | `GRHSmoothBound` | $a \equiv pqs$, $p, q \le m$, $s$ prime, $s \le K (\log m)^2(\log\log m)^2$ | Theorem W. Improves [BS26, Thm 1.3]. |
| `Buchstab.buchstab_identity`, `lemmaC`, `lemmaC'`, `lemmaC'_of_H4Block` (Buchstab) | none | exact Buchstab identity [Buc37] for $A_a$; finite certificate for $N(a) > 0$ (every $m \ge 2$) | Elementary. |
| `eos_of_H4` (GapH4) | `TypeISifted`, `RoughCounts` (cited unconditional theorems); **`H4 η λ` (open, beyond GRH)** | the full conjecture | Conditional reduction. H4 is stronger than EOS. |
| `estermann_long_log` (Estermann) | none | $a \equiv ps$, $p \le m$ prime, $s \le 56\, m\log m$ squarefree ($m \ge 400^4$) | Elementary remark. |
| `estermann_of_typeISifted` (Estermann) | `TypeISifted` | $a \equiv ps$, $p \le m$ prime, $s < m$ squarefree | Known: [Yau19, Thm 3.1]. |
| `SumTwoSquares.sumTwoSq_of_typeIHalf` | **`TypeIHalf` (open: Type I at level exactly 1/2)** | $m$ prime: $a \equiv p(x^2 + y^2)$, $p \le m$, $x^2 + y^2 < m$ | Conditional reduction. |
| `GRH.riemannHypothesis`, `GRH_iff_forall` (GRH) | none | literal GRH ⇒ Mathlib's `RiemannHypothesis`; GRH for primitive characters ⇔ GRH for all characters | Infrastructure for the literal-GRH chain. |
| `psiCesaro_eq_verticalIntegral` (GRHAnalytic/Dirichlet) | none | $\tilde\psi(x,\chi)$ as a vertical contour integral of $-L'/L\cdot x^s/(s(s+1))$, $\sigma>1$ | Infrastructure (milestone M2, §9.4). |
| `eos_of_grhBounds` (Statement) | `GRHBounds` | the conjecture | **Open.** The only `sorry`. |

The Lean statements use $\varphi(m) \le m$. The paper versions are slightly sharper: they have $K\varphi(m)\log^2 m$,
$K\varphi(m)^2\log^3 m/m$ and $K(\varphi(m)/m)^2(\log m)^2(\log\log m)^2$.

### 3.2 Results proved on paper only

| Result | Statement | Status | Where |
|---|---|---|---|
| Theorem B | GRH + an unconditional uniform twin-prime upper-bound sieve: $p \le \varphi(m)\log m$, $q \le K\varphi(m)\log^2 m$ | proved (sieve input cited) | `notes/routes/C-log-exponent.md` §4 |
| Theorem E (exceptional set) | GRH: all but $K(\varphi/m)^2\log^3 m$ classes are $pq$ with $p, q \le m$ | proved; this is [BS26, Thm 1.4] | C §3 |
| Proposition L | Nonnegativity, total mass and the GRH sup bound cannot give a symmetric range below $c\varphi(m)\log^2 m$ | proved (uses Spencer's theorem) | C §5 |
| Theorem G | Conjugation barrier (§6.1) | proved, unconditional | `notes/routes/D-new-connections.md` §1 |
| Barrier A\* | A set with the Type I data and GRH-size character sums of the primes, but no primes | proved under GRH, using one sketched input | `notes/routes/A-typeII.md` §4.2 |
| Theorem E (Buchstab) | TypeISifted + H4 ⇒ $N(a) \ge 0.4\mu$ for every $a$ | proved from the named inputs; Lean proves the weaker conclusion $N(a) > 0$ | `notes/routes/E-buchstab-H4.md` |
| Prop Q′ | The analogue of H4 for $P^{-1}$ fails for every large $m$ | proved | E §5 |
| W, zero-free strip | Under a zero-free half-plane $\sigma > \sigma_0$: $\ell_3 \ll (\log m)^{3/(2-2\sigma_0)+o(1)}$ | sketched | `notes/routes/W-referee.md` §3 |

---

## 4. The Parseval wall

The source for this section is `notes/01-parseval-wall.md`. Every identity in it is *proved* and elementary.

### 4.1 Setup

Let $P = \lbrace p \le m \text{ prime} : p \nmid m\rbrace$. Every $p \in P$ satisfies $1 \le p \le m - 1$, so the
elements of $P$ are **distinct residues** in $G$. Put $\varphi = \varphi(m)$, $\rho = \lvert P\rvert/\varphi \approx 1/\log m$,
and for a Dirichlet character $\chi$ mod $m$ put $S(\chi) = \sum_{p \in P}\chi(p)$. Let

$$
N(a) = \lvert\lbrace (p, q) \in P^2 : pq \equiv a\rbrace\rvert = \frac{1}{\varphi}\sum_{\chi}\bar\chi(a)\,S(\chi)^2 = \mu + E(a),
\qquad \mu = \frac{\lvert P\rvert^2}{\varphi},\quad E(a) = \frac1\varphi\sum_{\chi \ne \chi_0}\bar\chi(a)\,S(\chi)^2 .
$$

EOS is the statement $N(a) > 0$ for every $a \in G$. The main term is $\mu \asymp (m/\varphi)\, m/\log^2 m$.

### 4.2 The identity and the wall

Because $P$ consists of distinct residues, Parseval is an **exact** identity:

$$
\frac1\varphi\sum_\chi \lvert S(\chi)\rvert^2 = \lvert P\rvert,
\qquad\text{hence}\qquad
\frac1\varphi\sum_{\chi\ne\chi_0}\lvert S(\chi)\rvert^2 = \lvert P\rvert(1-\rho).
$$

The best bound that uses only the sizes $\lvert S(\chi)\rvert$ is therefore
$\lvert E(a)\rvert \le \lvert P\rvert(1-\rho)$. This exceeds $\mu$ by the factor $(1-\rho)/\rho \asymp \log m$.
**Size information loses exactly one logarithm.**

The loss is not an artefact of the triangle inequality. On the physical side, put $f = 1_P - \rho$ on $G$ and
$\iota_a(x) = a\bar x$. A direct expansion gives the exact identity

$$
E(a) = \sum_{x \in G} f(x)\, f(\iota_a x),
\qquad \lvert E(a)\rvert \le \lVert f\rVert_2^2 = \lvert P\rvert(1-\rho).
$$

Near-equality $E(a) \approx -\lVert f\rVert^2$ happens when $P$ contains at most one element of each pair
$\lbrace x, a\bar x\rbrace$. So EOS says exactly that $P$ is **not anti-correlated with its reflection under the
involution $\iota_a$**. This makes EOS a binary problem: the multiplicative analogue of binary Goldbach, where the
involution is $x \mapsto N - x$. On the Fourier side, Theorem G (§6.1) exhibits a pair with identical magnitudes
$\lvert S(\chi)\rvert$ for which the corresponding count vanishes.

### 4.3 Why GRH does not help

Under GRH, $\lvert S(\chi)\rvert \ll \sqrt m\,\log m$ for $\chi \ne \chi_0$. So $\lvert S(\chi)\rvert^2$ is at most
about $\log^3 m$ times its average $\lvert P\rvert$, and no single character dominates. But GRH says nothing about the
**phases** of $\bar\chi(a)S(\chi)^2$ across the family of $\varphi$ characters. If the phases were independent and
uniform, $\lvert E(a)\rvert$ would be about $\lvert P\rvert/\sqrt\varphi \approx \sqrt m/\log m$, far below
$\mu \approx m/\log^2 m$. The numerics (§8) agree with this. A proof needs only one logarithm of phase cancellation,
but it needs it **pointwise in $a$**, and no known tool supplies that.

The same point appears in moment form (`notes/lit/02-tools.md` §2.2, *proved*). By Cauchy–Schwarz and the exact
identity,

$$
\sum_a (N(a) - \mu)^2 \ge (1 - o(1))\lvert P\rvert^2,
$$

while concluding $N(a) > 0$ for all $a$ from this needs $\sum_a (N(a)-\mu)^2 < \mu^2$, i.e. $\lvert P\rvert > \varphi$.
So no energy (fourth-moment) bound, however sharp, suffices on its own.

### 4.4 Ternary versus binary

For $p_1p_2p_3 \equiv a$, the error is at most $\max_{\chi\ne\chi_0}\lvert S(\chi)\rvert \cdot \lvert P\rvert$ against a
main term $\lvert P\rvert^3/\varphi$. The sup bound only has to beat the trivial bound by a logarithm, and GRH (or
much less) does this. This is why three primes $\le m$ is known [EOS87, MT24] while two primes is not, just as
Vinogradov's three-primes theorem is known while binary Goldbach is not.

### 4.5 The three log layers above range $m$

At range $X > m$ (primes $p, q \le X$), Parseval is no longer exact, and the gap has three layers.

1. **The GRH sup bound loses two logarithms.** It gives $X \asymp \varphi\log^2 m$ (Theorem S, §5.2). Proposition L
   (route C §5, *proved*) shows that this exponent 2 is sharp for the inputs "nonnegativity, total mass, and the sup
   bound $\lvert\hat\Theta(\chi)\rvert \le C\sqrt X\log m$". Its proof uses a Spencer-signed antisymmetric set.
2. **A variance asymptotic would recover one logarithm**, giving $X \asymp \varphi\log m$. This would be a
   Hooley / Friedlander–Goldston-type asymptotic $V(X) \sim cX\log m$ for a single modulus, which is not known under
   GRH alone. Numerically, at $m = 982801$ the exact Parseval mass falls below the main term at $X \approx 11$–$16\,m$
   (*computed*, `compute/lab/FINDINGS.md` §5).
3. **The last logarithm needs phase information.** At $X = m$, Parseval is exact and only this layer remains.

---

## 5. GRH-conditional results

The sources are `notes/routes/C-log-exponent.md` (refereed in `C-referee.md`) and `notes/brainstorm/r1-wildcard.md`
§1 (refereed in `notes/routes/W-referee.md`). All results are formalized in Lean (`LogSquare.lean`,
`ThreePrimes.lean`).

### 5.1 The analytic input

Let

$$
\tilde\psi(x,\chi) = \sum_{n \le x}\Lambda(n)\chi(n)\Bigl(1 - \frac nx\Bigr).
$$

**Hypothesis H (`GRHSmoothBound`).** There is an absolute $C$ such that for every $q \ge 1$, every Dirichlet character
$\chi$ mod $q$ and every real $x \ge 1$,

$$
\bigl\lvert \tilde\psi(x,\chi) - [\chi = \chi_0]\,x/2 \bigr\rvert \le C\sqrt x\,\log(2q).
$$

H follows from GRH. Route C §1 gives a self-contained proof. It moves the contour only to $\operatorname{Re}s = 1/4$
with the kernel $x^s/(s(s+1))$, and treats imprimitive characters by comparing sums. An agent referee re-derived the
proof and corrected three cosmetic slips. For nonprincipal $\chi$ the bound is [BS26, Lemma 2.5], which is derived from
Montgomery–Vaughan (13.28). A numerical test over 20 moduli and $1 \le x \le 10^6$ found no violation, and showed that
any valid $C$ is at least $1.057$ (*computed*).

The Cesàro weight is the point: it saves one logarithm over the sharp-cutoff bound
$\lvert\psi(x,\chi) - [\chi=\chi_0]x\rvert \ll \sqrt x\log^2(qx)$ (`GRHBounds`).

### 5.2 The deduction (proved from H)

Put $L = \log m$ and

$$
\Theta(X;b) = \sum_{\substack{p \le X\\ p \equiv b}} \log p\,\Bigl(1 - \frac pX\Bigr), \qquad
\tilde\vartheta(X,\chi) = \sum_{b\in G}\Theta(X;b)\chi(b), \qquad T(X) = \tilde\vartheta(X,\chi_0),
$$

$$
M(X) = \max_{\chi\ne\chi_0}\lvert\tilde\vartheta(X,\chi)\rvert,\qquad
V^\circ(X) = \frac1\varphi\sum_{\chi\ne\chi_0}\lvert\tilde\vartheta(X,\chi)\rvert^2 = \sum_b\Bigl(\Theta(X;b) - \frac{T(X)}\varphi\Bigr)^2 .
$$

By orthogonality, the weighted count of representations $a \equiv pq$ with $p < X_1$ and $q < X_2$ is

$$
R(a) = \sum_{b}\Theta(X_1;b)\,\Theta(X_2;a\bar b) = \frac{T(X_1)T(X_2)}{\varphi} + E(a),\qquad
E(a) = \frac1\varphi\sum_{\chi\ne\chi_0}\bar\chi(a)\,\tilde\vartheta(X_1,\chi)\,\tilde\vartheta(X_2,\chi).
$$

**Lemma 5.1** (route C, Lemmas D2–D5).
1. *(from H at $q = 1$)* $T(X) \ge X/8$ for $X \ge \max(X_0, 8L)$.
2. *(from H at $q = m$, prime powers removed)* $M(X) \le C_3\sqrt X\,L$ for $1 \le X \le m^3$.
3. *(unconditional, exact Parseval)* $V^\circ(X) \le (\log 4)\,X\log X$ for $X \le m$.
4. *(unconditional, Cauchy–Schwarz)* $\lvert E(a)\rvert \le M(X_1)\,V^\circ(X_2)^{1/2}$.

Part 3 is the only place where the range $m$ is special. Primes $p \le X \le m$ lie in distinct classes, so each
$\Theta(X;b)$ has at most one term.

**Theorem S** (GRH). For $m \ge m_0$, every unit $a$ is $pq$ with $p, q \le K\varphi(m)\log^2 m$.

*Proof.* Take $X_1 = X_2 = X$. By Lemma 5.1, $\lvert E(a)\rvert \le M(X)\,V^\circ(X)^{1/2} \le M(X)^2 \le C_3^2 X L^2$,
while the main term is at least $X^2/(64\varphi)$. So $R(a) > 0$ once $X > 64C_3^2\varphi L^2$. ∎

**Corollary A1** (GRH). For $m \ge m_0$, every unit $a$ is $pq$ with $p \le m$ and
$q \le K\varphi(m)^2\log^3 m/m \le K m\log^3 m$.

*Proof.* Take $X_2 = m$ and $X_1 = X$. Then

$$
\lvert E(a)\rvert \le C_3\sqrt X\,L\cdot(1.39\, m\log m)^{1/2},
\qquad \frac{T(X)T(m)}{\varphi} \ge \frac{Xm}{64\varphi},
$$

so $R(a) > 0$ once $X \ge K\varphi^2 L^3/m$. ∎

*Remarks.*
- Theorem S was already sketched in the project's literature notes as a two-line modification of [EOS87, Cor. 3]
  using the weights of [BS26].
- The agent referee's assessment of A1 is that it is "a new *statement* and a routine *proof*": the smoothed GRH
  variance bound plus pigeonhole over the $\gg m/\log m$ classes $a\bar p$. It is not a new technique.
- Neither of A1 and [BS26, Thm 1.3] implies the other.
- Theorem E at $X_1 = X_2 = m$ (an exceptional set of size $\le K(\varphi/m)^2\log^3 m$) coincides with
  [BS26, Thm 1.4], including the factor $(\varphi/m)^2$, which is already in their proof.
- Theorem B in §3.2 uses an additional sieve input and is not formalized.

### 5.3 Theorem W: a small third prime

For a finite $\mathcal S \subset G$ and $k \ge 1$, define the $k$-fold multiplicative energy

$$
E_k(\mathcal S) = \frac1\varphi\sum_\chi \lvert\hat 1_{\mathcal S}(\chi)\rvert^{2k},\qquad
\hat 1_{\mathcal S}(\chi) = \sum_{c\in\mathcal S}\chi(c).
$$

Take $X_1 = X_2 = m$ in §5.2.

**Lemma M** (*proved*, unconditional; Hölder with exponents $2k/(2k-1)$ and $2k$).

$$
\Bigl\lvert\sum_{c\in\mathcal S}E(c)\Bigr\rvert \le M^{1/k}\,(V^\circ)^{1-1/2k}\,E_k(\mathcal S)^{1/2k}.
$$

**Lemma S** (*proved*, unconditional). Let $\mathcal W$ be a set of primes not dividing $m$, all below $m^{1/k}$, and
put $\mathcal S = \lbrace a\bar s : s \in \mathcal W\rbrace$. Then

$$
E_k(\mathcal S) = E_k(\mathcal W) \le k!\,\lvert\mathcal W\rvert^k .
$$

*Proof.* A congruence $s_1\cdots s_k \equiv s'_1\cdots s'_k \pmod m$ between products below $m$ is an equality of
integers. By unique factorization, $s'$ is then a permutation of $s$. ∎

**Theorem W** (GRH). For all large $m$, every unit $a$ is $pqs$ with primes $p, q < m$ and
$s \le K(\varphi/m)^2(\log m)^2(\log\log m)^2$.

*Proof.* Let $k = \lceil\log L\rceil$, let $\mathcal W$ be the primes $s \le y$ with $s \nmid m$, and suppose
$R(a\bar s) = 0$ for every $s \in \mathcal W$. Then $\sum_{c\in\mathcal S}E(c) = -\lvert\mathcal W\rvert T^2/\varphi$.
Lemma 5.1, Lemma M and Lemma S give

$$
\lvert\mathcal W\rvert\frac{m^2}{64\varphi} \le (\log 4)\,mL\cdot\Bigl(\frac{C_3^2 L}{\log 4}\Bigr)^{1/2k}(k!)^{1/2k}\,\lvert\mathcal W\rvert^{1/2}.
$$

Since $L^{1/(2\log L)} = e^{1/2}$ and $(k!)^{1/2k} \le \sqrt k$, this forces
$\lvert\mathcal W\rvert \le K_0(\varphi/m)^2L^2\lceil\log L\rceil$. Choosing
$y = K'(\varphi/m)^2L^2(\log L)^2$ makes $\pi(y) - \omega(m)$ larger than this, and $y^k < m$ holds. This is a
contradiction. ∎

**Comparison with [BS26].** In their Theorem 1.3 the third prime enters through a **sup bound**: the non-principal part
is bounded by

$$
\frac1\varphi\sum_\chi\lvert\vartheta(m,\chi)\rvert^2\cdot\max_{\chi\ne\chi_0}\lvert\tilde\vartheta(y,\chi)\rvert
\ll m\log m\cdot y^{1/2}\log m .
$$

Positivity then needs $y^{1/2} \gg \log^2 m$, which gives $(\log m)^4$. We instead use **Hölder against a high moment of
the short prime character sum**. That moment is diagonal by unique factorization as long as $y^k < m$. The GRH sup bound
for the long sums is then needed only to the power $1/k$, which costs a constant when $k \asymp \log\log m$.

A weaker improvement was already available from their own work. Their Theorem 1.4 (exceptional set $O(\log^3 m)$) plus
pigeonhole over the distinct classes $a\bar s$ gives $s \ll (\log m)^3\log\log m$ (route D, Remark 5.1). They do not
state this. Both devices are standard: diagonal moments of short prime character sums, and the multiplicative-energy
form of Hölder. Theorem W is an easy refinement, not a new idea.

Novelty status: the result was "not found in a targeted search" (`W-referee.md` §1). That search had no MathSciNet or
zbMATH access, and [BS26] is a v1 preprint.

*Further remarks* (status as tagged in the notes).
- Under a zero-free half-plane $\sigma > \sigma_0$, the same argument gives $\ell_3 \ll (\log m)^{3/(2-2\sigma_0)+o(1)}$,
  against $(\log m)^{2/(1-\sigma_0)}$ in [BS26] (*sketched*).
- The $\mathbb F_q[t]$ analogue of Theorem W holds unconditionally for every $q$ (*sketched*, Weil in place of GRH).
- Theorem W is conjugation-blind (§6.1), so this method cannot be refined to a single class.
- **A heuristic "conservation law."** Size methods prove "$a$ is a product of primes from boxes" only when the
  integer product of the box sizes is at least $m^2(\log m)^c$:
  - Theorem S gives $pq \le K\varphi^2 L^4$;
  - Corollary A1 and Theorem B give $\varphi^2L^3$;
  - Theorem W gives $pqs \le m^2L^{2+o(1)}$.

  EOS asks for $m^2$ exactly, with zero slack.

---

## 6. Barriers

A *barrier* here is an object that satisfies every input a proof strategy uses, yet for which the conclusion
"$a \in P\cdot P$" fails. The project used six such objects as a checklist. Every proposal in the brainstorm was tested
against them (`notes/brainstorm/r2-skeptic-barriers.md`).

### 6.1 The conjugation barrier (Theorem G)

Source: `notes/routes/D-new-connections.md` §1. Let $N^-(a) = \lvert\lbrace (p,q)\in P^2 : p \equiv aq\rbrace\rvert$.
With $Q = P^{-1}$, the Fourier transform of $1_Q$ is $\overline{S(\chi)}$, so

$$
N^-(a) = \frac1\varphi\sum_\chi\bar\chi(a)\,\lvert S(\chi)\rvert^2,
\qquad\text{against}\qquad
N(a) = \frac1\varphi\sum_\chi\bar\chi(a)\,S(\chi)^2 .
$$

**Theorem G** (*proved*, unconditional). Let $m \ge 3$ be odd.
1. $N^-(-1) = 2\cdot[m-2 \text{ is prime}]$. In particular $-1 \notin P\cdot P^{-1}$ whenever $m - 2$ is composite.
2. The pairs $(1_P, 1_{P^{-1}})$ and $(1_P, 1_P)$ share every size statistic:
   - the same $\lvert\hat\cdot(\chi)\rvert$ at every truncation $p \le x$ and for every weight;
   - hence every consequence of GRH, and hypothesis H;
   - the same exact Parseval identity, all moments $\sum_\chi\lvert\cdot\rvert^{2k}$, and the multiplicative energy;
   - equidistribution of each set separately in residue classes to small moduli.
3. Consequently every proof of EOS must use an input that fails for $(P, P^{-1})$.

*Proof of 1.* If $p \equiv -q$ with $1 \le p, q \le m-1$, then $m \mid p + q$ and $2 \le p+q \le 2m-2$, so
$p + q = m$. Since $m$ is odd, one of $p, q$ is 2 and the other is $m - 2$. ∎

*Remarks.*
- For even $m$, $N^-(-1)$ is the Goldbach count of $m$. An argument that proves $a \in P\cdot P$ from inputs invariant
  under conjugating one factor would therefore prove a false statement for odd $m$, and binary Goldbach for even $m$.
- The barrier kills every method that works "in the category of abelian groups with a subset". This includes Kneser- and
  Plünnecke-type product-set theorems, Gowers norms on $G$, expander mixing for the Cayley graph of $P$, mixed-norm
  bounds on $S$, and zero statistics of the individual $L(s,\chi)$.
- It does not kill arguments that use the joint structure of $P$ and $A_a$. In particular, **a proof must use the
  distribution of $a\bar p \bmod m$ (as an integer in $[1,m]$) to small moduli, already modulo 2**, i.e. Kloosterman
  sums over primes or an equivalent (Corollary G2, *proved* as a statement about inputs). For $a = -1$ the conjugate
  sequence $\lbrace m - p\rbrace$ is all even.
- The size bias is real for the primes (Corollary G1, *proved*, *computed*):
  $\sum_{\chi\ \mathrm{odd}}\lvert S(\chi)\rvert^2 = (\varphi/2)(\lvert P\rvert - N^-(-1))$ exactly. So the primes
  exhibit a correlation between $\lvert S(\chi)\rvert^2$ and $\chi(-1)$ of exactly the critical relative strength
  $\asymp 1/\log m$. In the product problem the class $-1$ survives only because the arguments of $S(\chi)^2$ are
  spread out:
  $\sum_{\chi\ne\chi_0}\chi(-1)\lvert S\rvert^2 = -\lvert P\rvert^2$, while
  $\sum_{\chi\ne\chi_0}\chi(-1)\operatorname{Re}S^2/\lvert P\rvert^2 \in [-0.009, 0.035]$ for four primes
  $m \in [10^4, 3\cdot 10^6]$.

### 6.2 Random pairing-avoiding sets

Source: `notes/lit/02-tools.md` §4.3(b). The argument is a standard probabilistic construction, written out there
without full details (*sketched*).

Partition $G \setminus\lbrace x : x^2 = a\rbrace$ into orbits $\lbrace x, a\bar x\rbrace$, keep each orbit with
probability $2\delta$, and then keep one of its two elements at random. The resulting set $A$ satisfies
$A\cap aA^{-1} = \varnothing$, so $a \notin A\cdot A$. Yet by Bernstein's inequality and a union bound,
$\max_{\chi\ne\chi_0}\lvert\hat 1_A(\chi)\rvert \ll \sqrt{\delta\varphi\log\varphi}$. For $\delta = 1/\log m$ this is
stronger than the GRH bound for $S(\chi)$. Weighting the choice within orbits lets $A$ match prescribed Type I
statistics, and its Kloosterman sums are $\ll\sqrt{m\log m}$.

Conclusion: bounds on $\lvert S(\chi)\rvert$, Kloosterman bounds and Type I axioms together do not imply
$a \in P\cdot P$. Proposition L (§4.5) is a deterministic version, via Spencer's theorem [Spe85], at the scale
$X \ge \varphi\log m$.

### 6.3 Deletion and redaction

Source: `notes/lit/02-tools.md` §4.3(a) and `notes/lit/03-grh-techniques.md` §4.

- **Deletion (elementary).** The pairs $\lbrace p, a\bar p\rbrace$ with both entries in $P$ are disjoint. Deleting one
  prime from each, a proportion $\approx 1/\log m$ of $P$ chosen depending on $a$, gives $a \notin A\cdot A$. Any
  method whose conclusion is stable under deleting $o(1)$ of the primes cannot prove EOS. This includes dense-model and
  transference arguments. This is why [MT24] reaches $(2/3 - \varepsilon)\varphi$ classes, not all of them.
- **Redacted primes (*heuristic*).** $P' = P\setminus\lbrace p : a\bar p\in P\rbrace$ plausibly satisfies GRH-quality
  bounds, but this is not proved, since the character sums over the removed set are themselves binary sums.

### 6.4 The A\* barrier (Type I data plus sizes)

Source: `notes/routes/A-typeII.md` §4.2, Theorem B there. Status: *proved* under GRH, except that one smoothed
prime-sum bound is quoted from a *sketched* derivation.

Fix $0 < \theta < 1/2$ and $D = m^\theta$. For every large $m$ and every unit $a$ there is a set
$A^\* \subset [1,m]$ of integers coprime to $m$ with the following properties:
- the size of $A_a$;
- character sums of size $\ll_\theta \sqrt m$ (better than GRH gives for $P$);
- the full Type I data of $A_a$ to every level $d \le D$;
- **no primes in $(D, m]$**.

The construction moves the mass of the primes onto products of two primes $> D$, which Type I moduli $\le D$ cannot
see. This is a parity-type example. Any Vaughan- or Heath-Brown-type identity with Type I level $\le D$ then has
multilinear part $\approx -\rho m$.

Conclusion: no proof can rest on sizes of $S(\chi)$, exact orthogonality and Type I data alone, even with the
genuine Möbius coefficients on the sifted side. Some Type II (bilinear) information about $A_a$ is needed.

### 6.5 Parity

Products of exactly two primes are the standard parity example. This is why sieve results [Shp13, Shp17, Zha22]
produce almost-primes rather than primes. The barrier A\* is the form of parity relevant here.

### 6.6 The phase lab: no localized phase pattern

Source: `compute/lab/FINDINGS.md`. All items are *computed*, for $m$ between $10^5$ and $10^7$, including prime and
composite $m$; the interpretations are *heuristic*.

The phase lab decomposes $E(a) = \sum_{\chi\ne\chi_0}\bar\chi(a)S(\chi)^2/\varphi$ by groupings of characters: order,
conductor, parity, $\lvert S\rvert$-quantile, and cosets $\chi H^\perp$ of subgroups (as in Xie's proof), with coset
sizes from 4 to $5\cdot 10^5$. It compares the primes with the barrier objects above (redacted, pairing-avoiding, A\*,
conjugate), a random set, and the smooth toy $\lvert\lbrace n_1n_2n_3n_4 \equiv a,\ n_i \le \sqrt m\rbrace\rvert$.

1. **The primes behave like independent random phases in every grouping tried.** Within-group cancellation matches the
   random-phase value to $\pm 0.05$ in log scale. For Xie cosets this is $\tfrac12\log h$ over five decades of the
   coset size $h$. Given its total, the vector of partial sums matches the conditioned Gaussian
   ($W/W_{\mathrm{cond}} = 1.00 \pm 0.1$, $\chi^2/\mathrm{dof} \approx 1$), both at typical and at the worst $a$.
2. **Every set barrier looks like the primes conditioned on one large deviation.** The deficit $-\mu$ is a
   $57\sigma$–$85\sigma$ outlier for prime $m \approx 10^6$, and up to $180\sigma$ at $m = 510510$. It is spread over
   groups in proportion to $\sum_{\chi\in g}\lvert S(\chi)\rvert^4$, which is the Gaussian large-deviation allocation.
   It is not concentrated on large characters, low orders or any coset. Adding the missing $\mu$ back at $a$ restores
   the primes' kurtosis, skewness and twisted correlations.
3. **Separating statistics are spike detectors.** Every statistic found that separates $P$ from all barriers detects
   the isolated spike at $a$. Examples are Xie within-coset cancellation at coset size $h \gg \log^2 m$, which is at
   least as strong as EOS, and the kurtosis of $b \mapsto E(b)$, which needs an 8-prime count to relative precision
   $\approx 1/\varphi$. Route A's arc statistic separates A\* only.
4. **The smooth toy cancels differently.** $0.1\%$ of its characters carry 56–83% of its variance, against 2% for the
   primes. This is a major-arc phenomenon the primes do not share.

**The resulting picture (*heuristic*).** A proof must rule out a single spike in $b\mapsto E(b)$, i.e. sub-Gaussian
behaviour of $E$ at deviation $\mu$. No localized phase pattern in $\chi \mapsto \bar\chi(a)S(\chi)^2$ distinguishes the
primes from the barriers. This is a statement about the statistics tried, not a theorem.

### 6.7 What the barriers require of a proof

Combining §6.1–§6.5 (`notes/routes/D-new-connections.md` §1.4), a proof of EOS must use:
- joint Type I information about $(P, a)$, because of Theorem G;
- an input that fails after deleting $o(1)$ of the primes;
- more than Type I data plus sizes, because of A\*;
- something that separates one prime from two, because of parity.

The project found only two kinds of object that could meet all four: a Type II estimate for $A_a$, or a second spectral
expansion of $a\mapsto N(a)$ with few terms, as in the function-field proofs. The brainstorm synthesis
(`notes/brainstorm/r3-synthesis.md` §4) adds a methodological point. A reduction "H ⇒ EOS" that "passes all six
barriers" has usually moved the barriers into H, so checklists should distinguish *passed* from *transferred to the
hypothesis*.

---

## 7. The H4 reduction and the Lean gap theorem

The source is `notes/routes/E-buchstab-H4.md`, which has the complete paper proof. The Lean versions are in
`EOS/EOS/Buchstab.lean` and `EOS/EOS/GapH4.lean`. **GRH is not used in this section.**

### 7.1 The exact part (Buchstab)

Recall that $N(a)$ is the number of primes in $A_a = \lbrace a\bar p \bmod m : p\in P\rbrace \subset [1,m)$. Write
$P^-(n)$ for the least prime factor of $n$ and $S(\mathcal A, z) = \lvert\lbrace n\in\mathcal A : n = 1 \text{ or } P^-(n)\ge z\rbrace\rvert$.

**Lemma C** (Buchstab identity; *proved*; Lean `lemmaC`). For $z \le \sqrt m$,

$$
\lvert\lbrace\text{primes } n\ge\sqrt m \text{ in } A_a\rbrace\rvert = S(A_a, z) - [1\in A_a] - B(a),
\qquad
B(a) = \sum_{z\le p_1<\sqrt m}\lvert\lbrace k : p_1k\in A_a,\ P^-(k)\ge p_1\rbrace\rvert .
$$

Split $[z, \sqrt m)$ into blocks $I_j = [M_j, M_{j+1})$ and let
$\mathcal K_j = \lbrace k \le m/M_j : (k,m) = 1,\ k = 1 \text{ or } P^-(k) \ge M_j\rbrace$. Then
$B(a) \le \sum_j\sum_{k\in\mathcal K_j}\pi_j(a\bar k)$, where $\pi_j(c)$ counts primes $p_1 \in I_j$ with
$c\bar p_1 \in P$. Centre $\pi_j$ at its exact mean: $\delta_j = \pi_j - \rho\iota_j$, with $\iota_j$ the number of
primes in $I_j$ not dividing $m$. Since $k \mapsto a\bar k$ is injective on $\mathcal K_j$, Hölder gives

$$
\sum_{k\in\mathcal K_j}\delta_j(a\bar k) \le \lvert\mathcal K_j\rvert^{3/4}\Bigl(\sum_{c\in G}\delta_j(c)^4\Bigr)^{1/4}.
$$

The right side **does not depend on $a$**. This yields a finite certificate (Lean `lemmaC'`):
$N(a) > 0$ as soon as

$$
S(A_a,z) - 1 - \sum_j\Bigl(\rho\,\iota_j\lvert\mathcal K_j\rvert + \lvert\mathcal K_j\rvert^{3/4}Y_j^{1/4}\Bigr) > 0
\qquad\text{for some } Y_j \ge \sum_{c\in G}\delta_j(c)^4 .
$$

### 7.2 The hypothesis H4, exactly as in Lean

The block system $\mathfrak B(m,\eta,\lambda)$ has $J = \lceil(1/2-\eta)\log m/\log(1+\lambda)\rceil$ blocks with
points $M_j = \lceil m^{\eta + j(1/2-\eta)/J}\rceil$. The blocks tile $[\lceil m^\eta\rceil, \lceil\sqrt m\rceil)$.
The definitions, verbatim from the Lean source:

```lean
-- EOS/EOS/Buchstab.lean
def primesP (m : ℕ) : Finset ℕ := (range (m + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ m)
noncomputable def rho (m : ℕ) : ℝ := (#(primesP m) : ℝ) / m.totient
def primesIn (m : ℕ) (I : Finset ℕ) : ℕ := #{p ∈ I | p.Prime ∧ ¬ p ∣ m}
def roughUnits (m M : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun k => 0 < k ∧ k.Coprime m ∧ k * M ≤ m ∧ (k = 1 ∨ M ≤ k.minFac))
def blockCount (m : ℕ) (I : Finset ℕ) (c : ZMod m) : ℕ :=
  #{p ∈ I | p.Prime ∧ ¬ p ∣ m ∧ (c * (p : ZMod m)⁻¹).val ∈ primesP m}
noncomputable def delta (m : ℕ) (I : Finset ℕ) (ν : ℝ) (c : ZMod m) : ℝ :=
  (blockCount m I c : ℝ) - ν
def H4Block (m : ℕ) [NeZero m] (I : Finset ℕ) (M : ℕ) (η : ℝ) : Prop :=
  ∑ c ∈ univ.filter IsUnit, delta m I (rho m * primesIn m I) c ^ 4 ≤
    (η / 2) ^ 4 * rho m ^ 4 * (primesIn m I : ℝ) ^ 4 * #(roughUnits m M)

-- EOS/EOS/GapH4.lean
noncomputable def numBlocks (m : ℕ) (η lam : ℝ) : ℕ :=
  ⌈(1 / 2 - η) * Real.log m / Real.log (1 + lam)⌉₊
noncomputable def blockPt (m : ℕ) (η lam : ℝ) (j : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ (η + (1 / 2 - η) * j / numBlocks m η lam)⌉₊
def H4 (η lam : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ [NeZero m], ∀ j < numBlocks m η lam,
    H4Block m (Ico (blockPt m η lam j) (blockPt m η lam (j + 1))) (blockPt m η lam j) η
```

In words, **H4$(\eta,\lambda)$** says the following. For all large $m$ and every block $j < J$,

$$
\sum_{c\in(\mathbb Z/m\mathbb Z)^\times}\delta_j(c)^4 \le \Bigl(\frac\eta2\Bigr)^4\rho^4\,\iota_j^4\,\lvert\mathcal K_j\rvert,
$$

where:
- $\delta_j(c) = \lvert\lbrace p\in I_j \text{ prime}, p\nmid m : c\bar p \in P\rbrace\rvert - \rho\,\iota_j$;
- $\iota_j = \lvert\lbrace p \in I_j\text{ prime}, p\nmid m\rbrace\rvert$;
- $\rho = \lvert P\rvert/\varphi(m)$;
- $\mathcal K_j$ = `roughUnits m M_j`.

H4 is a fourth-moment bound, over all residue classes, for the number of primes in a block that land in $P$ after
multiplication by $c$. It does not mention $a$.

### 7.3 The gap theorem

```lean
theorem eos_of_H4 (hT : TypeISifted) (hR : RoughCounts) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ lam : ℝ, 0 < lam → lam ≤ κ * η → H4 η lam → Conjecture
```

The two unconditional inputs are named `Prop`s for cited theorems.

- **`TypeISifted`.** For every $\varepsilon > 0$ there is $\eta_1$ such that for $\eta \le \eta_1$, $m \ge m_1(\eta)$
  and every unit $a$:

  $$
  S(A_a, m^\eta) \ge \rho\bigl((1-\varepsilon\eta)\Phi_m(m, m^\eta) - \varepsilon\pi(m)\bigr),
  $$

  where $\Phi_m(x,y)$ counts $y$-rough $n \le x$ coprime to $m$. It follows from the uniform Type I bound
  $\bigl\lvert\lvert\lbrace n\in A_a : d\mid n\rbrace\rvert - \lvert P\rvert/d\bigr\rvert \le m^{15/16+\varepsilon}$
  ([Shp17, Lemma 5.4], resting on [FS11, Thm 3.1]) plus the fundamental lemma of the sieve.
- **`RoughCounts`** is the conjunction of two statements.
  - A dimension-1 sieve upper bound: the number of $n \in (a, a+H]$ with $n = 1$ or $P^-(n) \ge y$ is at most
    $CH/\log y$ for $2\le y\le H$ [HR74].
  - $\eta\,\Phi(m,m^\eta) \le (e^{-\gamma}+\varepsilon)\pi(m)$ for small $\eta$ and large $m$. This follows from
    Buchstab–de Bruijn [Buc37, dB50] and the prime number theorem.

  Chebyshev's bound and $\gamma > 1/2$ come from Mathlib.

*Proof idea.*
1. Under H4 the Hölder term is at most $(\eta/2)\rho\,\iota_j\lvert\mathcal K_j\rvert$. The certificate becomes
   $S(A_a,z) - 1 - (1+\eta/2)\rho\sum_j\iota_j\lvert\mathcal K_j\rvert > 0$.
2. An exact combinatorial step plus the sieve bound gives
   $\sum_j\iota_j\lvert\mathcal K_j\rvert \le B_0 + O(\eta^{-2}m/\log^2 m + \lambda\eta^{-1}m/\log m)$, where
   $B_0 = \Phi_m(m,z) - 1 - \lvert\lbrace p\in P: p\ge\sqrt m\rbrace\rvert$ by the Buchstab identity applied to all
   units.
3. The main terms $\rho\Phi_m$ cancel. What remains is $\rho\pi(m)$ minus terms controlled by
   $\eta\Phi_m \le (e^{-\gamma} + 0.01)\pi(m)$, and the certificate is at least $0.48\rho\pi(m) - 1 > 0$.

The paper proof gives the stronger conclusion $N(a) \ge 0.4\mu$ for every $a$.

### 7.4 What H4 is and is not

- **H4 is stronger than EOS.** With the unconditional inputs it gives $N(a)\ge 0.4\mu$ for every unit $a$.
- **H4 is not known to follow from GRH.** A\* (§6.4) has GRH-size character sums and the right Type I data, yet
  violates H4. So H4 cannot be proved from sizes plus Type I data. By the project's accounting
  (`r3-synthesis.md` §1), H4 sits about $5 + 3/k$ logarithms beyond what GRH-provable bounds give, with
  $k = \lfloor\log m/\log M\rfloor$. GRH is not a hypothesis of `eos_of_H4`.
- **H4 is not conjugation-blind.** Its analogue for $P^{-1}$ fails for every block and every large $m$, prime or
  composite (Prop Q′, *proved*). For $c = b \le (m-1)/M_{j+1}$ the product $bp_1$ is an integer below $m$ and is
  composite, so $\delta^-_j(b) = -\rho\iota_j$ for about $\varphi/M_{j+1}$ classes. This is consistent with Theorem G:
  H4 is not ruled out as a hypothesis by the conjugation barrier.
- **H4 is untestable at accessible sizes.** At $m \approx 10^5$–$10^6$ and $\eta = 1/4$, the ratio
  $\sum\delta^4/\text{RHS}$ is $10^6$–$10^7$ for the primes and equally large for every barrier object. The fourth
  moment is Gaussian noise $3\varphi(\rho\iota)^2$, which exceeds the threshold until the block scale
  $M \gtrsim (\log m)^5/\eta^4$ (*computed*, `compute/harness/`). The theorem needs $\eta\lesssim 1/100$, where
  $(\eta/2)^4 \approx 10^{-9}$, so $m_0$ is astronomically large.
- **The separation is visible on the arc.** Write $T(a) = \sum_j\sum_{k\in\mathcal K_j}\delta_j(a\bar k)/(\rho\sum_j\iota_j\lvert\mathcal K_j\rvert)$.
  At $m = 1000003$ and $m = 1009^2$, the primes have $\max_a T(a) = 0.044$–$0.049$, against the threshold
  $\eta/2 = 0.125$. The parity object A\* sits at $0.72$–$0.73$ (*computed*).
- **Caveat.** `H4 η λ` as a bare definition is trivially true outside $0<\eta<1/2$, $\lambda>0$, because then
  $J = 0$. `eos_of_H4` uses it only for $0<\eta\le\eta_0\le 1/4$ and $0<\lambda\le\kappa\eta$, where the blocks are
  non-degenerate (`notes/lean-referee.md`, caveat 1).

### 7.5 Other conditional reductions

Source: `notes/routes/F-estermann-sumsquares.md`.

- **Prime × squarefree (Estermann-type).**
  - *F0* (Lean `estermann_long_log`, hypothesis-free) is an elementary union bound over the pairs $(p,j)$ with
    $s = a\bar p \bmod m + jm$. It gives $s \le 56\,m\log m$.
  - *F1′* (Lean `estermann_of_typeISifted`) gives $s < m$ squarefree from `TypeISifted`.
  - **F1′ is known**: [Yau19, Thm 3.1] proves it with a power saving and with $p, s \le m^{16/17+\varepsilon}$.
  - The note also shows (*proved*, as a statement about the method) that GRH alone does not give F1 by any size
    argument. For the pair (primes, squarefrees) the $L^2$ deficit is $\asymp\sqrt{\log m}$. The wall is governed by
    the product of the densities.
- **Prime × sum of two squares** (Lean `SumTwoSquares.sumTwoSq_of_typeIHalf`, prime $m$ only). Assume `TypeIHalf`: a
  Type I bound for $A_a$ in classes mod $4d$ for **all** $d < \sqrt m$, with total error $\le\lvert P\rvert/\log m$.
  Then every unit is $p(x^2+y^2)$ with $p\le m$ and $x^2+y^2<m$. TypeIHalf sits exactly at the Weil/Kloosterman
  barrier (level 1/2, endpoint included). It is open and not implied by GRH. The proof uses only the vanishing of
  $\sum_{d\mid n}\chi_4(d)$ for $n\equiv 1\ (4)$ not a sum of two squares, and an alternating-series bound. Composite
  $m$ is not treated.

---

## 8. Numerics

Source: `compute/RESULTS.md`; C code in `compute/src/`, data in `compute/data/`. All items are *computed*. About 17
minutes of wall time on an 18-core machine.

### 8.1 Verification

For every $m \le 10^6$ and every unit $a$ there are primes $p,q\le m$ with $pq\equiv a$, **except for exactly 48
moduli**. **The largest failure is $m = 401$**, with the single bad class $a = 385$. The list is:

> 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 17, 19, 23, 25, 27, 29, 31, 33, 35, 37, 41, 43, 47, 53, 55, 57, 59, 61, 67,
> 69, 71, 73, 83, 89, 91, 97, 101, 103, 121, 127, 137, 169, 173, 179, 191, 397, 401.

So EOS holds for $401 < m \le 10^6$.

- **Distinct primes.** If $p \ne q$ is required, so that $a = p^2$ does not count, there are 62 failing moduli, the
  largest being $m = 431$ with $a = 169 = 13^2$.
- **Cross-checks.**
  - Two independent C programs agree for $m\le 2000$.
  - A brute-force Python count agrees on 9 moduli.
  - An FFT method over characters reproduces the minimum, the energy and the normalized minimum exactly for all 301
    primes $\le 2000$.
- The project did not find this computation in the literature *[UNVERIFIED that it is absent]*.

### 8.2 Trends

- **Normalized minimum.** Let $R(m) = \min_a N(a)/\mu$, with $N$ counting ordered pairs. $R(m)$ stays bounded below
  and increases to 1:
  - $\min R \ge 0.136$ for $m\ge 10^3$;
  - $\min R \ge 0.57$ for $m \ge 10^4$;
  - $R\approx 0.927$ for primes in $[10^6, 2\cdot10^6)$;
  - $R \approx 0.985$ for primes near $9\cdot 10^7$.

  The depth of the minimum is 0.78–0.91 of the Gaussian extreme-value prediction for a random set of the same size.
  Worst moduli are primes, prime powers, and $m$ with $\varphi(m)/m$ near 1. Relative to the random model every type
  of modulus behaves the same. No class $a$ is special: $N(\pm1)/\mu\approx 1$, and the argmin is $\pm1$ in 0.01% of
  moduli.
- **Fourth moment.** $\sum_a(N(a)-\mu)^2$ is 0.86–0.94 of the fixed-size random-subset value, creeping towards 1.
- **Character sums** (prime $m$). $\max_{\chi\ne\chi_0}\lvert S(\chi)\rvert \approx \sqrt{0.6\,\lvert P\rvert\log\varphi}$.
  Relative to the GRH scale, $\max\lvert S\rvert/(\sqrt m\log m)\le 0.058$ for $m\ge 2\cdot 10^6$, and decreasing.
- **Thinner sets.**
  - Primes up to $y(m) \approx 0.47\sqrt m(\log m)^{1.86}$ already cover every class (a coupon-collector law).
  - With one prime small and the other $\le m$: $p\le 1669$ suffices for every $m\le 10^6$. Block maxima fit
    $z\approx 3.3(\log m)^{2.4}$, consistent with a geometric-trials model $z\asymp\log^2m\,\log\log m$.

**Reading (*heuristic*).** Numerically $N(a)$ behaves like a random set of the same size, slightly better than random.
The true error $\lvert N(a)-\mu\rvert\lesssim 2\sqrt{\mu\log\varphi}$ has enormous room below $\mu$. Nothing in the
data looks like a log-power obstruction; the obstruction is one of proof technique.

---

## 9. Lean formalization

### 9.1 What is formalized

The development is Lean 4 with Mathlib, both pinned at `v4.36.0-rc2`, in `EOS/`. It has about 4,700 lines of
project code in `EOS/EOS/*.lean`, plus about 220 lines in `EOS/EOS/GRHAnalytic/` and about 4,560 vendored lines (§9.4). Mathlib is used from the cache. The build is
`cd EOS && lake exe cache get && lake build`. The results are listed in §3.1. Their proofs follow the notes, with these
deviations:
- **Weights.** The Lean proofs use $\Lambda$-weights throughout and handle prime powers directly, instead of passing
  to the prime-supported $\tilde\vartheta$.
- **Totient.** The Lean proofs use $\varphi(m)\le m$.
- **Lemma S.** It is formalized in the weak form $k^k$ in place of $k!$.
- **Lemma 2.2 of the H4 note.** It is replaced by an additive bound that needs neither a lower bound for rough
  numbers nor the prime number theorem.
- **Block endpoints.** They are rounded up to integers. This makes the Lean H4 marginally stronger per block than the
  paper's.

### 9.2 Hypotheses and their audit

The GRH-conditional theorems assume named consequences of GRH, not GRH itself.
- `GRHBounds`: $\lvert\psi(x,\chi)-[\chi=\chi_0]x\rvert\le C\sqrt x\log^2(qx)$, sharp cutoff [Dav00, ch. 20; LLS15].
- `GRHSmoothBound`: hypothesis H of §5.1.

Open hypotheses beyond GRH (`H4`, `TypeIHalf`) are single named `Prop`s whose docstrings say they are open, stronger
than or independent of GRH, and that the theorem is a conditional reduction.

An agent referee audited each definition and conclusion for faithfulness (`notes/lean-referee.md`). It found **no
defect**. Points worth knowing:
- **The characters.** `χ = 1` is the principal character mod $q$, which vanishes at non-units. It is not the constant
  function 1.
- **Necessary constants** (*computed*). Any valid constant must be at least $1.93$ for `GRHBounds` and at least
  $1.057$ for `GRHSmoothBound`, attained at $q=1$ and tiny $x$. Nothing grows with $q$.
- **`TypeISifted`.** It asserts that the minimum over $a$ of $S(A_a,m^\eta)$ is close to its exact mean
  $\rho\Phi_m$. At $m\approx10^5$ it fails for a positive fraction of $a$, as expected for an asymptotic statement
  whose slack $\asymp m/\log^2 m$ overtakes the fluctuation $\asymp\sqrt m$ only for large $m$.
- **Sources of the cited inputs.** The underlying sources were only partly read (§11).
- **Weaker than the notes.** `RoughCounts` omits a lower bound for rough numbers that the paper proof uses, so it is
  a weaker hypothesis set than the note's.
- **Existential constants.** The constants in `eos_of_H4` are existential, so the theorem does not name a specific pair
  $(\eta,\lambda)$.
- **Coverage.** The audit covered `LogFour`, `LogSquare`, `Buchstab`, `ThreePrimes`, `GapH4` and `Statement`.
  `Estermann.lean`, `SumTwoSquares.lean` and `GRH.lean` were added later. Their hypotheses (`TypeISifted`, already
  audited, and `TypeIHalf`) and their status are documented in the files and in route F. They have not had a separate
  referee audit.

### 9.3 Axioms

`#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound` for all 20 main declarations. These are
every theorem in §3.1, the GRH-definition lemmas, the new `GRHAnalytic` theorems and the key vendored PNT+ theorems.
The check is reproducible: `cd EOS && lake env lean checks/Axioms.lean`, with output recorded in
`EOS/checks/axioms-output.txt`. `eos_of_grhBounds` additionally depends on `sorryAx`, as intended (it is the open
problem). A text scan finds no `native_decide`, `implemented_by`, `opaque`, `axiom`, `unsafe` or `extern` in the
project sources.

### 9.4 Towards literal GRH

`EOS/EOS/GRH.lean` states GRH literally, using Mathlib's `DirichletCharacter.LFunction` [LS25]:

```lean
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2
```

It proves `GRH → RiemannHypothesis` and the equivalence with the same statement for all characters. The strict
inequality $\operatorname{Re}s<1$ avoids the junk value of Mathlib's $L$-function at the pole.

The plan (`notes/grh-blueprint.md`) is to prove `GRH → GRHSmoothBound` and then obtain the four GRH theorems from
`GRH`. The $\log^4$ theorem follows from the $\log^2$ one by monotonicity, so `GRHBounds` leaves the chain. The
recommended route replaces Hadamard factorization by Landau's local partial-fraction lemma (Borel–Carathéodory plus
Jensen). This avoids the functional equation and $\Gamma$-factor bounds. It uses:
- a Perron formula for the kernel $x^s/(s(s+1))$;
- a residue theorem on rectangles;
- the logarithmic-derivative residue lemmas.

Mathlib lacks these. About 4,560 lines are vendored from the PrimeNumberTheoremAnd project [PNT+] (Apache-2.0,
upstream commit `a4fb698`) into `EOS/EOS/Vendor/PNT/`:
- the residue theorem on rectangles;
- the Perron formula;
- Borel–Carathéodory and Landau-type bounds, taken from PNT+'s `StrongPNT.lean`, which originates in Math Inc's
  autoformalization.

The original attribution, a list of local modifications and the licence text are kept
(`EOS/EOS/Vendor/PNT/NOTICE.md`). The vendoring involved seven small version-drift fixes and no other changes to
proofs. A Lake dependency was not possible without moving the Mathlib pin.

**Status at the time of writing.**

| Milestone | Content | Status |
|---|---|---|
| M0 | `GRH`, `GRH → RiemannHypothesis`, `GRH_iff_forall` | done |
| M1 | vendoring from PNT+ | done; builds with no `sorry` |
| M2 (part) | `EOS/EOS/GRHAnalytic/Dirichlet.lean`: $-L'/L$ as the $L$-series of $\Lambda\chi$; the Cesàro Perron kernel identity $\frac1{2\pi i}\int_{(\sigma)}y^s\,\frac{ds}{s(s+1)} = \max(0, 1-1/y)$, including $y = 1$; and `EOS.psiCesaro_eq_verticalIntegral`, which writes $\tilde\psi(x,\chi)$ as $\frac1{2\pi i}\int_{(\sigma)}(-L'/L)(s,\chi)\,x^s\,\frac{ds}{s(s+1)}$ for $\sigma>1$, any $\chi$ | done; no `sorry` |
| M3 | growth bounds for $L(s,\chi)$ and Landau's lemma for $L$ | to do |
| M4 | GRH bounds for $L'/L$ on $\operatorname{Re}s = 1/4$, and zero counts | to do |
| M5 | contour shift and residues | to do |
| M6 | assembly: `GRH → GRHSmoothBound`, then the four GRH theorems from `GRH` | to do |

Until M3–M6 are done, the GRH theorems are conditional on the named consequence `GRHSmoothBound`, whose proof from GRH
is on paper only. The blueprint judges M3 (Landau for $L$) and M5 (contour and residues) to carry most of the risk
(*heuristic*).

**Reusable machinery for M3–M6** (`notes/lean-reuse-survey.md`; static inspection only, nothing compiled).
- *TauCeti* [TauCeti] is an Apache-2.0, AI-written Lean library downstream of Mathlib. It contains several missing
  pieces:
  - Landau's lemma at a general centre;
  - Jensen-type zero counts;
  - growth bounds for $L(s,\chi)$ on $\operatorname{Re}s>0$;
  - the Cesàro Mellin kernel.

  These would cut the remaining new code by an estimated 500–800 lines. TauCeti uses a newer Lean/Mathlib, so they
  would need backporting.
- The Lean archive accompanying [Remark] contains a complete classical explicit formula for primitive Dirichlet
  $L$-functions, with truncated Perron, contour shift and Landau-type bounds. It would shorten the remaining work
  considerably. It carries no licence, so we treat it as reference only. It is unreviewed and was not compiled here.

---

## 10. Methodology

The work was done between 22 and 23 November 2026 (dates of the notes). A human user set the goals and made the main
decisions, recorded in `CLAUDE.md`: the deliverables, the literal statement of GRH, and the vendoring. An
orchestrating AI agent (Claude Opus 5.5, run through Claude Code; research sub-agents ran on Claude Fable 5.2 and
Lean-formalization sub-agents on Claude Opus 5.5) dispatched sub-agents, merged their outputs and kept the notes.
The stages were as follows.

1. **Setup.** The orchestrator wrote the problem statement and a first sketch of the obstruction (`notes/00-setup.md`,
   `notes/01-parseval-wall.md`).
2. **Literature agents.** Four strands (`notes/lit/01`–`04`): direct literature, analytic tools, GRH techniques, and
   "where has an exact Parseval identity been beaten". Each citation carries a provenance tag: read in the source,
   secondary, recalled, or unverified. PDFs were text-extracted. There was no MathSciNet or zbMATH access.
3. **Route agents.** Six routes (`notes/routes/A`–`F`):
   - A: Type II / Vaughan;
   - B: function-field transfer;
   - C: the log exponent;
   - D: new connections and barriers;
   - E: Buchstab and H4;
   - F: Estermann and sums of two squares.

   Each route agent wrote a note with status tags and supporting scripts.
4. **Adversarial referees.** Separate agents were asked to break claims, not confirm them:
   - `C-referee.md` re-derived every step of route C, tested H numerically, and downgraded novelty claims;
   - `W-referee.md` re-derived Theorem W and did the literature comparison;
   - `lean-referee.md` audited the Lean hypotheses and conclusions.

   The referees found and fixed real errors. Examples:
   - a false monotonicity claim and a contour-height gap in the proof of H;
   - a false block-majorant claim near $\sqrt m$ in the first version of the H4 lemma;
   - a miscount for composite $m$ in the first version of Prop Q′;
   - a misquotation of Ramaré–Walker in the orchestrator's own brief.
5. **Persona brainstorm** (`notes/brainstorm/`). Round 1: five personas (analytic, automorphic, combinatorial,
   geometer, wildcard) made fifteen proposals. Round 2: a barrier skeptic tested each proposal against the six barrier
   objects, a technical skeptic re-derived the claimed proofs, and a builder tried to repair them. Round 3: a moderator
   synthesis ranked them. The brainstorm produced Theorem W and the H4 reduction. None of the fifteen proposals was
   judged to have more than a 1% chance of reaching EOS.
6. **Lean agents** formalized the deliverables under fixed rules:
   - Mathlib only from the cache;
   - every analytic input a named `Prop` with a citation;
   - no unused GRH hypotheses;
   - docstrings stating plainly when a hypothesis is open.
7. **Numerics and phase lab** (`compute/`). C and FFT programs for verification and moments. A Python phase lab for
   barrier comparisons, and a barrier harness for the H4 statistics.
8. **Independent verification by the orchestrator.** Every Lean result reported by a sub-agent was checked by the
   orchestrator before it was recorded: build, `#print axioms`, and a `sorry` scan. Sub-agent reports were not taken
   on trust.

Two observations about the process may interest readers who run similar projects.
- **Referees and novelty.** The referees were most useful on novelty. Several "new" results were downgraded to
  "routine" or "known" (Corollary A1, Theorem E, F1′).
- **Barrier checklists.** They were effective at killing proposals early. The phrase "passes all barriers" usually
  meant that the barriers had been moved into a hypothesis.

---

## 11. Limitations and open problems

### 11.1 Limitations

- **Nothing is refereed.** The mathematics was produced by AI agents and checked by other AI agents. Lean checks the
  formal deductions only. All novelty claims are relative to agent literature searches without MathSciNet or zbMATH,
  and a recent paper could have been missed.
- **Every GRH result is conditional.** The announced proof [Remark] has not been checked here. Moreover, the Lean
  theorems assume the GRH *consequences* `GRHSmoothBound` and `GRHBounds`. The derivation from literal GRH is on paper
  (route C §1, agent-refereed) and is being formalized.
- **The new results are modest.**
  - Theorem S and Corollary A1 are new statements with routine proofs.
  - Theorem W is an easy refinement of [BS26].
  - The H4 reduction replaces EOS by a stronger, untestable hypothesis.
  - F1′ is known [Yau19].
- **Cited inputs read only in part.**
  - `TypeISifted` rests on [Shp17, Lemma 5.4], which was read. That lemma delegates its proof to Shparlinski (2013),
    Lemma 2, which was not read, and to [FS11, Thm 3.1], which was not read.
  - The fundamental lemma of the sieve and the Buchstab–de Bruijn asymptotics are cited with recalled theorem numbers.
  - The A\* barrier uses one smoothed prime-sum bound whose derivation is sketched.
- **Heuristics.** The phase-lab conclusions, the "conservation law", the log accounting for H4, and the
  random-pairing barrier are heuristic or sketched as tagged. The numerics test sizes up to $10^6$ (verification) and
  $9\cdot10^7$ (moments). They say nothing about asymptotic hypotheses such as H4.
- **Partial audit.** The Lean audit did not separately cover `Estermann.lean`, `SumTwoSquares.lean`, `GRH.lean` or
  `GRHAnalytic/Dirichlet.lean`. In
  preparing this report no build was re-run; the statements of §3.1 and §9 were checked against the source text and
  the recorded audit outputs.

### 11.2 Open problems

1. **EOS under GRH.** Pointwise phase cancellation in $\sum_{\chi\ne\chi_0}\bar\chi(a)S(\chi)^2$ worth one logarithm.
   Equivalently, rule out a single large deviation of $b\mapsto E(b)$.
2. **Lower the exponents under GRH:**
   - below 2 in the symmetric range $K\varphi\log^2 m$;
   - below 3 in the asymmetric range $p\le m$, $q\le Km\log^3 m$;
   - below 3 in the exceptional set at range exactly $m$.

   The symmetric case would need a prime-pair upper bound with constant below 2 (the sieve's parity constant),
   averaged over the shifts $km$.
3. **Remove the $(\log\log m)^2$ in Theorem W, or reach $s\ll\log^{2-\delta}m$.** By the Wiener-norm hierarchy of
   `r1-wildcard.md`, dropping the auxiliary prime is equivalent, for this method, to a parity-breaking prime-pair bound
   (*heuristic*).
4. **A Type II estimate for $A_a = \lbrace a\bar p\bmod m\rbrace$**, or any route to H4 or to its weak-type form LD.
5. **Function fields at small $q$.** The EOS analogue over $\mathbb F_2[t]$ or $\mathbb F_3[t]$ as the degree tends to
   infinity appears open *[UNVERIFIED]*. It holds numerically for sampled moduli of degree $11\le n\le 23$. The
   conjugation barrier has no analogue there, so it tests barriers 1–5 only.
6. **Complete the Lean chain `GRH → GRHSmoothBound`**, and so obtain the GRH theorems from literal GRH.

---

## 12. References

Bibliographic details are as recorded in the repository (`README.md`, `notes/lit/`). Where details were not recorded,
the item is cited by title or identifier only.

- **[Ban26]** W. D. Banks, *Products of two elements of Granville's random model in residue classes*, arXiv:2609.37434 (2026).
- **[BS26]** W. Banks, I. E. Shparlinski, *On the Erdős–Odlyzko–Sárközy conjecture for prime-power moduli*, arXiv:2610.19597 (2026).
- **[Buc37]** A. A. Buchstab, Asymptotic estimates of a general number-theoretic function, Mat. Sb. 2(44) (1937).
- **[Dav00]** H. Davenport, *Multiplicative Number Theory*, 3rd ed., rev. H. L. Montgomery, GTM 74, Springer (2000).
- **[dB50]** N. G. de Bruijn, On the number of uncancelled elements in the sieve of Eratosthenes, Proc. Ned. Akad. Wetensch. 53 (1950).
- **[EOS87]** P. Erdős, A. M. Odlyzko, A. Sárközy, *On the residues of products of prime numbers*, Period. Math. Hungar. 18 (1987), 229–239. doi:10.1007/BF01848086.
- **[FKS08]** J. B. Friedlander, P. Kurlberg, I. E. Shparlinski, *Products in residue classes*, Math. Res. Lett. 15 (2008), 1133–1147. doi:10.4310/MRL.2008.v15.n6.a6. arXiv:0708.1562.
- **[FS11]** É. Fouvry, I. E. Shparlinski, *On a ternary quadratic form over primes*, Acta Arith. 150 (2011), 285–314.
- **[Gar12]** M. Z. Garaev, *On multiplicative congruences*, Math. Z. 272 (2012), 473–482. doi:10.1007/s00209-011-0944-1.
- **[HR74]** H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press (1974).
- **[LLS15]** Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic non-residue and related problems*, Math. Comp. 84 (2015), 2391–2412; corrigendum Math. Comp. 86 (2017). arXiv:1309.3595.
- **[LS25]** D. Loeffler, M. Stoll, *Formalizing zeta and L-functions in Lean*, arXiv:2503.00959.
- **[MT24]** K. Matomäki, J. Teräväinen, *Products of primes in arithmetic progressions*, J. reine angew. Math. 808 (2024), 193–240. doi:10.1515/crelle-2023-0096. arXiv:2301.07679.
- **[MV]** H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory* (cited for eq. (13.28)).
- **[TauCeti]** TauCeti, AI-written Lean library downstream of Mathlib (Lean FRO / Mathlib Initiative), https://github.com/TauCetiProject/TauCeti, surveyed at commit `547786e7`. Apache License 2.0.
- **[PNT+]** PrimeNumberTheoremAnd (A. Kontorovich, T. Tao et al.), https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b`. Apache License 2.0; copyright the PrimeNumberTheoremAnd contributors. The vendored `StrongPNT.lean` material (Borel–Carathéodory, Landau-type bounds) comes from Math Inc's autoformalization, merged into PNT+.
- **[Remark]** *Remark* (announcement of a Lean-formalized proof of RH/GRH), https://alpo.ge/remark.pdf (2026). Not checked here.
- **[RW18]** O. Ramaré, A. Walker, *Products of primes in arithmetic progressions: a footnote in parity breaking*, J. Théor. Nombres Bordeaux 30 (2018), 219–225. doi:10.5802/jtnb.1024. arXiv:1610.05804.
- **[Saw24]** W. Sawin, *Square-root cancellation for sums of factorization functions over squarefree progressions in F_q[t]*, Acta Math. 233 (2024), 285–418. arXiv:2102.09730.
- **[Shp13]** I. E. Shparlinski, *On products of primes and almost primes in arithmetic progressions*, Period. Math. Hungar. 67 (2013), 55–61. doi:10.1007/s10998-013-2736-3.
- **[Shp17]** I. E. Shparlinski, *On short products of primes in arithmetic progressions*, Proc. Amer. Math. Soc. 147 (2019), 977–986. doi:10.1090/proc/14289. arXiv:1705.06087.
- **[Spe85]** J. Spencer, *Six standard deviations suffice*, Trans. Amer. Math. Soc. 289 (1985).
- **[Sza24]** B. Szabó, *On the existence of products of primes in arithmetic progressions*, Bull. LMS 56 (2024), 1227–1243. doi:10.1112/blms.12990. arXiv:2208.05762.
- **[Wal16]** A. Walker, *A multiplicative analogue of Schnirelmann's theorem*, Bull. LMS 48 (2016), 1018–1028. doi:10.1112/blms/bdw062. arXiv:1505.03328.
- **[Xie26]** Xie, *On a conjecture of Erdős over function fields*, Math. Z. 313 (2026), Paper 64. doi:10.1007/s00209-026-04077-6. arXiv:2510.17612.
- **[Yau19]** K. H. Yau, *On products of primes and square-free integers in arithmetic progressions*, arXiv:1907.06016.
- **[Zha22]** L. Zhao, *On products of primes and almost primes in arithmetic progressions*, Acta Arith. 204 (2022), 253–267. doi:10.4064/aa211215-2-6.

**Software.** [Lean 4](https://lean-lang.org); [Mathlib](https://github.com/leanprover-community/mathlib4); [PNT+] as above.

---

## Appendix: where to find each claim

| Topic | File |
|---|---|
| Problem setup, the wall | `notes/00-setup.md`, `notes/01-parseval-wall.md` |
| Literature | `notes/lit/01-eos-direct.md` … `04-beating-parseval.md` |
| H, Theorem S, Corollary A1, Theorem B, Prop L | `notes/routes/C-log-exponent.md`, `notes/routes/C-referee.md` |
| Theorem W | `notes/brainstorm/r1-wildcard.md` §1, `notes/routes/W-referee.md` |
| Theorem G | `notes/routes/D-new-connections.md` §1 |
| A\* | `notes/routes/A-typeII.md` §4.2 |
| Function fields | `notes/routes/B-function-field.md` |
| H4 reduction | `notes/routes/E-buchstab-H4.md`; `EOS/EOS/Buchstab.lean`, `EOS/EOS/GapH4.lean` |
| Estermann, sums of two squares | `notes/routes/F-estermann-sumsquares.md`; `EOS/EOS/Estermann.lean`, `EOS/EOS/SumTwoSquares.lean` |
| Brainstorm | `notes/brainstorm/r1-*.md`, `r2-*.md`, `r3-synthesis.md` |
| Numerics | `compute/RESULTS.md`, `compute/data/` |
| Phase lab, barrier harness | `compute/lab/FINDINGS.md`, `compute/harness/` |
| Lean audit | `notes/lean-referee.md` |
| Literal GRH plan | `notes/grh-blueprint.md`, `EOS/EOS/GRH.lean`, `EOS/EOS/Vendor/PNT/NOTICE.md` |
