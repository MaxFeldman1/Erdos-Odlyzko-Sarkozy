# Erdős–Odlyzko–Sárközy conjecture: research notes and Lean formalization

**Conjecture (Erdős–Odlyzko–Sárközy, 1987).** For all sufficiently large m and every a with gcd(a, m) = 1,
there are primes p, q ≤ m with pq ≡ a (mod m).

This repository records an AI-orchestrated attack on the conjecture, conditional on the Generalized Riemann
Hypothesis (GRH) for Dirichlet L-functions. GRH was recently announced as proved
([remark](https://alpo.ge/remark.pdf)); that proof has not been checked here, so every result below is stated as
conditional. The work has four parts: a literature review, several research routes, numerics, and a Lean 4 / Mathlib
formalization.

**Bottom line.** The full conjecture remains open, even under GRH. The obstruction is isolated precisely (see
*The Parseval wall* below), several barriers are identified, and the strongest rigorous GRH results are formalized in
Lean with no `sorry`.

## Lean results (`EOS/`)

Every theorem below is proved with **no `sorry`**. Each depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The hypotheses were audited for faithfulness and truth in `notes/lean-referee.md`.

| Theorem | Hypothesis | Statement (all large m, every unit a mod m) |
|---|---|---|
| `coveredBy_of_grhBounds` | `GRHBounds` (GRH consequence) | a ≡ pq, with p, q ≤ K m log⁴ m |
| `coveredBy_log_sq` | `GRHSmoothBound` (GRH consequence) | a ≡ pq, with p, q ≤ K m log² m |
| `coveredByAsym_m_log_cube` | `GRHSmoothBound` | a ≡ pq, with **p ≤ m** and q ≤ K m log³ m |
| `coveredBy_three_primes` | `GRHSmoothBound` | a ≡ pqs, with p, q ≤ m and s ≪ log² m (log log m)² |
| `Buchstab.lemmaC`, `lemmaC'` | none | exact Buchstab identity and finite certificate |
| `estermann_long_log` | none | a ≡ p·s, with p ≤ m prime and s ≤ 56 m log m squarefree |
| `estermann_of_typeISifted` | cited unconditional Type I input | a ≡ p·s, with p ≤ m, s < m squarefree (known: Yau 2019) |
| `SumTwoSquares.sumTwoSq_of_typeIHalf` | **TypeIHalf** (open: Type I level 1/2) | m prime: a ≡ p·(x² + y²), with p ≤ m and x² + y² < m |
| `eos_of_H4` | cited unconditional inputs + **H4** | the full conjecture |

Notes on the hypotheses and the last theorem:
- The GRH hypotheses are standard explicit consequences of GRH. Deriving them from GRH stated literally (zeros of
  L-functions) is in progress.
- `eos_of_H4` does not use GRH. H4 is a fourth-moment hypothesis over residue classes. It is **stronger than the
  conjecture and not known to follow from GRH**: it isolates the gap rather than closing it.
- `TypeIHalf` is likewise an open hypothesis beyond GRH; the theorem using it is a conditional reduction.
- The open target `eos_of_grhBounds` in `EOS/Statement.lean` is the only `sorry`.

Build (Mathlib comes from the cache; never build Mathlib from source):
```
cd EOS && lake exe cache get && lake build
```

## Mathematical findings

- **Theorem W** (`notes/routes/W-referee.md`). Under GRH every unit is p·q·s with p, q ≤ m and s ≪ (log m)²(log log m)².
  This improves the (log q)⁴ of Banks–Shparlinski (arXiv:2610.19597). It appears to be new.
- **The Parseval wall** (`notes/01-parseval-wall.md`). At range exactly m, Parseval is an exact identity. Bounds that
  use only the sizes |S(χ)| lose exactly one log, and the phases of χ̄(a)S(χ)² are what decide the conjecture.
  EOS is a multiplicative binary-Goldbach problem.
- **Barriers.**
  - The conjugation barrier (Theorem G, `notes/routes/D-new-connections.md`): the quotient problem has identical |S|
    data, yet −1 ∉ P·P⁻¹.
  - Random pairing-avoiding sets.
  - Deletion: removing about a 1/log m fraction of the primes can kill a class.
  - Parity.
  - Route A's sequence A*: the same Type I data and character-sum sizes, but no primes.
- **Phase lab** (`compute/lab/FINDINGS.md`). The primes behave like independent random phases in every grouping of
  characters tried. Barrier objects look exactly like the primes conditioned on one large deviation. A proof must
  therefore rule out a single spike in b ↦ E(b); no localized phase pattern distinguishes the primes.
- **Numerics** (`compute/RESULTS.md`). The conjecture holds for every m in [402, 10⁶]. The largest failure is m = 401
  (a = 385), and there are 48 failing moduli in total.

## Layout

| Path | Contents |
|---|---|
| `notes/00-setup.md`, `notes/01-parseval-wall.md` | problem setup; primer on the core obstruction |
| `notes/lit/` | literature reviews: direct results, analytic tools, GRH techniques, beating Parseval |
| `notes/routes/` | research routes A–F, referee reports, and the H4 reduction (`E-buchstab-H4.md`) |
| `notes/brainstorm/` | multi-persona brainstorm (specialists, skeptics, builder, moderator synthesis) |
| `notes/lean-referee.md` | audit of every Lean hypothesis and conclusion |
| `compute/` | C and Python numerics, the phase lab (`compute/lab/`), and the barrier harness |
| `EOS/` | Lean 4 + Mathlib formalization |

Claims in the notes are tagged *proved / sketched / heuristic / [UNVERIFIED]*. Most of the mathematics was produced
by AI agents and checked by other agents and by Lean. Treat anything not formalized as a research note, not as a
refereed result.
