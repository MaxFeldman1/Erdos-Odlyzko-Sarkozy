# Erdős–Odlyzko–Sárközy conjecture: research notes and Lean formalization

**Conjecture (Erdős–Odlyzko–Sárközy [EOS87]).** For all sufficiently large m and every a with gcd(a, m) = 1,
there are primes p, q ≤ m with pq ≡ a (mod m).

This repository records an AI-orchestrated attack on the conjecture, conditional on the Generalized Riemann
Hypothesis (GRH) for Dirichlet L-functions. GRH was recently announced as proved
[Remark]; that proof has not been checked here, so every result below is stated as
conditional. The work has four parts: a literature review, several research routes, numerics, and a Lean 4 / Mathlib
formalization.

**Write-up:** [`WRITEUP.md`](WRITEUP.md) is the full, paper-style report.

**Bottom line.** The full conjecture remains open, even under GRH. The obstruction is isolated precisely (see
*The Parseval wall* below), several barriers are identified, and the strongest rigorous GRH results are formalized in
Lean with no `sorry`.

## Lean results (`EOS/`)

Every theorem below is proved with **no `sorry`**. Each depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The hypotheses were audited for faithfulness and truth in `notes/lean-referee.md`.

| Theorem | Hypothesis | Statement (all large m, every unit a mod m) |
|---|---|---|
| `coveredBy_of_grhBounds` | `GRHBounds` (GRH consequence) | a ≡ pq, with p, q ≤ K m log⁴ m ([EOS87, Cor. 3], extended to all m) |
| `coveredBy_log_sq` | `GRHSmoothBound` (GRH consequence) | a ≡ pq, with p, q ≤ K m log² m (smoothed refinement of [EOS87]) |
| `coveredByAsym_m_log_cube` | `GRHSmoothBound` | a ≡ pq, with **p ≤ m** and q ≤ K m log³ m |
| `coveredBy_three_primes` | `GRHSmoothBound` | a ≡ pqs, with p, q ≤ m and s ≪ log² m (log log m)² (improves [BS26, Thm 1.3]) |
| `Buchstab.lemmaC`, `lemmaC'` | none | exact Buchstab identity [Buc37] and finite certificate |
| `estermann_long_log` | none | a ≡ p·s, with p ≤ m prime and s ≤ 56 m log m squarefree |
| `estermann_of_typeISifted` | cited unconditional Type I input | a ≡ p·s, with p ≤ m, s < m squarefree (known: [Yau19, Thm 3.1]) |
| `SumTwoSquares.sumTwoSq_of_typeIHalf` | **TypeIHalf** (open: Type I level 1/2) | m prime: a ≡ p·(x² + y²), with p ≤ m and x² + y² < m |
| `eos_of_H4` | cited unconditional inputs [FS11, Shp13, Shp17, HR74, dB50] + **H4** | the full conjecture |

Notes on the hypotheses and the last theorem:
- The GRH hypotheses are standard explicit consequences of GRH [Dav00, ch. 20; LLS15; BS26, Lemma 2.5]. Deriving them from GRH stated literally (zeros of
  L-functions, `EOS.GRH` in `EOS/EOS/GRH.lean`, with `GRH → RiemannHypothesis` proved) is in progress; see
  `notes/grh-blueprint.md`.
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
  This improves the (log q)⁴ of [BS26, Thm 1.3]. It appears to be new (literature search in `notes/routes/W-referee.md`;
  no MathSciNet access).
- **The Parseval wall** (`notes/01-parseval-wall.md`). At range exactly m, Parseval is an exact identity. Bounds that
  use only the sizes |S(χ)| lose exactly one log, and the phases of χ̄(a)S(χ)² are what decide the conjecture.
  EOS is a multiplicative binary-Goldbach problem. The barrier is stated in [Ban26]; the function-field analogue is
  proved by a second, Deligne-type spectral expansion [Saw24, Xie26].
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
- **Context.** The best unconditional results are in [MT24] (two primes for ≥ (2/3 − ε)φ(m) classes; three primes)
  and [Sza24, RW18, Wal16]. Under GRH, all but O(log³ m) classes are covered at range m [BS26, Thm 1.4]; see also
  [FKS08, Gar12, Zha22].
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

## References

- **[Ban26]** W. D. Banks, *Products of two elements of Granville's random model in residue classes*, arXiv:2609.37434 (2026).
- **[BS26]** W. Banks, I. E. Shparlinski, *On the Erdős–Odlyzko–Sárközy conjecture for prime-power moduli*,
  arXiv:2610.19597 (2026).
- **[Buc37]** A. A. Buchstab, Asymptotic estimates of a general number-theoretic function, Mat. Sb. 2(44) (1937).
- **[Dav00]** H. Davenport, *Multiplicative Number Theory*, 3rd ed., rev. H. L. Montgomery, GTM 74, Springer (2000).
- **[dB50]** N. G. de Bruijn, On the number of uncancelled elements in the sieve of Eratosthenes,
  Proc. Ned. Akad. Wetensch. 53 (1950).
- **[EOS87]** P. Erdős, A. M. Odlyzko, A. Sárközy, *On the residues of products of prime numbers*,
  Period. Math. Hungar. 18 (1987), 229–239. doi:10.1007/BF01848086.
- **[FKS08]** J. B. Friedlander, P. Kurlberg, I. E. Shparlinski, *Products in residue classes*, Math. Res. Lett. 15 (2008),
  1133–1147. doi:10.4310/MRL.2008.v15.n6.a6. arXiv:0708.1562.
- **[FS11]** É. Fouvry, I. E. Shparlinski, Acta Arith. 150 (2011), 285–314 (Kloosterman sums over primes, Thm 3.1).
- **[Gar12]** M. Z. Garaev, *On multiplicative congruences*, Math. Z. 272 (2012), 473–482. doi:10.1007/s00209-011-0944-1.
- **[HR74]** H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press (1974) (fundamental lemma, upper-bound sieve).
- **[LLS15]** Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic non-residue and related
  problems*, Math. Comp. 84 (2015), 2391–2412; corrigendum Math. Comp. 86 (2017). arXiv:1309.3595.
- **[MT24]** K. Matomäki, J. Teräväinen, *Products of primes in arithmetic progressions*, J. reine angew. Math. 808 (2024),
  193–240. doi:10.1515/crelle-2023-0096. arXiv:2301.07679.
- **[Remark]** *Remark* (announcement of a Lean-formalized proof of RH/GRH), https://alpo.ge/remark.pdf (2026). Not checked here.
- **[RW18]** O. Ramaré, A. Walker, *Products of primes in arithmetic progressions: a footnote in parity breaking*,
  J. Théor. Nombres Bordeaux 30 (2018), 219–225. doi:10.5802/jtnb.1024. arXiv:1610.05804.
- **[Saw24]** W. Sawin, *Square-root cancellation for sums of factorization functions over squarefree progressions in
  F_q[t]*, Acta Math. 233 (2024), 285–418. arXiv:2102.09730.
- **[Shp13]** I. E. Shparlinski, *On products of primes and almost primes in arithmetic progressions*,
  Period. Math. Hungar. 67 (2013), 55–61. doi:10.1007/s10998-013-2736-3.
- **[Shp17]** I. E. Shparlinski, arXiv:1705.06087 (Lemma 5.4: Type I bounds for a·p̄ mod m).
- **[Sza24]** B. Szabó, *On the existence of products of primes in arithmetic progressions*, Bull. LMS 56 (2024),
  1227–1243. doi:10.1112/blms.12990. arXiv:2208.05762.
- **[Wal16]** A. Walker, *A multiplicative analogue of Schnirelmann's theorem*, Bull. LMS 48 (2016), 1018–1028.
  doi:10.1112/blms/bdw062. arXiv:1505.03328.
- **[Xie26]** Xie, *On a conjecture of Erdős over function fields*, Math. Z. 313 (2026), Paper 64.
  doi:10.1007/s00209-026-04077-6. arXiv:2510.17612.
- **[Yau19]** K. H. Yau, *On products of primes and square-free integers in arithmetic progressions*, arXiv:1907.06016.
- **[Zha22]** L. Zhao, *On products of primes and almost primes in arithmetic progressions*, Acta Arith. 204 (2022),
  253–267. doi:10.4064/aa211215-2-6.

**Software.** [Lean 4](https://lean-lang.org) and [Mathlib](https://github.com/leanprover-community/mathlib4)
(Dirichlet L-functions in Mathlib: D. Loeffler, M. Stoll, *Formalizing zeta and L-functions in Lean*, arXiv:2503.00959).

Full bibliographies, with the reading status of each source, are in `notes/lit/` and in each route note.
