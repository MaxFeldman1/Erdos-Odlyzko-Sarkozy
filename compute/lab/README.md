# phaselab: where the phase cancellation in E(a) comes from

A library and CLI for studying

  E(a) = N(a) − μ = (1/φ) Σ_{χ≠χ0} χ̄(a) S(χ)²,  S(χ) = Σ_{p∈P} w(p) χ(p),

character by character. The aim is to locate the phase cancellation that the Parseval wall
(`notes/01-parseval-wall.md`) says sizes alone cannot supply. The lab compares the primes with the barrier objects,
which share size or Type I data with P but have N(a) = 0.

Results are in `FINDINGS.md`. Everything here is numerics: no claim in this directory is a proof.

```
compute/lab/
  phaselab/            the library (pure numpy; FFTs via numpy.fft)
    group.py           UnitGroup(m): discrete logs on (Z/m)^* = Π C_{n_i}, characters, order/conductor/parity, subgroups
    sets.py            weight vectors: primes (w = 1, log p, Cesàro; any range X), integers, barrier objects
    core.py            Problem: N(a) = (1/φ) Σ χ̄(a) Π_k S_k(χ)  (binary, conjugate, bilinear, 4-fold toy, ...)
    decomp.py          groupings of characters, within/across cancellation, random-phase surrogates, Xie cosets
    phases.py          phase harmonics, histograms and Kuiper test at a; ψ-shift correlations; moments of E(b)
    dynamics.py        S_X(χ) as X runs: phase winding, decorrelation, coherence of χ and χψ
    blocks.py          route A / H4 block statistics δ_I(c) and the arc statistic
    objects.py         the standard catalogue: P, P_worst, conj, redacted, redacted_half, pairing, random, astar, toy
    report.py          full runs (report), separation table (compare), scaling table (scan), figures
    __main__.py        CLI
  tests/test_lab.py    cross-checks against direct counting and against compute/data/char_small.csv
  fig/                 figures used by FINDINGS.md
  data/                JSON outputs and logs (large or regenerable; gitignored)
```

Requirements: Python ≥ 3.9, numpy, matplotlib (figures only). No compilation is needed. At m ≈ 10⁶ one FFT takes
about 50 ms, and a full `report` for all nine objects takes about 1 minute.

## Conventions

They are the same as in `compute/src/eos_char.c`, extended to non-cyclic G.

- G = (Z/m)^* ≅ Π_i C_{n_i}, built by CRT over the prime powers q ∥ m:
  - odd q = p^k gives one cyclic factor, with a primitive root;
  - q = 4 gives ⟨−1⟩;
  - q = 2^k with k ≥ 3 gives ⟨−1⟩ × ⟨5⟩.
  
  e(x) is the exponent vector of the unit x. Its flat (C-order) index in the grid of shape (n_1, …, n_r) is
  `G.flat_of_res[x]`, and `G.res_of_flat` inverts it.
- Characters are indexed by j in the same grid: χ_j(x) = exp(−2πi Σ_i j_i e_i(x)/n_i). Hence
  `np.fft.fftn(f)[j] = Σ_x f(x) χ_j(x) = S(χ_j)`. The principal character is j = 0, and the conjugate of j is
  `G.neg[j]`.
- A `Problem(G, [w_1, …, w_K], conj=[…])` has T(χ) = Π_k S_k(χ), with S_k replaced by its conjugate where
  `conj[k]` is set. Then:
  - N(a) = (1/φ) Σ_χ χ̄(a) T(χ) = Σ_{x_1^{±1}⋯x_K^{±1} = a} Π w_k(x_k);
  - μ = `prob.main` = T(χ0)/φ;
  - the terms of E(a) are `prob.terms(a)[j]` = χ̄_j(a) T(χ_j)/φ, and j = 0 is the main term.
- Weights for integers above m add up in their residue class, so the range X > m works directly.

## Quick start

```bash
cd compute/lab
python3 tests/test_lab.py                     # 8 cross-checks, a few seconds
python3 -m phaselab info 1000003              # |P|, μ, Parseval mass A, min N
python3 -m phaselab decompose 982801 --by coset:pow:3510 --object P_worst
python3 -m phaselab decompose 1000000 --by conductor --a 3
python3 -m phaselab phases 982801 --object redacted
python3 -m phaselab psi 982801 --dmax 6
python3 -m phaselab blocks 982801 --object astar
python3 -m phaselab compare 100801            # every object × every diagnostic, markdown table
python3 -m phaselab report 982801             # + dynamics, range X > m, figures → fig/982801_*.png, data/report_982801.json
python3 -m phaselab scan 100003 1000003 5000011   # scaling table → data/scan_*.json
```

Common options:
- `--object` is one of P, P_worst, conj, redacted, redacted_half, pairing, random, astar, toy. The default is P.
- `--a A` sets the class. The default is a seeded random unit. P_worst and toy use their own argmin, and conj uses −1.
- `--X` sets the range and `--weight` the weight: `1`, `log`, `cesaro`, or a product such as `log*cesaro`.

Groupings for `--by`:

| spec | groups | notes |
|---|---|---|
| `order` | characters of each exact order | |
| `conductor` | characters of each conductor | composite m |
| `parity` | χ(−1) = ±1 | |
| `quantile:q` | q equal-count bins of \|T(χ)\| = \|S(χ)\|² | |
| `coset:pow:d` | cosets χH^⊥, where H = G^d and H^⊥ = characters of order dividing d | |
| `coset:mod:m1` | cosets χH^⊥, where H = {x ≡ 1 mod m1} and H^⊥ = characters of conductor dividing m1 | |
| `coset:gens:a,b,…` | cosets χH^⊥, where H = ⟨a, b, …⟩ | |

## Python API (the main entry points)

```python
from phaselab import UnitGroup, Problem, sets, decomp, phases, dynamics, blocks
from phaselab.objects import catalogue

G  = UnitGroup(982801)
wP = sets.prime_weights(G.m, X=None, weight="1")      # X = m by default; X > m allowed
P  = Problem(G, [wP, wP])                              # binary problem
P.N(a), P.E(a), P.main, P.parseval_mass(), P.rms_E(), P.worst_a(k), P.N_flat(), P.N_res()
t  = P.terms(a)                                        # χ̄(a)S(χ)²/φ for every χ

lab = decomp.make_labels(P, "coset:pow:3510")          # or decomp.by_order(G), by_quantile(P, 20), ...
d   = decomp.decompose(P, lab, a)                      # E, A, W, within/across, surrogates, per-group table
keys, M = decomp.partial_sums_all_a(P, decomp.by_order(G))   # T_g(a) for every a (one inverse FFT per group)
al  = decomp.allocation(P, decomp.by_quantile(P, 10), P.worst_a(200))  # share of E per group vs V_g/V and A_g/A

phases.phase_stats(P, a); phases.psi_correlation(P, 12); phases.moments(P)
tr = dynamics.trajectories(G, sets.primes_upto(4*G.m), js, dynamics.log_grid(1e3, 4*G.m, 2000), "log*cesaro")
blocks.block_moments(G, wP, M=G.m**0.5, a=a)

cat = catalogue(G.m, a=a, G=G)                         # name -> Obj(prob, a, desc)
```

What `decompose` reports (E = Σ_g T_g is the sum of real partial sums, with conjugate groups merged):
- A = Σ_χ |t_χ| (the wall: A = |P|(1 − ρ) for the binary prime problem at X = m), and W = Σ_g |T_g|.
- `within` = log(A/W), `across` = log(W/|E|), and `total` = log(A/|E|).
- `W_surr` and `within_surr` come from a surrogate with the same |t_χ| and independent uniform phases (conjugate
  symmetry kept).
- `W_cond` comes from the Gaussian surrogate **conditioned on the observed E**: T_g ~ N(E·V_g/V, V_g(1 − V_g/V)),
  with V_g = Σ_{χ∈g} |t_χ|².
- W/W_cond ≈ 1 and `chi2_dof` ≈ 1 mean that, given its total, the partial sums look like random phases.

## Adding a new set

A set is a float array `w` of length m, indexed by residue. Only units are used, and weights add up within a residue
class.
1. Write a constructor in `sets.py`, e.g. `def my_set(G, ...) -> np.ndarray`. `G.inverse_table()`, `G.units` and
   `prime_mask` are available.
2. Use it directly: `Problem(G, [w, w])` for binary, `Problem(G, [w, w], conj=[False, True])` for the quotient
   problem, `Problem(G, [wP, w])` for bilinear (as for A*), and `Problem(G, [w]*k)` for k-fold.
3. To include it in `compare`/`report`, add a branch and a description in `objects.catalogue`.

## Adding a new decomposition

A grouping is an int array of length φ indexed by flat character index j. Label −1 excludes a character, and
χ0 is always excluded.
1. Write `def by_xxx(G or prob) -> np.ndarray` in `decomp.py`. Character attributes are available as `G.order`,
   `G.conductor`, `G.parity`, `G.jvec` (the index vectors), `G.char_frac(x)` (χ_j(x) as an integer phase mod
   `G.L`), and `G.subgroup_labels(gens)` (labels by restriction to a subgroup).
2. Register it in `make_labels`, and it is then available as `--by xxx` and in `report.groupings`.
3. Conjugate groups are merged automatically (`merge_conj=True`), so that partial sums are real. Keep that unless
   you want the complex coset sums themselves.

## Tests

`python3 tests/test_lab.py` (also runs under pytest). It checks:
- the group structure, i.e. homomorphism, orthogonality, order, parity and conductor, by brute force for 29
  moduli including 2^k, 4·odd, prime powers and squarefree composites;
- N(a) from the character side against direct convolution:
  - binary primes, with weights 1, log, Cesàro and log·Cesàro, at X = m and X > m;
  - the conjugate problem, with N⁻(−1) = #{p + q = m};
  - the smooth toy (four-fold);
  - bilinear problems;
- that every barrier has N(a) = 0, and that A* has N*(a) = #{primes in A*};
- Xie's coset identity Σ_{χ∈C} t_χ(a) = (1/|H|) Σ_{h∈H} N(ah) χ(h), against direct summation over H;
- that the decomposition sums reproduce E(a), together with A ≥ W ≥ |E| and Parseval A = |P|(1 − ρ);
- `partial_sums_all_a` against per-a decompositions;
- agreement with `compute/data/char_small.csv` (from `eos_char.c`) on min N, max|S|/√π and Σ|S|⁴/φ.

## Limits

- Sieve up to X ≈ 2·10⁸ (memory ≈ X bytes).
- m up to about 2·10⁷ is fine in memory, since a complex vector of length φ takes 16 bytes per character.
- `report` holds about 10 Problems at once, which is about 3 GB at m = 10⁷.
- Coset groupings with very many groups are handled per a (bincount). `partial_sums_all_a` is meant for at most a
  few hundred groups.
