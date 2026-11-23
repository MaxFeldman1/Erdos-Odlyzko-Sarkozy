"""Cross-checks for phaselab. Run:  cd compute/lab && python3 tests/test_lab.py   (or pytest, if installed).

Every character-side quantity is compared with direct counting on small moduli, covering prime, prime-power,
2-power and mixed non-cyclic groups.
"""
from __future__ import annotations

import csv
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from phaselab import UnitGroup, Problem, sets, decomp, phases  # noqa: E402

MODULI = [3, 4, 5, 8, 9, 12, 16, 24, 25, 27, 32, 45, 60, 64, 97, 100, 105, 120, 121, 128, 210, 243, 360,
          401, 720, 1001, 1024, 1155, 2310]


def brute_count(m, factors, conj=None):
    """N(a) by direct convolution over residues (O(m^2) per factor)."""
    conj = conj or [False] * len(factors)
    N = np.zeros(m)
    N[1 % m] = 1.0
    inv = [0] * m
    for x in range(m):
        if math.gcd(x, m) == 1:
            inv[x] = pow(x, -1, m)
    for w, c in zip(factors, conj):
        new = np.zeros(m)
        for b in np.nonzero(N)[0]:
            for x in np.nonzero(w)[0]:
                if math.gcd(int(x), m) != 1:
                    continue
                y = inv[x] if c else x
                new[(b * y) % m] += N[b] * w[x]
        N = new
    return N


def test_group_structure():
    for m in MODULI:
        G = UnitGroup(m)
        assert G.phi == sum(1 for x in range(m) if math.gcd(x, m) == 1)
        # chi_j is a homomorphism and the j-grid is the full dual
        xs = G.units[:5]
        for x in xs:
            for y in xs:
                lhs = G.chi(int(x * y % m))
                rhs = G.chi(int(x)) * G.chi(int(y))
                assert np.allclose(lhs, rhs)
        # orthogonality: sum_x chi_j(x) = phi [j = 0]
        tot = sum(G.chi(int(x)) for x in G.units)
        assert abs(tot[0] - G.phi) < 1e-8 and np.abs(tot[1:]).max() < 1e-6
        # order and parity, by brute force
        vals = np.array([G.chi(int(x)) for x in G.units])     # (phi_x, phi_j)
        for j in range(G.phi):
            o = G.order[j]
            assert np.allclose(vals[:, j] ** o, 1) and all(not np.allclose(vals[:, j] ** d, 1)
                                                            for d in range(1, o) if o % d == 0)
        assert np.allclose(G.parity, G.chi(m - 1).real)
        # conductor: smallest d | m with chi trivial on {x = 1 mod d}
        divs = [d for d in range(1, m + 1) if m % d == 0]
        for j in range(G.phi):
            f = next(d for d in divs if all(abs(vals[i, j] - 1) < 1e-9
                                            for i, x in enumerate(G.units) if x % d == 1 % d))
            assert G.conductor[j] == f, (m, j, G.conductor[j], f)
        # inverse table
        inv = G.inverse_table()
        assert all((x * inv[x]) % m == 1 for x in G.units)


def test_binary_primes_vs_direct():
    for m in MODULI:
        G = UnitGroup(m)
        for X, weight in [(m, "1"), (m, "log"), (m, "cesaro"), (3 * m + 7, "1"), (2.5 * m, "log*cesaro")]:
            w = sets.prime_weights(m, X, weight)
            pr = Problem(G, [w, w])
            Nd = brute_count(m, [w, w])
            assert np.allclose(pr.N_res()[G.units], Nd[G.units], atol=1e-6 * (1 + Nd.max())), (m, X, weight)
            # Parseval
            assert np.isclose((np.abs(pr.spectra[0]) ** 2).sum() / G.phi, (w[G.units] ** 2).sum())


def test_conjugate_and_toy_and_bilinear():
    rng = np.random.default_rng(1)
    for m in [45, 97, 105, 128, 401, 1155]:
        G = UnitGroup(m)
        wP = sets.prime_weights(m)
        cj = Problem(G, [wP, wP], conj=[False, True])
        assert np.allclose(cj.N_res()[G.units], brute_count(m, [wP, wP], [False, True])[G.units], atol=1e-6)
        if m % 2:
            # N^-(-1) = #{p + q = m} (as residues p, q < m)
            direct = sum(1 for p in np.nonzero(wP)[0] if wP[m - p] > 0)
            assert round(cj.N(m - 1)) == direct
        wI = sets.integer_weights(m, math.isqrt(m))
        toy = Problem(G, [wI] * 4)
        assert np.allclose(toy.N_res()[G.units], brute_count(m, [wI] * 4)[G.units], atol=1e-6 * toy.main)
        wR = sets.random_subset(G, 0.2, rng)
        bl = Problem(G, [wP, wR])
        assert np.allclose(bl.N_res()[G.units], brute_count(m, [wP, wR])[G.units], atol=1e-6)


def test_barriers_vanish_at_a():
    rng = np.random.default_rng(2)
    for m in [97, 401, 1155, 2310, 4096 + 3, 10007]:
        G = UnitGroup(m)
        wP = sets.prime_weights(m)
        for a in [1, m - 1, 2, int(G.units[len(G.units) // 2])]:
            if math.gcd(a, m) != 1:
                continue
            for w in (sets.redacted(G, wP, a), sets.redacted_half(G, wP, a),
                      sets.pairing_avoiding(G, a, 0.1, rng)):
                assert abs(Problem(G, [w, w]).N(a)) < 1e-6
            if m > 1000:
                wS, A = sets.astar(G, wP, a, rng=rng, return_A=True)
                isp = sets.prime_mask(m)
                assert abs(Problem(G, [wP, wS]).N(a) - isp[A].sum()) < 1e-6


def test_coset_identity_and_decomposition():
    """Coset sum of chi H^perp at a equals (1/|H|) sum_{h in H} N(ah) chi(h)."""
    for m, spec in [(97, "pow:4"), (401, "pow:8"), (1155, "pow:2"), (1155, "mod:35"), (720, "mod:16"),
                    (2310, "pow:3"), (1024, "pow:4")]:
        G = UnitGroup(m)
        wP = sets.prime_weights(m)
        pr = Problem(G, [wP, wP])
        gens, order = G.subgroup_gens(spec)
        lab = G.subgroup_labels(gens)
        Hsize = np.unique(lab).size
        if order is not None:
            assert Hsize == order
        # enumerate H
        H = {1}
        frontier = [1]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = x * g % m
                if y not in H:
                    H.add(y)
                    frontier.append(y)
        assert len(H) == Hsize
        Nres = pr.N_res()
        for a in [1, 2, m - 1]:
            if math.gcd(a, m) != 1:
                continue
            t = pr.terms(a)
            for k in np.unique(lab)[:6]:
                j = int(np.nonzero(lab == k)[0][0])
                coset_sum = t[lab == k].sum()
                direct = sum(Nres[a * h % m] * G.chi(h)[j] for h in H) / Hsize
                assert abs(coset_sum - direct) < 1e-8 * (1 + abs(direct)), (m, spec, a, k)
            for by in ["order", "conductor", "parity", "quantile:5", "coset:" + spec]:
                d = decomp.decompose(pr, decomp.make_labels(pr, by), a, n_surr=2)
                assert abs(d["E"] - pr.E(a)) < 1e-8 * (1 + abs(pr.main))
                assert d["imag_residual"] < 1e-8 * (1 + pr.main)
                assert d["A"] >= d["W"] - 1e-9 >= abs(d["E"]) - 2e-9
        # Parseval wall: A = |P|(1 - rho) exactly for the binary prime problem at X <= m
        P = wP[G.units].sum()
        assert np.isclose(pr.parseval_mass(), P * (1 - P / G.phi))


def test_all_a_partial_sums():
    for m in [401, 1155]:
        G = UnitGroup(m)
        wP = sets.prime_weights(m)
        pr = Problem(G, [wP, wP])
        keys, M = decomp.partial_sums_all_a(pr, decomp.by_order(G))
        assert np.allclose(M.sum(axis=0), pr.N_flat() - pr.main)
        a = 13
        d = decomp.decompose(pr, decomp.by_order(G), a, n_surr=0)
        assert np.allclose(M[:, G.flat_of_res[a]], d["groups"]["T"])


def test_phase_stats():
    G = UnitGroup(401)
    wP = sets.prime_weights(401)
    pr = Problem(G, [wP, wP])
    ps = phases.phase_stats(pr, 5)
    # weighted first harmonic is exactly E/A
    assert np.isclose(ps["c_w"][0], pr.E(5) / pr.parseval_mass())


def test_against_eos_char_csv():
    """Reproduce compute/data/char_small.csv (written by compute/src/eos_char.c) for some primes."""
    path = os.path.join(HERE, "..", "..", "data", "char_small.csv")
    if not os.path.exists(path):
        print("  (char_small.csv not found; skipped)")
        return
    want = {401, 1009, 4001, 10007, 19997}
    with open(path) as f:
        rows = [r for r in csv.DictReader(f) if int(r["m"]) in want]
    assert rows
    for r in rows:
        m = int(r["m"])
        G = UnitGroup(m)
        wP = sets.prime_weights(m)
        pr = Problem(G, [wP, wP])
        N = pr.N_flat()
        assert int(round(N.min())) == int(float(r["minN"]))
        S = pr.spectra[0]
        pi = int(r["pi"])
        assert np.isclose(np.abs(S[1:]).max() / math.sqrt(pi), float(r["maxS_over_sqrtpi"]), atol=1e-5)
        assert np.isclose((np.abs(S) ** 4).sum() / G.phi, float(r["E"]), rtol=1e-7)


def _run_all():
    tests = [(k, v) for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for name, fn in tests:
        fn()
        print(f"ok  {name}")
    print(f"{len(tests)} tests passed")


if __name__ == "__main__":
    _run_all()
