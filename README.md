# Erdős–Odlyzko–Sárközy conjecture (products of two primes)

**Conjecture (EOS, 1987).** For all sufficiently large m and every a with gcd(a, m) = 1,
there exist primes p, q ≤ m with pq ≡ a (mod m).

## Standing assumption
GRH for all Dirichlet L-functions. The claimed proof is in `sources/remark.pdf`
(a Lean-formalized announcement; see https://alpo.ge/remark.pdf). It has **not** been independently
checked here, so every result in this repo is labelled *conditional on GRH*.

## Layout
- `notes/00-setup.md` covers the problem reformulations and the basic barrier computation.
- `notes/lit/` holds the literature review, one file per strand.
- `notes/routes/` holds the attack routes: one file per route, with an honest status.
- `compute/` holds numerical experiments.
- `sources/` holds downloaded references (untrusted inputs).
