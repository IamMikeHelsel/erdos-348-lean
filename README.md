# Erdős Problem 348 in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib proof of
[Erdős Problem 348](https://www.erdosproblems.com/348), stated exactly as in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/348.lean`), packaged for the
[Palomar registry](https://palomar-registry.org) (Challenge / Solution / Comparator layout).

## The problem

For which pairs $0 \le m < n$ is there a non-decreasing sequence of natural numbers
$a_1 \le a_2 \le \cdots$ which is *complete* (every sufficiently large integer is a sum of
terms with distinct indices) such that

1. the sequence stays complete after deleting **any** $m$ terms, but
2. the sequence is **not** complete after deleting **any** $n$ terms?

J. Geneson, *Deletion thresholds and exponential examples for complete sequences*,
[arXiv:2609.25107](https://arxiv.org/abs/2609.25107) (2026), Theorem 1, proved that such a
sequence exists exactly when $m \le 1$:

* $m = 0$: the powers of two $1, 2, 4, 8, \dots$;
* $m = 1$: the Fibonacci sequence $1, 1, 2, 3, 5, \dots$;
* $m \ge 2$ is impossible: if a sequence survives every deletion of two terms then, for every
  $n$, some deletion of $n$ terms is still complete (Geneson's central-interval theorem and
  extension of complete finite deletions).

## What is proved

[`Challenge.lean`](Challenge.lean) contains only the statement (it imports only Mathlib):

```lean
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer
```

with `erdos_348.answer = {(m, n) | m < n ∧ m ≤ 1}`, in namespace `Erdos348`. The statement and
the definitions `subseqSums'` and `IsAddCompleteNatSeq'` are copied verbatim from
formal-conjectures (commit `197f7f8dcc457f556754f826389d2ec7a0d85b92`, Apache-2.0); only the
docstrings were expanded and the formal-conjectures `@[category ...]` attribute was dropped.

Conventions: sequences are monotone functions `ℕ → ℕ`, so repeated values are allowed;
deleting the indices in a finite set `s` sets those indexed terms to `0`
(`Function.updateFinset a s 0`), so a deletion removes one indexed occurrence and other
occurrences of the same value remain; completeness (`IsAddCompleteNatSeq'`) allows finitely many
exceptions. Geneson states Theorem 1 for non-decreasing integer sequences with the same
occurrence convention; the formal statement is its natural-number case (see
`fidelity.divergences` in [`formalization.yaml`](formalization.yaml)).

[`Solution.lean`](Solution.lean) proves `Erdos348.erdos_348`. Following the Comparator
convention it does not import `Challenge`: it repeats the same definitions and the same theorem
statement (with the same public imports) and supplies the proof. Main components:

* `central`: Geneson's central-interval theorem (Theorem 2), via his states, the two transitions
  and the potential function (Lemmas 6–8);
* `slack_diverges`, `extend_core`, `exists_complete_deletion`: Lemma 3, Lemma 4 and
  Proposition 5, which rule out $m \ge 2$;
* `two_pow_complete`, `two_pow_not_complete`, `fibSeq_one_deletion`, `fibSeq_not_complete`:
  the constructions for $m = 0$ and $m = 1$.

## Building and checking

Requires [elan](https://github.com/leanprover/elan) and, for Comparator,
[bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`). The toolchain is
`leanprover/lean4:v4.35.0` with Mathlib `v4.35.0`.

```sh
lake exe cache get              # download prebuilt Mathlib
lake build Challenge Solution   # Challenge reports its deliberate `sorry`
lake comparator --config comparator.json            # statement match, axioms, kernel replay
lake comparator --config comparator.json --paranoid # also lean4lean, nanoda, con-leche, con-ron
lake check                      # replays the default target (Solution) through the kernel
```

`lake comparator` (built into Lean ≥ 4.35) builds `Challenge` and `Solution` in a sandbox, checks
that `Erdos348.erdos_348` has the same statement in both (including every definition it uses),
that the proof uses only `propext`, `Quot.sound` and `Classical.choice`, and that the kernel
accepts it. Expected output ends with:

```
Lean default kernel accepts the solution
Your solution is okay!
```

To print the axioms directly:

```sh
echo 'import Solution
#print axioms Erdos348.erdos_348' > /tmp/Axioms.lean && lake env lean /tmp/Axioms.lean
# 'Erdos348.erdos_348' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The workflow [`.github/workflows/palomar-preflight.yml`](.github/workflows/palomar-preflight.yml)
runs Palomar's reusable verifier (pinned to a full PalomarSubmission commit) as an advisory
preflight on every push to `main`, using the GitHub-hosted `palomar-standard-v1` execution
profile (Palomar's default profile requires a Namespace runner).

## Palomar entry

One Palomar entry corresponds to [`comparator.json`](comparator.json): the single theorem
`Erdos348.erdos_348` (the full classification of Erdős Problem 348, i.e. Geneson's Theorem 1 in
the formal-conjectures formulation), with permitted axioms `propext`, `Quot.sound` and
`Classical.choice`, and no definition holes. Provenance, sources, automation and review details
are in [`formalization.yaml`](formalization.yaml).

## Attribution

* Mathematics: J. Geneson, arXiv:2609.25107. All credit for the mathematical argument is his.
* Formalization: Mike Helsel. The Lean proof was written by an AI agent (Claude Code, model
  claude-opus-5-5, orchestrated by claude-fable-5-1) and checked by the Lean kernel and
  `lake comparator`; it has not been reviewed line by line by a human.
* Statement and definitions: google-deepmind/formal-conjectures (The Formal Conjectures Authors).
* W. van Doorn posted a Lean formalization (generated by Aristotle, Harmonic) of the set version
  (no repeated values) of Geneson's Proposition 5 at
  <https://github.com/Woett/Lean-files/blob/main/ErdosProblem348.lean>. It was not used here,
  since the formal-conjectures statement allows repeated terms.
* An independent parallel formalization:
  <https://github.com/xccElephant/justin-sun-prize-lean/blob/master/JspBounties/Erdos348.lean>.

## License

Apache License 2.0 (see [LICENSE](LICENSE)), matching formal-conjectures.
