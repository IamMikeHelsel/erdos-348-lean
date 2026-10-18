/-
Copyright 2026 Mike Helsel.
Released under the Apache License, Version 2.0; see the LICENSE file.

The definitions `subseqSums'` and `IsAddCompleteNatSeq'` are copied verbatim from
`FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`, and the statement of
`Erdos348.erdos_348` (with `Erdos348.erdos_348.answer`) is copied verbatim from
`FormalConjectures/ErdosProblems/348.lean`, both in google-deepmind/formal-conjectures
(https://github.com/google-deepmind/formal-conjectures, commit
197f7f8dcc457f556754f826389d2ec7a0d85b92; Copyright 2025 The Formal Conjectures Authors,
Apache License 2.0). Only the docstrings were expanded, and the formal-conjectures-specific
`@[category ...]`/`@[AMS ...]` attributes were dropped so that the statement imports only Mathlib.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Data.Finset.Update

/-!
# Erdős Problem 348 (statement)

*References:*
- [erdosproblems.com/348](https://www.erdosproblems.com/348)
- [Ge26] Geneson, J., *Deletion thresholds and exponential examples for complete sequences*.
  [arXiv:2609.25107](https://arxiv.org/abs/2609.25107) (2026), Theorem 1.

This file contains only the statement; the proof is in `Solution.lean`.

Conventions (as in formal-conjectures):
- a sequence is a function `a : ℕ → ℕ`, required to be `Monotone` (non-decreasing), so repeated
  values are allowed;
- deleting the terms with indices in a finite set `s : Finset ℕ` is modelled by
  `Function.updateFinset a s 0`, i.e. the indexed terms `a i` (`i ∈ s`) are replaced by `0`,
  which contributes nothing to any sum; deleting one occurrence of a repeated value leaves the
  other occurrences in place;
- a sequence is complete (`IsAddCompleteNatSeq'`) if every sufficiently large natural number is a
  sum `∑ i ∈ B, a i` over a finite set `B` of indices (each index used at most once), so finitely
  many exceptions are allowed.
-/

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a sequence `A : ℕ → M`: all values `∑ i ∈ B, A i` for a finite set
`B : Finset ℕ` of indices. Each index is used at most once, but different indices may carry the
same value, so repeated values of the sequence may each be used ("repetition is allowed").
The empty set of indices gives `0`.

(Copied verbatim from google-deepmind/formal-conjectures, Apache-2.0.) -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A sequence `A : ℕ → M` is complete if every sufficiently large element of `M` is a subset
sum of `A` in the sense of `subseqSums'`, i.e. `∀ᶠ k in atTop, k ∈ subseqSums' A`. For
`M = ℕ` this says: there is `K` such that every `k ≥ K` equals `∑ i ∈ B, A i` for some finite
set of indices `B`.

(Copied verbatim from google-deepmind/formal-conjectures, Apache-2.0; the upstream docstring reads
"sum of (not necessarily distinct) terms", meaning that terms with equal values at different
indices may both be used.) -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos348

open Erdos348

/-- The answer to Erdős Problem 348: the pairs `(m, n)` of natural numbers with `m < n` and
`m ≤ 1`. -/
def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.

Geneson [Ge26, Theorem 1] proved that the pairs are exactly those with $m \leq 1$.
Completeness allows finitely many exceptions, and deletions remove indexed occurrences.

Formally: the set of pairs `(m, n)` with `m < n` for which there is a monotone `a : ℕ → ℕ` such
that zeroing out any `m` indexed terms leaves a complete sequence, while zeroing out any `n`
indexed terms leaves an incomplete one, equals `erdos_348.answer = {(m, n) | m < n ∧ m ≤ 1}`.
-/
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer := by
  sorry

end Erdos348
