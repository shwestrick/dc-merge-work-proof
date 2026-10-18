# Proof of linear work for parallel divide-and-conquer merge

This repository formalizes the writeup `writeup.pdf` ("A Proof of Linear Work for Parallel
Divide-and-Conquer Merge", S. Westrick) in Lean 4 with Mathlib. It proves every result in the
writeup, and the Lean proofs follow the writeup's proofs step by step. It has no `sorry`, and the
main theorems depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Acknowledgment.** The writeup's proof is derived from a Rocq formalization developed by
Alexandre Moine, Sam Westrick and Joseph Tassarotti as part of their work on verifying the
time complexity of parallel programs:

Alexandre Moine, Sam Westrick, and Joseph Tassarotti. 2026. **[A Separation Logic for
Parallel Time Complexity with Work and Span Credits](https://dl.acm.org/doi/10.1145/3828679).**
*Proc. ACM Program. Lang.* 10, ICFP, Article 281 (Aug. 2026), 30 pages.
[doi:10.1145/3828679](https://doi.org/10.1145/3828679)

The Rocq development is at [github.com/nobrakal/parcas](https://github.com/nobrakal/parcas)
(see `src/examples/merge_work_bound.v`). It proves the linear work bound for a verified
merge implementation, together with functional correctness and a span bound. This repository
came from re-formalizing my own digestion of that proof, assisted by Claude, of course.

## Building

```
lake build
```

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (see `lean-toolchain`, `lakefile.toml`).

## Where each part of the writeup lives

| Writeup | Lean | File |
|---|---|---|
| Notation: `lg` rounded-up log, `lg 0 = 0`; floor division; truncated subtraction | `lg := Nat.clog 2` (`ℕ` division and subtraction are already floor and truncated) | `DCMerge/Lg.lean` |
| §2 cost trees, labels, weights, Figure 2 | `CostTree n m`, `CostTree.weight` (`‖T‖`), `levelM`, `k` (`k_d`), `M` (`M_d`) | `DCMerge/CostTree.lean` |
| §3 leaf weight `= n + m − i` | `leafWeight_add_numInternal` | `DCMerge/Main.lean` |
| §3 `M_d ≤ m`, `k_d ≤ 2^d` | `M_le`, `k_le` | `DCMerge/Main.lean` |
| §3 grouping internal nodes by depth | `internalWeight_eq_sum` | `DCMerge/Main.lean` |
| §3 zero-padded-layer bound `≤ 2^d lg(M_d/2^d) + O(2^d)` | `level_le` | `DCMerge/Main.lean` |
| §3 internal weight is linear | `internalWeight_le` | `DCMerge/Main.lean` |
| **Theorem 2.1** | `theorem_2_1` (`‖T‖ ≤ 11n + 5m + 7`), `theorem_2_1_bigO` (`∃ C, ∀ T, ‖T‖ ≤ C(n+m)`, with `C = 18`) | `DCMerge/Main.lean` |
| **Lemma 4.1** (even spreading), with `O(k) = 3k` | `EvenSpreading.lemma_4_1` | `DCMerge/EvenSpreading.lean` |
| Lemma 4.1 proof: replace zeros by ones / per-element rounding / the maximization process | `lemma_4_1` steps 1–4, `sum_lg_le_lg_prod`, `prod_le_balanced` | `DCMerge/EvenSpreading.lean` |
| **Lemma 5.1**, and the exact identity `∑ i 2^(k−i) = 2^(k+1) − k − 2` | `LevelSum.lemma_5_1`, `LevelSum.sum_eq` | `DCMerge/LevelSum.lean` |
| **Lemma 5.2**, with `O(n+m) = 4n + 4m + 3` | `LevelSum.lemma_5_2` | `DCMerge/LevelSum.lean` |
| Figure 1 `Merge` (not formalized in the writeup) | `merge`, `merge_work_is_cost_tree`, `merge_work_le` | `DCMerge/Merge.lean` |

### How closely the proofs follow the writeup

- **Lemma 5.1**: induction on `k`, proving the exact identity, as in the writeup.
- **Lemma 5.2**: the same proof. It uses `lg(m/2^d) ≤ B − d`, splits on `D > B` or `D ≤ B`,
  drops the zero terms and reindexes `i = B − d` (lemma `reindex`), and in the second case splits
  `B − d = (B − D) + (D − d)` and uses `x ≤ 2^x`. It reaches the writeup's intermediate bounds
  `4m + 2`, `2m + 1` and `4n + 2` exactly.
- **Lemma 4.1**: the four steps of the proof sketch, in order. The "maximization process" is
  formalized literally. In `prod_le_balanced`, if the largest and smallest elements differ by two
  or more, one unit moves from the larger to the smaller. This keeps the length and the total,
  does not decrease the product, and strictly decreases the sum of squares, which is the
  induction measure. When no such pair exists, every element is at most `⌊S/k⌋ + 1`.
- **Theorem 2.1 / §3**: split into leaves and internal nodes, group the internal nodes by depth,
  pad each level with zeros to `2^d` elements, apply Lemma 4.1, use `M_d ≤ m`, sum the `O(2^d)`
  terms, and apply Lemma 5.2.
- `DCMerge/Merge.lean` is extra. It implements Figure 1 with a work counter and proves that every
  run's work is the weight of some cost tree. This turns §2's informal sentence "each cost tree
  corresponds to a run of Merge" into a theorem, so Theorem 2.1 bounds the work of `merge`.

## Accuracy of the writeup

Out of curiosity, I asked Claude to review the writeup and check how faithful it is
to the formalization. Here's Claude's review:

1. **Off-by-one in the range of levels (a real error, but harmless asymptotically).** Section 3
   says that "the tree has height `lg n`" and bounds the internal nodes by summing over
   `d < lg n` (Lemma 5.2's index set). With the writeup's convention that `lg` is the rounded-up
   logarithm, this misses the deepest level whenever `n` is a power of two:
   - `n = 1`: the root `(1, m)` can be internal, with weight `lg m`, but `∑_{d < lg 1}` is empty.
   - `n = 2`: the root `(2, m)` has an internal child `(1, p)` at depth `1 = lg 2`.

   In general an internal node at depth `d` has `1 ≤ n_v ≤ ⌊n/2^d⌋`, so internal nodes occur at
   every depth up to `⌊log₂ n⌋`, and `⌊log₂ n⌋ = lg n` when `n` is a power of two. The correct
   range is `d < lg(n + 1)` (`= ⌊log₂ n⌋ + 1` for `n ≥ 1`). The formalization uses that range
   (`internalWeight_eq_sum`, `child_lg_le`). It then applies Lemma 5.2, which is correct as
   stated, to `n + 1` in place of `n`. Only the constants change.

2. **Lemma 4.1 proof sketch: small gaps.**
   - The sketch does not say why the maximization process terminates. A potential such as the
     sum of squares is needed. The formalization uses it.
   - After zeros are replaced by ones, the total is up to `M + k`. So "within one of the
     average" means each element is at most `M/k + 2`, not `M/k + 1`. This is still `O(1)`, as
     the sketch says.
   - `lg(M/k + O(1)) = lg(M/k) + O(1)` also needs the case `M/k = 0`. It holds because
     `lg 0 = 0`.
   - The statement leaves `M/k` undefined for `k = 0`. In Lean `M/0 = 0`, and the case is trivial.

3. **The cost model charges nothing for the constant work at internal nodes.** An internal
   node's weight is `lg m`. This is `0` for `m ≤ 1`, and nothing is charged for computing `i`,
   writing `A[i]` to the output, or spawning the two calls. Also, a real binary search over `m`
   elements uses about `lg(m + 1)` comparisons, which can be `lg m + 1`. This does not affect
   the result, because there are at most `n` internal nodes (`numInternal_le`). We prove the
   strengthened bound `‖T‖ + #internal ≤ 12n + 5m + 7` (`weight_add_numInternal_le`), which
   charges one extra unit per internal node.

4. **"Each cost tree corresponds to a run of Merge" is informal in the writeup.** `Merge.lean`
   proves that the work of the implemented `merge` is a cost-tree weight. Its limits:
   - The binary search is modeled: the split point is `countP (· < A[i]) B`, which equals the
     binary-search result on sorted `B`, and the step is charged `lg |B|`. No binary-search code
     is implemented.
   - The output of `merge` is not proven correct (sorted, a permutation of the inputs). The
     writeup does not claim this either.

5. **Constants.** The writeup states only `O(·)` bounds. It says the authors' own Lean
   mechanization tracks constant factors, but that mechanization is not included, so we could
   not compare against it. Our explicit constants are `‖T‖ ≤ 11n + 5m + 7 ≤ 18(n + m)`. These
   come from our choices: `3k` in Lemma 4.1 (hence `3·2^d` per level) and `4n + 4m + 3` in
   Lemma 5.2.

Claims we checked and found correct as stated:
- the leaf total is exactly `n + m − i`;
- `M_d ≤ m` and `k_d ≤ 2^d`;
- padding each level with `m_v = 0` leaves both `∑ lg m_v` and `M_d` unchanged (since `lg 0 = 0`),
  so Lemma 4.1 applies to the padded level with `M = M_d` directly;
- the exact identity in Lemma 5.1;
- every inequality in the proof of Lemma 5.2, including `2^B ≤ 2m + 1` and `2^(B+1) ≤ 4m + 2`.

## Token cost

This repository was produced with Claude Code using `claude-opus-5-5` (1M context), with no
subagents. Total token usage, measured from the session transcript just before the final commit:

| | Tokens | Rate (USD / MTok) | Cost |
|---|---:|---:|---:|
| Input (uncached) | 130 | $4.00 | $0.00 |
| Output (incl. thinking) | 82,035 | $20.00 | $1.64 |
| Cache writes (5-minute TTL) | 351,739 | $5.00 | $1.76 |
| Cache writes (1-hour TTL) | 0 | $8.00 | $0.00 |
| Cache reads | 9,151,375 | $0.20 | $1.83 |
| **Total** (65 API calls) | 9,585,279 | | **$5.23** |

The prices are first-party Anthropic API list prices for Claude Opus 5.5, with no long-context
premium. The total is what this usage would cost at those prices. It is not an invoice.
