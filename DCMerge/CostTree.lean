import DCMerge.Lg

/-!
# Section 2. Cost Trees

A cost tree is a binary tree mirroring the recursive calls of `Merge`. Each node
carries a label `(n, m)` (here: the type indices). An internal node with label
`(n, m)` requires `n ≥ 1` and has children labelled `(⌊n/2⌋, p)` and
`(n - 1 - ⌊n/2⌋, m - p)` for an arbitrary split point `0 ≤ p ≤ m`; its weight is
`lg m`. A leaf with label `(n, m)` has weight `n + m`.
-/

/-- Cost trees with root label `(n, m)` (Figure 2). -/
inductive CostTree : ℕ → ℕ → Type where
  /-- Leaf node (base case), weight `n + m`. -/
  | leaf (n m : ℕ) : CostTree n m
  /-- Internal node (recursive case), weight `lg m`; any split `p ≤ m`, only when `n ≥ 1`. -/
  | node {n m : ℕ} (p : ℕ) (hp : p ≤ m) (hn : 1 ≤ n)
      (l : CostTree (n / 2) p) (r : CostTree (n - 1 - n / 2) (m - p)) : CostTree n m

namespace CostTree

variable {n m : ℕ}

/-- `‖T‖`: the sum of the weights of all nodes of `T`. -/
def weight : {n m : ℕ} → CostTree n m → ℕ
  | _, _, leaf n m => n + m
  | _, m, node _ _ _ l r => lg m + l.weight + r.weight

/-- Total weight of the leaf nodes. -/
def leafWeight : {n m : ℕ} → CostTree n m → ℕ
  | _, _, leaf n m => n + m
  | _, _, node _ _ _ l r => l.leafWeight + r.leafWeight

/-- Total weight of the internal nodes. -/
def internalWeight : {n m : ℕ} → CostTree n m → ℕ
  | _, _, leaf _ _ => 0
  | _, m, node _ _ _ l r => lg m + l.internalWeight + r.internalWeight

/-- Number of internal nodes. -/
def numInternal : {n m : ℕ} → CostTree n m → ℕ
  | _, _, leaf _ _ => 0
  | _, _, node _ _ _ l r => 1 + l.numInternal + r.numInternal

/-- The list of `m_v` labels of the internal nodes `v` at depth `d`.
Its length is `k_d` and its sum is `M_d`. -/
def levelM : {n m : ℕ} → CostTree n m → ℕ → List ℕ
  | _, _, leaf _ _, _ => []
  | _, m, node _ _ _ _ _, 0 => [m]
  | _, _, node _ _ _ l r, d + 1 => l.levelM d ++ r.levelM d

/-- `k_d`, the number of internal nodes at depth `d`. -/
def k (T : CostTree n m) (d : ℕ) : ℕ := (T.levelM d).length

/-- `M_d`, the sum of the `m_v` labels across internal nodes `v` at depth `d`. -/
def M (T : CostTree n m) (d : ℕ) : ℕ := (T.levelM d).sum

end CostTree
