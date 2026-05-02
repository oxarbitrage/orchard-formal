import Orchard.Spec

namespace Orchard

/-! # Merkle path verification

Orchard uses a depth-32 Merkle tree of note commitments. Membership
is proved by an authentication path: a sequence of sibling hashes
and direction bits that reconstruct the root from a leaf.

The Merkle CRH is Sinsemilla in the actual protocol. We abstract the
hash function and prove structural properties of path verification.

See §4.1.7 of the Zcash protocol specification.
-/

open Pasta

noncomputable section

/-! ## Merkle hash abstraction -/

/-- The Merkle hash function, combining two children into a parent.
In Orchard this is `SinsemillaHash("z.cash:Orchard-MerkleCRH", l ‖ r)`.
We axiomatize it as an opaque function. -/
axiom merkleHash (layer : ℕ) (left right : Pasta.Fp) : Pasta.Fp

/-! ## Merkle tree -/

/-- A binary Merkle tree of a given depth. -/
inductive MerkleTree : ℕ → Type where
  | leaf : Pasta.Fp → MerkleTree 0
  | node {d : ℕ} : MerkleTree d → MerkleTree d → MerkleTree d.succ

/-- The root hash of a Merkle tree. -/
def MerkleTree.root {d : ℕ} : MerkleTree d → Pasta.Fp
  | .leaf v => v
  | @MerkleTree.node d' l r => merkleHash d' l.root r.root

/-- Membership: a value exists as a leaf in the tree. -/
def MerkleTree.member (v : Pasta.Fp) {d : ℕ} : MerkleTree d → Prop
  | .leaf w => v = w
  | .node l r => l.member v ∨ r.member v

/-! ## Authentication path -/

/-- A Merkle authentication path as a list of sibling-position pairs. -/
abbrev AuthPath := List (Pasta.Fp × Bool)

/-- Verify an authentication path from leaf to root.
At each layer, the position bit determines child ordering. -/
def verifyPath : AuthPath → Pasta.Fp → ℕ → Pasta.Fp
  | [], current, _ => current
  | (sibling, pos) :: rest, current, layer =>
    let parent := if pos then merkleHash layer sibling current
                  else merkleHash layer current sibling
    verifyPath rest parent (layer + 1)

/-- Verify starting from layer 0. -/
def verifyPathFromLeaf (path : AuthPath) (leaf : Pasta.Fp) : Pasta.Fp :=
  verifyPath path leaf 0

/-- A path is valid if verification reaches the claimed root. -/
def validPath (path : AuthPath) (leaf root : Pasta.Fp) : Prop :=
  verifyPathFromLeaf path leaf = root

/-! ## Properties -/

/-- **Path verification is deterministic**: same inputs → same output. -/
theorem verifyPath_deterministic (path : AuthPath) (leaf : Pasta.Fp) :
    verifyPathFromLeaf path leaf = verifyPathFromLeaf path leaf := rfl

/-- **Unique root**: if a path validates against two roots, they must be equal. -/
theorem path_unique_root (path : AuthPath) (leaf r₁ r₂ : Pasta.Fp)
    (h₁ : validPath path leaf r₁) (h₂ : validPath path leaf r₂) :
    r₁ = r₂ := by
  unfold validPath at h₁ h₂
  rw [← h₁, ← h₂]

/-- **Empty path**: with no siblings, the leaf is the root. -/
theorem verifyPath_nil (leaf : Pasta.Fp) (layer : ℕ) :
    verifyPath [] leaf layer = leaf := by
  unfold verifyPath; rfl

/-- A leaf is always a member of itself. -/
theorem member_leaf (v : Pasta.Fp) :
    MerkleTree.member v (MerkleTree.leaf v) := rfl

/-- Membership in a node means membership in a subtree. -/
theorem member_node_left {d : ℕ} (v : Pasta.Fp)
    (l r : MerkleTree d) (h : l.member v) :
    (MerkleTree.node l r).member v :=
  Or.inl h

/-- Membership in a node means membership in a subtree. -/
theorem member_node_right {d : ℕ} (v : Pasta.Fp)
    (l r : MerkleTree d) (h : r.member v) :
    (MerkleTree.node l r).member v :=
  Or.inr h

/-- The root of a leaf tree is the leaf value. -/
theorem root_leaf (v : Pasta.Fp) :
    (MerkleTree.leaf v).root = v := by
  unfold MerkleTree.root; rfl

/-- The root of a node is the hash of its children's roots. -/
theorem root_node {d : ℕ} (l r : MerkleTree d) :
    (MerkleTree.node l r).root = merkleHash d l.root r.root := by
  simp only [MerkleTree.root]

/-! ## Collision resistance -/

/-- **Merkle collision resistance (axiom)**: if two different (left, right)
pairs at the same layer produce the same hash, a hash collision exists.
This is the standard assumption for Merkle tree security. -/
axiom merkleHash_collision_resistant (layer : ℕ)
    (l₁ r₁ l₂ r₂ : Pasta.Fp)
    (h : merkleHash layer l₁ r₁ = merkleHash layer l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂

/-- **Root determines leaves (depth 0)**: equal leaf roots imply equal values. -/
theorem leaf_root_injective (v₁ v₂ : Pasta.Fp)
    (h : (MerkleTree.leaf v₁).root = (MerkleTree.leaf v₂).root) :
    v₁ = v₂ := by
  rw [root_leaf, root_leaf] at h; exact h

/-- Under collision resistance, a node's root determines both children's roots. -/
theorem node_root_injective {d : ℕ}
    (l₁ r₁ l₂ r₂ : MerkleTree d)
    (h : (MerkleTree.node l₁ r₁).root = (MerkleTree.node l₂ r₂).root) :
    l₁.root = l₂.root ∧ r₁.root = r₂.root := by
  rw [root_node, root_node] at h
  exact merkleHash_collision_resistant d l₁.root r₁.root l₂.root r₂.root h

end

end Orchard
