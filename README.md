# orchard-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of Zcash's Orchard shielded protocol, composing formalized primitives for Poseidon hashing, Sinsemilla commitments, and RedPallas signatures into machine-verified proofs of the protocol's core security properties.

## Overview

Orchard is Zcash's third-generation shielded payment pool, introduced in the NU5 network upgrade. It replaces Sapling's Jubjub-based design with Pallas/Vesta cycle arithmetic, enabling efficient recursive proof composition via Halo 2. An Orchard transaction consists of one or more *actions*, each of which simultaneously spends a shielded note and creates a new one, bound together by a single binding signature that proves the net value flows are balanced.

This formalization covers the algebraic and protocol layer of Orchard — not the arithmetic circuit constraints, but the mathematical objects and properties that the circuit is designed to enforce. The five main security areas addressed are: value commitments (Pedersen homomorphism and balance), nullifier derivation (double-spend prevention), note commitments (binding to note content), Diffie-Hellman key agreement (note encryption), and Merkle tree membership (note commitment tree authentication paths).

All definitions and theorems live under the `Orchard` namespace. The formalization composes `poseidon-formal` (for the nullifier's `PoseidonHash`), `redpallas-formal` (for scalar multiplication on Pallas, the `BindingG` generator, and the RedDSA verification equation), and `sinsemilla-formal` (axiomatized here as `noteCommitHash` and `merkleHash` — the Sinsemilla operations used for note commitments and Merkle tree hashing). No `sorry` placeholder is used anywhere in the project source.

## Protocol Components

### Value Commitments

Each Orchard action carries a value commitment `cv = [v]·ValueBaseV + [rcv]·BindingG`, a Pedersen commitment over the Pallas curve using two independent generators. The scheme is additively homomorphic: `cv₁ + cv₂ = valueCommit(v₁+v₂, rcv₁+rcv₂)`. This homomorphism is the algebraic foundation of balance verification — the verifier computes `Σ cv_in - Σ cv_out` without learning any individual values, and a valid binding signature (whose verification key is exactly that net commitment) proves the signer knows the net randomness `rcv_net`, which together with range proofs in the circuit establishes `v_net = 0`.

### Nullifiers

The nullifier for a note is `nf = [PoseidonHash(nk, ρ) + ψ]·K + cm`, where `nk` is the nullifier key, `ρ` and `ψ` are per-note field elements, `K` is the nullifier base point, and `cm` is the note commitment. Spending a note requires revealing `nf` publicly; the nullifier set prevents double-spending without revealing which note was spent. The key property — distinct note commitments produce distinct nullifiers (for fixed `nk`, `ρ`, `ψ`) — is proven directly from the group cancellation law. Full collision resistance under varying `ψ` reduces to the discrete logarithm problem on `K`.

### Note Commitments

A note commitment is `cm = noteCommitHash(note) + [rcm]·NoteCommitR`, where `noteCommitHash` is a Sinsemilla-based hash of the note's fields (`g_d`, `pk_d`, `v`, `rho`, `psi`) and `NoteCommitR` is an independent randomness generator. This Pedersen-blinded structure makes commitments hiding and binding: for a fixed note, equal commitments imply equal randomness blinding at the group level.

### DH Key Agreement

Orchard uses diversified Diffie-Hellman key agreement on the Pallas curve for note encryption. The sender derives a diversified public key as `pk_d = [ivk]·g_d` and computes the shared secret as `[esk]·pk_d`. The recipient computes `[ivk]·epk` where `epk = [esk]·g_d` is the ephemeral public key. The shared secret is identical in both cases by commutativity of scalar multiplication: `[esk]·[ivk]·g_d = [ivk]·[esk]·g_d`.

### Merkle Tree Membership

The Orchard note commitment tree is a depth-32 binary Merkle tree whose internal nodes are hashed with `SinsemillaHash("z.cash:Orchard-MerkleCRH", l ‖ r)`. An authentication path is a list of `(sibling, position_bit)` pairs that, given a leaf, reconstruct the root layer by layer. Under collision resistance of `merkleHash`, the root determines both children's roots at every level, making the root a binding digest of the entire tree.

### Action Circuit

Each Orchard action proves three things simultaneously: (1) the value commitment `cv` is correctly formed from the note value and randomness; (2) the nullifier `nf` is correctly derived from the nullifier key, per-note randomness, and the note commitment; (3) the note commitment appears in the commitment tree, authenticated by a valid Merkle path. The action satisfaction predicate `actionSatisfied` captures all three checks, and soundness and anti-double-spend properties follow from the component theorems.

## Formalization

### `Orchard/Spec.lean`

Defines the core protocol objects and functions:

- `ValueBaseV : Pallas.toAffine.Point` — value commitment generator (axiom)
- `K : Pallas.toAffine.Point` — nullifier base point (axiom)
- `NoteCommitR : Pallas.toAffine.Point` — note commitment randomness generator (axiom)
- `noteCommitHash : Note → Pallas.toAffine.Point` — Sinsemilla-based note commitment hash (axiom)
- `valueCommit (v rcv : Fq) : Point` — `[v]·ValueBaseV + [rcv]·BindingG`
- `deriveNullifier (nk rho psi : Fp) (cm : Point) : Point` — `[PoseidonHash(nk, rho) + psi]·K + cm`
- `noteCommit (note : Note) (rcm : Fq) : Point` — `noteCommitHash note + [rcm]·NoteCommitR`
- `Note` structure with fields `g_d`, `pk_d`, `v`, `rho`, `psi`

Imports: `Poseidon.Spec`, `RedPallas.Spec`, `RedPallas.ScalarMul`.

### `Orchard/Properties.lean`

Contains all ~38 machine-verified theorems, organized by category.

**Value Commitment Homomorphism:**
- `valueCommit_add` — `valueCommit v₁ rcv₁ + valueCommit v₂ rcv₂ = valueCommit (v₁+v₂) (rcv₁+rcv₂)`
- `valueCommit_zero` — `valueCommit 0 0 = 0`
- `valueCommit_neg` — `valueCommit (-v) (-rcv) = -valueCommit v rcv`
- `valueCommit_sub` — subtraction distributes over both arguments
- `valueCommit_sum` — finite-sum homomorphism over any index type

**Balance Verification:**
- `balance_single` — single action: `cv_in - cv_out = valueCommit (v_in - v_out) (rcv_in - rcv_out)`
- `balanced_bvk` — balanced case: `valueCommit 0 rcv = [rcv]·BindingG`
- `balance_multi` — multi-action: `Σ cv_in - Σ cv_out = valueCommit (Σv_in - Σv_out) (Σrcv_in - Σrcv_out)`
- `balance_multi_binding` — balanced multi-action: net commitment = `[(Σrcv_in - Σrcv_out)]·BindingG`

**Nullifier Security:**
- `deriveNullifier_deterministic` — same inputs always produce the same nullifier
- `nullifier_binding` — equal nullifiers (same `nk`, `rho`, `psi`) imply equal note commitments
- `nullifier_psi_collision` — collision under different `ψ` reduces to scalar collision on `K`
- `nullifier_uniqueness` — distinct note commitments produce distinct nullifiers (main double-spend theorem)
- `note_nullifier_binding` — equal nullifiers from committed notes imply equal commitments

**Note Commitments:**
- `noteCommit_binding` — same note, equal commitments imply equal randomness blinding

**Binding Signature:**
- `binding_sig_verify` — RedDSA verification equation holds for `BindingG` and `rcv_net`
- `balance_binding_sig` — balanced `valueCommit 0 rcv_net` satisfies the binding signature check

**Composite Results:**
- `spend_auth_balance` — balanced tx: net commitment = `[(rcv_in - rcv_out)]·BindingG`
- `spend_authorization` — balance integrity ∧ binding signature ∧ nullifier uniqueness in one theorem

### `Orchard/KeyAgreement.lean`

Formalizes Orchard's diversified DH key agreement (§5.4.5.3):

- `derivePublicKey (ivk : Fq) (g_d : Point) : Point` — `[ivk]·g_d`
- `ephemeralKey (esk : Fq) (g_d : Point) : Point` — `[esk]·g_d`
- `keyAgreement (esk : Fq) (pk_d : Point) : Point` — `[esk]·pk_d`

Key theorems:
- `dh_shared_secret` — `[esk]·([ivk]·g_d) = [ivk]·([esk]·g_d)`: machine-verified commutativity guaranteeing sender and recipient derive the same shared secret
- `keyAgreement_eq_mul` — `keyAgreement esk (derivePublicKey ivk g_d) = [esk * ivk]·g_d`
- `recipient_recovers` — `[ivk]·epk = [esk]·pk_d`
- `keyAgreement_zero_key` — `keyAgreement 0 pk_d = 0`
- `keyAgreement_add_key` — distributes over key addition

### `Orchard/MerklePath.lean`

Formalizes the Orchard note commitment tree (§4.1.7):

- `merkleHash (layer : ℕ) (left right : Fp) : Fp` — Sinsemilla-based Merkle CRH (axiom)
- `MerkleTree : ℕ → Type` — depth-indexed binary tree (`leaf` | `node`)
- `MerkleTree.root` — computes the root hash recursively
- `MerkleTree.member` — leaf membership predicate
- `verifyPath : AuthPath → Fp → ℕ → Fp` — reconstructs root from leaf via authentication path
- `validPath path leaf root` — path verification predicate
- `merkleHash_collision_resistant` — standard collision-resistance assumption (axiom)

Key theorems:
- `path_unique_root` — a path and leaf determine the root uniquely
- `node_root_injective` — under collision resistance, equal node roots imply equal left and right child roots
- `leaf_root_injective` — equal leaf roots imply equal leaf values
- `member_leaf`, `member_node_left`, `member_node_right` — structural membership lemmas

### `Orchard/ActionCircuit.lean`

Formalizes the Orchard action satisfaction predicate (§4.17.4):

- `commitToLeaf : Point → Fp` — note commitment to Merkle leaf (x-coordinate; axiom)
- `ActionStatement` — public inputs: `nf`, `cv`, `cmRoot`
- `ActionWitness` — private witness: `note`, `rcm`, `rcv`, `nk`, `authPath`
- `actionSatisfied stmt wit` — `cv` correct ∧ `nf` correct ∧ Merkle membership

Key theorems:
- `action_cv_correct` — satisfied action's public `cv` equals `valueCommit note.v rcv`
- `action_nf_correct` — satisfied action's public `nf` equals `deriveNullifier nk rho psi cm`
- `action_membership` — satisfied action's commitment is in the tree
- `action_no_double_spend` — two satisfied actions with equal nullifiers (same `nk`, `rho`, `psi`) must spend equal note commitments

## Key Results

### 1. Nullifier Uniqueness (`nullifier_uniqueness`)

For fixed nullifier key `nk`, rho `ρ`, and `ψ`, any two distinct note commitments `cm₁ ≠ cm₂` produce distinct nullifiers: `deriveNullifier nk ρ ψ cm₁ ≠ deriveNullifier nk ρ ψ cm₂`. This is the formal proof of double-spend prevention at the algebraic level: because the nullifier formula is `[PoseidonHash(nk,ρ)+ψ]·K + cm`, injectivity in `cm` follows directly from group cancellation (`add_left_cancel`). Spending a note reveals `nf` but not `cm`, achieving unlinkability while preventing reuse.

### 2. Multi-Action Balance (`balance_multi_binding`)

For `n` balanced actions (where `Σ v_in_i = Σ v_out_i`), the net value commitment satisfies:

```
Σ valueCommit(v_in_i, rcv_in_i) - Σ valueCommit(v_out_i, rcv_out_i)
  = [(Σ rcv_in_i - Σ rcv_out_i)] · BindingG
```

This is the algebraic foundation for the binding signature in multi-action transactions: the binding verification key is exactly the net randomness commitment, and a valid signature proves knowledge of `rcv_net = Σ rcv_in_i - Σ rcv_out_i`.

### 3. DH Shared Secret (`dh_shared_secret`)

Machine-verified commutativity of Pallas scalar multiplication:

```
keyAgreement esk (derivePublicKey ivk g_d) = keyAgreement ivk (ephemeralKey esk g_d)
```

that is, `[esk]·([ivk]·g_d) = [ivk]·([esk]·g_d)`. Proved via `fqSmul_mul` (associativity of scalar multiplication) and `mul_comm` in `Fq`. This guarantees sender and recipient always derive the same shared secret.

### 4. Merkle Root Injectivity (`node_root_injective`)

Under the `merkleHash_collision_resistant` axiom, equal roots of depth-`d+1` trees imply equal roots of both subtrees:

```
(MerkleTree.node l₁ r₁).root = (MerkleTree.node l₂ r₂).root →
  l₁.root = l₂.root ∧ r₁.root = r₂.root
```

This propagates inductively: the root is a binding digest of the entire tree structure.

### 5. Action Double-Spend Prevention (`action_no_double_spend`)

In two satisfied Orchard actions sharing the same nullifier key `nk`, rho, and `ψ`, equal public nullifiers imply equal note commitments:

```
actionSatisfied stmt₁ wit₁ → actionSatisfied stmt₂ wit₂ →
  stmt₁.nf = stmt₂.nf → wit₁.nk = wit₂.nk → wit₁.note.rho = wit₂.note.rho →
  wit₁.note.psi = wit₂.note.psi →
    noteCommit wit₁.note wit₁.rcm = noteCommit wit₂.note wit₂.rcm
```

This is the circuit-level anti-double-spend theorem: the action circuit cannot be satisfied twice for different notes with the same nullifier.

## Axioms

| Axiom | File | Justification |
|-------|------|---------------|
| `ValueBaseV` | Spec.lean | Value commitment generator (certified parameter, hash-to-curve) |
| `ValueBaseV_ne_zero` | Spec.lean | Generator is not the identity |
| `K` | Spec.lean | Nullifier base point (certified parameter) |
| `K_ne_zero` | Spec.lean | Generator is not the identity |
| `NoteCommitR` | Spec.lean | Note commitment randomness generator |
| `noteCommitHash` | Spec.lean | Sinsemilla-based note hash, axiomatized as opaque |
| `merkleHash` | MerklePath.lean | Sinsemilla Merkle CRH, axiomatized as opaque |
| `merkleHash_collision_resistant` | MerklePath.lean | Standard collision-resistance assumption for the Merkle CRH |
| `commitToLeaf` | ActionCircuit.lean | Note commitment → Merkle leaf (x-coordinate extraction) |

**From dependencies** (via `redpallas-formal`): `BindingG`, `challengeHash`, `verify_sign_generic`, `fqSmul_mul`, `fqSmul_add`, `fqSmul_neg`.

## Dependencies

- Lean 4 (v4.30.0-rc2)
- Mathlib4
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta curve definitions and primality proofs
- [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) — Poseidon hash function specification
- [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) — RedPallas signature scheme, scalar multiplication lemmas, and `BindingG`
- [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) — Sinsemilla hash function (operations axiomatized in this library as `noteCommitHash` and `merkleHash`)

## Building

```shell
lake update    # fetch Mathlib + all dependencies (~3 GB of cached oleans)
lake build
```

## References

- [Zcash Protocol Specification §4.2 — Action Transfers](https://zips.z.cash/protocol/protocol.pdf)
- [Zcash Protocol Specification §4.3 — Note Commitments](https://zips.z.cash/protocol/protocol.pdf)
- [Zcash Protocol Specification §4.7 — Nullifiers](https://zips.z.cash/protocol/protocol.pdf)
- [Zcash Protocol Specification §4.17 — Balance](https://zips.z.cash/protocol/protocol.pdf)
- [Halo 2 book — Orchard design](https://zcash.github.io/halo2/)

## License

MIT
