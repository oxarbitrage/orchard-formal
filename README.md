# orchard-formal

Lean 4 formalization of the [Zcash Orchard](https://zcash.github.io/orchard/) protocol, composing cryptographic primitives from [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal), [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal), and [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal).

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Orchard` namespace. Built on top of [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

| Component | File | Description |
|-----------|------|-------------|
| Value commitment | `Orchard/Spec.lean` | `cv = [v] ValueBaseV + [rcv] BindingG` |
| Nullifier derivation | `Orchard/Spec.lean` | `nf = [PoseidonHash(nk, rho) + psi] K + cm` |
| Value commitment homomorphism | `Orchard/Properties.lean` | `valueCommit(v₁,r₁) + valueCommit(v₂,r₂) = valueCommit(v₁+v₂, r₁+r₂)` |
| Value commitment zero | `Orchard/Properties.lean` | `valueCommit(0, 0) = 0` |
| Value commitment negation | `Orchard/Properties.lean` | `valueCommit(-v, -r) = -valueCommit(v, r)` |
| Value commitment subtraction | `Orchard/Properties.lean` | `valueCommit(v₁,r₁) - valueCommit(v₂,r₂) = valueCommit(v₁-v₂, r₁-r₂)` |
| Balance equation | `Orchard/Properties.lean` | Input minus output commitments = net value commitment |
| Balanced BVK | `Orchard/Properties.lean` | `valueCommit(0, rcv) = [rcv] BindingG` |
| Nullifier determinism | `Orchard/Properties.lean` | Same inputs → same nullifier |
| **Nullifier binding** | `Orchard/Properties.lean` | Equal nullifiers (same nk, rho, psi) → equal note commitments |
| Nullifier psi collision | `Orchard/Properties.lean` | Collision resistance reduces to DLP on K |
| **Binding signature correctness** | `Orchard/Properties.lean` | Signing with `rcv_net` verifies against `bvk` |
| **Balance ↔ binding signature** | `Orchard/Properties.lean` | Balanced transaction → valid binding signature |
| DH key agreement | `Orchard/KeyAgreement.lean` | `ka = [esk] pk_d` key agreement |
| **DH commutativity** | `Orchard/KeyAgreement.lean` | Sender and recipient compute the same shared secret |
| Recipient key recovery | `Orchard/KeyAgreement.lean` | `[ivk] epk = [esk] pk_d` |
| Key agreement linearity | `Orchard/KeyAgreement.lean` | Distributes over key addition |
| Merkle tree type | `Orchard/MerklePath.lean` | Binary tree with depth-indexed `leaf` and `node` |
| Merkle path verification | `Orchard/MerklePath.lean` | Authentication path from leaf to root |
| **Path unique root** | `Orchard/MerklePath.lean` | Same path + leaf → same root |
| Leaf/node membership | `Orchard/MerklePath.lean` | Structural membership predicates |
| **Node root injectivity** | `Orchard/MerklePath.lean` | Under collision resistance, root determines children |

## Security argument

The formalization captures the algebraic core of Orchard's privacy and integrity guarantees:

1. **Value privacy**: value commitments are Pedersen commitments — computationally hiding under the DLP assumption.
2. **Balance integrity** (proven): value commitment homomorphism ensures `Σ cv_in - Σ cv_out = valueCommit(v_net, rcv_net)`. A valid binding signature proves the signer knows `rcv_net`, which (with range proofs in the circuit) implies `v_net = 0`.
3. **Double-spend prevention** (proven): nullifier binding ensures each note maps to a unique nullifier. Publishing a nullifier marks exactly one note as spent.
4. **Key agreement** (proven): DH commutativity ensures sender and recipient derive the same shared secret, enabling note encryption.
5. **Merkle tree security** (axiom + proven): collision resistance of the Merkle hash implies root determines the tree structure. Path verification is deterministic and yields a unique root.

See §4.16, §5.4.5.3, §4.1.7, and §5.4.8.3 of the [Zcash protocol specification](https://zips.z.cash/protocol/protocol.pdf).

## Axioms

Generator points and the challenge hash are axiomatized (opaque data/functions):

- `ValueBaseV` — value commitment generator
- `K` — nullifier deriving key base point
- `BindingG`, `G` — from RedPallas (binding and spend auth generators)
- `challengeHash` — from RedPallas (BLAKE2b-based hash)
- `roundConstants` — from Poseidon (Grain LFSR output)
- `merkleHash` — Merkle CRH (Sinsemilla in the protocol)
- `merkleHash_collision_resistant` — collision resistance of the Merkle hash

No mathematical claims are axiomatized beyond standard collision resistance — all security properties are proven from the algebraic structure.

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib + all dependencies (~3 GB of cached oleans)
lake build     # builds in ~10 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — finite field theory, big operators, tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas/Vesta curve definitions and primality proofs
- **[poseidon-formal](https://github.com/oxarbitrage/poseidon-formal)** — Poseidon hash function specification
- **[redpallas-formal](https://github.com/oxarbitrage/redpallas-formal)** — RedPallas signature scheme and scalar multiplication
- **[sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal)** — Sinsemilla hash function

## References

- [Zcash protocol specification, §4.16, §5.4.8.3](https://zips.z.cash/protocol/protocol.pdf) — Nullifier derivation, value commitments
- [zcash/orchard](https://github.com/zcash/orchard) — Rust implementation
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization
