# orchard-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of Zcash's Orchard shielded protocol, composing Poseidon, Sinsemilla, and RedPallas into machine-verified proofs of the protocol's core security properties.

## What's formalized

**Key results:**

- **`nullifier_uniqueness`** — distinct notes produce distinct nullifiers: the formal proof of double-spend prevention.
- **`balance_multi_binding`** — a balanced multi-action transaction produces a verifiable binding key [Σ rcvᵢ]·BindingG.
- **`dh_shared_secret`** — sender and recipient derive identical shared secrets: [esk]·pk_d = [ivk]·epk.
- **`node_root_injective`** — under collision resistance, equal Merkle roots imply equal subtrees.
- **`action_no_double_spend`** — satisfied action circuits cannot double-spend.

~35 theorems total across value commitments, nullifiers, note commitments, DH key agreement, Merkle paths, and action circuit soundness.

## Axioms

| Axiom | Justification |
|-------|--------------|
| `ValueBaseV`, `K`, `NoteCommitR` | Certified Zcash generators |
| `noteCommitHash` | Sinsemilla-based hash, axiomatized as opaque |
| `merkleHash_collision_resistant` | Standard collision-resistance assumption |
| `commitToLeaf` | Leaf hash function, axiomatized as opaque |

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4), [pasta-formal](https://github.com/oxarbitrage/pasta-formal), [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal), [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal), [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal).

## References

- [Zcash Protocol Spec §4.2, §4.3, §4.7, §4.17](https://zips.z.cash/protocol/protocol.pdf)
- [Halo 2 book](https://zcash.github.io/halo2/)

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
