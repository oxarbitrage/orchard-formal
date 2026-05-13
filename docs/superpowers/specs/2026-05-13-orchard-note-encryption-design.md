# Orchard Note Encryption and Decryption Correctness Design

## Problem

The current `orchard-formal` development already formalizes a meaningful part of the Orchard key and address story:

- the viewing-key hierarchy,
- payment-address construction,
- transmission-key derivation,
- sender/recipient Diffie-Hellman agreement at the address layer.

What remains missing is the next protocol-facing step: a correctness account of how a sender uses that address material to construct note-encryption inputs, and how the intended recipient uses incoming viewing material to recover the same plaintext.

This gap matters because it is the bridge between "an address is well formed" and "a recipient can actually recover the note contents intended for that address." It is also a natural continuation of the current repository because the main ingredients are already present in the viewing-key and address formalization.

## Proposed Approach

Extend `orchard-formal` with a note-encryption and decryption correctness layer that proves end-to-end recovery of the intended plaintext while keeping the concrete ciphertext / AEAD transform abstract.

The first pass should formalize:

1. note plaintext objects and validity conditions,
2. sender-side note-encryption inputs derived from valid Orchard addresses,
3. receiver-side decryption inputs derived from incoming viewing material and transmitted public data,
4. end-to-end correctness theorems stating that decryption recovers the original plaintext for the intended recipient.

The first pass should **not** attempt to prove AEAD security or model wallet scanning behavior. Instead, it should introduce a narrow explicit assumptions boundary for ciphertext correctness and leave the cryptographic security properties of that layer out of scope.

## Goals

1. Formalize the recipient-visible note plaintext structure used in the first proof pass.
2. Formalize sender-side note-encryption inputs built from payment addresses and ephemeral sender material.
3. Formalize receiver-side decryption / recovery inputs from incoming viewing material and transmitted public data.
4. Prove sender/receiver agreement on the derived material needed for recovery.
5. Prove that decrypting a ciphertext produced for a valid Orchard address recovers the original plaintext under the explicit ciphertext correctness assumptions.
6. Make the new assumptions boundary precise in the repository and README.

## Non-goals

1. Proving IND-CPA, IND-CCA, authenticity, or any other AEAD security notion.
2. Modeling wallet scanning over many ciphertexts.
3. Formalizing outgoing plaintext recovery in this first pass.
4. Formalizing full consensus-state or transaction-acceptance semantics.
5. Eliminating all opaque KDF/hash assumptions in the same project.

## Why This Is the Right Next Step

This is the most coherent follow-on to the current Orchard work:

- it reuses the newly formalized viewing-key and address machinery,
- it upgrades the story from address correctness to recipient recovery correctness,
- it is visibly tied to the Zcash specification,
- it remains narrow enough to be a standalone formalization result.

Compared with starting on wallet behavior or transaction semantics, this project stays closer to the algebraic core already present in `orchard-formal` while still moving materially upward in protocol semantics.

## Alternative Approaches Considered

### 1. Opaque ciphertext / AEAD boundary

Treat encryption and decryption as an abstract interface with explicit correctness assumptions, and prove the protocol dataflow above that boundary.

**Pros**

- strongest balance of impact and tractability,
- easiest to land as a standalone result,
- maximizes reuse of the current Orchard development.

**Cons**

- does not yet model the concrete encryption construction in full detail.

### 2. Semi-concrete encryption model

Model more of the protocol key-derivation flow explicitly while still leaving the final encryption primitive abstract.

**Pros**

- closer to the specification,
- stronger fidelity to the eventual full model.

**Cons**

- more assumptions and proof plumbing,
- higher risk of scope expansion in the first pass.

### 3. Near-full concrete encryption path

Try to model most of the note-encryption construction directly.

**Pros**

- highest protocol fidelity.

**Cons**

- much heavier project,
- less likely to produce a clean near-term standalone theorem layer.

The recommended approach for this project is **Approach 1**.

## Repository Placement

This work should live in `orchard-formal`.

### Why `orchard-formal`

1. Note encryption and decryption are Orchard protocol concepts rather than generic primitives.
2. The development depends directly on the existing viewing-key, address, and Orchard group-algebra definitions.
3. Keeping this layer in the same repository preserves the protocol narrative instead of splitting closely related semantics across repositories.

## Scope of the First Pass

The first pass should cover:

1. a note plaintext type capturing the payload recovered by the intended recipient,
2. sender-side derivation of note-encryption inputs from:
   - a valid Orchard payment address,
   - ephemeral sender material,
   - the already formalized shared-secret path,
3. receiver-side derivation of decryption inputs from:
   - incoming viewing material,
   - transmitted public data,
4. an abstract ciphertext / decryption interface with explicit correctness assumptions,
5. end-to-end recovery theorems tying sender construction to recipient recovery.

The first pass should explicitly stop short of:

1. security properties of the encryption layer,
2. outgoing viewing-key recovery behavior,
3. wallet scanning semantics across candidate ciphertexts,
4. consensus-level reasoning about accepted transactions.

## Recommended Module Decomposition

### 1. `Orchard/NotePlaintext.lean`

Defines the note payload object used in the first pass and any validity predicates required by later theorems.

Likely contents:

- a note plaintext structure,
- any well-formedness predicates needed for the theorem layer,
- helper lemmas for field projection and equality.

### 2. `Orchard/NoteEncryption.lean`

Defines sender-side note-encryption inputs and the abstract ciphertext interface.

Likely contents:

- ephemeral sender input structures,
- sender-side derived secret material,
- plaintext packaging,
- abstract `encrypt` operation and its assumptions boundary.

### 3. `Orchard/NoteDecryption.lean`

Defines receiver-side reconstruction and decryption inputs.

Likely contents:

- transmitted public-data structures,
- receiver-side derived secret material,
- abstract `decrypt` operation tied to the ciphertext interface,
- recovery functions producing note plaintext.

### 4. `Orchard/NoteEncryptionProperties.lean`

Proves the main correctness theorems.

Likely theorem shapes:

- sender and receiver derive matching shared-secret material,
- decryption of an encryption generated for the intended recipient recovers the original plaintext,
- recovered plaintext fields agree with the sender's note payload fields,
- validity / well-formedness is preserved across the end-to-end recovery theorem.

### 5. `Orchard.lean`

Exports the new modules.

### 6. `README.md`

Documents the new result, its assumptions boundary, and how it extends the current Orchard story.

## Data Flow

The intended proof story should be:

1. start from a valid payment address and note plaintext,
2. derive sender-side encryption inputs using ephemeral sender material,
3. expose the transmitted public data needed by the receiver,
4. reconstruct the corresponding receiver-side decryption inputs from the incoming viewing path,
5. apply the ciphertext correctness boundary,
6. conclude that the recovered plaintext is equal to the original plaintext.

This should be stated both at the level of whole plaintext objects and at the level of important projected fields, so the final result is meaningful for later note-level reasoning rather than being just a byte-string round-trip statement.

## Assumptions Boundary

The assumptions should be explicit and narrow.

### Opaque assumptions

1. Encryption/decryption correctness for the abstract ciphertext interface.
2. Any KDF/hash-like steps that are not yet concretely formalized in this project.

### Proved in Lean

1. Sender/receiver agreement on the DH-derived material already supported by the Orchard address layer.
2. Correct threading from address material into sender encryption inputs.
3. Correct threading from incoming viewing material and transmitted public data into receiver decryption inputs.
4. Equality between the original note plaintext and the recovered note plaintext.

### Out of scope

1. Security of the ciphertext interface.
2. Multi-ciphertext scanning or recovery selection semantics.
3. Outgoing plaintext recovery.

## Theorem Layer

The final theorem layer should include named results for:

1. sender-side derived material,
2. receiver-side derived material,
3. sender/receiver agreement,
4. note decryption correctness,
5. note field recovery correctness,
6. any well-formedness preservation theorem needed by downstream note semantics.

The theorem names should be public-facing and README-worthy rather than remaining as anonymous examples.

## Documentation Requirements

The repository documentation should:

1. describe this as a **correctness** formalization rather than a security proof,
2. identify the abstract ciphertext / AEAD boundary plainly,
3. explain how this result extends the existing viewing-key and payment-address work,
4. avoid overstating protocol fidelity where assumptions remain opaque.

## Acceptance Criteria

This project is successful when `orchard-formal` includes:

1. named definitions for note plaintext, sender encryption inputs, receiver decryption inputs, and the abstract ciphertext interface,
2. named theorems for sender/receiver agreement on the derived recovery material,
3. a named end-to-end theorem stating that encrypting for a valid payment address and decrypting with the matching incoming viewing material recovers the original plaintext,
4. README updates that clearly separate proved results from assumed boundaries.

## Future Extensions

This design is intentionally staged. Natural follow-on projects after this one are:

1. outgoing plaintext recovery,
2. more protocol-faithful modeling of the encryption derivation path,
3. wallet scanning / trial-decryption semantics,
4. tighter integration with broader Orchard note and transaction semantics.
