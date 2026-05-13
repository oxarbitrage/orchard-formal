# Orchard Viewing Keys and Address Derivation Design

## Problem

The current Zcash formalization stack covers much of the Orchard cryptographic core:

- Pasta curve foundations
- Poseidon
- Sinsemilla
- RedPallas
- Orchard algebraic constructions
- Halo 2 gadget semantics

What remains underformalized is an important spec-facing layer sitting directly above that algebraic core: the Orchard viewing-key hierarchy and payment-address derivation story.

This area matters because it is how the protocol is actually used by wallets and applications. It connects secret key material, viewing capabilities, diversifiers, transmission keys, and payment addresses. It is also close enough to the current `orchard-formal` development that a first formalization pass can focus on correctness and consistency without requiring full note-encryption semantics or wallet modeling.

## Proposed Approach

Extend `orchard-formal` with a new viewing-keys and address-derivation layer that formalizes:

1. key hierarchy objects and derivation functions,
2. diversifier and transmission-key address construction,
3. correctness and consistency theorems for derived address components,
4. a minimal explicit assumptions boundary where the spec depends on opaque hash-like constructions.

This first project should remain intentionally narrow. It should formalize the structure and correctness of the viewing-key and address story, not the full semantics of note encryption, wallet recovery, or consensus-state handling.

## Goals

1. Formalize the Orchard viewing-key hierarchy as protocol objects in Lean.
2. Formalize payment-address derivation from viewing material and diversifiers.
3. Prove core correctness and consistency theorems relating the key hierarchy to address components.
4. Make explicit which parts depend only on algebra and which rely on opaque assumptions from the Zcash spec.
5. Keep the work close to existing `orchard-formal` abstractions so it can reuse the current algebraic stack.

## Non-goals

1. Formalizing note decryption or outgoing plaintext recovery.
2. Proving AEAD or note-encryption security.
3. Modeling full wallet behavior or scanning semantics.
4. Formalizing transaction acceptance or consensus-state transitions.
5. Solving the broader cryptographic-assumptions refactor in this first project.

## Why This Is the Right Next Step

This is a high-impact, low-friction extension of the current work:

- It is visibly part of the Zcash protocol specification.
- It sits very close to the Orchard algebra already formalized.
- It enables later work on note encryption and receiver-side correctness.
- It is meaningful on its own, even without full protocol-state semantics.

Compared with tackling full transaction semantics or note-encryption correctness, viewing keys and address derivation provide a much cleaner first expansion of the spec surface.

## Repository Placement

This work should live in `orchard-formal`.

### Why `orchard-formal`

1. The concepts are Orchard protocol concepts, not general-purpose primitives.
2. The development will depend on existing Orchard note and group-algebra definitions.
3. It avoids unnecessary repo sprawl.
4. It keeps the protocol story in one place instead of splitting closely related semantics across repositories.

This should be treated as a protocol-semantics extension of the existing repository, not as a separate standalone package.

## Scope of the First Pass

The first pass should cover:

1. spending-key-related derivation objects needed for viewing material,
2. full viewing key / incoming viewing key / outgoing viewing key relationships,
3. diversifier-based payment-address derivation,
4. transmission-key correctness and agreement properties,
5. consistency theorems connecting derived keys and derived addresses.

The first pass should explicitly stop short of:

1. note plaintext structure,
2. note decryption correctness,
3. outgoing plaintext recovery,
4. wallet scanning behavior,
5. encryption security proofs.

## Recommended Module Decomposition

The implementation should be broken into small modules with clear responsibilities.

### 1. Viewing-key types and derivation

This module should define the protocol objects for the Orchard viewing-key hierarchy and the functions deriving them from the relevant secret material.

Likely contents:

- viewing-key structures,
- derivation functions,
- helper lemmas showing definitional and algebraic relationships.

### 2. Address construction

This module should define payment-address construction from diversifiers and viewing material.

Likely contents:

- diversifier-related definitions,
- transmission-key derivation,
- address structure,
- address-construction functions.

### 3. Correctness theorems

This module should prove the main correctness and consistency properties.

Likely theorem shapes:

- derived transmission keys match the address constructor,
- address construction is well-formed under the required validity conditions,
- viewing-key-derived components agree with the corresponding address fields,
- key-derivation and address-derivation functions compose as expected.

### 4. Minimal assumptions boundary

Where the Zcash spec relies on opaque hashes, group-hash constructions, or validity predicates that are not yet mechanized, those should be isolated behind a minimal explicit assumptions layer local to this work.

The key principle is to keep assumptions narrow and visible, rather than letting them spread across every theorem statement.

## Theorem Targets

The first milestone should target correctness and consistency theorems, not security proofs.

Recommended initial theorem families:

1. **Derivation correctness**
   - derived viewing components equal their intended algebraic definitions,
   - derived address components equal the output of the address-construction formulas.

2. **Agreement theorems**
   - multiple derivation paths to the same protocol object produce the same result,
   - transmission-key definitions agree across the viewing-key and address layers.

3. **Well-formedness theorems**
   - if the required validity predicate for a diversifier/address constructor holds, the resulting address is well formed.

4. **Injectivity / non-aliasing style lemmas**
   - where realistically provable, distinct inputs produce distinct address components under explicit assumptions.

These theorems should be strong enough to make the development useful, but modest enough to avoid prematurely turning this project into a wallet-semantics or encryption project.

## Assumptions Boundary

This project should avoid broad cryptographic abstraction work. However, it should still state clearly when a theorem depends on an opaque construction from the spec.

Likely assumptions may include:

- validity predicates for diversifier-based address construction,
- opaque hash-derived key components,
- hash-to-curve style behavior where required by the spec.

The design rule is:

> prefer algebraic correctness theorems wherever possible; isolate opaque spec-dependent behavior behind small explicit assumptions only where unavoidable.

## Data Flow

The intended conceptual flow is:

1. secret key material gives rise to viewing-key material,
2. viewing-key material plus diversifier data gives rise to address components,
3. address components determine the protocol-visible payment address,
4. theorem statements connect those levels and prove they are mutually consistent.

This gives a clean mathematical story matching the structure of the protocol text.

## Migration Strategy

This work should be developed incrementally.

### Phase 1

Add the core definitions for viewing-key objects and address objects, with minimal theorem content.

### Phase 2

Add derivation functions and the core definitional lemmas.

### Phase 3

Prove the main correctness and agreement theorems.

### Phase 4

Add a small number of well-formedness or injectivity-style lemmas where the assumptions are clear and local.

This sequencing keeps definitions stable before theorem work expands.

## Validation Strategy

The project is successful if it produces a spec-facing formal layer that is both understandable and reusable.

Success criteria for the first milestone:

1. the key hierarchy is represented explicitly in Lean,
2. payment-address derivation is represented explicitly in Lean,
3. at least a handful of correctness/agreement theorems connect the two layers,
4. assumptions remain narrow and visible,
5. the result reads as a recognizable formal counterpart of the relevant Orchard spec sections.

## Risks

### 1. Scope creep into wallet semantics

Viewing keys naturally tempt a jump into scanning, decryption, and note discovery.

**Mitigation:** stop at derivation and address correctness in the first pass.

### 2. Overcommitting to assumptions too early

If opaque constructions are introduced too casually, the development may lose the clean algebraic character that makes it tractable.

**Mitigation:** prove all possible algebraic equalities first; isolate assumptions only after the definitions force them.

### 3. Building the wrong abstraction boundary

If the viewing-key hierarchy is modeled too concretely, future extensions become painful. If modeled too abstractly, the spec connection becomes weak.

**Mitigation:** mirror the protocol objects closely in the first pass and generalize only where reuse is clearly needed.

## Testing and Review Expectations

Since this is a design-level and theorem-structure project, review should focus on:

1. whether the chosen objects correspond cleanly to the Orchard specification,
2. whether theorem targets are strong enough to be useful,
3. whether assumptions are minimized and explicit,
4. whether the work is properly scoped away from encryption and wallet logic for the first pass.

## Recommended First Milestone

The first milestone should be:

1. add viewing-key and address definitions to `orchard-formal`,
2. formalize diversifier and transmission-key address construction,
3. prove core derivation correctness theorems,
4. prove core agreement theorems between key-derived and address-derived components,
5. stop before decryption, recovery, and wallet-scanning behavior.

This gives a strong, spec-facing result without pulling in too much adjacent complexity.

## Summary

The right next spec-facing expansion of `orchard-formal` is a formalization of the Orchard viewing-key hierarchy and payment-address derivation. This area is important in the Zcash spec, close to the current algebraic development, and tractable as a correctness-and-consistency project. A narrow first pass here would create a strong bridge from the current Orchard formalization toward later work on note encryption, receiver semantics, and higher-level protocol behavior.
