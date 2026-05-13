import Orchard.KeyAgreement

namespace Orchard

/-! # Viewing keys

Definitions of viewing-key structures and simple derivation functions for Orchard.

This module defines the spending key components, a full viewing key, and
compact incoming/outgoing viewing keys with minimal first-pass derivations.

Note: this lightweight model treats `rivk` directly as the incoming viewing
key (IVK). The PRF / hash-based derivation of IVK from `rivk` in the Zcash
spec is deferred for a later iteration.
-/

open Pasta RedPallas

noncomputable section

/-- A spending key's secret components: `ask` (authorizing key scalar),
    `nk` (nullifier key), `rivk` (randomized ivk material), and `ovk`
    (outgoing viewing key). -/
structure SpendingKey where
  ask : Pasta.Fq
  nk : Pasta.Fp
  rivk : Pasta.Fq
  ovk : Pasta.Fp

/-- A full viewing key exposing the public authorization key `ak`,
    together with `nk`, `rivk`, and `ovk`. -/
structure FullViewingKey where
  ak : Pallas.toAffine.Point
  nk : Pasta.Fp
  rivk : Pasta.Fq
  ovk : Pasta.Fp

/-- The incoming viewing key (IVK) used to detect incoming notes. -/
structure IncomingViewingKey where
  ivk : Pasta.Fq

/-- The outgoing viewing key (OVK) used by recipients to decrypt outgoing plaintext.
    In this model it is represented as an `Fp` element. -/
structure OutgoingViewingKey where
  ovk : Pasta.Fp

/-- Derive the full viewing key from a spending key. This extracts the
    public authorization key using `keygen` and copies the other components.

    Note: the `rivk` field is treated directly as IVK material in this model; a
    full PRF/hash-based IVK derivation is left to a later refinement. -/
def deriveFullViewingKey (sk : SpendingKey) : FullViewingKey :=
  { ak := keygen sk.ask
    nk := sk.nk
    rivk := sk.rivk
    ovk := sk.ovk }

/-- Derive the incoming viewing key from a full viewing key.

    In this first-pass model we use `fvk.rivk` directly as the IVK. -/
def deriveIncomingViewingKey (fvk : FullViewingKey) : IncomingViewingKey :=
  { ivk := fvk.rivk }

/-- Derive the outgoing viewing key from a full viewing key. -/
def deriveOutgoingViewingKey (fvk : FullViewingKey) : OutgoingViewingKey :=
  { ovk := fvk.ovk }

example (sk : SpendingKey) :
    (deriveFullViewingKey sk).ak = keygen sk.ask := by
  rfl

example (sk : SpendingKey) :
    (deriveIncomingViewingKey (deriveFullViewingKey sk)).ivk = sk.rivk := by
  rfl

example (sk : SpendingKey) :
    (deriveOutgoingViewingKey (deriveFullViewingKey sk)).ovk = sk.ovk := by
  rfl

end

end Orchard
