import Orchard.Addresses

namespace Orchard

/-! # Viewing key properties

Theorems about viewing-key/address correctness, agreement, and well-formedness.
This module contains lemmas establishing that deriving a full viewing key from a
spending key exposes the expected components, that payment addresses expose the
correct diversified public key, that key agreement with a payment address's `pk_d`
agrees with the derived public key, and that constructed payment addresses are
well-formed when given a valid diversifier.
-/

open Pasta RedPallas

noncomputable section

/-! ## Viewing-key derivation lemmas -/

/-- The authorization key component of a `FullViewingKey` derived from a `SpendingKey`.

    This lemma states that `deriveFullViewingKey sk` exposes the expected public
    authorization key given by `keygen sk.ask`.
-/
theorem deriveFullViewingKey_ak (sk : SpendingKey) :
    (deriveFullViewingKey sk).ak = keygen sk.ask := by
  rfl

/-- The nullifier key component `nk` of a `FullViewingKey` derived from a `SpendingKey`. -/
theorem deriveFullViewingKey_nk (sk : SpendingKey) :
    (deriveFullViewingKey sk).nk = sk.nk := by
  rfl

/-- The incoming viewing key `ivk` obtained from deriving a `FullViewingKey` equals the spending key's `rivk`. -/
theorem deriveIncomingViewingKey_rivk (sk : SpendingKey) :
    (deriveIncomingViewingKey (deriveFullViewingKey sk)).ivk = sk.rivk := by
  rfl

/-- The outgoing viewing key `ovk` component of a `FullViewingKey` derived from a `SpendingKey`. -/
theorem deriveOutgoingViewingKey_ovk (sk : SpendingKey) :
    (deriveOutgoingViewingKey (deriveFullViewingKey sk)).ovk = sk.ovk := by
  rfl

/-- The diversified group element `g_d` of a `paymentAddress` equals the `g_d` used to construct it. -/
theorem paymentAddress_g_d (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).g_d = g_d := by
  rfl

/-- The diversified public key `pk_d` of a `paymentAddress` is the transmission key derived from the `ivk` and `g_d`. -/
theorem paymentAddress_pk_d (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).pk_d = deriveTransmissionKey ivk g_d := by
  rfl

/-- The diversified public key `pk_d` of a `paymentAddress` constructed from a
    `SpendingKey`'s derived IVK equals the public key obtained by deriving the
    public key from `sk.rivk`.

    **First-pass simplification caveat:** This theorem holds because the current
    model sets `IVK = rivk` directly, bypassing the full Orchard PRF-based IVK
    derivation (`IVK = PRF^{ivk}(ak, nk)` from the protocol spec §4.2.3).  The
    result equates two derivation paths — the chain
    `sk → deriveFullViewingKey → deriveIncomingViewingKey` versus the shortcut
    `sk.rivk` — only because those paths coincide under this simplification.
    Once a PRF-faithful IVK model is introduced the theorem statement will need
    to be updated.
-/
theorem paymentAddress_pk_d_from_spendingKey (sk : SpendingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      derivePublicKey sk.rivk g_d := by
  rfl

/-- Key-agreement with a payment address's `pk_d` agrees with key-agreement
    against the directly derived public key from `sk.rivk`.

    This shows that key agreement using an ephemeral secret `esk` yields the same
    result whether using the `paymentAddress`'s `pk_d` or the `derivePublicKey`
    constructed from the spending key's `rivk`.

    **First-pass simplification caveat:** Like `paymentAddress_pk_d_from_spendingKey`,
    this theorem relies on the model-level equality `IVK = rivk` rather than the
    full Orchard PRF-based IVK derivation.  The agreement holds trivially because
    both sides reduce to the same `sk.rivk`-derived key under this simplification;
    it is not yet a proof of the full protocol's DH-agreement property.
-/
theorem paymentAddress_keyAgreement (sk : SpendingKey)
    (esk : Pasta.Fq) (g_d : Pallas.toAffine.Point) :
    keyAgreement esk
        (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      keyAgreement esk (derivePublicKey sk.rivk g_d) := by
  rfl

/-- A `paymentAddress` constructed from a valid diversifier is well-formed.

    The `IsValid` predicate for `PaymentAddress` is satisfied when the diversifier
    `g_d` meets the `ValidDiversifier` condition.
-/
theorem paymentAddress_wellFormed (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) (h : ValidDiversifier g_d) :
    (paymentAddress ivk g_d).IsValid := by
  exact paymentAddress_valid ivk g_d h


end

end Orchard
