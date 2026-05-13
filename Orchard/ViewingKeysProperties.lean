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

theorem deriveFullViewingKey_nk (sk : SpendingKey) :
    (deriveFullViewingKey sk).nk = sk.nk := by
  rfl

theorem deriveIncomingViewingKey_rivk (sk : SpendingKey) :
    (deriveIncomingViewingKey (deriveFullViewingKey sk)).ivk = sk.rivk := by
  rfl

theorem deriveOutgoingViewingKey_ovk (sk : SpendingKey) :
    (deriveOutgoingViewingKey (deriveFullViewingKey sk)).ovk = sk.ovk := by
  rfl

theorem paymentAddress_g_d (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).g_d = g_d := by
  rfl

theorem paymentAddress_pk_d (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).pk_d = deriveTransmissionKey ivk g_d := by
  rfl

/-- The diversified public key `pk_d` of a `paymentAddress` constructed from a
    `SpendingKey`'s derived IVK equals the public key obtained by deriving the
    public key from `sk.rivk`.
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

example (sk : SpendingKey) :
    (deriveFullViewingKey sk).ak = keygen sk.ask := by
  exact deriveFullViewingKey_ak sk

example (sk : SpendingKey) (g_d : Pallas.toAffine.Point) :
    (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      derivePublicKey sk.rivk g_d := by
  exact paymentAddress_pk_d_from_spendingKey sk g_d

example (sk : SpendingKey) (esk : Pasta.Fq) (g_d : Pallas.toAffine.Point) :
    keyAgreement esk
        (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      keyAgreement esk (derivePublicKey sk.rivk g_d) := by
  exact paymentAddress_keyAgreement sk esk g_d

end

end Orchard
