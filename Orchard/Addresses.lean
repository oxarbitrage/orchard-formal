import Orchard.ViewingKeys

namespace Orchard

/-! # Addresses

Definitions for Orchard payment addresses and diversifiers.

This module models the diversifier validation predicate and payment address
structure used to derive transmission keys and detect incoming notes.

See §4.3.2 (Diversifiers) and §5.6 (Payment addresses) of the Zcash
protocol specification for the conceptual design.
-/

open Pasta RedPallas

noncomputable section

/-- A predicate indicating that a point g_d is a valid diversifier.

This represents the deferred diversifier-validity / hash-to-group condition
from the Zcash spec: a diversifier must map to a group element satisfying
the protocol's validity checks. The concrete construction is modelled as an
axiom here and instantiated/refined later.
-/
axiom ValidDiversifier : Pallas.toAffine.Point → Prop

/-- A recipient's payment address consisting of a diversifier `g_d` and the
    corresponding diversified public key `pk_d`.

    `pk_d` is the Pallas group element derived from the IVK and `g_d`.
-/
structure PaymentAddress where
  g_d : Pallas.toAffine.Point
  pk_d : Pallas.toAffine.Point

/-- The validity predicate for a payment address.

    An address is valid iff its diversifier `g_d` satisfies
    the (deferred) `ValidDiversifier` condition.
-/
def PaymentAddress.IsValid (addr : PaymentAddress) : Prop :=
  ValidDiversifier addr.g_d

/-- Derive the transmission (diversified) public key `pk_d` from an IVK and diversifier.

    This is defined as `pk_d = [ivk] g_d` using `derivePublicKey`.
-/
def deriveTransmissionKey (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  derivePublicKey ivk.ivk g_d

/-- Build a `PaymentAddress` from an IVK and a diversifier `g_d`.

    The resulting `pk_d` is computed with `deriveTransmissionKey`.
-/
def paymentAddress (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) : PaymentAddress :=
  { g_d := g_d
    pk_d := deriveTransmissionKey ivk g_d }

/-- If the diversifier `g_d` is valid then the constructed `paymentAddress` is valid.
-/
theorem paymentAddress_valid (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) (h : ValidDiversifier g_d) :
    (paymentAddress ivk g_d).IsValid := by
  exact h

-- Inline regression test: equality of `pk_d` with derived transmission key.
-- This is a small TDD-style example; it will be promoted to a named theorem
-- in a later task.
example (ivk : IncomingViewingKey) (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).pk_d = deriveTransmissionKey ivk g_d := by
  rfl

example (ivk : IncomingViewingKey) (g_d : Pallas.toAffine.Point)
    (h : ValidDiversifier g_d) :
    (paymentAddress ivk g_d).IsValid := by
  exact paymentAddress_valid ivk g_d h

end

end Orchard
