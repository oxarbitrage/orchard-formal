import Orchard.ViewingKeys

namespace Orchard

open Pasta RedPallas

noncomputable section

axiom ValidDiversifier : Pallas.toAffine.Point → Prop

structure PaymentAddress where
  g_d : Pallas.toAffine.Point
  pk_d : Pallas.toAffine.Point

def PaymentAddress.IsValid (addr : PaymentAddress) : Prop :=
  ValidDiversifier addr.g_d

def deriveTransmissionKey (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  derivePublicKey ivk.ivk g_d

def paymentAddress (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) : PaymentAddress :=
  { g_d := g_d
    pk_d := deriveTransmissionKey ivk g_d }

theorem paymentAddress_valid (ivk : IncomingViewingKey)
    (g_d : Pallas.toAffine.Point) (h : ValidDiversifier g_d) :
    (paymentAddress ivk g_d).IsValid := by
  exact h

example (ivk : IncomingViewingKey) (g_d : Pallas.toAffine.Point) :
    (paymentAddress ivk g_d).pk_d = deriveTransmissionKey ivk g_d := by
  rfl

example (ivk : IncomingViewingKey) (g_d : Pallas.toAffine.Point)
    (h : ValidDiversifier g_d) :
    (paymentAddress ivk g_d).IsValid := by
  exact paymentAddress_valid ivk g_d h

end

end Orchard
