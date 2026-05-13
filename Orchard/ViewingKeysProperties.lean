import Orchard.Addresses

namespace Orchard

open Pasta RedPallas

noncomputable section

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

theorem paymentAddress_pk_d_from_spendingKey (sk : SpendingKey)
    (g_d : Pallas.toAffine.Point) :
    (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      derivePublicKey sk.rivk g_d := by
  rfl

theorem paymentAddress_keyAgreement (sk : SpendingKey)
    (esk : Pasta.Fq) (g_d : Pallas.toAffine.Point) :
    keyAgreement esk
        (paymentAddress (deriveIncomingViewingKey (deriveFullViewingKey sk)) g_d).pk_d =
      keyAgreement esk (derivePublicKey sk.rivk g_d) := by
  rfl

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
