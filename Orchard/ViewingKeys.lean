import Orchard.KeyAgreement
import RedPallas.Properties

namespace Orchard

open Pasta RedPallas

noncomputable section

structure SpendingKey where
  ask : Pasta.Fq
  nk : Pasta.Fp
  rivk : Pasta.Fq
  ovk : Pasta.Fp

structure FullViewingKey where
  ak : Pallas.toAffine.Point
  nk : Pasta.Fp
  rivk : Pasta.Fq
  ovk : Pasta.Fp

structure IncomingViewingKey where
  ivk : Pasta.Fq

structure OutgoingViewingKey where
  ovk : Pasta.Fp

def deriveFullViewingKey (sk : SpendingKey) : FullViewingKey :=
  { ak := keygen sk.ask
    nk := sk.nk
    rivk := sk.rivk
    ovk := sk.ovk }

def deriveIncomingViewingKey (fvk : FullViewingKey) : IncomingViewingKey :=
  { ivk := fvk.rivk }

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
