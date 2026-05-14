import Orchard.Spec
import Orchard.Addresses

namespace Orchard

/-! # Note plaintext

This module introduces a first-pass plaintext object for Orchard note
encryption/decryption correctness. It stays close to the existing `Note`
structure while giving the theorem layer an explicit recipient-visible payload
type. `NotePlaintext` is kept separate from `Note` even though they currently
share fields so the two notions can diverge later without changing the current
note API.
-/

open Pasta RedPallas

noncomputable section

/-- The plaintext payload recovered by the intended recipient in the first-pass
    note-encryption model. -/
structure NotePlaintext where
  g_d : Pallas.toAffine.Point
  pk_d : Pallas.toAffine.Point
  v : Pasta.Fq
  rho : Pasta.Fp
  psi : Pasta.Fp

/-- Convert a `NotePlaintext` into the existing Orchard `Note` structure so the
    new layer can connect cleanly to the current note-commitment development. -/
def NotePlaintext.toNote (plaintext : NotePlaintext) : Note :=
  { g_d := plaintext.g_d
    pk_d := plaintext.pk_d
    v := plaintext.v
    rho := plaintext.rho
    psi := plaintext.psi }

/-- A plaintext matches a payment address when its diversifier and diversified
    public key are the ones carried by that address. This does not imply
    `ValidDiversifier`; callers that need a valid address must prove that
    separately. -/
def NotePlaintext.matchesAddress (plaintext : NotePlaintext)
    (addr : PaymentAddress) : Prop :=
  plaintext.g_d = addr.g_d ∧ plaintext.pk_d = addr.pk_d

example (plaintext : NotePlaintext) :
    plaintext.toNote.g_d = plaintext.g_d := by
  rfl

example (plaintext : NotePlaintext) :
    plaintext.toNote.pk_d = plaintext.pk_d := by
  rfl

example (plaintext : NotePlaintext) (addr : PaymentAddress)
    (hgd : plaintext.g_d = addr.g_d)
    (hpk : plaintext.pk_d = addr.pk_d) :
    plaintext.matchesAddress addr := by
  exact And.intro hgd hpk

end

end Orchard
