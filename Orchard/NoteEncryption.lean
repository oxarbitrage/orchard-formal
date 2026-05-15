import Orchard.NotePlaintext
import Orchard.KeyAgreement

namespace Orchard

/-! # Note encryption inputs

Sender-side inputs for the first-pass Orchard note-encryption correctness model.
This layer keeps the ciphertext interface abstract and focuses on the protocol
data that feeds it.
-/

open Pasta RedPallas

noncomputable section

/-- Opaque ciphertext type for the first-pass note-encryption model. -/
axiom Ciphertext : Type

/-- Sender-side inputs used to build an encrypted note for a recipient. -/
structure SenderNoteEncryption where
  addr : PaymentAddress
  esk : Pasta.Fq
  plaintext : NotePlaintext

/-- The payment address targeted by the sender. -/
def senderAddress (sender : SenderNoteEncryption) : PaymentAddress :=
  sender.addr

/-- The sender's ephemeral public key `epk = [esk] g_d`. -/
def senderEphemeralKey (sender : SenderNoteEncryption) : Pallas.toAffine.Point :=
  ephemeralKey sender.esk sender.addr.g_d

/-- The sender-side shared secret derived from the address's diversified public
    key. -/
def senderSharedSecret (sender : SenderNoteEncryption) : Pallas.toAffine.Point :=
  keyAgreement sender.esk sender.addr.pk_d

/-- Opaque encryption interface, parameterized by the shared secret and
    plaintext payload. -/
axiom encrypt : Pallas.toAffine.Point → NotePlaintext → Ciphertext

/-- The public data transmitted to the recipient in the first-pass model. -/
structure TransmittedNote where
  epk : Pallas.toAffine.Point
  ciphertext : Ciphertext

/-- Build the transmitted note from sender inputs. -/
def encryptNote (sender : SenderNoteEncryption) : TransmittedNote :=
  { epk := senderEphemeralKey sender
    ciphertext := encrypt (senderSharedSecret sender) sender.plaintext }

/-- Sender-side well-formedness: the diversifier is valid and the plaintext is
    aligned with the targeted payment address. -/
def SenderNoteEncryption.WellFormed (sender : SenderNoteEncryption) : Prop :=
  sender.addr.IsValid ∧
  sender.plaintext.matchesAddress (senderAddress sender)

example (sender : SenderNoteEncryption) :
    (encryptNote sender).epk = senderEphemeralKey sender := by
  rfl

example (sender : SenderNoteEncryption) :
    (encryptNote sender).ciphertext =
      encrypt (senderSharedSecret sender) sender.plaintext := by
  rfl

example (sender : SenderNoteEncryption)
    (h : sender.WellFormed) :
    sender.plaintext.matchesAddress (senderAddress sender) := by
  exact h.2

end

end Orchard
