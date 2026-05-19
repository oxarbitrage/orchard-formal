import Orchard.NoteEncryption

namespace Orchard

/-! # Note decryption inputs

Receiver-side inputs and decryption interface for the first-pass Orchard
note-encryption correctness model.
-/

open Pasta RedPallas

noncomputable section

/-- Recipient-side shared-secret reconstruction from the incoming viewing key
    and transmitted ephemeral public key. -/
def recipientSharedSecret (ivk : IncomingViewingKey)
    (epk : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  keyAgreement ivk.ivk epk

/-- Opaque decryption interface for the first-pass ciphertext layer. -/
axiom decrypt : Pallas.toAffine.Point → Ciphertext → NotePlaintext

/-- Correctness boundary for the abstract ciphertext interface. -/
axiom decrypt_encrypt_roundtrip :
  ∀ (shared : Pallas.toAffine.Point) (plaintext : NotePlaintext),
    decrypt shared (encrypt shared plaintext) = plaintext

/-- Receiver-side inputs required to attempt note recovery. -/
structure ReceiverNoteDecryption where
  ivk : IncomingViewingKey
  transmitted : TransmittedNote

/-- The receiver-side shared secret derived from the transmitted `epk`. -/
def receiverSharedSecret (receiver : ReceiverNoteDecryption) :
    Pallas.toAffine.Point :=
  recipientSharedSecret receiver.ivk receiver.transmitted.epk

/-- Recover the note plaintext from the receiver inputs. -/
def decryptNote (receiver : ReceiverNoteDecryption) : NotePlaintext :=
  decrypt (receiverSharedSecret receiver) receiver.transmitted.ciphertext

example (receiver : ReceiverNoteDecryption) :
    receiverSharedSecret receiver =
      recipientSharedSecret receiver.ivk receiver.transmitted.epk := by
  rfl

example (receiver : ReceiverNoteDecryption) :
    decryptNote receiver =
      decrypt (receiverSharedSecret receiver) receiver.transmitted.ciphertext := by
  rfl

end

end Orchard
