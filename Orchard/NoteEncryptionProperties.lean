import Orchard.NoteDecryption

namespace Orchard

/-! # Note-encryption correctness properties

Named theorems tying together sender-side note construction, receiver-side
recovery, and the explicit ciphertext correctness boundary.
-/

open Pasta RedPallas

noncomputable section

/-- Sender-side shared secret agrees with the receiver-side reconstruction from
    the transmitted ephemeral key. -/
theorem sender_receiver_sharedSecret (sender : SenderNoteEncryption)
    (ivk : IncomingViewingKey)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    senderSharedSecret sender =
      recipientSharedSecret ivk (senderEphemeralKey sender) := by
  unfold senderSharedSecret recipientSharedSecret senderEphemeralKey senderAddress
  rw [hpk]
  simpa [deriveTransmissionKey] using
    (dh_shared_secret sender.esk ivk.ivk sender.addr.g_d)

/-- Decrypting the transmitted note built from sender inputs recovers the
    original plaintext, assuming ciphertext round-tripping. -/
theorem decrypt_encryptNote (sender : SenderNoteEncryption)
    (ivk : IncomingViewingKey)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    decryptNote
      { ivk := ivk
        transmitted := encryptNote sender } = sender.plaintext := by
  have hshared :
      recipientSharedSecret ivk (senderEphemeralKey sender) =
        senderSharedSecret sender := by
    exact (sender_receiver_sharedSecret sender ivk hpk).symm
  unfold decryptNote receiverSharedSecret encryptNote
  rw [hshared, decrypt_encrypt_roundtrip]

/-- The recovered plaintext converts back into the same Orchard `Note` as the
    sender plaintext. -/
theorem decrypt_encryptNote_toNote (sender : SenderNoteEncryption)
    (ivk : IncomingViewingKey)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    (decryptNote
      { ivk := ivk
        transmitted := encryptNote sender }).toNote =
      sender.plaintext.toNote := by
  rw [decrypt_encryptNote sender ivk hpk]

/-- When the sender inputs are well formed, the recovered plaintext matches the
    payment address targeted by the sender. -/
theorem decrypt_encryptNote_matchesAddress (sender : SenderNoteEncryption)
    (ivk : IncomingViewingKey)
    (hwell : sender.WellFormed)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    (decryptNote
      { ivk := ivk
        transmitted := encryptNote sender }).matchesAddress
      (senderAddress sender) := by
  rw [decrypt_encryptNote sender ivk hpk]
  exact hwell.2

example (sender : SenderNoteEncryption) (ivk : IncomingViewingKey)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    senderSharedSecret sender =
      recipientSharedSecret ivk (senderEphemeralKey sender) := by
  exact sender_receiver_sharedSecret sender ivk hpk

example (sender : SenderNoteEncryption) (ivk : IncomingViewingKey)
    (hpk : sender.addr.pk_d = deriveTransmissionKey ivk sender.addr.g_d) :
    decryptNote
      { ivk := ivk
        transmitted := encryptNote sender } = sender.plaintext := by
  exact decrypt_encryptNote sender ivk hpk

end

end Orchard
