import Orchard.Spec

namespace Orchard

/-! # Diffie-Hellman key agreement

Orchard uses a Diffie-Hellman key agreement on the Pallas curve for
note encryption. The sender and recipient derive a shared secret from
their respective secret and public keys.

See §5.4.5.3 of the Zcash protocol specification.
-/

open Pasta RedPallas

noncomputable section

/-- Derive a diversified public key: `pk_d = [ivk] g_d`. -/
def derivePublicKey (ivk : Pasta.Fq) (g_d : Pallas.toAffine.Point) :
    Pallas.toAffine.Point :=
  ivk ⬝ g_d

/-- Compute the ephemeral public key: `epk = [esk] g_d`. -/
def ephemeralKey (esk : Pasta.Fq) (g_d : Pallas.toAffine.Point) :
    Pallas.toAffine.Point :=
  esk ⬝ g_d

/-- Key agreement: `ka = [esk] pk_d`. -/
def keyAgreement (esk : Pasta.Fq) (pk_d : Pallas.toAffine.Point) :
    Pallas.toAffine.Point :=
  esk ⬝ pk_d

/-! ## DH correctness -/

/-- The sender's shared secret equals scalar product `[esk * ivk] g_d`. -/
theorem keyAgreement_eq_mul (esk ivk : Pasta.Fq)
    (g_d : Pallas.toAffine.Point) :
    keyAgreement esk (derivePublicKey ivk g_d) = (esk * ivk) ⬝ g_d := by
  unfold keyAgreement derivePublicKey
  rw [fqSmul_mul]

/-- **DH commutativity**: sender and recipient compute the same shared secret.

The sender computes `[esk] pk_d = [esk]([ivk] g_d)`.
The recipient computes `[ivk] epk = [ivk]([esk] g_d)`.
These are equal by commutativity of scalar multiplication. -/
theorem dh_shared_secret (esk ivk : Pasta.Fq)
    (g_d : Pallas.toAffine.Point) :
    keyAgreement esk (derivePublicKey ivk g_d) =
    keyAgreement ivk (ephemeralKey esk g_d) := by
  unfold keyAgreement derivePublicKey ephemeralKey
  rw [← fqSmul_mul, ← fqSmul_mul, mul_comm]

/-- The recipient can recover the shared secret from the ephemeral key. -/
theorem recipient_recovers (esk ivk : Pasta.Fq)
    (g_d : Pallas.toAffine.Point) :
    ivk ⬝ (ephemeralKey esk g_d) =
    esk ⬝ (derivePublicKey ivk g_d) := by
  unfold ephemeralKey derivePublicKey
  rw [← fqSmul_mul, ← fqSmul_mul, mul_comm]

/-- Key agreement with zero secret key yields the identity. -/
theorem keyAgreement_zero_key (pk_d : Pallas.toAffine.Point) :
    keyAgreement 0 pk_d = 0 := by
  unfold keyAgreement; simp

/-- Key agreement distributes over key addition. -/
theorem keyAgreement_add_key (esk₁ esk₂ : Pasta.Fq)
    (pk_d : Pallas.toAffine.Point) :
    keyAgreement (esk₁ + esk₂) pk_d =
    keyAgreement esk₁ pk_d + keyAgreement esk₂ pk_d := by
  unfold keyAgreement; rw [fqSmul_add]

end

end Orchard
