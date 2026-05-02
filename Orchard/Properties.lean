import Orchard.Spec
import RedPallas.Properties

namespace Orchard

/-! # Properties of Orchard protocol components

Key properties:

1. **Value commitment homomorphism**: `valueCommit` is additively homomorphic,
   enabling balance verification without revealing values.

2. **Binding signature correctness**: the net value commitment serves as
   the binding verification key.
-/

open Pasta RedPallas

noncomputable section

/-! ## Value commitment homomorphism

The value commitment scheme is additively homomorphic:
  `valueCommit(v₁, rcv₁) + valueCommit(v₂, rcv₂) = valueCommit(v₁+v₂, rcv₁+rcv₂)`

This allows miners to verify that inputs and outputs balance by checking
a binding signature, without learning any values.
-/

/-- Value commitments are additively homomorphic. -/
theorem valueCommit_add (v₁ v₂ rcv₁ rcv₂ : Pasta.Fq) :
    valueCommit v₁ rcv₁ + valueCommit v₂ rcv₂ =
    valueCommit (v₁ + v₂) (rcv₁ + rcv₂) := by
  unfold valueCommit
  rw [fqSmul_add v₁ v₂ ValueBaseV, fqSmul_add rcv₁ rcv₂ BindingG]
  abel

/-- Committing to zero value with zero randomness gives the identity. -/
theorem valueCommit_zero : valueCommit 0 0 = 0 := by
  unfold valueCommit
  simp [fqSmul_def, ZMod.val_zero]

/-- Value commitment negation: negating both value and randomness
    negates the commitment. -/
theorem valueCommit_neg (v rcv : Pasta.Fq) :
    valueCommit (-v) (-rcv) = -valueCommit v rcv := by
  unfold valueCommit
  rw [fqSmul_neg, fqSmul_neg]
  abel

/-- Value commitment subtraction. -/
theorem valueCommit_sub (v₁ v₂ rcv₁ rcv₂ : Pasta.Fq) :
    valueCommit v₁ rcv₁ - valueCommit v₂ rcv₂ =
    valueCommit (v₁ - v₂) (rcv₁ - rcv₂) := by
  simp only [sub_eq_add_neg]
  rw [← valueCommit_neg, valueCommit_add]

/-! ## Balance verification

In an Orchard Action, input value commitments minus output value commitments
equals a commitment to the net value flow. The binding signature proves
the prover knows `rcv_net`, which (together with range proofs in the circuit)
ensures balance.
-/

/-- Balance equation: the sum of input commitments minus the sum of output
    commitments equals a commitment to the net value and net randomness.

    For a single input/output pair. -/
theorem balance_single (v_in v_out rcv_in rcv_out : Pasta.Fq) :
    valueCommit v_in rcv_in - valueCommit v_out rcv_out =
    valueCommit (v_in - v_out) (rcv_in - rcv_out) :=
  valueCommit_sub v_in v_out rcv_in rcv_out

/-- The binding verification key for a balanced transaction (net value = 0)
    is independent of the value generators. -/
theorem balanced_bvk (rcv_net : Pasta.Fq) :
    valueCommit 0 rcv_net = rcv_net ⬝ BindingG := by
  unfold valueCommit
  simp [fqSmul_def, ZMod.val_zero]

/-! ## Nullifier properties -/

/-- **Nullifier determinism**: the same inputs always produce the same nullifier. -/
theorem deriveNullifier_deterministic (nk rho psi : Pasta.Fp)
    (cm : Pallas.toAffine.Point) :
    deriveNullifier nk rho psi cm = deriveNullifier nk rho psi cm := rfl

/-- **Nullifier binding (w.r.t. note commitment)**: for fixed `nk`, `rho`, `psi`,
    equal nullifiers imply equal note commitments.

    This is essential for preventing double-spending: each note has a unique
    nullifier, so revealing a nullifier publicly marks exactly one note as spent. -/
theorem nullifier_binding (nk rho psi : Pasta.Fp)
    (cm₁ cm₂ : Pallas.toAffine.Point)
    (h : deriveNullifier nk rho psi cm₁ = deriveNullifier nk rho psi cm₂) :
    cm₁ = cm₂ := by
  unfold deriveNullifier at h
  exact add_left_cancel h

/-- **Nullifier binding (w.r.t. psi)**: for fixed `nk`, `rho`, `cm`,
    if two different `psi` values produce the same nullifier, then the
    scalar multiples of `K` must collide.

    Full collision resistance requires the discrete log assumption on `K`. -/
theorem nullifier_psi_collision (nk rho psi₁ psi₂ : Pasta.Fp)
    (cm : Pallas.toAffine.Point)
    (h : deriveNullifier nk rho psi₁ cm = deriveNullifier nk rho psi₂ cm) :
    (Poseidon.poseidonHash nk rho + psi₁).val • K =
    (Poseidon.poseidonHash nk rho + psi₂).val • K := by
  unfold deriveNullifier at h
  exact add_right_cancel h

/-! ## Binding signature correctness

The binding signature proves balance. In Orchard:
1. Each action has a value commitment `cv = valueCommit(v, rcv)`
2. The binding verification key is `bvk = Σ cv_in - Σ cv_out`
3. By homomorphism, `bvk = valueCommit(v_net, rcv_net)`
4. For a balanced transaction (`v_net = 0`), `bvk = [rcv_net] BindingG`
5. The prover signs with `rcv_net` using generator `BindingG`
6. A valid signature proves knowledge of `rcv_net`, hence balance
-/

/-- **Binding signature verification**: for a balanced transaction,
    signing with `rcv_net` as the secret key and `BindingG` as the
    generator produces a signature that verifies against the binding
    verification key `bvk = valueCommit 0 rcv_net`.

    Uses `verify_sign_generic` from RedPallas: the RedDSA verification
    equation holds for any generator point. -/
theorem binding_sig_verify (rcv_net : Pasta.Fq) (msg : List UInt8)
    (r : Pasta.Fq) :
    let bvk := rcv_net ⬝ BindingG
    let R := r ⬝ BindingG
    let c := challengeHash R bvk msg
    let S := r + c * rcv_net
    S ⬝ BindingG = R + c ⬝ bvk := by
  exact verify_sign_generic BindingG rcv_net msg r

/-- **Balance implies valid binding signature**: if a transaction is balanced
    (net value = 0), then the binding verification key is `[rcv_net] BindingG`,
    and signing with `rcv_net` produces a valid binding signature. -/
theorem balance_binding_sig (rcv_net : Pasta.Fq) (msg : List UInt8)
    (r : Pasta.Fq) :
    let bvk := valueCommit 0 rcv_net
    let R := r ⬝ BindingG
    let c := challengeHash R bvk msg
    let S := r + c * rcv_net
    S ⬝ BindingG = R + c ⬝ bvk := by
  simp only [balanced_bvk]
  exact verify_sign_generic BindingG rcv_net msg r

end

end Orchard
