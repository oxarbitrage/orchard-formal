import Orchard.Spec
import RedPallas.Properties
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

/-- Value commitment sum homomorphism: the sum of individual commitments
    equals a commitment to the sums of values and randomness. -/
theorem valueCommit_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (v rcv : ι → Pasta.Fq) :
    ∑ i ∈ s, valueCommit (v i) (rcv i) =
    valueCommit (∑ i ∈ s, v i) (∑ i ∈ s, rcv i) := by
  induction s using Finset.induction_on with
  | empty => simp [valueCommit_zero]
  | @insert a s hmem ih =>
    rw [Finset.sum_insert hmem, Finset.sum_insert hmem, Finset.sum_insert hmem,
        ih, valueCommit_add]

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

/-- **Multi-action balance**: the net commitment across n actions equals
    a commitment to the net value and net randomness. -/
theorem balance_multi {ι : Type} [DecidableEq ι] (s : Finset ι)
    (v_in v_out rcv_in rcv_out : ι → Pasta.Fq) :
    (∑ i ∈ s, valueCommit (v_in i) (rcv_in i)) -
    (∑ i ∈ s, valueCommit (v_out i) (rcv_out i)) =
    valueCommit ((∑ i ∈ s, v_in i) - ∑ i ∈ s, v_out i)
               ((∑ i ∈ s, rcv_in i) - ∑ i ∈ s, rcv_out i) := by
  rw [valueCommit_sum, valueCommit_sum, valueCommit_sub]

/-- **Multi-action binding**: for a balanced multi-action transaction,
    the net commitment depends only on the randomness difference. -/
theorem balance_multi_binding {ι : Type} [DecidableEq ι] (s : Finset ι)
    (v_in v_out rcv_in rcv_out : ι → Pasta.Fq)
    (hbal : ∑ i ∈ s, v_in i = ∑ i ∈ s, v_out i) :
    (∑ i ∈ s, valueCommit (v_in i) (rcv_in i)) -
    (∑ i ∈ s, valueCommit (v_out i) (rcv_out i)) =
    ((∑ i ∈ s, rcv_in i) - ∑ i ∈ s, rcv_out i) ⬝ BindingG := by
  rw [balance_multi, hbal, sub_self, balanced_bvk]

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

/-! ## Note commitment properties -/

/-- **Note commitment binding**: for the same note, equal commitments
    imply equal randomness blinding (at the group level). -/
theorem noteCommit_binding (note : Note) (rcm₁ rcm₂ : Pasta.Fq)
    (h : noteCommit note rcm₁ = noteCommit note rcm₂) :
    rcm₁ ⬝ NoteCommitR = rcm₂ ⬝ NoteCommitR := by
  unfold noteCommit at h
  exact add_left_cancel h

/-- **Note-to-nullifier binding**: the nullifier derived from a note
    commitment binds to that specific commitment. -/
theorem note_nullifier_binding (nk rho psi : Pasta.Fp)
    (note₁ note₂ : Note) (rcm₁ rcm₂ : Pasta.Fq)
    (h : deriveNullifier nk rho psi (noteCommit note₁ rcm₁) =
         deriveNullifier nk rho psi (noteCommit note₂ rcm₂)) :
    noteCommit note₁ rcm₁ = noteCommit note₂ rcm₂ :=
  nullifier_binding nk rho psi _ _ h

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

/-! ## Spend authorization composite

The full security argument for Orchard spend authorization combines:
1. **Balance integrity**: value commitment homomorphism ensures the
   net commitment reduces to a randomness commitment for balanced txns.
2. **Binding signature**: verifiable knowledge of `rcv_net` proves balance.
3. **Double-spend prevention**: nullifier binding ensures each note maps
   to a unique nullifier.

See §4.16 and §5.4.8.3 of the Zcash protocol specification.
-/

/-- **Balance reduces to randomness**: for a balanced transaction,
    the net value commitment depends only on the randomness difference. -/
theorem spend_auth_balance (v_in v_out rcv_in rcv_out : Pasta.Fq)
    (hbal : v_in = v_out) :
    valueCommit v_in rcv_in - valueCommit v_out rcv_out =
    (rcv_in - rcv_out) ⬝ BindingG := by
  rw [valueCommit_sub, hbal, sub_self, balanced_bvk]

/-- **Nullifier uniqueness**: distinct note commitments produce distinct
    nullifiers (for the same nk, rho, psi). Contrapositive of
    `nullifier_binding`; captures double-spend prevention. -/
theorem nullifier_uniqueness (nk rho psi : Pasta.Fp)
    (cm₁ cm₂ : Pallas.toAffine.Point) (hcm : cm₁ ≠ cm₂) :
    deriveNullifier nk rho psi cm₁ ≠ deriveNullifier nk rho psi cm₂ := by
  intro h
  exact hcm (nullifier_binding nk rho psi cm₁ cm₂ h)

/-- **Spend authorization composite**: for a balanced transaction with
    distinct notes, all three security properties hold simultaneously:
    1. Net commitment = randomness commitment (balance integrity)
    2. Binding signature verifies (knowledge of rcv_net)
    3. Nullifiers are distinct (double-spend prevention) -/
theorem spend_authorization (v_in v_out rcv_in rcv_out : Pasta.Fq)
    (nk rho psi : Pasta.Fp) (cm₁ cm₂ : Pallas.toAffine.Point)
    (msg : List UInt8) (r : Pasta.Fq)
    (hbal : v_in = v_out) (hcm : cm₁ ≠ cm₂) :
    (valueCommit v_in rcv_in - valueCommit v_out rcv_out =
     (rcv_in - rcv_out) ⬝ BindingG) ∧
    (let bvk := (rcv_in - rcv_out) ⬝ BindingG
     let R := r ⬝ BindingG
     let c := challengeHash R bvk msg
     (r + c * (rcv_in - rcv_out)) ⬝ BindingG = R + c ⬝ bvk) ∧
    (deriveNullifier nk rho psi cm₁ ≠ deriveNullifier nk rho psi cm₂) :=
  ⟨spend_auth_balance v_in v_out rcv_in rcv_out hbal,
   verify_sign_generic BindingG (rcv_in - rcv_out) msg r,
   nullifier_uniqueness nk rho psi cm₁ cm₂ hcm⟩

end

end Orchard
