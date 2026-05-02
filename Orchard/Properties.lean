import Orchard.Spec

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

end

end Orchard
