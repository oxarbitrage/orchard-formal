import Poseidon.Spec
import RedPallas.Spec
import RedPallas.ScalarMul

namespace Orchard

/-! # Orchard protocol specification

Formalizes key components of the Zcash Orchard protocol:

- **Value commitment**: Pedersen commitment to transaction values
- **Nullifier derivation**: uses PoseidonHash to derive nullifiers
- **Balance**: value commitments are homomorphic, enabling balance checks

See §4.1.8, §4.7.1, §4.16, and §5.4.1 of the Zcash protocol specification.
-/

open Pasta RedPallas

noncomputable section

/-! ## Value commitment

A Pedersen commitment to a note value `v`, with randomness `rcv`.
Uses two independent generators: `ValueBaseV` for the value and
the RedPallas `BindingG` (= `R`) for the randomness.

`cv = [v] ValueBaseV + [rcv] BindingG`

See §5.4.8.3 of the Zcash protocol specification.
-/

/-- Generator for value commitments. Independent of the signing generator `G`. -/
axiom ValueBaseV : Pallas.toAffine.Point
axiom ValueBaseV_ne_zero : ValueBaseV ≠ 0

/-- Value commitment: `cv = [v] ValueBaseV + [rcv] BindingG`. -/
def valueCommit (v rcv : Pasta.Fq) : Pallas.toAffine.Point :=
  v ⬝ ValueBaseV + rcv ⬝ BindingG

/-! ## Nullifier derivation

The nullifier for an Orchard note is:

  `nf = [F_nk(rho) + psi] K + cm`

where `F_nk(rho) = PoseidonHash(nk, rho)`, `K` is the nullifier
deriving key point, and `cm` is the note commitment.

See §4.16 of the Zcash protocol specification.
-/

/-- Nullifier base point. -/
axiom K : Pallas.toAffine.Point
axiom K_ne_zero : K ≠ 0

/-- Nullifier derivation: `nf = [PoseidonHash(nk, rho) + psi] K + cm`. -/
def deriveNullifier (nk rho psi : Pasta.Fp)
    (cm : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  let f := Poseidon.poseidonHash nk rho
  (f + psi).val • K + cm

/-! ## Balance

In an Orchard transaction, the sum of input value commitments minus
the sum of output value commitments equals `[v_net] ValueBaseV + [rcv_net] BindingG`.

The binding signature verification key is exactly this net commitment,
so a valid binding signature proves balance.
-/

/-- Net value commitment: the difference of total input and output commitments
    equals a commitment to the net value with net randomness. -/
def valueCommitNet (v_net rcv_net : Pasta.Fq) : Pallas.toAffine.Point :=
  valueCommit v_net rcv_net

end

end Orchard
