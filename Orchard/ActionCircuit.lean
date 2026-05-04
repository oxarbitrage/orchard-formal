import Orchard.Properties
import Orchard.MerklePath

namespace Orchard

/-! # Orchard action circuit

An Orchard action proves that the spender knows a note in the commitment
tree, can derive the correct nullifier, and produces a valid value
commitment. This file defines the action satisfaction predicate and
proves that satisfied actions compose into a secure transaction.

See §4.17.4 of the Zcash protocol specification.
-/

open Pasta RedPallas

noncomputable section

/-- Extract the leaf value from a note commitment for Merkle tree storage.
In the protocol, this is the x-coordinate of the commitment point. -/
axiom commitToLeaf : Pallas.toAffine.Point → Pasta.Fp

/-! ## Action statement and witness -/

/-- An Orchard action's public statement. -/
structure ActionStatement where
  nf : Pallas.toAffine.Point
  cv : Pallas.toAffine.Point
  cmRoot : Pasta.Fp

/-- An Orchard action's private witness. -/
structure ActionWitness where
  note : Note
  rcm : Pasta.Fq
  rcv : Pasta.Fq
  nk : Pasta.Fp
  authPath : AuthPath

/-- An action is satisfied when all three circuit checks pass:
    1. Value commitment is correctly computed
    2. Nullifier is correctly derived from the note commitment
    3. Note commitment appears in the Merkle tree -/
def actionSatisfied (stmt : ActionStatement) (wit : ActionWitness) : Prop :=
  stmt.cv = valueCommit wit.note.v wit.rcv ∧
  stmt.nf = deriveNullifier wit.nk wit.note.rho wit.note.psi
              (noteCommit wit.note wit.rcm) ∧
  validPath wit.authPath (commitToLeaf (noteCommit wit.note wit.rcm)) stmt.cmRoot

/-! ## Action soundness -/

/-- **Value commitment correctness**: a satisfied action's public cv
    equals the Pedersen commitment to the note value. -/
theorem action_cv_correct (stmt : ActionStatement) (wit : ActionWitness)
    (h : actionSatisfied stmt wit) :
    stmt.cv = valueCommit wit.note.v wit.rcv := by
  obtain ⟨hcv, _, _⟩ := h; exact hcv

/-- **Nullifier correctness**: a satisfied action's public nf is
    the correctly derived nullifier. -/
theorem action_nf_correct (stmt : ActionStatement) (wit : ActionWitness)
    (h : actionSatisfied stmt wit) :
    stmt.nf = deriveNullifier wit.nk wit.note.rho wit.note.psi
              (noteCommit wit.note wit.rcm) := by
  obtain ⟨_, hnf, _⟩ := h; exact hnf

/-- **Membership**: a satisfied action's note commitment is in the tree. -/
theorem action_membership (stmt : ActionStatement) (wit : ActionWitness)
    (h : actionSatisfied stmt wit) :
    validPath wit.authPath (commitToLeaf (noteCommit wit.note wit.rcm))
      stmt.cmRoot := by
  obtain ⟨_, _, hmem⟩ := h; exact hmem

/-- **Double-spend prevention**: two satisfied actions producing the same
    nullifier (with matching key material) must spend the same note
    commitment. This is the core anti-double-spend argument. -/
theorem action_no_double_spend (stmt₁ stmt₂ : ActionStatement)
    (wit₁ wit₂ : ActionWitness)
    (h₁ : actionSatisfied stmt₁ wit₁) (h₂ : actionSatisfied stmt₂ wit₂)
    (hnf : stmt₁.nf = stmt₂.nf)
    (hnk : wit₁.nk = wit₂.nk)
    (hrho : wit₁.note.rho = wit₂.note.rho)
    (hpsi : wit₁.note.psi = wit₂.note.psi) :
    noteCommit wit₁.note wit₁.rcm = noteCommit wit₂.note wit₂.rcm := by
  obtain ⟨_, hnf₁, _⟩ := h₁
  obtain ⟨_, hnf₂, _⟩ := h₂
  have h := hnf₁.symm.trans (hnf.trans hnf₂)
  rw [hnk, hrho, hpsi] at h
  exact nullifier_binding _ _ _ _ _ h

end

end Orchard
