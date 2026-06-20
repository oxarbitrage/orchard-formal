import Orchard.Spec
import RedPallas.Extractability

namespace Orchard

/-! # Balance from binding signature extractability

The forward direction (balance → valid binding sig) is in `Properties.lean`.
This file proves the reverse: from a valid binding signature, conclude balance.

The argument (following Zcash spec §4.14):
1. The binding verification key decomposes as `bvk = A ⬝ V + B ⬝ R` where
   `A = Σv_in - Σv_out - v_balance` and `B = Σrcv_in - Σrcv_out`.
2. Extractability (from `RedPallas.Extractability`): a valid binding signature
   yields `bsk` such that `bvk = bsk ⬝ R`.
3. Substituting: `A ⬝ V = (bsk - B) ⬝ R`. If `A ≠ 0`, this is a nontrivial
   discrete-log relation between `V` and `R`.
4. Under DLR hardness, no such relation exists, so `A = 0`: the bundle balances.

Step 4 is a computational assumption, stated as a hypothesis.
-/

open Pasta RedPallas

noncomputable section

/-! ## Part 1: Imbalance exhibits a DLR relation -/

/-- From extractability (`bvk = bsk ⬝ BindingG`) and the value commitment
decomposition (`bvk = A ⬝ ValueBaseV + B ⬝ BindingG`), the value coefficient
satisfies `A ⬝ ValueBaseV = (bsk - B) ⬝ BindingG`. Pure algebra. -/
theorem value_coeff_eq_rand (A B bsk : Pasta.Fq)
    (hExtract : A ⬝ ValueBaseV + B ⬝ BindingG = bsk ⬝ BindingG) :
    A ⬝ ValueBaseV = (bsk - B) ⬝ BindingG := by
  have h : A ⬝ ValueBaseV = bsk ⬝ BindingG - B ⬝ BindingG := by
    calc A ⬝ ValueBaseV
        = A ⬝ ValueBaseV + B ⬝ BindingG - B ⬝ BindingG := (add_sub_cancel_right _ _).symm
      _ = bsk ⬝ BindingG - B ⬝ BindingG := by rw [hExtract]
  rw [h, ← fqSmul_sub]

/-- If the bundle is imbalanced (`A ≠ 0`) and extractability holds, then
`ValueBaseV` and `BindingG` satisfy a nontrivial DLR relation:
`A ⬝ ValueBaseV + (B - bsk) ⬝ BindingG = 0` with `A ≠ 0`. -/
theorem relation_of_imbalance (A B bsk : Pasta.Fq)
    (hA : A ≠ 0)
    (hExtract : A ⬝ ValueBaseV + B ⬝ BindingG = bsk ⬝ BindingG) :
    A ≠ 0 ∧ A ⬝ ValueBaseV + (B - bsk) ⬝ BindingG = 0 := by
  refine ⟨hA, ?_⟩
  have := value_coeff_eq_rand A B bsk hExtract
  rw [this, ← fqSmul_add]
  have : (bsk - B) + (B - bsk) = (0 : Pasta.Fq) := by ring
  rw [this, fqSmul_zero]

/-! ## Part 2: DLR assumption implies field balance -/

/-- DLR hardness for `ValueBaseV` and `BindingG`: the only linear relation
`a ⬝ ValueBaseV + b ⬝ BindingG = 0` is the trivial one (`a = 0 ∧ b = 0`).

This is a computational assumption — it holds in the generic group model and
under the discrete-log assumption for the Pallas curve. -/
def DLR_Hard : Prop :=
  ∀ a b : Pasta.Fq, a ⬝ ValueBaseV + b ⬝ BindingG = 0 → a = 0 ∧ b = 0

/-- **Field balance from extractability + DLR**: if the binding signature is
valid (extractability gives `bvk = bsk ⬝ BindingG`) and DLR holds for the
generators, then `A = 0` — the bundle balances in `Fq`. -/
theorem field_balance_of_extract (A B bsk : Pasta.Fq)
    (hDLR : DLR_Hard)
    (hExtract : A ⬝ ValueBaseV + B ⬝ BindingG = bsk ⬝ BindingG) :
    A = 0 := by
  by_contra hA
  have ⟨_, hrel⟩ := relation_of_imbalance A B bsk hA hExtract
  have ⟨hA', _⟩ := hDLR A (B - bsk) hrel
  exact hA hA'

/-! ## Part 3: Integer lift — field balance implies integer balance -/

/-- If an integer is zero modulo `q` and its absolute value is less than `q`,
then it is zero. This lifts field balance to integer balance. -/
theorem int_balance_of_field_balance (x : ℤ) (q : ℕ) [NeZero q]
    (hfield : (x : ZMod q) = 0)
    (hbound : x.natAbs < q) :
    x = 0 := by
  have hdvd : (q : ℤ) ∣ x := (CharP.intCast_eq_zero_iff (ZMod q) q x).mp hfield
  rcases hdvd with ⟨k, hk⟩
  rcases eq_or_ne k 0 with rfl | hk_ne
  · simp_all
  · exfalso
    have habs_pos : 0 < k.natAbs := Int.natAbs_pos.mpr hk_ne
    have : q ≤ x.natAbs := by
      rw [hk, Int.natAbs_mul]
      simp only [Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right q habs_pos
    omega

/-! ## Composite: end-to-end balance -/

/-- **End-to-end balance**: given a bundle where
- `v_net` is the net value (Σv_in - Σv_out - v_balance) as an integer
- `rcv_net` is the net randomness
- a valid binding signature yields `bsk` via extractability
- DLR holds for the generators
- `|v_net| < q` (guaranteed by 64-bit value range and action count bounds)

then `v_net = 0`: no value is created or destroyed. -/
theorem bundle_balances (v_net : ℤ) (rcv_net bsk : Pasta.Fq)
    (hDLR : DLR_Hard)
    (hExtract : (v_net : Pasta.Fq) ⬝ ValueBaseV + rcv_net ⬝ BindingG = bsk ⬝ BindingG)
    (hbound : v_net.natAbs < Fq.p) :
    v_net = 0 := by
  have hfield : (v_net : Pasta.Fq) = 0 :=
    field_balance_of_extract (v_net : Pasta.Fq) rcv_net bsk hDLR hExtract
  exact int_balance_of_field_balance v_net Fq.p hfield hbound

end

end Orchard
