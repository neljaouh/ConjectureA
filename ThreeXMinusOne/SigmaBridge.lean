import ThreeXMinusOne.UnitPhysicalMap

/-!
# Packet sums: `Σ`-form and double-sum form

Layer 43 had to state its bound over a `Σ` type because `Fintype.sum_sigma` timed out in `whnf`
inside that proof.  The census files ahead state everything as `∑ i, ∑ z`, so the two forms have
to be reconciled somewhere.  This file is that reconciliation, isolated: whether it elaborates at
all is the question, and keeping it in one small file makes the answer cheap to obtain.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators

noncomputable section

variable {Label : Type*} [Fintype Label] [DecidableEq Label] {root : Label → ℕ}

theorem sum_sigma_packetM (shift : Label → ℕ) (b K : ℕ)
    (f : (i : Label) → UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K → ℝ) :
    (∑ z : Σ i : Label, UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K,
      f z.1 z.2) =
      ∑ i : Label, ∑ z : UnitChildIncidenceM ({i} : Finset Label) root b (shift i) K, f i z :=
  Fintype.sum_sigma _

end

end ThreeXMinusOne
