import Erdos1135.Tao.Renewal.HoldExpectation
import Erdos1135.Tao.Renewal.HoldIID
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos1135

namespace Tao

def TaoSection7QBounded01
    (Q : TaoSection7RenewalPoint → ℝ) : Prop :=
  ∀ p, 0 ≤ Q p ∧ Q p ≤ 1

noncomputable def taoSection7FullHoldQRecursionRHS
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (Q : TaoSection7RenewalPoint → ℝ)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7QWhiteFactor epsilon W p *
    taoSection7HoldExpectationFull (fun h => Q (p + h))

end Tao

end Erdos1135
