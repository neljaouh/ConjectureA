import Erdos1135.Tao.Probability.PascalPrime
import Mathlib.Tactic

namespace Erdos1135

namespace Tao

@[ext]
structure TaoSection7RenewalPoint where
  j : ℕ+
  l : ℤ
deriving DecidableEq, Repr

namespace TaoSection7RenewalPoint

def add (p h : TaoSection7RenewalPoint) : TaoSection7RenewalPoint :=
  { j := p.j + h.j
    l := p.l + h.l }

instance : Add TaoSection7RenewalPoint where
  add := add

@[simp] theorem add_j (p h : TaoSection7RenewalPoint) :
    (p + h).j = p.j + h.j :=
  rfl

@[simp] theorem add_l (p h : TaoSection7RenewalPoint) :
    (p + h).l = p.l + h.l :=
  rfl

end TaoSection7RenewalPoint

namespace TaoSection7HoldPoint

end TaoSection7HoldPoint

def taoSection7ShiftIndex (j : ℕ+) (n : ℕ) : ℕ+ :=
  ⟨(j : ℕ) + n, Nat.add_pos_left j.2 n⟩

@[simp] theorem taoSection7ShiftIndex_one_zero (n : ℕ) :
    taoSection7ShiftIndex (1 : ℕ+) n =
      ⟨n + 1, Nat.succ_pos n⟩ := by
  apply Subtype.ext
  simp [taoSection7ShiftIndex]
  omega

end Tao

end Erdos1135
