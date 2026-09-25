import Erdos1135.Tao.Probability.Geom
import Erdos1135.Tao.Syracuse.Affine
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card

namespace Erdos1135

namespace Tao

abbrev PNatBelow (M : ℕ) : Type :=
  {a : Fin M // 0 < (a : ℕ)}

namespace PNatBelow

def toPNat {M : ℕ} (a : PNatBelow M) : ℕ+ :=
  ⟨a.1, a.2⟩

instance (M : ℕ) : Fintype (PNatBelow M) := inferInstance

end PNatBelow

abbrev BoundedValuationTuple (n M : ℕ) : Type :=
  {v : Fin n → PNatBelow M //
    (Finset.univ.sum fun i => (PNatBelow.toPNat (v i) : ℕ)) < M}

namespace BoundedValuationTuple

instance (n M : ℕ) : Fintype (BoundedValuationTuple n M) := inferInstance

def toList {n M : ℕ} (v : BoundedValuationTuple n M) : List ℕ+ :=
  List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)

theorem toList_length {n M : ℕ} (v : BoundedValuationTuple n M) :
    (toList v).length = n := by
  simp [toList]

end BoundedValuationTuple

end Tao

end Erdos1135
