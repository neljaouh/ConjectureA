import Erdos1135.Tao.Section6.Corollary63

namespace Erdos1135

namespace Tao

noncomputable section

noncomputable def taoSection6HeadGate
    (CA : ℝ) (n k l : ℕ) (head : List ℕ+) : Prop :=
  head.length = k + 1 ∧
    taoCor63StarInclusiveTypical CA n head ∧
    ((taoTupleWeight (head.take k) : ℕ) : ℝ) ≤ taoCor63StarQ CA n ∧
    taoCor63StarQ CA n < ((taoTupleWeight head : ℕ) : ℝ) ∧
    taoTupleWeight head = l

theorem taoSection6HeadGate_length
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    head.length = k + 1 :=
  h.1

theorem taoSection6HeadGate_typical
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    taoCor63StarInclusiveTypical CA n head :=
  h.2.1

theorem taoSection6HeadGate_crossing
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    ((taoTupleWeight (head.take k) : ℕ) : ℝ) ≤ taoCor63StarQ CA n ∧
      taoCor63StarQ CA n < ((taoTupleWeight head : ℕ) : ℝ) :=
  ⟨h.2.2.1, h.2.2.2.1⟩

theorem taoSection6HeadGate_weight
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    taoTupleWeight head = l :=
  h.2.2.2.2

end

end Tao

end Erdos1135
