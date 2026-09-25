import Erdos1135.Tao.Renewal.Lemma710PostStoppedKernel

namespace Erdos1135

namespace Tao

namespace TaoSection7Lemma710

def EprimeSourceEvent
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  EprimeVerticalSourceEvent start old verticalSourceThreshold full ∨
    EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full

end TaoSection7Lemma710

end Tao

end Erdos1135
