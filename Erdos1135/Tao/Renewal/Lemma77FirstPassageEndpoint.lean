import Erdos1135.Tao.Renewal.HoldStoppedTail
import Erdos1135.Tao.Renewal.Lemma77HorizontalMarginal

namespace Erdos1135

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

def lemma77CenteredHorizontalDisplacement (s r : ℕ) : ℝ :=
  (r : ℝ) - (s : ℝ) / 4

def lemma77PointwiseEndpointKernel
    (A B C D : ℝ) (s r : ℕ) (overshoot : ℤ) : ℝ :=
  C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp
        (-A * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) +
      Real.exp (-B * |lemma77CenteredHorizontalDisplacement s r|)) *
    Real.exp (-D * (overshoot : ℝ))

end TaoSection7Lemma77

end

end Tao

end Erdos1135
