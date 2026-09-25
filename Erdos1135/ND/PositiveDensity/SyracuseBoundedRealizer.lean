import Erdos1135.Tao.Fourier.Section7SourceLaw

namespace Erdos1135

namespace ND

namespace PositiveDensity

noncomputable section

def ndThreeUnitResidue {m : ℕ} (x : ZMod (3 ^ m)) : Prop :=
  x.val % 3 ≠ 0

end

end PositiveDensity

end ND

end Erdos1135
