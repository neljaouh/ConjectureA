import Erdos1135.Tao.Fourier.Section7Cancellation
import Erdos1135.Tao.Fourier.Section7Geometry

namespace Erdos1135

namespace Tao

noncomputable def taoSection7SourceBlackPoint
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) : Prop :=
  taoSection7Black epsilon (taoSection7ThetaResidue n xi p.j p.l)

noncomputable def taoSection7SourceWhitePoint
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) : Prop :=
  taoSection7White epsilon (taoSection7ThetaResidue n xi p.j p.l)

def taoSection7SourcePointInDomain (J : ℕ) (p : TaoSection7Point) : Prop :=
  (p.j : ℕ) ≤ J

noncomputable def taoSection7SourceBlackInDomain
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ)
    (p : TaoSection7Point) : Prop :=
  taoSection7SourcePointInDomain J p ∧
    taoSection7SourceBlackPoint n xi epsilon p

theorem taoSection7SourceBlackInDomain_domain
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hp : taoSection7SourceBlackInDomain n xi epsilon J p) :
    (p.j : ℕ) ≤ J :=
  hp.1

end Tao

end Erdos1135
