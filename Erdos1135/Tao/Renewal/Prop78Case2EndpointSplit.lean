import Erdos1135.Tao.Renewal.Prop78Case1White

namespace Erdos1135

namespace Tao

theorem taoSection7QmBoundary_of_horizontalAdvance
    {J m r : ℕ} {p q : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary J m p)
    (hjq : (q.j : ℕ) = (p.j : ℕ) + r)
    (hr : r < m) :
    taoSection7QmBoundary J (m - r) q := by
  unfold taoSection7QmBoundary at *
  omega

end Tao

end Erdos1135
