import Erdos1135.Tao.Section6.ConductorDFT

namespace Erdos1135

namespace Tao

theorem taoSection6_conductor_add_eq_tail_and_positive
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    r + j = T ∧ 1 ≤ r := by
  omega

theorem taoSection6_m_sub_k_le_conductor
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    m - k ≤ r := by
  omega

theorem taoSection6_head_add_frequency_add_conductor_eq
    {n k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T) :
    k + j + 1 + r = n := by
  omega

theorem taoSection6_n_le_twenty_mul_m_sub_k
    {n m k : ℕ} (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    n ≤ 20 * (m - k) := by
  omega

theorem taoSection6_conductor_index_bounds
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    r + j = T ∧
      1 ≤ r ∧
      m - k ≤ r ∧
      n ≤ 20 * (m - k) ∧
      n ≤ 20 * r := by
  have hadd_pos :=
    taoSection6_conductor_add_eq_tail_and_positive
      htail hconductor hhead hfrequency
  have hmkr :=
    taoSection6_m_sub_k_le_conductor
      htail hconductor hhead hfrequency
  have hnmk := taoSection6_n_le_twenty_mul_m_sub_k hhead hm hk
  omega

end Tao

end Erdos1135
