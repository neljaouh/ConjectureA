import Erdos1135.Basic

namespace Erdos1135

lemma collatzStep_eq_div_two_of_even {n : ℕ} (hn : Even n) :
    collatzStep n = n / 2 := by
  simp [collatzStep, CollatzConjecture.collatzStep, hn]

lemma collatzStep_eq_three_mul_add_one_of_not_even {n : ℕ} (hn : ¬ Even n) :
    collatzStep n = 3 * n + 1 := by
  simp [collatzStep, CollatzConjecture.collatzStep, hn]

end Erdos1135
