import Erdos1135.Tao.Syracuse.CollatzBridge

namespace Erdos1135

def Reaches (a b : ℕ) : Prop :=
  ∃ m, collatzStep^[m] a = b

lemma reaches_refl (n : ℕ) : Reaches n n :=
  ⟨0, rfl⟩

lemma reaches_of_step_eq {a b : ℕ} (h : collatzStep a = b) :
    Reaches a b :=
  ⟨1, by simpa only [Function.iterate_one] using h⟩

lemma Reaches.trans {a b c : ℕ} (hab : Reaches a b) (hbc : Reaches b c) :
    Reaches a c := by
  rcases hab with ⟨m, hm⟩
  rcases hbc with ⟨n, hn⟩
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply, hm, hn]

lemma iterate_collatzStep_succ_apply (m n : ℕ) :
    collatzStep^[m.succ] n = collatzStep^[m] (collatzStep n) := by
  rw [Function.iterate_succ_apply]

namespace Tao

theorem reaches_powTwo_mul (a M : ℕ) :
    Reaches ((2 : ℕ) ^ a * M) M :=
  ⟨a, collatz_iterate_powTwo_mul a M⟩

theorem reaches_syracuse {M : ℕ} (hM : Odd M) :
    Reaches M (syracuse M) :=
  ⟨syracuseExponent M + 1, collatz_iterate_syracuse_block hM⟩

theorem reaches_syracuse_iterate {M : ℕ} (hM : Odd M) (k : ℕ) :
    Reaches M ((syracuse^[k]) M) := by
  induction k generalizing M with
  | zero =>
      simpa using reaches_refl M
  | succ k ih =>
      have hhead : Reaches M (syracuse M) := reaches_syracuse hM
      have htail : Reaches (syracuse M) ((syracuse^[k]) (syracuse M)) :=
        ih (syracuse_odd M)
      simpa only [Function.iterate_succ_apply] using hhead.trans htail

end Tao

def ReachesOne (n : ℕ) : Prop :=
  Reaches n 1

lemma reachesOne_step_of_reachesOne {n : ℕ} (h : ReachesOne n) :
    ReachesOne (collatzStep n) := by
  rcases h with ⟨m, hm⟩
  cases m with
  | zero =>
      subst hm
      exact ⟨2, by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        norm_num [collatzStep, CollatzConjecture.collatzStep]⟩
  | succ m =>
      exact ⟨m, by
        simpa [iterate_collatzStep_succ_apply] using hm⟩

lemma reachesOne_iterate_of_reachesOne {n : ℕ} (h : ReachesOne n) (m : ℕ) :
    ReachesOne (collatzStep^[m] n) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      simpa [Function.iterate_succ_apply'] using reachesOne_step_of_reachesOne ih

lemma reachesOne_tail_of_reachesOne_of_iterate_eq {a b : ℕ} {m : ℕ}
    (hiter : collatzStep^[m] a = b)
    (h : ReachesOne a) :
    ReachesOne b := by
  simpa [hiter] using reachesOne_iterate_of_reachesOne h m

end Erdos1135
