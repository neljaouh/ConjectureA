import ThreeXMinusOne.Map
import Erdos1135.Tao.Syracuse.FirstPassageInterval
import Erdos1135.Tao.Syracuse.ValuationDistribution
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reverse edges and prefix-mass telescoping for `3x−1`

Layer 2 of the port: `CommonZReverseGenerator` and `CommonZPathTelescoping` with the sign
reversed.  The list-level machinery (`taoTupleWeight`, `geom2PNatListMass`) is generic in the
map and is reused verbatim from the artifact.

**This is where the first of the two sign reversals actually lands.**  On the `+1` side
`ndCommonZOrbitPrefixMass_eq_next_add_defect` has a *non-negative* defect, so the prefix mass is
antitone and `ndCommonZOrbitPrefixMass_le_zero` bounds it by `1/N` for every depth.  Here the
defect is negative, that argument is unavailable, and `prefixMassM_succ_eq_mul` replaces it: the
mass is multiplied by exactly `1 + 1/(3s_k−1)` at each step.  `prefixMassM_le_of_floor` then
recovers a bound of the same shape as `..._le_zero`, paying a factor `(1+1/(3R−1))^k` whenever
every source on the prefix is at least `R`.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.Tao

noncomputable section

/-! ## The valuation word of a `3x−1` orbit -/

def syrMValuationPNatList : (n N : ℕ) → Odd N → List ℕ+
  | 0, _N, _hN => []
  | n + 1, N, hN =>
      ⟨syrMExponent N, syrMExponent_pos_of_odd hN⟩ ::
        syrMValuationPNatList n (syrM N) (syrM_odd hN.pos)

theorem syrMValuationPNatList_add (m n N : ℕ) (hN : Odd N) :
    syrMValuationPNatList (m + n) N hN =
      syrMValuationPNatList m N hN ++
        syrMValuationPNatList n ((syrM^[m]) N) (syrM_iterate_odd m N hN) := by
  induction m generalizing N with
  | zero => simp [syrMValuationPNatList]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [syrMValuationPNatList, List.cons_append]
      rw [ih (syrM N) (syrM_odd hN.pos)]
      congr 2

def syrMTerminalExponentPNat (r M : ℕ) (hM : Odd M) : ℕ+ :=
  ⟨syrMExponent ((syrM^[r]) M), syrMExponent_pos_of_odd (syrM_iterate_odd r M hM)⟩

theorem syrMValuationPNatList_succ_eq_append_terminal (r M : ℕ) (hM : Odd M) :
    syrMValuationPNatList (r + 1) M hM =
      syrMValuationPNatList r M hM ++ [syrMTerminalExponentPNat r M hM] := by
  rw [syrMValuationPNatList_add r 1 M hM]
  simp [syrMValuationPNatList, syrMTerminalExponentPNat]

theorem taoTupleWeight_syrMValuationPNatList_succ (r M : ℕ) (hM : Odd M) :
    taoTupleWeight (syrMValuationPNatList (r + 1) M hM) =
      taoTupleWeight (syrMValuationPNatList r M hM) +
        (syrMTerminalExponentPNat r M hM : ℕ) := by
  rw [syrMValuationPNatList_succ_eq_append_terminal, taoTupleWeight_append_trajectory]
  simp [taoTupleWeight]

/-! ## Reverse edges -/

/-- A reverse edge of the `3x−1` backward generator, `2^exponent · target = 3·source − 1`,
written without truncated subtraction.  Mirrors `NDCommonZReverseEdge`. -/
structure EdgeM where
  source : ℕ
  target : ℕ
  exponent : ℕ
  source_pos : 0 < source
  target_pos : 0 < target
  affine : 2 ^ exponent * target + 1 = 3 * source

namespace EdgeM

variable (q : ℕ) (e : EdgeM)

def sourceWeight : ℝ := (3 : ℝ) ^ q / (e.source : ℝ)

def transportedWeight : ℝ :=
  (3 : ℝ) ^ (q + 1) / ((2 : ℝ) ^ e.exponent * (e.target : ℝ))

/-- The magnitude of the (now negative) transport defect. -/
def excess : ℝ := (3 : ℝ) ^ q / ((e.source : ℝ) * (3 * (e.source : ℝ) - 1))

theorem source_pos_real : (0 : ℝ) < (e.source : ℝ) := by exact_mod_cast e.source_pos

theorem three_source_sub_one_pos : (0 : ℝ) < 3 * (e.source : ℝ) - 1 := by
  have h1 : (1 : ℝ) ≤ (e.source : ℝ) := by exact_mod_cast e.source_pos
  linarith

theorem affine_real : (2 : ℝ) ^ e.exponent * (e.target : ℝ) = 3 * (e.source : ℝ) - 1 := by
  have h : ((2 ^ e.exponent * e.target + 1 : ℕ) : ℝ) = ((3 * e.source : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) e.affine
  push_cast at h
  linarith

theorem excess_nonneg : 0 ≤ e.excess q := by
  have h1 := e.source_pos_real
  have h2 := e.three_source_sub_one_pos
  unfold excess
  positivity

/-- **The sharp multiplicative form of the reversal.** -/
theorem transported_eq_source_mul :
    e.transportedWeight q = e.sourceWeight q * (1 + 1 / (3 * (e.source : ℝ) - 1)) := by
  have hs : (e.source : ℝ) ≠ 0 := ne_of_gt e.source_pos_real
  have hd : 3 * (e.source : ℝ) - 1 ≠ 0 := ne_of_gt e.three_source_sub_one_pos
  unfold transportedWeight sourceWeight
  rw [e.affine_real, pow_succ]
  field_simp
  ring

/-- Where `3x+1` has `source = transported + defect`, `3x−1` has `source = transported − excess`. -/
theorem source_eq_transported_sub_excess :
    e.sourceWeight q = e.transportedWeight q - e.excess q := by
  have hs : (e.source : ℝ) ≠ 0 := ne_of_gt e.source_pos_real
  have hd : 3 * (e.source : ℝ) - 1 ≠ 0 := ne_of_gt e.three_source_sub_one_pos
  rw [e.transported_eq_source_mul q]
  unfold excess sourceWeight
  field_simp
  ring

end EdgeM

/-- The actual backward edge at an odd point of the `3x−1` dynamics. -/
def actualEdgeM (v : ℕ) (hv : 0 < v) : EdgeM where
  source := v
  target := syrM v
  exponent := syrMExponent v
  source_pos := hv
  target_pos := syrM_pos hv
  affine := two_pow_syrMExponent_mul_syrM_add_one hv

def orbitEdgeM (N : ℕ) (hN : Odd N) (k : ℕ) : EdgeM :=
  actualEdgeM ((syrM^[k]) N) (syrM_iterate_pos k N hN)

@[simp] theorem orbitEdgeM_source (N : ℕ) (hN : Odd N) (k : ℕ) :
    (orbitEdgeM N hN k).source = (syrM^[k]) N := rfl

@[simp] theorem orbitEdgeM_target (N : ℕ) (hN : Odd N) (k : ℕ) :
    (orbitEdgeM N hN k).target = (syrM^[k + 1]) N := by
  unfold orbitEdgeM actualEdgeM
  simp only
  rw [Function.iterate_succ_apply']

@[simp] theorem orbitEdgeM_exponent (N : ℕ) (hN : Odd N) (k : ℕ) :
    (orbitEdgeM N hN k).exponent = syrMExponent ((syrM^[k]) N) := rfl

/-! ## Prefix mass -/

def prefixGeomMassM (N : ℕ) (hN : Odd N) (k : ℕ) : ℝ :=
  geom2PNatListMass (syrMValuationPNatList k N hN)

def prefixMassM (N : ℕ) (hN : Odd N) (k : ℕ) : ℝ :=
  prefixGeomMassM N hN k * (orbitEdgeM N hN k).sourceWeight k

theorem prefixGeomMassM_pos (N : ℕ) (hN : Odd N) (k : ℕ) : 0 < prefixGeomMassM N hN k := by
  unfold prefixGeomMassM
  rw [geom2PNatListMass_eq_inv_pow]
  positivity

theorem prefixGeomMassM_succ (N : ℕ) (hN : Odd N) (k : ℕ) :
    prefixGeomMassM N hN (k + 1) =
      prefixGeomMassM N hN k / (2 : ℝ) ^ syrMExponent ((syrM^[k]) N) := by
  unfold prefixGeomMassM
  rw [geom2PNatListMass_eq_inv_pow, geom2PNatListMass_eq_inv_pow,
    taoTupleWeight_syrMValuationPNatList_succ]
  rw [pow_add]
  simp [syrMTerminalExponentPNat]
  rw [div_eq_mul_inv]
  ring

theorem orbit_transport_eq_nextMassM (N : ℕ) (hN : Odd N) (k : ℕ) :
    prefixGeomMassM N hN k * (orbitEdgeM N hN k).transportedWeight k =
      prefixMassM N hN (k + 1) := by
  unfold prefixMassM
  rw [prefixGeomMassM_succ]
  unfold EdgeM.transportedWeight EdgeM.sourceWeight
  simp only [orbitEdgeM_exponent, orbitEdgeM_target, orbitEdgeM_source]
  rw [pow_succ]
  ring

@[simp] theorem prefixMassM_zero (N : ℕ) (hN : Odd N) :
    prefixMassM N hN 0 = 1 / (N : ℝ) := by
  change geom2PNatListMass [] * ((3 : ℝ) ^ 0 / (N : ℝ)) = 1 / (N : ℝ)
  simp [geom2PNatListMass]

/-- **The replacement for `ndCommonZOrbitPrefixMass_antitone_step`.**  The prefix mass is not
antitone for `3x−1`; it is multiplied by exactly `1 + 1/(3s_k−1)` at step `k`. -/
theorem prefixMassM_succ_eq_mul (N : ℕ) (hN : Odd N) (k : ℕ) :
    prefixMassM N hN (k + 1) =
      prefixMassM N hN k * (1 + 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) := by
  rw [← orbit_transport_eq_nextMassM N hN k,
    (orbitEdgeM N hN k).transported_eq_source_mul k]
  unfold prefixMassM
  simp only [orbitEdgeM_source]
  ring

theorem prefixMassM_pos (N : ℕ) (hN : Odd N) (k : ℕ) : 0 < prefixMassM N hN k := by
  unfold prefixMassM EdgeM.sourceWeight
  have h1 := prefixGeomMassM_pos N hN k
  have h2 : (0 : ℝ) < ((orbitEdgeM N hN k).source : ℝ) := (orbitEdgeM N hN k).source_pos_real
  positivity

/-- **The replacement for `ndCommonZOrbitPrefixMass_le_zero`.**  If every source on the prefix of
length `k` is at least `R`, the mass at depth `k` exceeds its depth-zero value `1/N` by at most
the accumulated inflation `(1 + 1/(3R−1))^k`. -/
theorem prefixMassM_le_of_floor (N : ℕ) (hN : Odd N) {R : ℝ} (hR : 1 < R) (k : ℕ)
    (hfloor : ∀ j, j < k → R ≤ (((syrM^[j]) N : ℕ) : ℝ)) :
    prefixMassM N hN k ≤ prefixMassM N hN 0 * (1 + 1 / (3 * R - 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : ∀ j, j < k → R ≤ (((syrM^[j]) N : ℕ) : ℝ) := fun j hj =>
        hfloor j (by omega)
      have hstep := prefixMassM_succ_eq_mul N hN k
      have hs : R ≤ (((syrM^[k]) N : ℕ) : ℝ) := hfloor k (by omega)
      have hRpos : (0 : ℝ) < 3 * R - 1 := by linarith
      have hspos : (0 : ℝ) < 3 * (((syrM^[k]) N : ℕ) : ℝ) - 1 := by linarith
      have hratio : 1 + 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1) ≤ 1 + 1 / (3 * R - 1) := by
        have : 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1) ≤ 1 / (3 * R - 1) := by
          apply one_div_le_one_div_of_le hRpos; linarith
        linarith
      have hprev := ih hk
      have hpos := (prefixMassM_pos N hN k).le
      have hfac : (0 : ℝ) ≤ 1 + 1 / (3 * R - 1) := by positivity
      calc prefixMassM N hN (k + 1)
          = prefixMassM N hN k * (1 + 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) := hstep
        _ ≤ prefixMassM N hN k * (1 + 1 / (3 * R - 1)) := by
            exact mul_le_mul_of_nonneg_left hratio hpos
        _ ≤ (prefixMassM N hN 0 * (1 + 1 / (3 * R - 1)) ^ k) * (1 + 1 / (3 * R - 1)) := by
            exact mul_le_mul_of_nonneg_right hprev hfac
        _ = prefixMassM N hN 0 * (1 + 1 / (3 * R - 1)) ^ (k + 1) := by ring

/-- `(1 + x)^k ≤ exp (k·x)` for `0 ≤ x`. -/
theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (k * x) := by
  have hstep : (1 : ℝ) + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
      have hnn : (0 : ℝ) ≤ (1 + x) ^ k := by positivity
      calc (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := by ring
        _ ≤ Real.exp ((k : ℝ) * x) * Real.exp x :=
            mul_le_mul ih hstep (by linarith) (Real.exp_nonneg _)
        _ = Real.exp (((k : ℕ) + 1 : ℕ) * x) := by
            rw [← Real.exp_add]; push_cast; ring_nf

/-! ## The sharp accumulation: the path-harmonic sum

`prefixMassM_le_of_floor` bounds every step by the single worst source on the path, so its
exponent is `depth/(3R−1)` — linear in the depth.  That is fatal downstream: in M2's own
application `depth ≤ 250·(log source − log root)` grows like `log Y` while the seed root is a
constant fixed before `Y` is quantified, so no single `δ` works for all `Y` and the density
constant decays like `1/log Y`.

The true accumulated inflation is the *path-harmonic sum* `∑_{j<k} 1/(3·s_j − 1)`, which for an
orbit that descends geometrically is `O(1/min s_j)` and does **not** grow with the depth.  The
per-step law `prefixMassM_succ_eq_mul` is already sharp, so this is pure summation. -/

theorem prefixMassM_le_exp_pathSum (N : ℕ) (hN : Odd N) (k : ℕ) :
    prefixMassM N hN k ≤
      prefixMassM N hN 0 *
        Real.exp (∑ j ∈ Finset.range k, 1 / (3 * (((syrM^[j]) N : ℕ) : ℝ) - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs : (1 : ℝ) ≤ (((syrM^[k]) N : ℕ) : ℝ) := by
        exact_mod_cast (syrM_iterate_odd k N hN).pos
      have hspos : (0 : ℝ) < 3 * (((syrM^[k]) N : ℕ) : ℝ) - 1 := by linarith
      have hterm : (0 : ℝ) ≤ 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1) := by positivity
      have hstep : 1 + 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)
          ≤ Real.exp (1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) := by
        have := Real.add_one_le_exp (1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1))
        linarith
      have hpos := (prefixMassM_pos N hN k).le
      have hzero := (prefixMassM_pos N hN 0).le
      calc prefixMassM N hN (k + 1)
          = prefixMassM N hN k * (1 + 1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) :=
            prefixMassM_succ_eq_mul N hN k
        _ ≤ prefixMassM N hN k * Real.exp (1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left hstep hpos
        _ ≤ (prefixMassM N hN 0 *
              Real.exp (∑ j ∈ Finset.range k, 1 / (3 * (((syrM^[j]) N : ℕ) : ℝ) - 1))) *
              Real.exp (1 / (3 * (((syrM^[k]) N : ℕ) : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
        _ = prefixMassM N hN 0 *
              Real.exp (∑ j ∈ Finset.range (k + 1), 1 / (3 * (((syrM^[j]) N : ℕ) : ℝ) - 1)) := by
            rw [Finset.sum_range_succ, Real.exp_add]
            ring

/-- The bound in the form the downstream counting argument consumes:
`prefixMass k ≤ (1/N) · exp (k/(3R−1))`. -/
theorem prefixMassM_le_exp (N : ℕ) (hN : Odd N) {R : ℝ} (hR : 1 < R) (k : ℕ)
    (hfloor : ∀ j, j < k → R ≤ (((syrM^[j]) N : ℕ) : ℝ)) :
    prefixMassM N hN k ≤ (1 / (N : ℝ)) * Real.exp ((k : ℝ) * (1 / (3 * R - 1))) := by
  have h1 := prefixMassM_le_of_floor N hN hR k hfloor
  rw [prefixMassM_zero] at h1
  have hRpos : (0 : ℝ) < 3 * R - 1 := by linarith
  have h2 : (1 + 1 / (3 * R - 1)) ^ k ≤ Real.exp ((k : ℝ) * (1 / (3 * R - 1))) :=
    one_add_pow_le_exp (by positivity) k
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN.pos
  have hinv : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hinv)

end

end ThreeXMinusOne
