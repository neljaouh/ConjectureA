import ThreeXMinusOne.TerminalInjectivity

/-!
# `3x−1` orbit paths, and the source-side census bridge

`Geom2ShiftedWideSymmetricRootSideHistoryPhysicalCollision` plus the seed-uniqueness block of
`…GeometricFullTerminalCount`, mirrored.

Layer 33 showed a terminal incidence is determined by its *ancestor and word*.  The census needs
it determined by its *ancestor and source* — a source is a natural number, which is what the
predecessor count counts.  The bridge is the orbit itself: a path from the source up to the
ancestor's root records both the depth and the valuation word, so equal sources at equal depths
force equal words, and Layer 33 finishes.

Everything the path needs was built at Layers 0, 2 and 7: `syrMValuationPNatList` and its
append law, `syrM_iterate_odd`, and the source trio `sourceM_odd` / `sourceM_valuation` /
`sourceM_iterate`.

**Where `3x−1` is easier.**  The `+1` argument has to rule out two different hit times `d < e`
for the same target.  It gets `syracuse^[e-d] target = target` and needs a contradiction; since
`3x+1` genuinely has the fixed point `1`, it cannot argue from the map alone, and must assume the
seed reaches `1` and is not `1`, then push the return around the cycle to contradict.  For
`3x−1` the non-returning hypothesis contradicts `syrM^[k] target = target` immediately.  So
`hseedHitsOne` disappears entirely, and `Residue.exists_large_nonreturning_predecessorM_in_residue`
already supplies what is left.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

/-- A `3x−1` orbit segment from `source` to `terminal`, carrying its valuation word. -/
structure SyrMPath (source terminal : ℕ) where
  sourceOdd : Odd source
  depth : ℕ
  word : List ℕ+
  word_length : word.length = depth
  valuation_eq : syrMValuationPNatList depth source sourceOdd = word
  terminal_eq : (syrM^[depth]) source = terminal

def SyrMPath.nil (N : ℕ) (hN : Odd N) : SyrMPath N N where
  sourceOdd := hN
  depth := 0
  word := []
  word_length := rfl
  valuation_eq := rfl
  terminal_eq := by simp

private theorem syrMValuationPNatList_congr_source {n M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMN : M = N) : syrMValuationPNatList n M hM = syrMValuationPNatList n N hN := by
  subst N; rfl

variable {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}

/-- Extend a path across one `3x−1` incidence. -/
noncomputable def SyrMPath.appendIncidenceM {source : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (z : IncidenceM Label root base shift K)
    (p : SyrMPath source (sourceM z)) : SyrMPath source (root (labelM z)) where
  sourceOdd := p.sourceOdd
  depth := p.depth + depthM z
  word := p.word ++ chronologicalWordM z
  word_length := by
    rw [List.length_append, p.word_length, chronologicalWordM_length]
  valuation_eq := by
    have htail :
        syrMValuationPNatList (depthM z) ((syrM^[p.depth]) source)
            (syrM_iterate_odd p.depth source p.sourceOdd) = chronologicalWordM z :=
      (syrMValuationPNatList_congr_source
        (syrM_iterate_odd p.depth source p.sourceOdd) (sourceM_odd hrootOdd z)
        p.terminal_eq).trans (sourceM_valuation hrootOdd z)
    rw [syrMValuationPNatList_add, p.valuation_eq, htail]
  terminal_eq := by
    rw [Nat.add_comm, Function.iterate_add_apply, p.terminal_eq, sourceM_iterate hrootOdd z]

@[simp] theorem SyrMPath.appendIncidenceM_depth {source : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (z : IncidenceM Label root base shift K)
    (p : SyrMPath source (sourceM z)) :
    (p.appendIncidenceM hrootOdd z).depth = p.depth + depthM z := rfl

theorem SyrMPath.word_eq_of_source_depth_eq {s₁ s₂ t₁ t₂ : ℕ}
    (p : SyrMPath s₁ t₁) (q : SyrMPath s₂ t₂) (hsource : s₁ = s₂) (hdepth : p.depth = q.depth) :
    p.word = q.word := by
  have hp := p.valuation_eq
  have hq := q.valuation_eq
  subst s₂
  rw [hdepth] at hp
  exact hp.symm.trans hq

/-- **Hit times are unique for a non-returning target.**  No `hseedHitsOne`: the `3x−1` map has
no fixed point to push a return around. -/
theorem nonreturning_hit_time_unique {source target : ℕ} {d e : ℕ}
    (ht : ∀ k, 0 < k → (syrM^[k]) target ≠ target)
    (hd : (syrM^[d]) source = target) (he : (syrM^[e]) source = target) : d = e := by
  suffices h : ∀ d e : ℕ, (syrM^[d]) source = target → (syrM^[e]) source = target →
      d < e → False by
    exact le_antisymm (le_of_not_gt (h e d he hd)) (le_of_not_gt (h d e hd he))
  intro d e hd he hde
  refine ht (e - d) (by omega) ?_
  have heq : e = (e - d) + d := by omega
  rw [heq, Function.iterate_add_apply, hd] at he
  exact he

/-- The orbit path realised by a terminal incidence, from its source up to the ancestor root. -/
noncomputable def fullTerminalPathM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) → (shift : (forwardIterateM U cap n).state.Label → ℕ) → (K : ℕ) →
    (z : FullTerminalAtM U cap n shift K) →
    SyrMPath (sourceM z) (U.state.root (fullTerminalAncestorM z))
  | 0, _, _, z =>
      (SyrMPath.nil (sourceM z) (sourceM_odd U.state.root_odd z)).appendIncidenceM
        U.state.root_odd z
  | n + 1, shift, K, z =>
      ((fullTerminalPathM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n shift K
        z).appendIncidenceM U.state.root_odd
          (toPhysicalM (forwardFirstIncidenceM U cap n (labelM z))))

theorem fullTerminalPathM_word_eq_reverse
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ)
    (z : FullTerminalAtM U cap n shift K) :
    (fullTerminalPathM U cap n shift K z).word = (fullTerminalWordM z).reverse := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change (fullTerminalPathM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n shift K
          z).word ++ chronologicalWordM (toPhysicalM
            (forwardFirstIncidenceM U cap n (labelM z))) = _
      rw [ih]
      simp only [fullTerminalWordM, forwardWordM, chronologicalWordM, toPhysicalM_word,
        List.reverse_append, List.append_assoc]
      rfl

/-- **The census bridge, source form.**  Ancestor and source determine a terminal incidence. -/
theorem fullTerminalM_eq_of_nonreturningSeed_ancestor_source_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (forwardIterateM U cap n).state.Label → ℕ} {K : ℕ}
    (hseed : ∀ i k, 0 < k → (syrM^[k]) (U.state.root i) ≠ U.state.root i)
    {z w : FullTerminalAtM U cap n shift K}
    (ha : fullTerminalAncestorM z = fullTerminalAncestorM w)
    (hs : sourceM z = sourceM w) : z = w := by
  set p := fullTerminalPathM U cap n shift K z with hpdef
  set q := fullTerminalPathM U cap n shift K w with hqdef
  have hq : (syrM^[q.depth]) (sourceM z) = U.state.root (fullTerminalAncestorM z) := by
    rw [hs, ha]; exact q.terminal_eq
  have hd := nonreturning_hit_time_unique (hseed (fullTerminalAncestorM z)) p.terminal_eq hq
  have hword := SyrMPath.word_eq_of_source_depth_eq p q hs hd
  have hpw := fullTerminalPathM_word_eq_reverse U cap n shift K z
  have hqw := fullTerminalPathM_word_eq_reverse U cap n shift K w
  refine fullTerminalM_eq_of_ancestor_word_eq ha (List.reverse_injective ?_)
  exact hpw.symm.trans (hword.trans hqw)

end

end ThreeXMinusOne
