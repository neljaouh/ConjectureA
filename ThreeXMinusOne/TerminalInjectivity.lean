import ThreeXMinusOne.ForwardCoreMass
import ThreeXMinusOne.IncidenceExt

/-!
# Terminal incidences are determined by their ancestor and their word

The injectivity half of `Geom2ShiftedWideSymmetricRootSideGeometricFullTerminalCount`.

This is what makes the census a *census*: the terminal mass is a sum over incidences, but the
predecessor count is a sum over distinct naturals, and the two agree only if distinct incidences
carry distinct data.  The bridge is that a terminal incidence is pinned down by two things — the
generation-zero label it descends from, and the concatenated word of the whole descent.

The proof peels the descent from the front, one generation at a time, and at each step uses that
two unit-child incidences with the same label whose words are prefixes of a common list must be
equal.  That is Layer 21's `unitChildM_eq_of_label_eq_of_commonPrefix`; the terminal step is
Layer 18's `incidenceM_eq_of_label_eq_of_commonPrefix`.  Both were built for the minus finsets
at the negated residue, so nothing here re-treads the residue flip.
-/

namespace ThreeXMinusOne

open Erdos1135 Erdos1135.ND.PositiveDensity

noncomputable section

variable {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}

/-- The concatenated word of an `n`-generation descent, peeled from the front. -/
def forwardWordM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) :
    (n : ℕ) → (forwardIterateM U cap n).state.Label → List ℕ+
  | 0, _ => []
  | n + 1, z =>
      ucWordM (forwardFirstIncidenceM U cap n z) ++
        forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z

/-- **The descent is determined by its ancestor and its word**, even with an unknown tail
appended: the tail is determined too. -/
theorem forwardLabelM_tail_eq_of_append
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ)
    (z w : (forwardIterateM U cap n).state.Label) (tailZ tailW : List ℕ+)
    (ha : forwardAncestorM U cap n z = forwardAncestorM U cap n w)
    (hw : forwardWordM U cap n z ++ tailZ = forwardWordM U cap n w ++ tailW) :
    z = w ∧ tailZ = tailW := by
  induction n generalizing U cap with
  | zero => exact ⟨ha, by simpa [forwardWordM] using hw⟩
  | succ n ih =>
      set iz := forwardFirstIncidenceM U cap n z with hiz
      set iw := forwardFirstIncidenceM U cap n w with hiw
      have hpz : ucWordM iz = (forwardWordM U cap (n + 1) z ++ tailZ).take (ucDepthM iz) := by
        rw [← ucWordM_length iz]
        simp only [forwardWordM, List.append_assoc, iz, List.take_left]
      have hpw : ucWordM iw = (forwardWordM U cap (n + 1) z ++ tailZ).take (ucDepthM iw) := by
        rw [hw, ← ucWordM_length iw]
        simp only [forwardWordM, List.append_assoc, iw, List.take_left]
      have hf : iz = iw :=
        unitChildM_eq_of_label_eq_of_commonPrefix U.state.root_odd
          (by have h := U.floor_twoHundred; omega)
          (fun i => (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans
            (U.state.rootLower i))
          ha hpz hpw
      have ht : forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n z ++ tailZ =
          forwardWordM (nextFloorM U (cap 0)) (ndGeom2RootSideCapTail cap) n w ++ tailW := by
        change (ucWordM iz ++ _) ++ tailZ = (ucWordM iw ++ _) ++ tailW at hw
        rw [hf] at hw
        exact List.append_cancel_left (by simpa only [List.append_assoc] using hw)
      exact ih (U := nextFloorM U (cap 0)) (cap := ndGeom2RootSideCapTail cap) z w hf ht

/-- A terminal `3x−1` incidence at generation `n`. -/
abbrev FullTerminalAtM (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (shift : (forwardIterateM U cap n).state.Label → ℕ) (K : ℕ) :=
  IncidenceM (forwardIterateM U cap n).state.Label (forwardIterateM U cap n).state.root
    (fun _ => (forwardIterateM U cap n).floor) shift K

def fullTerminalAncestorM {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (forwardIterateM U cap n).state.Label → ℕ} {K : ℕ}
    (z : FullTerminalAtM U cap n shift K) : U.state.Label :=
  forwardAncestorM U cap n (labelM z)

def fullTerminalWordM {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (forwardIterateM U cap n).state.Label → ℕ} {K : ℕ}
    (z : FullTerminalAtM U cap n shift K) : List ℕ+ :=
  forwardWordM U cap n (labelM z) ++ rootSideWordM z

/-- **The census bridge.**  Ancestor and word determine a terminal incidence. -/
theorem fullTerminalM_eq_of_ancestor_word_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (forwardIterateM U cap n).state.Label → ℕ} {K : ℕ}
    {z w : FullTerminalAtM U cap n shift K}
    (ha : fullTerminalAncestorM z = fullTerminalAncestorM w)
    (hw : fullTerminalWordM z = fullTerminalWordM w) : z = w := by
  have h := forwardLabelM_tail_eq_of_append U cap n (labelM z) (labelM w)
    (rootSideWordM z) (rootSideWordM w) ha hw
  refine incidenceM_eq_of_label_eq_of_commonPrefix h.1
    (fullRootSide := rootSideWordM z) ?_ ?_
  · rw [← wordM_length z, List.take_length]
  · rw [h.2, ← wordM_length w, List.take_length]

end

end ThreeXMinusOne
