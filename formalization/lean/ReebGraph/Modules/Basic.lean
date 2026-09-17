import Mathlib

/-!
# Generic support lemmas

Generic, reusable support lemmas with no Reeb-graph content.

Everything here is stated purely in terms of Mathlib notions -- real
arithmetic, `ℝ≥0∞`, connectedness, and filter limits -- and is used from
several different groups downstream.  Nothing in this file mentions
crossings, slices, realizations, or Reeb quotients.

Contents:
* `abs_affine_sub_le` -- convex interpolation keeps a common error bound.
* `ennrealOrderDist` and its `comm` / `self` / `triangle` lemmas -- the
  symmetric order distance used to define `reebDist`.
* `isConnected_preimage_subtypeVal` -- connectedness transported into a
  larger subtype.
* The four `Tendsto` lemmas driving every asymptotic statement.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- A convex interpolation stays within a common absolute-error bound. -/
theorem abs_affine_sub_le
    {a b c E s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a - c| ≤ E) (hb : |b - c| ≤ E) :
    |(1 - s) * a + s * b - c| ≤ E := by
  have hE : 0 ≤ E := (abs_nonneg (a - c)).trans ha
  calc
    |(1 - s) * a + s * b - c| =
        |(1 - s) * (a - c) + s * (b - c)| := by ring_nf
    _ ≤ |(1 - s) * (a - c)| + |s * (b - c)| := abs_add _ _
    _ = (1 - s) * |a - c| + s * |b - c| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_nonneg hs0]
    _ ≤ (1 - s) * E + s * E := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hs1))
        (mul_le_mul_of_nonneg_left hb hs0)
    _ = E := by ring


/-- Symmetric order distance on extended nonnegative reals.  Unlike coercion
through `toReal`, this retains infinite intrinsic distances. -/
noncomputable def ennrealOrderDist (a b : ℝ≥0∞) : ℝ≥0∞ :=
  (a - b) ⊔ (b - a)

theorem ennrealOrderDist_comm (a b : ℝ≥0∞) :
    ennrealOrderDist a b = ennrealOrderDist b a := by
  simp only [ennrealOrderDist, sup_comm]

theorem ennrealOrderDist_self (a : ℝ≥0∞) : ennrealOrderDist a a = 0 := by
  simp [ennrealOrderDist]

theorem ennrealOrderDist_triangle (a b c : ℝ≥0∞) :
    ennrealOrderDist a c ≤ ennrealOrderDist a b + ennrealOrderDist b c := by
  apply sup_le
  · exact (tsub_le_tsub_add_tsub.trans
      (add_le_add le_sup_left le_sup_left))
  · calc
      c - a ≤ c - b + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ennrealOrderDist b c + ennrealOrderDist a b :=
        add_le_add le_sup_right le_sup_right
      _ = ennrealOrderDist a b + ennrealOrderDist b c := add_comm _ _


/-- Connectedness is preserved when a connected set is viewed inside a
larger subtype containing it. -/
theorem isConnected_preimage_subtypeVal
    {X : Type} [TopologicalSpace X] {U W : Set X}
    (hW : IsConnected W) (hWU : W ⊆ U) :
    IsConnected (((↑) : U → X) ⁻¹' W) := by
  constructor
  · rcases hW.nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hWU hx⟩, hx⟩
  · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hWU]
    exact hW.isPreconnected


/-- The deterministic error scale vanishes when all of its constituent scales
vanish. -/
theorem approximation_error_tendsto_zero
    (L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => L * r n + δ n + η n + q n)
      Filter.atTop (nhds 0) := by
  simpa using (((hr.const_mul L).add hδ).add hη).add hq

theorem crossing_slack_tendsto_zero
    (L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => L * (r n + δ n) + η n + q n)
      Filter.atTop (nhds 0) := by
  simpa using (((hr.add hδ).const_mul L).add hη).add hq

/-- Approximate slice heights converge to the continuum height when their
scalar slack vanishes. -/
theorem threshold_tendsto_of_abs_sub_le
    (threshold slack : ℕ → ℝ) (t : ℝ)
    (hslack : Filter.Tendsto slack Filter.atTop (nhds 0))
    (hbound : ∀ n, |threshold n - t| ≤ slack n) :
    Filter.Tendsto threshold Filter.atTop (nhds t) := by
  apply tendsto_iff_dist_tendsto_zero.2
  have habs : Filter.Tendsto (fun n => |threshold n - t|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg (threshold n - t)) hbound hslack
  simpa only [Real.dist_eq] using habs

/-- Multiplication by the fixed comparison constant preserves the vanishing
error scale. -/
theorem scaled_approximation_error_tendsto_zero
    (C L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => C * (L * r n + δ n + η n + q n))
      Filter.atTop (nhds 0) := by
  simpa using
    (approximation_error_tendsto_zero L r δ η q hr hδ hη hq).const_mul C

end ReebGraph
