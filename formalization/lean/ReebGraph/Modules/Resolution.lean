import ReebGraph.Modules.Crossing

/-!
# Scalar-resolution estimates

Scalar-resolution estimates: how metric scale, filter error, and
quantization error bound the scalar band containing a crossing edge or a
support component.

These are the quantitative workhorses reused throughout the approximation
argument.  They are supporting lemmas rather than headline results, but
they are generic enough that several of them (`estimated_`,
`quantized_`, `sampled_edge_oscillation_bound`) depend on nothing but
Mathlib and a Lipschitz hypothesis.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ## Scalar-resolution lemmas -/

section Resolution

variable {V : Type*}

/-- If every graph edge changes the filter by at most `ε`, then both endpoints
of an edge crossing `t` lie in the `ε`-thickened level band. -/
theorem crossing_edge_endpoints_mem_band
    (G : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hε : ∀ ⦃u v⦄, G.Adj u v → |f u - f v| ≤ ε)
    {u v : V} (huv : G.Adj u v) (hcross : Crosses f t u v) :
    |f u - t| ≤ ε ∧ |f v - t| ≤ ε := by
  have huvε := hε huv
  have huv_bound : f u - f v ≤ ε :=
    (le_abs_self (f u - f v)).trans huvε
  have hvu_bound : f v - f u ≤ ε := by
    rw [← neg_sub (f u) (f v)]
    exact (neg_le_abs (f u - f v)).trans huvε
  rcases hcross with ⟨hmin, hmax⟩
  rcases le_total (f u) (f v) with huv_order | hvu_order
  · rw [min_eq_left huv_order] at hmin
    rw [max_eq_right huv_order] at hmax
    constructor <;> rw [abs_sub_le_iff] <;> constructor <;> linarith
  · rw [min_eq_right hvu_order] at hmin
    rw [max_eq_left hvu_order] at hmax
    constructor <;> rw [abs_sub_le_iff] <;> constructor <;> linarith

/-- A path in one support component stays within the thickened level band. -/
theorem support_component_mem_band
    (G : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hε : ∀ ⦃u v⦄, G.Adj u v → |f u - f v| ≤ ε)
    (c : CrossingComponent G f t) :
    componentSupport G f t c ⊆ {v | |f v - t| ≤ ε} := by
  intro v hv
  rcases componentSupport_isActive G f t c hv with ⟨w, hvw⟩
  exact (crossing_edge_endpoints_mem_band G f hε hvw.1 hvw.2).1

variable [PseudoMetricSpace V]

/-- Edgewise filter oscillation is controlled by geometric edge length and
uniform filter-estimation error. -/
theorem estimated_edge_oscillation_bound
    (G : SimpleGraph V) (f fhat : V → ℝ)
    {L r η : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist u v ≤ r)
    (hη : ∀ x, |fhat x - f x| ≤ η)
    {u v : V} (huv : G.Adj u v) :
    |fhat u - fhat v| ≤ L * r + 2 * η := by
  calc
    |fhat u - fhat v| =
        |(fhat u - f u) + (f u - f v) + (f v - fhat v)| := by ring_nf
    _ ≤ |fhat u - f u| + |f u - f v| + |f v - fhat v| :=
      abs_add_three _ _ _
    _ ≤ η + (L * dist u v) + η := by
      exact add_le_add
        (add_le_add (hη u) (hL u v))
        (by simpa only [abs_sub_comm] using hη v)
    _ ≤ η + (L * r) + η := by
      gcongr
      exact hedge huv
    _ = L * r + 2 * η := by ring

/-- Quantization adds at most twice its uniform pointwise error to the edgewise
oscillation bound. -/
theorem quantized_edge_oscillation_bound
    (G : SimpleGraph V) (f fhat fquant : V → ℝ)
    {L r η q : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist u v ≤ r)
    (hη : ∀ x, |fhat x - f x| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    {u v : V} (huv : G.Adj u v) :
    |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
  have hbase : |fhat u - fhat v| ≤ L * r + 2 * η :=
    estimated_edge_oscillation_bound G f fhat hL_nonneg hL hedge hη huv
  calc
    |fquant u - fquant v| =
        |(fquant u - fhat u) + (fhat u - fhat v) + (fhat v - fquant v)| := by
          ring_nf
    _ ≤ |fquant u - fhat u| + |fhat u - fhat v| + |fhat v - fquant v| :=
      abs_add_three _ _ _
    _ ≤ q + (L * r + 2 * η) + q := by
      exact add_le_add
        (add_le_add (hq u) hbase)
        (by simpa only [abs_sub_comm] using hq v)
    _ = L * r + 2 * η + 2 * q := by ring

omit [PseudoMetricSpace V] in
/-- The edgewise oscillation estimate when graph vertices are sample indices
rather than points of the ambient metric space. -/
theorem sampled_edge_oscillation_bound
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    {L r η : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    {u v : V} (huv : G.Adj u v) :
    |fhat u - fhat v| ≤ L * r + 2 * η := by
  calc
    |fhat u - fhat v| =
        |(fhat u - f (sample u)) +
          (f (sample u) - f (sample v)) +
          (f (sample v) - fhat v)| := by ring_nf
    _ ≤ |fhat u - f (sample u)| +
          |f (sample u) - f (sample v)| +
          |f (sample v) - fhat v| := abs_add_three _ _ _
    _ ≤ η + L * dist (sample u) (sample v) + η := by
      exact add_le_add
        (add_le_add (hη u) (hL (sample u) (sample v)))
        (by simpa only [abs_sub_comm] using hη v)
    _ ≤ η + L * r + η := by
      gcongr
      exact hedge huv
    _ = L * r + 2 * η := by ring

omit [PseudoMetricSpace V] in
/-- Soundness at sampled vertices: the support of a discrete support
component maps into a controlled level band of the continuum filter. -/
theorem sampled_support_component_mem_continuum_band
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    {L r η t : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (c : SupportComponent G fhat t) :
    componentSupport G fhat t c ⊆
      {v | |f (sample v) - t| ≤ L * r + 3 * η} := by
  have hedgeOsc : ∀ ⦃u v⦄, G.Adj u v →
      |fhat u - fhat v| ≤ L * r + 2 * η := by
    intro u v huv
    exact sampled_edge_oscillation_bound G sample f fhat
      hL_nonneg hL hedge hη huv
  intro v hv
  have hvBand : |fhat v - t| ≤ L * r + 2 * η :=
    support_component_mem_band G fhat hedgeOsc c hv
  calc
    |f (sample v) - t| =
        |(f (sample v) - fhat v) + (fhat v - t)| := by ring_nf
    _ ≤ |f (sample v) - fhat v| + |fhat v - t| := abs_add _ _
    _ ≤ η + (L * r + 2 * η) := by
      exact add_le_add (by simpa only [abs_sub_comm] using hη v) hvBand
    _ = L * r + 3 * η := by ring

omit [PseudoMetricSpace V] in
/-- Quantized sampled filters have the expected additional `2*q` edgewise
oscillation. -/
theorem sampled_quantized_edge_oscillation_bound
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ)
    (fhat fquant : V → ℝ) {L r η q : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    {u v : V} (huv : G.Adj u v) :
    |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
  have hbase : |fhat u - fhat v| ≤ L * r + 2 * η :=
    sampled_edge_oscillation_bound G sample f fhat
      hL_nonneg hL hedge hη huv
  calc
    |fquant u - fquant v| =
        |(fquant u - fhat u) + (fhat u - fhat v) +
          (fhat v - fquant v)| := by ring_nf
    _ ≤ |fquant u - fhat u| + |fhat u - fhat v| +
          |fhat v - fquant v| := abs_add_three _ _ _
    _ ≤ q + (L * r + 2 * η) + q := by
      exact add_le_add
        (add_le_add (hq u) hbase)
        (by simpa only [abs_sub_comm] using hq v)
    _ = L * r + 2 * η + 2 * q := by ring

omit [PseudoMetricSpace V] in
/-- Quantized version of sampled crossing-component soundness. -/
theorem sampled_quantized_component_mem_continuum_band
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ)
    (fhat fquant : V → ℝ) {L r η q t : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    (c : CrossingComponent G fquant t) :
    componentSupport G fquant t c ⊆
      {v | |f (sample v) - t| ≤ L * r + 3 * η + 3 * q} := by
  have hedgeOsc : ∀ ⦃u v⦄, G.Adj u v →
      |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
    intro u v huv
    exact sampled_quantized_edge_oscillation_bound G sample f fhat fquant
      hL_nonneg hL hedge hη hq huv
  intro v hv
  have hvBand : |fquant v - t| ≤ L * r + 2 * η + 2 * q :=
    support_component_mem_band G fquant hedgeOsc c hv
  have htrueQuant : |f (sample v) - fquant v| ≤ η + q := by
    calc
      |f (sample v) - fquant v| =
          |(f (sample v) - fhat v) + (fhat v - fquant v)| := by ring_nf
      _ ≤ |f (sample v) - fhat v| + |fhat v - fquant v| := abs_add _ _
      _ ≤ η + q := add_le_add
        (by simpa only [abs_sub_comm] using hη v)
        (by simpa only [abs_sub_comm] using hq v)
  calc
    |f (sample v) - t| =
        |(f (sample v) - fquant v) + (fquant v - t)| := by ring_nf
    _ ≤ |f (sample v) - fquant v| + |fquant v - t| := abs_add _ _
    _ ≤ (η + q) + (L * r + 2 * η + 2 * q) :=
      add_le_add htrueQuant hvBand
    _ = L * r + 3 * η + 3 * q := by ring

end Resolution

end ReebGraph
