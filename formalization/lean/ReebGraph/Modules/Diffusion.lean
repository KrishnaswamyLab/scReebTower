import Mathlib

/-!
# Diffusion-filter specialization

Optional diffusion-filter specialization, treated as preprocessing.

`diffusion_filter_uniform_convergence` records that a uniformly
convergent diffusion filter meets the filter-error hypothesis used by the
main theorems.  Nothing in `Main` depends on this file.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ## Diffusion-filter specialization -/

/-- Placeholder type for the discrete diffusion operator. -/
opaque DiffusionOperator (V : Type*) [Fintype V] : Type

/-- Placeholder for the selected nontrivial discrete diffusion eigenfunction. -/
opaque diffusionEigenfunction
    (V : Type*) [Fintype V] (P : DiffusionOperator V) : V → ℝ

/-- Uniform convergence on the sampled points, allowing the sign ambiguity of
an eigenfunction.  The core Reeb theorem assumes this property; a future
spectral theorem may establish it for a particular diffusion operator. -/
def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1

def UniformFilterConvergenceOnSamples
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (fhat : ∀ n, V n → ℝ) (f : M → ℝ) : Prop :=
    ∃ sign : ℕ → ℝ,
      (∀ n, IsSign (sign n)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop,
          ∀ v : V n,
            |sign n * fhat n v - f (sample n v)| < ε

/-- A vanishing explicit sup-norm error bound implies uniform convergence on
the sampled points. -/
theorem uniformFilterConvergenceOnSamples_of_error_bound
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (fhat : ∀ n, V n → ℝ) (f : M → ℝ)
    (η : ℕ → ℝ)
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hbound : ∀ n v, |fhat n v - f (sample n v)| ≤ η n) :
    UniformFilterConvergenceOnSamples M V sample fhat f := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro ε hε
  have hevent : ∀ᶠ n in Filter.atTop, η n < ε :=
    (tendsto_order.1 hη).2 ε hε
  filter_upwards [hevent] with n hn
  intro v
  simpa using (hbound n v).trans_lt hn

/-- The diffusion specialization is deliberately conditional: spectral
convergence is not needed by the core Reeb argument. -/
theorem diffusion_filter_uniform_convergence
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (P : ∀ n, DiffusionOperator (V n))
    (f : M → ℝ)
    (hconv : UniformFilterConvergenceOnSamples M V sample
      (fun n => diffusionEigenfunction (V n) (P n)) f) :
    UniformFilterConvergenceOnSamples M V sample
      (fun n => diffusionEigenfunction (V n) (P n)) f :=
  hconv

end ReebGraph
