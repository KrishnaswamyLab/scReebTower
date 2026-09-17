import ReebGraph.Modules.ContinuumReeb

/-!
# Tame level-set functions

Tame level-set functions: finitely many components per level, locally
path-connected fibers, and finitely many critical values.

Main results: `TameLevelSetFunction.sameLevelComponent_iff_joinedIn` and
`.quotientMap_eq_iff_joinedIn` -- under tameness the Reeb relation is
exactly path-connectedness inside a level, which is what makes band
lifting possible in `Approximation.BandLift`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Connected components of one exact scalar level set. -/
def LevelConnectedComponent
    (M : Type*) [TopologicalSpace M] (f : M → ℝ) (t : ℝ) :=
  ConnectedComponents {x : M // f x = t}

/-- A concrete finite-critical-value tameness condition.  Away from a finite
set of scalar values, the type of connected level-set components is locally
constant up to equivalence. -/
def TameLevelSetFunction
    (M : Type*) [TopologicalSpace M] (f : M → ℝ) : Prop :=
  Continuous f ∧
    (∀ t, LocPathConnectedSpace {x : M // f x = t}) ∧
    (∀ t, Finite (LevelConnectedComponent M f t)) ∧
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        Nonempty (LevelConnectedComponent M f a ≃ LevelConnectedComponent M f b)

theorem TameLevelSetFunction.continuous
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) : Continuous f :=
  h.1

theorem TameLevelSetFunction.finite_level_components
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) :
    Finite (LevelConnectedComponent M f t) :=
  h.2.2.1 t

theorem TameLevelSetFunction.locPathConnected_level
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) :
    LocPathConnectedSpace {x : M // f x = t} :=
  h.2.1 t

theorem TameLevelSetFunction.exists_finite_criticalValues
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) :
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        Nonempty (LevelConnectedComponent M f a ≃ LevelConnectedComponent M f b) :=
  h.2.2.2

/-- Numerical form of tameness: the number of connected level components is
constant across intervals containing no critical value. -/
noncomputable def TameLevelSetFunction.levelComponentCount
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) : ℕ := by
  letI : Finite (LevelConnectedComponent M f t) :=
    h.finite_level_components t
  letI : Fintype (LevelConnectedComponent M f t) := Fintype.ofFinite _
  exact Fintype.card (LevelConnectedComponent M f t)

theorem TameLevelSetFunction.exists_criticalValues_card_eq
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) :
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        h.levelComponentCount a = h.levelComponentCount b := by
  rcases h.exists_finite_criticalValues with ⟨C, hCfinite, hregular⟩
  refine ⟨C, hCfinite, ?_⟩
  intro a b hab hC
  letI : Finite (LevelConnectedComponent M f a) :=
    h.finite_level_components a
  letI : Finite (LevelConnectedComponent M f b) :=
    h.finite_level_components b
  letI : Fintype (LevelConnectedComponent M f a) := Fintype.ofFinite _
  letI : Fintype (LevelConnectedComponent M f b) := Fintype.ofFinite _
  simpa only [levelComponentCount] using
    Fintype.card_congr (Classical.choice (hregular hab hC))

/-- Under the local path-connectedness part of tameness, classical connected
level components are also path components. -/
theorem TameLevelSetFunction.joinedIn_of_sameLevelComponent
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) {x y : M}
    (hxy : SameLevelComponent f x y) :
    JoinedIn {z | f z = f x} x y := by
  rcases hxy with ⟨hfxy, hyComponent⟩
  have hxLevel : x ∈ {z | f z = f x} := rfl
  have hyLevel : y ∈ {z | f z = f x} :=
    connectedComponentIn_subset _ _ hyComponent
  let X := {z : M // f z = f x}
  let xs : X := ⟨x, hxLevel⟩
  let ys : X := ⟨y, hyLevel⟩
  have hyImage : y ∈ ((↑) : X → M) '' connectedComponent xs := by
    simpa only [connectedComponentIn_eq_image hxLevel] using hyComponent
  rcases hyImage with ⟨z, hzComponent, hzy⟩
  have hzys : z = ys := Subtype.ext hzy
  subst z
  letI : LocPathConnectedSpace X := htame.locPathConnected_level (f x)
  have hyPath : ys ∈ pathComponent xs := by
    rw [pathComponent_eq_connectedComponent]
    exact hzComponent
  apply (joinedIn_iff_joined hxLevel hyLevel).mpr
  exact mem_pathComponent_iff.mp hyPath

theorem TameLevelSetFunction.sameLevelComponent_iff_joinedIn
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) (x y : M) :
    SameLevelComponent f x y ↔ JoinedIn {z | f z = f x} x y :=
  ⟨htame.joinedIn_of_sameLevelComponent,
    sameLevelComponent_of_joinedIn f⟩

theorem TameLevelSetFunction.quotientMap_eq_iff_joinedIn
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) (x y : M) :
    continuumReebQuotientMap f x = continuumReebQuotientMap f y ↔
      JoinedIn {z | f z = f x} x y := by
  rw [continuumReebQuotientMap_eq_iff]
  exact htame.sameLevelComponent_iff_joinedIn x y

end ReebGraph
