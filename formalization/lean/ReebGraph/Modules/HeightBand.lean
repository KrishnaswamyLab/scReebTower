import ReebGraph.Modules.ContinuumReeb

/-!
# Height bands and filtered equivalences

Height-band connectivity, height-controlled homotopies, and filtered
equivalences of filtered Reeb graphs.

Main results: `HeightBandJoined.map_of_continuous_height_close` -- a band
connection survives any height-close continuous map -- and the
`FilteredReebGraphEquiv` transfer lemmas (`heightBandJoined_iff`,
`heightRangeDist_eq`).  Supporting lemmas are the monotonicity of
`HeightBandJoined` and the groupoid structure on equivalences.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Points joined inside one closed scalar band. -/
def HeightBandJoined (X : FilteredReebGraph) (a b : ℝ)
    (x y : X.Carrier) : Prop :=
  JoinedIn {z | a ≤ X.height z ∧ X.height z ≤ b} x y

theorem HeightBandJoined.mono
    {X : FilteredReebGraph} {a b a' b' : ℝ} {x y : X.Carrier}
    (h : HeightBandJoined X a b x y) (ha : a' ≤ a) (hb : b ≤ b') :
    HeightBandJoined X a' b' x y := by
  apply JoinedIn.mono h
  intro z hz
  exact ⟨ha.trans hz.1, hz.2.trans hb⟩

/-- A height-bounded active-incidence walk projects all the way to a path in
the filtered CW realization of the canonical component graph. -/
theorem heightBandJoined_of_canonicalActiveIncidence_walk
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ)
    {a b : ℝ} {x y : CanonicalActiveState G f}
    (p : (canonicalActiveIncidenceGraph G f).Walk x y)
    (hp : ∀ z, z ∈ p.support →
      a ≤ canonicalThreshold f z.1 ∧ canonicalThreshold f z.1 ≤ b) :
    HeightBandJoined (discreteReebRealization V G f) a b
      (graphRealizationVertex (canonicalDiscreteReebGraph G f)
        (canonicalActiveStateNode G f x))
      (graphRealizationVertex (canonicalDiscreteReebGraph G f)
        (canonicalActiveStateNode G f y)) := by
  induction p with
  | @nil x =>
      exact JoinedIn.refl (by
        change a ≤ canonicalThreshold f x.1 ∧
          canonicalThreshold f x.1 ≤ b
        simpa using hp x (by simp))
  | @cons u v w huv p ih =>
      have hu : a ≤ canonicalThreshold f u.1 ∧
          canonicalThreshold f u.1 ≤ b := hp u (by simp)
      have hv : a ≤ canonicalThreshold f v.1 ∧
          canonicalThreshold f v.1 ≤ b :=
        hp v (by simp [p.start_mem_support])
      have hstep : HeightBandJoined (discreteReebRealization V G f) a b
          (graphRealizationVertex (canonicalDiscreteReebGraph G f)
            (canonicalActiveStateNode G f u))
          (graphRealizationVertex (canonicalDiscreteReebGraph G f)
            (canonicalActiveStateNode G f v)) := by
        rcases canonicalActiveIncidence_adj_projects G f huv with heq | hadj
        · rw [heq]
          exact JoinedIn.refl (by
            change a ≤ canonicalThreshold f v.1 ∧
              canonicalThreshold f v.1 ≤ b
            exact hv)
        · let q : (canonicalDiscreteReebGraph G f).Walk
              (canonicalActiveStateNode G f u)
              (canonicalActiveStateNode G f v) := .cons hadj .nil
          apply joinedIn_graphRealization_of_walk
            (fun z : SliceNode G f (canonicalThreshold f) ↦
              canonicalThreshold f z.1) q
          intro z hz
          simp only [q, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons,
            List.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hu
          · rcases hz with rfl | hz
            · exact hv
            · simp at hz
      have htail := ih (fun z hz ↦ hp z (by simp [hz]))
      exact hstep.trans htail

/-- A continuous map with uniform height error `e` sends every scalar-band
path to the band enlarged by `e`. -/
theorem HeightBandJoined.map_of_continuous_height_close
    {X Y : FilteredReebGraph} {e a b : ℝ}
    {φ : X.Carrier → Y.Carrier} (hφ : Continuous φ)
    (hheight : ∀ z, |X.height z - Y.height (φ z)| ≤ e)
    {x x' : X.Carrier} (h : HeightBandJoined X a b x x') :
    HeightBandJoined Y (a - e) (b + e) (φ x) (φ x') := by
  refine ⟨h.somePath.map hφ, ?_⟩
  intro t
  have hz := h.somePath_mem t
  have he := hheight (h.somePath t)
  rw [abs_sub_le_iff] at he
  change a - e ≤ Y.height (φ (h.somePath t)) ∧
    Y.height (φ (h.somePath t)) ≤ b + e
  constructor <;> linarith [hz.1, hz.2, he.1, he.2]

/-- A homotopy whose track over `x` remains in a scalar band centered at
`center x`. -/
structure HeightControlledHomotopy
    (X : FilteredReebGraph) (center : X.Carrier → ℝ) (e : ℝ)
    (g₀ g₁ : X.Carrier → X.Carrier) where
  toFun : GraphUnitInterval × X.Carrier → X.Carrier
  continuous_toFun : Continuous toFun
  at_zero : ∀ x, toFun (graphUnitZero, x) = g₀ x
  at_one : ∀ x, toFun (graphUnitOne, x) = g₁ x
  height_control : ∀ t x,
    center x - e ≤ X.height (toFun (t, x)) ∧
    X.height (toFun (t, x)) ≤ center x + e

def HeightControlledHomotopy.path
    {X : FilteredReebGraph} {center : X.Carrier → ℝ} {e : ℝ}
    {g₀ g₁ : X.Carrier → X.Carrier}
    (h : HeightControlledHomotopy X center e g₀ g₁) (x : X.Carrier) :
    Path (g₀ x) (g₁ x) where
  toFun t := h.toFun (t, x)
  continuous_toFun := h.continuous_toFun.comp
    (continuous_id.prod_mk continuous_const)
  source' := by simpa only using h.at_zero x
  target' := by simpa only using h.at_one x

theorem HeightControlledHomotopy.joined
    {X : FilteredReebGraph} {center : X.Carrier → ℝ} {e : ℝ}
    {g₀ g₁ : X.Carrier → X.Carrier}
    (h : HeightControlledHomotopy X center e g₀ g₁) (x : X.Carrier) :
    HeightBandJoined X (center x - e) (center x + e) (g₀ x) (g₁ x) := by
  refine ⟨h.path x, ?_⟩
  intro t
  exact h.height_control t x

/-- Intrinsic scalar-range distance used in the functional distortion and
functional Gromov--Hausdorff distances.  It is the infimum of the lengths of
closed scalar intervals whose inverse image contains a path joining the two
points.  `ℝ≥0∞` correctly assigns distance `∞` when no such path exists. -/
noncomputable def heightRangeDist
    (X : FilteredReebGraph) (x y : X.Carrier) : ℝ≥0∞ :=
  sInf {w : ℝ≥0∞ | ∃ a b : ℝ,
    a ≤ b ∧ HeightBandJoined X a b x y ∧ w = ENNReal.ofReal (b - a)}

/-- An isomorphism of filtered spaces: a homeomorphism that preserves the
scalar value exactly.  This is the correct realization-level certificate for
a degree-two suppression; preservation of graph counts alone is insufficient. -/
structure FilteredReebGraphEquiv (X Y : FilteredReebGraph) where
  toHomeomorph : X.Carrier ≃ₜ Y.Carrier
  height_eq : ∀ x, Y.height (toHomeomorph x) = X.height x

namespace FilteredReebGraphEquiv

def symm {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y) :
    FilteredReebGraphEquiv Y X where
  toHomeomorph := e.toHomeomorph.symm
  height_eq y := by
    simpa using (e.height_eq (e.toHomeomorph.symm y)).symm

def refl (X : FilteredReebGraph) : FilteredReebGraphEquiv X X where
  toHomeomorph := Homeomorph.refl X.Carrier
  height_eq _ := rfl

def trans {X Y Z : FilteredReebGraph}
    (eXY : FilteredReebGraphEquiv X Y)
    (eYZ : FilteredReebGraphEquiv Y Z) : FilteredReebGraphEquiv X Z where
  toHomeomorph := eXY.toHomeomorph.trans eYZ.toHomeomorph
  height_eq x := by
    change Z.height (eYZ.toHomeomorph (eXY.toHomeomorph x)) = X.height x
    rw [eYZ.height_eq, eXY.height_eq]

theorem heightBandJoined {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) {a b : ℝ} {x x' : X.Carrier}
    (h : HeightBandJoined X a b x x') :
    HeightBandJoined Y a b (e.toHomeomorph x) (e.toHomeomorph x') := by
  refine ⟨h.somePath.map e.toHomeomorph.continuous, ?_⟩
  intro t
  change a ≤ Y.height (e.toHomeomorph (h.somePath t)) ∧
    Y.height (e.toHomeomorph (h.somePath t)) ≤ b
  simpa only [e.height_eq] using h.somePath_mem t

theorem heightBandJoined_iff {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) {a b : ℝ} {x x' : X.Carrier} :
    HeightBandJoined X a b x x' ↔
      HeightBandJoined Y a b (e.toHomeomorph x) (e.toHomeomorph x') := by
  constructor
  · exact e.heightBandJoined
  · intro h
    simpa [FilteredReebGraphEquiv.symm] using e.symm.heightBandJoined h

theorem heightRangeDist_eq {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) (x x' : X.Carrier) :
    heightRangeDist Y (e.toHomeomorph x) (e.toHomeomorph x') =
      heightRangeDist X x x' := by
  unfold heightRangeDist
  congr 1
  ext w
  constructor
  · rintro ⟨a, b, hab, hjoined, hw⟩
    exact ⟨a, b, hab, e.heightBandJoined_iff.mpr hjoined, hw⟩
  · rintro ⟨a, b, hab, hjoined, hw⟩
    exact ⟨a, b, hab, e.heightBandJoined_iff.mp hjoined, hw⟩

end FilteredReebGraphEquiv

end ReebGraph
