import ReebGraph.Modules.GraphGeometry

/-!
# Sampling density and level crossings

Sampling density, metric chains, and the quadratic level-crossing
condition that supplies active support coverage.

Main results: `quadraticLevelCrossingCondition_sq`, `_neg_sq`, `_saddle`,
and `_id` -- the four scalar normal forms verified with explicit
constants -- plus `activeMetricChain_of_joinedIn_of_dense` and the
`Proximity*Adequate` implication chain ending in
`ProximitySupportComplete.to_graph`.

Supporting: `ActiveMetricChain` algebra, the several density predicates,
and the monotonicity/sampling transfers between them.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Every continuum point has a nearby endpoint of an edge crossing a nearby
threshold.  The scalar slack is essential at extrema and for midpoint slices. -/
def CrossingCoverage
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fhat : V → ℝ) (δ ξ : ℝ) : Prop :=
  ∀ x : M, ∃ (t : ℝ) (u : V),
    IsActiveVertex G fhat t u ∧
    dist (sample u) x ≤ δ ∧ |t - f x| ≤ ξ

/-- Crossing coverage is monotone under inclusion of neighborhood graphs. -/
theorem CrossingCoverage.mono_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G H : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {δ ξ : ℝ}
    (hGH : G ≤ H) (h : CrossingCoverage M V G sample f fhat δ ξ) :
    CrossingCoverage M V H sample f fhat δ ξ := by
  intro x
  rcases h x with ⟨t, u, hu, hux, ht⟩
  exact ⟨t, u, isActiveVertex_mono hGH fhat t hu, hux, ht⟩

/-- Reachability by finitely many metric steps of length less than `κ`. -/
def MetricChain
    {X : Type*} [PseudoMetricSpace X] (κ : ℝ) (x y : X) : Prop :=
  Relation.ReflTransGen (fun a b => dist a b < κ) x y

/-- A preconnected metric space is chain connected at every positive scale. -/
theorem metricChain_of_preconnectedSpace
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    {κ : ℝ} (hκ : 0 < κ) (x y : X) : MetricChain κ x y := by
  let R : Set X := {z | MetricChain κ x z}
  have hRopen : IsOpen R := by
    refine isOpen_iff_forall_mem_open.2 ?_
    intro z hz
    refine ⟨Metric.ball z κ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hκ⟩
    intro w hw
    exact hz.tail (by simpa only [Metric.mem_ball, dist_comm] using hw)
  have hRcOpen : IsOpen Rᶜ := by
    refine isOpen_iff_forall_mem_open.2 ?_
    intro z hz
    refine ⟨Metric.ball z κ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hκ⟩
    intro w hw hwR
    exact hz (hwR.tail (by simpa only [Metric.mem_ball] using hw))
  have hRclopen : IsClopen R := ⟨isOpen_compl_iff.mp hRcOpen, hRopen⟩
  have hxR : x ∈ R := Relation.ReflTransGen.refl
  exact (isPreconnected_univ.subset_isClopen hRclopen ⟨x, Set.mem_univ x, hxR⟩)
    (Set.mem_univ y)

/-- A finite metric chain of active crossing witnesses.  This formulation is
independent of the algorithmic graph: consecutive sample points are required
only to lie within the canonical proximity radius. -/
inductive ActiveMetricChain
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} (sample : V → M) (fhat : V → ℝ) (ρ t : ℝ) : V → V → Prop
  | refl (u : V)
      (hu : IsActiveVertex (proximityGraph M V sample ρ) fhat t u) :
      ActiveMetricChain sample fhat ρ t u u
  | tail {u v w : V}
      (h : ActiveMetricChain sample fhat ρ t u v)
      (hw : IsActiveVertex (proximityGraph M V sample ρ) fhat t w)
      (hvw : v ≠ w) (hdist : dist (sample v) (sample w) ≤ ρ) :
      ActiveMetricChain sample fhat ρ t u w

theorem ActiveMetricChain.source_active
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    IsActiveVertex (proximityGraph M V sample ρ) fhat t u := by
  induction h with
  | refl hu => exact hu
  | tail _ _ _ _ ih => exact ih

theorem ActiveMetricChain.target_active
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    IsActiveVertex (proximityGraph M V sample ρ) fhat t v := by
  induction h with
  | refl hu => exact hu
  | tail _ hw _ _ _ => exact hw

/-- Every active metric chain is a walk in the support-induced slice of the
canonical proximity graph. -/
theorem ActiveMetricChain.reachable
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    (supportSliceGraph (proximityGraph M V sample ρ) fhat t).Reachable u v := by
  induction h with
  | refl _ => exact SimpleGraph.Reachable.refl _
  | tail h hw hvw hdist ih =>
      have hv := h.target_active
      have hadj :
          (supportSliceGraph (proximityGraph M V sample ρ) fhat t).Adj _ _ :=
        ⟨⟨hvw, hdist⟩, hv, hw⟩
      exact ih.trans ⟨.cons hadj .nil⟩

theorem ActiveMetricChain.of_dist
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (hu : IsActiveVertex (proximityGraph M V sample ρ) fhat t u)
    (hv : IsActiveVertex (proximityGraph M V sample ρ) fhat t v)
    (huv : u ≠ v) (hdist : dist (sample u) (sample v) ≤ ρ) :
    ActiveMetricChain sample fhat ρ t u v :=
  .tail (.refl u hu) hv huv hdist

theorem ActiveMetricChain.trans
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v w : V}
    (huv : ActiveMetricChain sample fhat ρ t u v)
    (hvw : ActiveMetricChain sample fhat ρ t v w) :
    ActiveMetricChain sample fhat ρ t u w := by
  induction hvw with
  | refl _ => exact huv
  | tail _ hx hne hdist ih => exact .tail ih hx hne hdist

theorem ActiveMetricChain.symm
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    ActiveMetricChain sample fhat ρ t v u := by
  induction h with
  | refl hu => exact .refl _ hu
  | tail h hw hvw hdist ih =>
      have hwv : ActiveMetricChain sample fhat ρ t _ _ :=
        .of_dist hw h.target_active hvw.symm (by simpa only [dist_comm] using hdist)
      exact hwv.trans ih

/-- Active crossing witnesses at the common threshold `t` are `ε`-dense on
the continuum set `S`. -/
def ActiveWitnessDenseOn
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (fhat : V → ℝ)
    (ρ t ε : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ u : V,
    IsActiveVertex (proximityGraph M V sample ρ) fhat t u ∧
    dist (sample u) z ≤ ε

/-- Every point of `S` has a nearby pair of distinct sample points within the
proximity radius whose observed scalar values straddle `t`. -/
def CrossingPairDenseOn
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (fhat : V → ℝ)
    (ρ t ε : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ u v : V,
    u ≠ v ∧ dist (sample u) (sample v) ≤ ρ ∧ Crosses fhat t u v ∧
    dist (sample u) z ≤ ε ∧ dist (sample v) z ≤ ε

/-- Fill-distance bound for a finite sample. -/
def SampleDense
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (σ : ℝ) : Prop :=
  ∀ x : M, ∃ u : V, dist x (sample u) ≤ σ

/-- A true continuum function has points on both sides of `t`, uniformly near
every point of `S` and with scalar margin `m`. -/
def TrueCrossingPairDenseOn
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (t a m : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ p n : M,
    dist p z ≤ a ∧ dist n z ≤ a ∧ f p + m < t ∧ t < f n - m

theorem CrossingPairDenseOn.activeWitnessDenseOn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ}
    {ρ t ε : ℝ} {S : Set M}
    (h : CrossingPairDenseOn M V sample fhat ρ t ε S) :
    ActiveWitnessDenseOn M V sample fhat ρ t ε S := by
  intro z hz
  rcases h z hz with ⟨u, v, huv, hd, hcross, huz, _⟩
  exact ⟨u, ⟨v, ⟨⟨huv, hd⟩, hcross⟩⟩, huz⟩

/-- Dense sampling turns robust true crossing pairs into observed crossing
pairs.  All spatial and scalar scale conversions are explicit. -/
theorem TrueCrossingPairDenseOn.sample
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ t a m ε : ℝ} {S : Set M}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (htrue : TrueCrossingPairDenseOn M f t a m S) :
    CrossingPairDenseOn M V sample fhat ρ t ε S := by
  intro z hz
  rcases htrue z hz with ⟨p, n, hpz, hnz, hp, hn⟩
  rcases hsample p with ⟨u, hpu⟩
  rcases hsample n with ⟨v, hnv⟩
  have huScalar : |f (sample u) - f p| ≤ L * σ := by
    calc
      |f (sample u) - f p| ≤ L * dist (sample u) p := hL _ _
      _ ≤ L * σ := by
        gcongr
        simpa only [dist_comm] using hpu
  have hvScalar : |f (sample v) - f n| ≤ L * σ := by
    calc
      |f (sample v) - f n| ≤ L * dist (sample v) n := hL _ _
      _ ≤ L * σ := by
        gcongr
        simpa only [dist_comm] using hnv
  have huBelow : f (sample u) + e < t := by
    have huDiff : f (sample u) - f p ≤ L * σ :=
      (le_abs_self _).trans huScalar
    linarith
  have hvAbove : t < f (sample v) - e := by
    have hvDiff : f n - f (sample v) ≤ L * σ := by
      have hneg := (neg_le_abs (f (sample v) - f n)).trans hvScalar
      linarith
    linarith
  have hcross : Crosses fhat t u v :=
    crosses_of_approximation_margin (fun w => f (sample w)) fhat herr huBelow hvAbove
  have huv : u ≠ v := by
    intro huv
    subst v
    exact (not_crosses_of_eq fhat t rfl) hcross
  have huvDist : dist (sample u) (sample v) ≤ ρ := by
    calc
      dist (sample u) (sample v) ≤
          dist (sample u) p + dist p (sample v) := dist_triangle _ _ _
      _ ≤ dist (sample u) p +
          (dist p z + dist z n + dist n (sample v)) := by
        gcongr
        exact dist_triangle4 _ _ _ _
      _ ≤ σ + (a + a + σ) := by
        exact add_le_add
          (by simpa only [dist_comm] using hpu)
          (add_le_add
            (add_le_add hpz (by simpa only [dist_comm] using hnz)) hnv)
      _ = 2 * (a + σ) := by ring
      _ ≤ ρ := hprox
  have huz : dist (sample u) z ≤ ε := by
    calc
      dist (sample u) z ≤ dist (sample u) p + dist p z := dist_triangle _ _ _
      _ ≤ σ + a := add_le_add (by simpa only [dist_comm] using hpu) hpz
      _ = a + σ := add_comm _ _
      _ ≤ ε := hwitness
  have hvz : dist (sample v) z ≤ ε := by
    calc
      dist (sample v) z ≤ dist (sample v) n + dist n z := dist_triangle _ _ _
      _ ≤ σ + a := add_le_add (by simpa only [dist_comm] using hnv) hnz
      _ = a + σ := add_comm _ _
      _ ≤ ε := hwitness
  exact ⟨u, v, huv, huvDist, hcross, huz, hvz⟩

/-- Uniformly dense active witnesses along a continuum path lift to a finite
active metric chain.  The scale inequality is exactly the triangle-inequality
budget for two witness errors and one continuum-chain step. -/
theorem activeMetricChain_of_joinedIn_of_dense
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ}
    {ρ t ε κ : ℝ} {S : Set M} {x y : M}
    (hκ : 0 < κ) (hscale : 2 * ε + κ ≤ ρ)
    (hdense : ActiveWitnessDenseOn M V sample fhat ρ t ε S)
    (hxy : JoinedIn S x y) :
    ∃ u v : V, ActiveMetricChain sample fhat ρ t u v ∧
      dist (sample u) x ≤ ε ∧ dist (sample v) y ≤ ε := by
  let γ := hxy.somePath
  let P : Set M := Set.range γ
  letI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)
  have hPpath : IsPathConnected P := isPathConnected_range γ.continuous
  letI : PreconnectedSpace P :=
    isPreconnected_iff_preconnectedSpace.mp hPpath.isConnected.isPreconnected
  let xs : P := ⟨x, ⟨0, γ.source⟩⟩
  let ys : P := ⟨y, ⟨1, γ.target⟩⟩
  have hpoint : ∀ z : P, ∃ u : V,
      IsActiveVertex (proximityGraph M V sample ρ) fhat t u ∧
      dist (sample u) z.1 ≤ ε := by
    intro z
    apply hdense z.1
    rcases z.2 with ⟨s, hs⟩
    simpa only [hs] using hxy.somePath_mem s
  have hchain : MetricChain κ xs ys :=
    metricChain_of_preconnectedSpace hκ xs ys
  have hlift : ∀ {a b : P}, MetricChain κ a b →
      ∃ u v : V, ActiveMetricChain sample fhat ρ t u v ∧
        dist (sample u) a.1 ≤ ε ∧ dist (sample v) b.1 ≤ ε := by
    intro a b hab
    induction hab with
    | refl =>
        rcases hpoint a with ⟨u, hu, hua⟩
        exact ⟨u, u, .refl u hu, hua, hua⟩
    | @tail b c _ hbc ih =>
        rcases ih with ⟨u, v, huv, hua, hvb⟩
        rcases hpoint c with ⟨w, hw, hwc⟩
        by_cases hvw : v = w
        · subst w
          exact ⟨u, v, huv, hua, hwc⟩
        · have hbc' : dist b.1 c.1 ≤ κ := by
            exact le_of_lt hbc
          have hvwDist : dist (sample v) (sample w) ≤ ρ := by
            calc
              dist (sample v) (sample w) ≤
                  dist (sample v) b.1 + dist b.1 (sample w) :=
                dist_triangle _ _ _
              _ ≤ dist (sample v) b.1 +
                  (dist b.1 c.1 + dist c.1 (sample w)) := by
                gcongr
                exact dist_triangle _ _ _
              _ ≤ ε + (κ + ε) := by
                gcongr
                simpa only [dist_comm] using hwc
              _ = 2 * ε + κ := by ring
              _ ≤ ρ := hscale
          exact ⟨u, w, .tail huv hw hvw hvwDist, hua, hwc⟩
  rcases hlift hchain with ⟨u, v, huv, hux, hvy⟩
  exact ⟨u, v, huv, by simpa [xs] using hux, by simpa [ys] using hvy⟩

/-- Along every exact continuum level path there is one nearby threshold whose
active proximity-graph witnesses are uniformly `δ`-dense on that path.  This is
the local statement to be supplied by regular-level and Morse critical charts. -/
def CommonThresholdActiveDensity
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      ActiveWitnessDenseOn M V sample fhat ρ t δ
        (pathComponentIn x {z | f z = s})

/-- The local crossing-pair condition expected from regular-level charts and
Morse normal forms. -/
def CommonThresholdCrossingPairDensity
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      CrossingPairDenseOn M V sample fhat ρ t δ
        (pathComponentIn x {z | f z = s})

/-- Common-threshold two-sided variation for the true continuum function. -/
def CommonThresholdTrueCrossingPairDensity
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (a m ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      TrueCrossingPairDenseOn M f t a m
        (pathComponentIn x {z | f z = s})

/-- Crossing-pair density is monotone under enlarging the spatial radius,
weakening the scalar margin, and enlarging the allowed threshold slack. -/
theorem CommonThresholdTrueCrossingPairDensity.mono
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {a m ξ a' m' ξ' : ℝ}
    (h : CommonThresholdTrueCrossingPairDensity M f a m ξ)
    (ha : a ≤ a') (hm : m' ≤ m) (hξ : ξ ≤ ξ') :
    CommonThresholdTrueCrossingPairDensity M f a' m' ξ' := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hpairs⟩
  refine ⟨t, hts.trans hξ, ?_⟩
  intro z hz
  rcases hpairs z hz with ⟨p, n, hpz, hnz, hp, hn⟩
  exact ⟨p, n, hpz.trans ha, hnz.trans ha, by linarith, by linarith⟩

/-- Reversing the scalar orientation preserves the quantitative crossing
condition.  The witnesses exchange their below/above roles and the common
threshold is negated. -/
theorem CommonThresholdTrueCrossingPairDensity.neg
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {a m ξ : ℝ}
    (h : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    CommonThresholdTrueCrossingPairDensity M (fun z ↦ -f z) a m ξ := by
  intro s x y hxy
  have hlevel : {z : M | f z = -s} = {z : M | -f z = s} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  have hxy' : JoinedIn {z : M | f z = -s} x y := by
    rw [hlevel]
    exact hxy
  rcases h (-s) hxy' with ⟨t, hts, hpairs⟩
  refine ⟨-t, ?_, ?_⟩
  · calc
      |-t - s| = |-(t - -s)| := by ring_nf
      _ = |t - -s| := abs_neg _
      _ ≤ ξ := hts
  · have hcomponent :
        pathComponentIn x {z : M | f z = -s} =
          pathComponentIn x {z : M | -f z = s} := by rw [hlevel]
    intro z hz
    have hz' : z ∈ pathComponentIn x {z : M | f z = -s} := by
      rw [hcomponent]
      exact hz
    rcases hpairs z hz' with ⟨p, n, hpz, hnz, hp, hn⟩
    refine ⟨n, p, hnz, hpz, ?_, ?_⟩
    · change -f n + m < -t
      linarith
    · change -t < -f p - m
      linarith

/-- The quantitative local consequence expected from Morse normal forms on a
compact manifold.  At every sufficiently small spatial radius `a`, crossings
have a quadratic scalar margin and extrema require at most a quadratic shift
of the common threshold.  Regular charts provide stronger linear variation;
the quadratic rate is the uniform rate that also covers critical charts.

This property is deliberately independent of samples and neighborhood graphs.
It isolates the one analytic statement whose derivation from the classical
Morse lemma is not currently available in Mathlib. -/
def QuadraticLevelCrossingCondition
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (cShift cMargin a₀ : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ a₀ →
    CommonThresholdTrueCrossingPairDensity M f a
      (cMargin * a ^ 2) (cShift * a ^ 2)

/-- Quadratic level crossings are invariant under reversing the filter. -/
theorem QuadraticLevelCrossingCondition.neg
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {cShift cMargin a₀ : ℝ}
    (h : QuadraticLevelCrossingCondition M f cShift cMargin a₀) :
    QuadraticLevelCrossingCondition M (fun z ↦ -f z)
      cShift cMargin a₀ := by
  intro a ha ha₀
  exact (h a ha ha₀).neg

/-- A quadratic level-crossing condition supplies the exact crossing property
at any larger proof slack. -/
theorem QuadraticLevelCrossingCondition.crossing_pairs
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {cShift cMargin a₀ a ξ : ℝ}
    (h : QuadraticLevelCrossingCondition M f cShift cMargin a₀)
    (ha : 0 < a) (ha₀ : a ≤ a₀)
    (hshift : cShift * a ^ 2 ≤ ξ) :
    CommonThresholdTrueCrossingPairDensity M f a
      (cMargin * a ^ 2) ξ :=
  (h a ha ha₀).mono le_rfl le_rfl hshift

/-- The one-dimensional Morse minimum normal form has uniform quadratic
crossings.  At the critical level the proof uses a threshold shifted upward by
`a² / 64`; away from the critical level it uses the smaller shift `a² / 128`.
This is the formal model for why exact crossing at an extremum must be replaced
by a nearby common threshold. -/
theorem quadraticLevelCrossingCondition_sq (a₀ : ℝ) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ x ^ 2)
      (1 / 64) (1 / 128) a₀ := by
  intro a ha _
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  by_cases hs : s = 0
  · refine ⟨a ^ 2 / 64, ?_, ?_⟩
    · rw [hs, sub_zero, abs_of_nonneg]
      · ring_nf
        exact le_rfl
      · positivity
    · intro z hz
      have hzLevelSet : z ∈ {w : ℝ | w ^ 2 = s} :=
        pathComponentIn_subset hz
      have hzLevel : z ^ 2 = s := hzLevelSet
      have hz0 : z = 0 := by nlinarith
      subst z
      refine ⟨0, a / 2, ?_, ?_, ?_, ?_⟩
      · simp [Real.dist_eq, ha0]
      · rw [Real.dist_eq, sub_zero, abs_of_nonneg]
        · linarith
        · positivity
      · norm_num
        nlinarith
      · norm_num
        nlinarith
  · refine ⟨s + a ^ 2 / 128, ?_, ?_⟩
    · rw [add_sub_cancel_left, abs_of_nonneg]
      · norm_num
        nlinarith [sq_nonneg a]
      · positivity
    · intro z hz
      have hzLevelSet : z ∈ {w : ℝ | w ^ 2 = s} :=
        pathComponentIn_subset hz
      have hzLevel : z ^ 2 = s := hzLevelSet
      have hz_ne : z ≠ 0 := by
        intro hz0
        subst z
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at hzLevel
        exact hs hzLevel.symm
      rcases lt_or_gt_of_ne hz_ne with hzneg | hzpos
      · by_cases hzsmall : -z ≤ a / 2
        · refine ⟨0, z - a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonpos hzneg.le]
            linarith
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith [sq_nonneg z]
          · norm_num
            nlinarith

        · have hzlarge : a / 2 < -z := lt_of_not_ge hzsmall
          refine ⟨z + a / 2, z - a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith
          · norm_num
            nlinarith
      · by_cases hzsmall : z ≤ a / 2
        · refine ⟨0, z + a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hzpos.le]
            linarith
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith [sq_nonneg z]
          · norm_num
            nlinarith
        · have hzlarge : a / 2 < z := lt_of_not_ge hzsmall
          refine ⟨z - a / 2, z + a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith
          · norm_num
            nlinarith

/-- The one-dimensional Morse maximum normal form follows by reversing the
scalar orientation of the minimum model. -/
theorem quadraticLevelCrossingCondition_neg_sq (a₀ : ℝ) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ -(x ^ 2))
      (1 / 64) (1 / 128) a₀ :=
  (quadraticLevelCrossingCondition_sq a₀).neg

/-- The two-dimensional saddle normal form has two-sided quadratic crossings
at the exact level.  Moving only in the positive-square coordinate raises the
function, while moving only in the negative-square coordinate lowers it. -/
theorem quadraticLevelCrossingCondition_saddle (a₀ : ℝ) :
    QuadraticLevelCrossingCondition (ℝ × ℝ)
      (fun z : ℝ × ℝ ↦ z.1 ^ 2 - z.2 ^ 2)
      0 (1 / 128) a₀ := by
  intro a ha _
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  refine ⟨s, by simp, ?_⟩
  intro z hz
  have hzLevelSet : z ∈ {w : ℝ × ℝ | w.1 ^ 2 - w.2 ^ 2 = s} :=
    pathComponentIn_subset hz
  have hzLevel : z.1 ^ 2 - z.2 ^ 2 = s := hzLevelSet
  let p : ℝ × ℝ :=
    (z.1, if 0 ≤ z.2 then z.2 + a / 2 else z.2 - a / 2)
  let n : ℝ × ℝ :=
    (if 0 ≤ z.1 then z.1 + a / 2 else z.1 - a / 2, z.2)
  refine ⟨p, n, ?_, ?_, ?_, ?_⟩
  · dsimp only [p]
    split_ifs with hz2
    · rw [← Prod.eta z, dist_prod_same_left, Real.dist_eq]
      have hdiff : z.2 + a / 2 - z.2 = a / 2 := by ring
      rw [hdiff, abs_of_nonneg]
      · linarith
      · positivity
    · rw [← Prod.eta z, dist_prod_same_left, Real.dist_eq]
      have hdiff : z.2 - a / 2 - z.2 = -(a / 2) := by ring
      rw [hdiff, abs_neg, abs_of_nonneg]
      · linarith
      · positivity
  · dsimp only [n]
    split_ifs with hz1
    · rw [← Prod.eta z, dist_prod_same_right, Real.dist_eq]
      have hdiff : z.1 + a / 2 - z.1 = a / 2 := by ring
      rw [hdiff, abs_of_nonneg]
      · linarith
      · positivity
    · rw [← Prod.eta z, dist_prod_same_right, Real.dist_eq]
      have hdiff : z.1 - a / 2 - z.1 = -(a / 2) := by ring
      rw [hdiff, abs_neg, abs_of_nonneg]
      · linarith
      · positivity
  · dsimp only [p]
    split_ifs with hz2
    · norm_num
      nlinarith
    · norm_num
      nlinarith
  · dsimp only [n]
    split_ifs with hz1
    · norm_num
      nlinarith
    · norm_num
      nlinarith

/-- On a regular chart the linear normal form has stronger, linear variation.
Restricting to radii `a ≤ a₀` turns this into the uniform quadratic margin
used by the global theorem. -/
theorem quadraticLevelCrossingCondition_id {a₀ : ℝ} (ha₀ : 0 < a₀) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ x)
      0 (1 / (8 * a₀)) a₀ := by
  intro a ha haa₀
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have hc0 : 0 ≤ 1 / (8 * a₀) := by positivity
  have ha2_le : a ^ 2 ≤ a * a₀ := by
    nlinarith
  have hmargin_le : (1 / (8 * a₀)) * a ^ 2 ≤ a / 8 := by
    calc
      (1 / (8 * a₀)) * a ^ 2 ≤
          (1 / (8 * a₀)) * (a * a₀) :=
        mul_le_mul_of_nonneg_left ha2_le hc0
      _ = a / 8 := by
        field_simp [ne_of_gt ha₀]
        <;> ring
  have hmargin_lt : (1 / (8 * a₀)) * a ^ 2 < a / 2 := by
    linarith
  refine ⟨s, by simp, ?_⟩
  intro z hz
  have hzLevelSet : z ∈ {w : ℝ | w = s} := pathComponentIn_subset hz
  have hzLevel : z = s := hzLevelSet
  refine ⟨z - a / 2, z + a / 2, ?_, ?_, ?_, ?_⟩
  · rw [Real.dist_eq]
    have hdiff : z - a / 2 - z = -(a / 2) := by ring
    rw [hdiff, abs_neg, abs_of_nonneg]
    · linarith
    · positivity
  · rw [Real.dist_eq]
    have hdiff : z + a / 2 - z = a / 2 := by ring
    rw [hdiff, abs_of_nonneg]
    · linarith
    · positivity
  · change z - a / 2 + (1 / (8 * a₀)) * a ^ 2 < s
    linarith
  · change s < z + a / 2 - (1 / (8 * a₀)) * a ^ 2
    linarith

/-- Quantitative continuum two-sided variation, dense sampling, and uniform
filter consistency imply the observed common-threshold crossing-pair condition. -/
theorem CommonThresholdTrueCrossingPairDensity.sample
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ a m ε ξ : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (htrue : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    CommonThresholdCrossingPairDensity M V sample f fhat ρ ε ξ := by
  intro s x y hxy
  rcases htrue s hxy with ⟨t, hts, hpairs⟩
  exact ⟨t, hts, hpairs.sample hL_nonneg hL hsample herr
    hmargin hprox hwitness⟩

theorem CommonThresholdCrossingPairDensity.to_activeDensity
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : CommonThresholdCrossingPairDensity M V sample f fhat ρ δ ξ) :
    CommonThresholdActiveDensity M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hpairs⟩
  exact ⟨t, hts, hpairs.activeWitnessDenseOn⟩

/-- The geometric active-witness task in finite-chain form.  Morse charts and
sampling density should construct this chain; no connectivity of an output
graph is assumed here. -/
def ActiveWitnessChainCoverage
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ (t : ℝ) (u v : V),
      ActiveMetricChain sample fhat ρ t u v ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧ |t - s| ≤ ξ

/-- Uniform common-threshold active density implies finite active-witness chain
coverage whenever the proximity radius has room for two sampling errors. -/
theorem CommonThresholdActiveDensity.to_chainCoverage
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ} (hgap : 2 * δ < ρ)
    (h : CommonThresholdActiveDensity M V sample f fhat ρ δ ξ) :
    ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hdense⟩
  have hxLevel : x ∈ {z : M | f z = s} := hxy.source_mem
  have hxComponent : x ∈ pathComponentIn x {z : M | f z = s} :=
    mem_pathComponentIn_self hxLevel
  have hyComponent : y ∈ pathComponentIn x {z : M | f z = s} := hxy
  have hxyComponent :
      JoinedIn (pathComponentIn x {z : M | f z = s}) x y :=
    (isPathConnected_pathComponentIn hxLevel).joinedIn
      x hxComponent y hyComponent
  have hκ : 0 < ρ - 2 * δ := by linarith
  have hscale : 2 * δ + (ρ - 2 * δ) ≤ ρ := by linarith
  rcases activeMetricChain_of_joinedIn_of_dense hκ hscale hdense hxyComponent with
    ⟨u, v, hchain, hux, hvy⟩
  exact ⟨t, u, v, hchain, hux, hvy, hts⟩

/-- Chain coverage includes pointwise crossing coverage as the constant-path
case. -/
theorem ActiveWitnessChainCoverage.crossingCoverage
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ) :
    CrossingCoverage M V (proximityGraph M V sample ρ) sample f fhat δ ξ := by
  intro x
  have hxx : JoinedIn {z | f z = f x} x x := JoinedIn.refl rfl
  rcases h (f x) hxx with ⟨t, u, v, hchain, hux, _, hts⟩
  exact ⟨t, u, hchain.source_active, hux, hts⟩

/-- Nearby crossing witnesses associated with one continuum level-set path
lie in the same support-induced slice component. -/
def SupportComplete
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fhat : V → ℝ) (δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ (t : ℝ) (u v : V),
      IsActiveVertex G fhat t u ∧ IsActiveVertex G fhat t v ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧
      |t - s| ≤ ξ ∧ (supportSliceGraph G fhat t).Reachable u v

/-- Support completeness formulated for the canonical proximity graph.  This
is the manifold-and-sampling statement that is independent of the supplied
neighborhood graph. -/
def ProximitySupportComplete
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  SupportComplete M V (proximityGraph M V sample ρ) sample f fhat δ ξ

/-- The complete active-witness statement for a canonical proximity graph:
nearby crossing witnesses exist and witnesses on one continuum level path are
connected at a common nearby threshold. -/
def ProximityWitnessAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  CrossingCoverage M V (proximityGraph M V sample ρ) sample f fhat δ ξ ∧
  ProximitySupportComplete M V sample f fhat ρ δ ξ

/-- A non-circular sufficient condition for proximity witness adequacy: finite
metric chains of active witnesses.  Pointwise crossing coverage follows from
the constant-path case. -/
def ProximityChainWitnessAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ

/-- The local geometric form of canonical witness adequacy. -/
def ProximityActiveDensityAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  2 * δ < ρ ∧ CommonThresholdActiveDensity M V sample f fhat ρ δ ξ

/-- The chart-level sufficient condition: a spatial scale gap and uniformly
dense crossing pairs at one nearby threshold. -/
def ProximityCrossingPairAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  2 * δ < ρ ∧ CommonThresholdCrossingPairDensity M V sample f fhat ρ δ ξ

/-- A single constructor reducing proximity witness adequacy to quantitative
two-sided variation of the true continuum function. -/
theorem ProximityCrossingPairAdequate.of_true
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ a m ε ξ : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (hgap : 2 * ε < ρ)
    (htrue : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    ProximityCrossingPairAdequate M V sample f fhat ρ ε ξ :=
  ⟨hgap, htrue.sample hL_nonneg hL hsample herr hmargin hprox hwitness⟩

theorem ProximityCrossingPairAdequate.to_activeDensityAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityCrossingPairAdequate M V sample f fhat ρ δ ξ) :
    ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ :=
  ⟨h.1, h.2.to_activeDensity⟩

theorem ProximityActiveDensityAdequate.to_chainWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ) :
    ProximityChainWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.2.to_chainCoverage h.1

theorem ActiveWitnessChainCoverage.to_proximitySupportComplete
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ) :
    ProximitySupportComplete M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, u, v, hchain, hux, hvy, hts⟩
  exact ⟨t, u, v, hchain.source_active, hchain.target_active,
    hux, hvy, hts, hchain.reachable⟩

/-- Finite metric witness chains prove the full canonical proximity-graph
witness theorem. -/
theorem ProximityChainWitnessAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityChainWitnessAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  ⟨h.crossingCoverage, h.to_proximitySupportComplete⟩

theorem ProximityActiveDensityAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.to_chainWitnessAdequate.to_proximityWitnessAdequate

theorem ProximityCrossingPairAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityCrossingPairAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.to_activeDensityAdequate.to_proximityWitnessAdequate

/-- Support completeness is monotone under inclusion of neighborhood graphs. -/
theorem SupportComplete.mono_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G H : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {δ ξ : ℝ}
    (hGH : G ≤ H) (h : SupportComplete M V G sample f fhat δ ξ) :
    SupportComplete M V H sample f fhat δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, u, v, hu, hv, hux, hvy, hts, huv⟩
  refine ⟨t, u, v,
    isActiveVertex_mono hGH fhat t hu,
    isActiveVertex_mono hGH fhat t hv,
    hux, hvy, hts, ?_⟩
  exact SimpleGraph.Reachable.mono (supportSliceGraph_mono hGH fhat t) huv

/-- The lower graph-sandwich inclusion transfers the canonical proximity-graph
completeness theorem to the actual neighborhood graph used by the algorithm. -/
theorem ProximitySupportComplete.to_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {ρ δ ξ : ℝ}
    (hclose : ContainsProximityGraph M V G sample ρ)
    (h : ProximitySupportComplete M V sample f fhat ρ δ ξ) :
    SupportComplete M V G sample f fhat δ ξ :=
  h.mono_graph hclose

/-- Both active-witness conclusions transfer together through the lower graph
sandwich. -/
theorem ProximityWitnessAdequate.to_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {ρ δ ξ : ℝ}
    (hclose : ContainsProximityGraph M V G sample ρ)
    (h : ProximityWitnessAdequate M V sample f fhat ρ δ ξ) :
    CrossingCoverage M V G sample f fhat δ ξ ∧
      SupportComplete M V G sample f fhat δ ξ :=
  ⟨h.1.mono_graph hclose, h.2.to_graph hclose⟩

end ReebGraph
