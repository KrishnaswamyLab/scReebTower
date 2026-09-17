import ReebGraph.Modules.FunctionalGH

/-!
# Band certificates for GH bounds

Band-level certificates: the reusable interface for turning a pair of
height-close, band-compatible maps into a functional GH bound.

Main results: `functionalGHDistance_le_of_band_certificate` and
`functionalGHDistance_le_of_continuous_approximation`.  Every later
distance bound in the development is obtained by constructing one of
these certificates.

Supporting lemmas: `FunctionalGHMapBandCompatibility.band_to_full` /
`.band_inv_full` and `functionalGHMapBandCompatibility_of_imageBandReflection`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- A band-level formulation of a functional-GH comparison.  It is the form
produced naturally by support-component soundness and completeness: every
path in a scalar band maps to a path in the band expanded by `e`, in both
directions and for the full two-map correspondence. -/
structure FunctionalGHBandCertificate
    (X Y : FilteredReebGraph) (e : ℝ) where
  error_nonneg : 0 ≤ e
  toFun : X.Carrier → Y.Carrier
  invFun : Y.Carrier → X.Carrier
  height_to : ∀ x, |X.height x - Y.height (toFun x)| ≤ e
  height_inv : ∀ y, |X.height (invFun y) - Y.height y| ≤ e
  band_to : ∀ {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ},
    FunctionalGHRel X Y toFun invFun x y →
    FunctionalGHRel X Y toFun invFun x' y' →
    a ≤ b → HeightBandJoined X a b x x' →
    HeightBandJoined Y (a - e) (b + e) y y'
  band_inv : ∀ {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ},
    FunctionalGHRel X Y toFun invFun x y →
    FunctionalGHRel X Y toFun invFun x' y' →
    a ≤ b → HeightBandJoined Y a b y y' →
    HeightBandJoined X (a - e) (b + e) x x'

/-- A local four-part form of band compatibility.  Mapwise band preservation
and controlled round trips imply the full two-map correspondence condition. -/
structure FunctionalGHMapBandCompatibility
    (X Y : FilteredReebGraph) (e : ℝ)
    (φ : X.Carrier → Y.Carrier) (ψ : Y.Carrier → X.Carrier) : Prop where
  band_to_map : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
    HeightBandJoined X a b x x' →
    HeightBandJoined Y (a - e) (b + e) (φ x) (φ x')
  band_inv_map : ∀ {a b : ℝ} {y y' : Y.Carrier}, a ≤ b →
    HeightBandJoined Y a b y y' →
    HeightBandJoined X (a - e) (b + e) (ψ y) (ψ y')
  roundtrip_X : ∀ x,
    HeightBandJoined X (Y.height (φ x) - e) (Y.height (φ x) + e)
      x (ψ (φ x))
  roundtrip_Y : ∀ y,
    HeightBandJoined Y (X.height (ψ y) - e) (X.height (ψ y) + e)
      y (φ (ψ y))

/-- Continuous height-controlled approximate inverses.  Continuity supplies
mapwise band preservation, while the controlled homotopies supply the two
round-trip clauses. -/
structure ContinuousFunctionalGHApproximation
    (X Y : FilteredReebGraph) (e : ℝ) where
  error_nonneg : 0 ≤ e
  toFun : X.Carrier → Y.Carrier
  invFun : Y.Carrier → X.Carrier
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun
  height_to : ∀ x, |X.height x - Y.height (toFun x)| ≤ e
  height_inv : ∀ y, |X.height (invFun y) - Y.height y| ≤ e
  roundtrip_X : HeightControlledHomotopy X (fun x => Y.height (toFun x)) e
    id (fun x => invFun (toFun x))
  roundtrip_Y : HeightControlledHomotopy Y (fun y => X.height (invFun y)) e
    id (fun y => toFun (invFun y))

def ContinuousFunctionalGHApproximation.toMapBandCompatibility
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    FunctionalGHMapBandCompatibility X Y e h.toFun h.invFun where
  band_to_map := by
    intro a b x x' _hab hxx'
    exact hxx'.map_of_continuous_height_close h.continuous_toFun h.height_to
  band_inv_map := by
    intro a b y y' _hab hyy'
    exact hyy'.map_of_continuous_height_close h.continuous_invFun
      (fun y => by simpa only [abs_sub_comm] using h.height_inv y)
  roundtrip_X := h.roundtrip_X.joined
  roundtrip_Y := h.roundtrip_Y.joined

/-- A reduced route to full two-map compatibility.  It suffices to preserve
bands forward, reflect bands only between points in the forward image, and
connect every target point to the image of its selected inverse.  The three
uses of the base error account for the factor `3`. -/
theorem functionalGHMapBandCompatibility_of_imageBandReflection
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (he : 0 ≤ e)
    (hforward : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
      HeightBandJoined X a b x x' →
      HeightBandJoined Y (a - e) (b + e) (φ x) (φ x'))
    (hheight_inv : ∀ y, |X.height (ψ y) - Y.height y| ≤ e)
    (hroundtripY : ∀ y,
      HeightBandJoined Y (X.height (ψ y) - e) (X.height (ψ y) + e)
        y (φ (ψ y)))
    (hreflect : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
      HeightBandJoined Y a b (φ x) (φ x') →
      HeightBandJoined X (a - e) (b + e) x x') :
    FunctionalGHMapBandCompatibility X Y (3 * e) φ ψ := by
  refine
    { band_to_map := ?_
      band_inv_map := ?_
      roundtrip_X := ?_
      roundtrip_Y := ?_ }
  · intro a b x x' hab hxx'
    exact HeightBandJoined.mono (hforward hab hxx')
      (by linarith) (by linarith)
  · intro a b y y' hab hyy'
    have hyClose := hheight_inv y
    have hy'Close := hheight_inv y'
    rw [abs_sub_le_iff] at hyClose hy'Close
    have hleftBase := hroundtripY y
    have hrightBase := hroundtripY y'
    have hleftWide : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        y (φ (ψ y)) :=
      HeightBandJoined.mono hleftBase
        (by linarith [hyy'.source_mem.1, hyClose.1])
        (by linarith [hyy'.source_mem.2, hyClose.2])
    have hrightWide : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        y' (φ (ψ y')) :=
      HeightBandJoined.mono hrightBase
        (by linarith [hyy'.target_mem.1, hy'Close.1])
        (by linarith [hyy'.target_mem.2, hy'Close.2])
    have hmiddle : HeightBandJoined Y (a - 2 * e) (b + 2 * e) y y' :=
      HeightBandJoined.mono hyy' (by linarith) (by linarith)
    have himage : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        (φ (ψ y)) (φ (ψ y')) :=
      hleftWide.symm.trans (hmiddle.trans hrightWide)
    have hreflected := hreflect (show a - 2 * e ≤ b + 2 * e by linarith)
      himage
    convert hreflected using 1 <;> ring
  · intro x
    have hxClose := hheight_inv (φ x)
    rw [abs_sub_le_iff] at hxClose
    have hbase := hroundtripY (φ x)
    have hwide : HeightBandJoined Y
        (Y.height (φ x) - 2 * e) (Y.height (φ x) + 2 * e)
        (φ x) (φ (ψ (φ x))) :=
      HeightBandJoined.mono hbase
        (by linarith [hxClose.1]) (by linarith [hxClose.2])
    have hreflected := hreflect
      (show Y.height (φ x) - 2 * e ≤ Y.height (φ x) + 2 * e by linarith)
      hwide
    convert hreflected using 1 <;> ring
  · intro y
    exact HeightBandJoined.mono (hroundtripY y)
      (by linarith) (by linarith)

theorem FunctionalGHMapBandCompatibility.band_to_full
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (h : FunctionalGHMapBandCompatibility X Y e φ ψ)
    {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ}
    (hxy : FunctionalGHRel X Y φ ψ x y)
    (hx'y' : FunctionalGHRel X Y φ ψ x' y')
    (hab : a ≤ b) (hxx' : HeightBandJoined X a b x x') :
    HeightBandJoined Y (a - e) (b + e) y y' := by
  have hmap := h.band_to_map hab hxx'
  have hleft : HeightBandJoined Y (a - e) (b + e) y (φ x) := by
    rcases hxy with hxy | hxy
    · subst y
      exact JoinedIn.refl hmap.source_mem
    · have hr := h.roundtrip_Y y
      rw [← hxy] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hxx'.source_mem.1])
        (by linarith [hxx'.source_mem.2])
  have hright : HeightBandJoined Y (a - e) (b + e) (φ x') y' := by
    rcases hx'y' with hx'y' | hx'y'
    · subst y'
      exact JoinedIn.refl hmap.target_mem
    · have hr := (h.roundtrip_Y y').symm
      rw [← hx'y'] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hxx'.target_mem.1])
        (by linarith [hxx'.target_mem.2])
  exact hleft.trans (hmap.trans hright)

theorem FunctionalGHMapBandCompatibility.band_inv_full
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (h : FunctionalGHMapBandCompatibility X Y e φ ψ)
    {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ}
    (hxy : FunctionalGHRel X Y φ ψ x y)
    (hx'y' : FunctionalGHRel X Y φ ψ x' y')
    (hab : a ≤ b) (hyy' : HeightBandJoined Y a b y y') :
    HeightBandJoined X (a - e) (b + e) x x' := by
  have hmap := h.band_inv_map hab hyy'
  have hleft : HeightBandJoined X (a - e) (b + e) x (ψ y) := by
    rcases hxy with hxy | hxy
    · have hr := h.roundtrip_X x
      rw [← hxy] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hyy'.source_mem.1])
        (by linarith [hyy'.source_mem.2])
    · rw [hxy]
      exact JoinedIn.refl hmap.source_mem
  have hright : HeightBandJoined X (a - e) (b + e) (ψ y') x' := by
    rcases hx'y' with hx'y' | hx'y'
    · have hr := (h.roundtrip_X x').symm
      rw [← hx'y'] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hyy'.target_mem.1])
        (by linarith [hyy'.target_mem.2])
    · rw [hx'y']
      exact JoinedIn.refl hmap.target_mem
  exact hleft.trans (hmap.trans hright)

def ContinuousFunctionalGHApproximation.toBandCertificate
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    FunctionalGHBandCertificate X Y e where
  error_nonneg := h.error_nonneg
  toFun := h.toFun
  invFun := h.invFun
  height_to := h.height_to
  height_inv := h.height_inv
  band_to := h.toMapBandCompatibility.band_to_full
  band_inv := h.toMapBandCompatibility.band_inv_full

/-- Expanding every scalar band by `e` increases intrinsic scalar-range
distance by at most `2e`. -/
theorem heightRangeDist_le_add_of_band_relation
    {X Y : FilteredReebGraph} {e : ℝ} (he : 0 ≤ e)
    {x x' : X.Carrier} {y y' : Y.Carrier}
    (hband : ∀ {a b : ℝ}, a ≤ b →
      HeightBandJoined X a b x x' →
      HeightBandJoined Y (a - e) (b + e) y y') :
    heightRangeDist Y y y' ≤
      heightRangeDist X x x' + ENNReal.ofReal (2 * e) := by
  unfold heightRangeDist
  rw [ENNReal.sInf_add]
  refine le_iInf fun w => le_iInf fun hw => ?_
  rcases hw with ⟨a, b, hab, hjoined, rfl⟩
  apply sInf_le
  refine ⟨a - e, b + e, by linarith, hband hab hjoined, ?_⟩
  rw [show (b + e) - (a - e) = (b - a) + 2 * e by ring]
  exact (ENNReal.ofReal_add (sub_nonneg.mpr hab)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he)).symm

/-- A band certificate yields the standard functional-GH certificate with the
same reported cost; the conventional half-distortion absorbs the two-sided
band expansion. -/
noncomputable def FunctionalGHBandCertificate.toFunctionalGH
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : FunctionalGHBandCertificate X Y e) :
    FunctionalGHCertificate X Y (ENNReal.ofReal e) where
  toFun := h.toFun
  invFun := h.invFun
  height_to x := ENNReal.ofReal_le_ofReal (h.height_to x)
  height_inv y := ENNReal.ofReal_le_ofReal (h.height_inv y)
  range_distortion := by
    intro x x' y y' hxy hx'y'
    have hforward : heightRangeDist Y y y' ≤
        heightRangeDist X x x' + ENNReal.ofReal (2 * e) := by
      exact heightRangeDist_le_add_of_band_relation h.error_nonneg
        (fun hab hjoined => h.band_to hxy hx'y' hab hjoined)
    have hbackward : heightRangeDist X x x' ≤
        heightRangeDist Y y y' + ENNReal.ofReal (2 * e) := by
      exact heightRangeDist_le_add_of_band_relation h.error_nonneg
        (fun hab hjoined => h.band_inv hxy hx'y' hab hjoined)
    have htwo : ENNReal.ofReal (2 * e) = 2 * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← htwo]
    apply sup_le
    · exact tsub_le_iff_right.mpr (by simpa [add_comm] using hbackward)
    · exact tsub_le_iff_right.mpr (by simpa [add_comm] using hforward)

theorem functionalGHDistance_le_of_band_certificate
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : FunctionalGHBandCertificate X Y e) :
    functionalGHDistance X Y ≤ ENNReal.ofReal e :=
  functionalGHDistance_le_of_certificate h.toFunctionalGH

theorem functionalGHDistance_le_of_continuous_approximation
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    functionalGHDistance X Y ≤ ENNReal.ofReal e :=
  functionalGHDistance_le_of_band_certificate h.toBandCertificate

end ReebGraph
