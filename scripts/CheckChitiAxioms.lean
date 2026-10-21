module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
import RequestProject.ChitiGeneral

/-! Strict audit of the complete actual Chiti mass-concentration proof chain. -/

meta section

open Lean Elab Command

elab "assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let rejected := axioms.filter fun a => !allowed.contains a
  if !rejected.isEmpty then
    throwError "{name}: disallowed axioms {rejected}; all axioms: {axioms}"
  logInfo m!"{name}: PASS; axioms: {axioms}"

assert_standard_axioms FourthRatio.cumulative_sq_homogeneous_of_ratio_monotone
assert_standard_axioms FourthRatio.integrable_sq_ballVolumeCut
assert_standard_axioms FourthRatio.integral_sq_ballVolumeCut_pos
assert_standard_axioms FourthRatio.decreasingProfile_sq_integrable_ae
assert_standard_axioms FourthRatio.integral_sq_decreasingProfile_eq_ae
assert_standard_axioms FourthRatio.setIntegral_sq_le_profile_initial_ae
assert_standard_axioms FourthRatio.eigen_profile_cumulative_homogeneous
assert_standard_axioms FourthRatio.ballVolumeSquareRadius_radialVolume
assert_standard_axioms FourthRatio.radialVolume_preimage_Iio
assert_standard_axioms FourthRatio.volume_ball_eq_ofReal_radialVolume
assert_standard_axioms FourthRatio.integral_radialVolume_comp
assert_standard_axioms FourthRatio.besselEntire_integral_radialVolume
assert_standard_axioms FourthRatio.besselEntire_ball_integral_volume
assert_standard_axioms FourthRatio.besselEntire_ball_inter_integral_volume
assert_standard_axioms FourthRatio.eigenfunction_ball_mass_nonnegative
assert_standard_axioms FourthRatio.first_eigenfunction_ball_mass

end
