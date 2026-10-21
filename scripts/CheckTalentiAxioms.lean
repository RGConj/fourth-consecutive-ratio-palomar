module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
import RequestProject.TalentiFiniteIncrement
import RequestProject.TalentiLocalLipschitz
import RequestProject.InitialMass
import RequestProject.TalentiDerivative
import RequestProject.ProfileEndpoint
import RequestProject.QuantileSquareAE

/-! Actual-object slab and finite-increment audit; full Chiti remains separate. -/

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

assert_standard_axioms FourthRatio.clipPair_norm_integral
assert_standard_axioms FourthRatio.eigen_slab_energy_identity
assert_standard_axioms FourthRatio.eigen_slab_energy_le
assert_standard_axioms FourthRatio.level_slab_gradient_lower_bound
assert_standard_axioms FourthRatio.quantile_slab_gradient_bound
assert_standard_axioms FourthRatio.decreasingQuantile_congr_ae
assert_standard_axioms FourthRatio.decreasingProfile_congr_ae
assert_standard_axioms FourthRatio.decreasingProfile_integrableOn_ae
assert_standard_axioms FourthRatio.setIntegral_le_profile_initial_ae
assert_standard_axioms FourthRatio.quantile_tail_mass_le_ae
assert_standard_axioms FourthRatio.talenti_finite_increment

assert_standard_axioms FourthRatio.eigen_profile_lipschitzOn_from
assert_standard_axioms FourthRatio.eigen_profile_locally_absolutelyContinuous
assert_standard_axioms FourthRatio.initialMass_continuousOn
assert_standard_axioms FourthRatio.initialMass_hasDerivAt

assert_standard_axioms FourthRatio.talenti_derivative_bound
assert_standard_axioms FourthRatio.talenti_derivative_bound_ae

assert_standard_axioms FourthRatio.tendsto_initialMass_zero
assert_standard_axioms FourthRatio.mul_le_initialMass_of_antitone
assert_standard_axioms FourthRatio.tendsto_mul_density_zero
assert_standard_axioms FourthRatio.decreasingProfile_mul_tendsto_zero
assert_standard_axioms FourthRatio.tendsto_wronskian_zero
assert_standard_axioms FourthRatio.decreasingProfile_sq_lintegral_eq_ae
assert_standard_axioms FourthRatio.setLIntegral_sq_le_profile_initial_ae

end
