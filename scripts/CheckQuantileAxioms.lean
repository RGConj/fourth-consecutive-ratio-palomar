module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
import RequestProject.QuantileSlabVolume
import RequestProject.QuantileTailMass
import RequestProject.QuantileSquareMass

/-! Audit of actual quantile and mass results; not a Chiti certificate. -/

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

assert_standard_axioms FourthRatio.decreasingProfile_strict_tail_le
assert_standard_axioms FourthRatio.decreasingProfile_closed_tail_ge
assert_standard_axioms FourthRatio.decreasingProfile_sq_lintegral_eq
assert_standard_axioms FourthRatio.quantile_slab_volume_le
assert_standard_axioms FourthRatio.decreasingProfile_integrableOn
assert_standard_axioms FourthRatio.rearrangedDensity_integrable
assert_standard_axioms FourthRatio.setLIntegral_le_profile_initial
assert_standard_axioms FourthRatio.setIntegral_le_profile_initial
assert_standard_axioms FourthRatio.quantile_tail_mass_le

end
