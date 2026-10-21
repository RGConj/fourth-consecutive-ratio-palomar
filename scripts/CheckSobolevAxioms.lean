module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
import RequestProject.SharpLevelSobolevH
import RequestProject.SobolevLevelSets
import RequestProject.SobolevClip
import RequestProject.L2FiniteIntegrable
import RequestProject.SlabCauchySchwarz

/-! Completed Sobolev foundations only; does not certify ChitiMass. -/

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

assert_standard_axioms FourthRatio.superlevel_measure_le_liminf
assert_standard_axioms FourthRatio.level_volume_lintegral_le_liminf
assert_standard_axioms FourthRatio.continuous_normL2
assert_standard_axioms FourthRatio.continuous_setIntegral_norm_L2
assert_standard_axioms FourthRatio.tendsto_integral_norm_L2_of_support
assert_standard_axioms FourthRatio.sharp_level_volume_gradient_bound_signed
assert_standard_axioms FourthRatio.sharp_level_volume_gradient_bound_H
assert_standard_axioms FourthRatio.chainPair_mem_testGraph
assert_standard_axioms FourthRatio.exists_subseq_chainPair_tendsto
assert_standard_axioms FourthRatio.chainPair_mem_H
assert_standard_axioms FourthRatio.grad_eq_zero_on_level

assert_standard_axioms FourthRatio.upperPartPair_mem_H
assert_standard_axioms FourthRatio.tendsto_shiftedGChain_upperPart
assert_standard_axioms FourthRatio.clipPair_mem_H
assert_standard_axioms FourthRatio.clipPair_snd_ae
assert_standard_axioms FourthRatio.integrable_indicator_norm_L2
assert_standard_axioms FourthRatio.integrable_L2_of_support
assert_standard_axioms FourthRatio.integrable_components_of_mem_H
assert_standard_axioms FourthRatio.setIntegral_norm_sq_le_measure_mul

end
