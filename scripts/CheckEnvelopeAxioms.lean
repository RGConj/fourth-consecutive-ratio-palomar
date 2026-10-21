module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
import RequestProject.SharpLevelSobolev

/-! Closed-axiom audit of the sharp level-volume gradient bound and its ingredients. -/

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

assert_standard_axioms FourthRatio.upperBallEnvelope_lipschitz
assert_standard_axioms FourthRatio.superlevel_add_ball_subset_upperBallEnvelope
assert_standard_axioms FourthRatio.tendsto_upperBallEnvelope_difference_quotient
assert_standard_axioms FourthRatio.upperBallEnvelope_hasCompactSupport
assert_standard_axioms FourthRatio.upperBallEnvelope_difference_quotient_norm_le
assert_standard_axioms FourthRatio.tendsto_integral_upperBallEnvelope_difference_quotient
assert_standard_axioms FourthRatio.upperBallEnvelope_level_isoperimetric
assert_standard_axioms FourthRatio.superlevel_difference_lintegral
assert_standard_axioms FourthRatio.superlevel_difference_div_lintegral
assert_standard_axioms FourthRatio.sharp_level_volume_gradient_bound

end
