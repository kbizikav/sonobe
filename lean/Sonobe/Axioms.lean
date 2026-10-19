import Sonobe.FinalSoundness
import Sonobe.FinalCompleteness
import Sonobe.FinalDecider
import Sonobe.Deployment
import Sonobe.Hypotheses

/-!
The headline theorems depend only on Lean's axioms `propext`, `Classical.choice` and `Quot.sound`:
no `sorry`, no added axiom, no `native_decide`. `lake build` fails if that changes.
-/

/-- info: 'Sonobe.Gadget.ivc_sound_of_circuits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Gadget.ivc_sound_of_circuits

/-- info: 'Sonobe.Gadget.ivc_complete_of_circuits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Gadget.ivc_complete_of_circuits

/-- info: 'Sonobe.Gadget.evm_decider_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Gadget.evm_decider_sound

/-- info: 'Sonobe.Deployment.evm_decider_sound_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Deployment.evm_decider_sound_deployed

/-- info: 'Sonobe.Deployment.ivc_complete_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Deployment.ivc_complete_deployed

/-- info: 'Sonobe.Poseidon.permRel_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Poseidon.permRel_iff

/-- info: 'Sonobe.SpongeCfg.absorb_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.SpongeCfg.absorb_eq_add

/-- info: 'Sonobe.SpongeCfg.squeeze_eq_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.SpongeCfg.squeeze_eq_get

/-- info: 'Sonobe.NonDegenerate.cheat_not_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.NonDegenerate.cheat_not_binds

/-- info: 'Sonobe.Primes.prime_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Primes.prime_r

/-- info: 'Sonobe.Primes.prime_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sonobe.Primes.prime_q
