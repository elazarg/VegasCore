/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCurrentBindingGain

/-! # Current binding gain dependencies -/

/-- info:
'Vegas.phaseProposal_current_finish_seed_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_current_finish_seed_marginal

/-- info:
'Vegas.phaseProposal_response_kernel_finish'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_response_kernel_finish

/-- info:
'Vegas.phaseProposal_current_binding_gain_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_current_binding_gain_le

/-- info:
'Vegas.phaseProposal_current_gain_flag_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_current_gain_flag_error
