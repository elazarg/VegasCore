/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalNativeFutureFlags
import Vegas.Game.PhaseProposalResetPayoff
import Vegas.Game.ReservedEpochBindingReset

/-! # Native continuation errors and reset payoff dependency guards -/

/-- info:
'Vegas.phaseProposal_current_gain_flag_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_current_gain_flag_error

/-- info:
'Vegas.phaseProposal_future_flags_withinTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_future_flags_withinTV

/-- info:
'Vegas.phaseProposal_finish_future_flags_withinTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_finish_future_flags_withinTV

/-- info:
'Vegas.phaseProposalUnflagged_available_send_reset_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_available_send_reset_boundary

/-- info:
'Vegas.phaseProposalUnflagged_available_send_stopped_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_available_send_stopped_word

/-- info:
'Vegas.phaseProposal_fresh_payoff_law_eq_of_erased_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_fresh_payoff_law_eq_of_erased_source
