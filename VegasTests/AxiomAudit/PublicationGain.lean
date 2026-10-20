/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalPublicationGain

/-! # Publication gain and original endpoint dependencies -/

/-- info:
'Vegas.phaseProposal_publication_gain_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_publication_gain_le

/-- info:
'Vegas.phaseProposal_original_publication_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_original_publication_payoff_law

/-- info:
'Vegas.phaseProposal_checkpoint_debt_finish_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_checkpoint_debt_finish_payoff

/-- info:
'Vegas.phaseProposal_opening_alias_finish_payoff_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_opening_alias_finish_payoff_eq

/-- info:
'Vegas.phaseProposal_opening_alias_normalized_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_opening_alias_normalized_eq

/-- info:
'Vegas.phaseProposalUnflagged_normalized_finish'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_normalized_finish

/-- info:
'Vegas.phaseProposalUnflagged_normalized_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_normalized_continuation

/-- info:
'Vegas.RecoverySourceWitness.completed_normalized_archived_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.completed_normalized_archived_source

/-- info:
'Vegas.phaseProposalUnflagged_paired_publication_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_paired_publication_boundary
