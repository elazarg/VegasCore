/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPayments
import Vegas.Game.ProgramPaymentLaws
import Vegas.Game.ProgramPaymentAsyncNash

/-! # Axiom guards for monetary laws and full-deviation payment equilibria -/

/-- info: 'GameTheory.Enforcement.TerminalAudit.jointSettlement_add_valuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.jointSettlement_add_valuation

/-- info: 'GameTheory.Enforcement.TerminalAudit.jointSettlement_sub_valuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.jointSettlement_sub_valuation

/-- info: 'Vegas.SourceProgram.Setup.scheduled_setup_payment_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.scheduled_setup_payment_law

/-- info: 'Vegas.SourceProgram.Setup.scheduled_setup_payment_utility_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.scheduled_setup_payment_utility_law

/-- info: 'Vegas.SourceProgram.Setup.eventGame_payment_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.eventGame_payment_approximate_nash_iff

/-- info: 'Vegas.SourceProgram.Setup.parameterEventGame_payment_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.parameterEventGame_payment_approximate_nash_iff

/-- info: 'Vegas.Examples.ProgramPayments.bonus_true_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.bonus_true_isNash

/-- info: 'Vegas.Examples.ProgramPayments.zero_false_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.zero_false_isNash

/-- info: 'Vegas.Examples.ProgramPayments.compiled_isNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_isNash_iff

/-- info: 'Vegas.Examples.ProgramPayments.compiled_bonus_true_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_bonus_true_isNash

/-- info: 'Vegas.Examples.ProgramPayments.compiled_zero_false_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_zero_false_isNash

/-- info: 'Vegas.AsyncServiceSpec.paymentExpectedUtility_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.paymentExpectedUtility_eq

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_isεNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_isεNash_iff

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law
