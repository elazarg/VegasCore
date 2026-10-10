/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.BindingRepairTrace

/-! # Continuation kernels against copied value-interface opponents -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- On a represented actual prefix, copied foreign laws equal the global
value-menu embedding. Equality is derived from actual retained sites. -/
theorem copied_foreign_law (admission : CommitmentInterface setup.program)
    (who observer : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (original : (setup.executionProtocol admission).History)
    (repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (related : setup.FocalRepair who original.state repaired.state)
    (observed : (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
      observer repaired.trace = (setup.informationModel admission).infoOf observer original.trace)
    (running : ¬ (setup.executionProtocol admission).terminal original.state)
    (foreign : observer ≠ who) :
    target observer ((setup.informationModel admission).infoOf observer original.trace) =
      (source observer ((setup.informationModel admission).infoOf observer original.trace)).map
        ((setup.valuesRestriction admission).choice observer
          ((setup.informationModel admission).infoOf observer original.trace)) := by
  by_cases active : (setup.executionProtocol admission).active original.state observer
  · have running' : ¬ (setup.executionProtocol
        (CommitmentInterface.values setup.program)).terminal repaired.state :=
      fun stopped => running ((FocalRepair.terminal_iff setup related admission).mp stopped)
    have active' : (setup.executionProtocol (CommitmentInterface.values setup.program)).active
        repaired.state observer := by
      change (setup.protocolObserve observer repaired.state).elim False
        (fun view => ProtocolView.actor observer setup.program view = some observer)
      rw [FocalRepair.foreign_observe setup related foreign]
      exact active
    obtain ⟨site, siteView⟩ := (setup.informationModel
      (CommitmentInterface.values setup.program)).exists_informationSite_of_active
        observer repaired running' active'
    have sameInfo : (setup.informationModel admission).infoOf observer original.trace = site.1 :=
      observed.symm.trans siteView.symm
    rw [sameInfo]
    exact copies observer site
  · exact (setup.informationModel admission).behavioral_eq_of_not_active
      (target observer)
      (fun info => (source observer info).map
        ((setup.valuesRestriction admission).choice observer info)) original.trace active

/-- The actual larger-game continuation against copied opponents has the
kernel of the fixed globally embedded source opponents, even after focal failed
commitments. No continuation optimality or kernel equality is assumed. -/
theorem run_copied_opponents_from_values_history [Fintype Player]
    (admission : CommitmentInterface setup.program) (who : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (start : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (fuel : ℕ) :
    (setup.informationModel admission).runBehavioralFrom
      (Function.update target who deviation) fuel
        ((setup.valuesRestriction admission).history start) =
    (setup.informationModel admission).runBehavioralFrom
      (Function.update (fun player info => (source player info).map
        ((setup.valuesRestriction admission).choice player info)) who deviation)
      fuel ((setup.valuesRestriction admission).history start) := by
  apply (setup.informationModel admission).runBehavioralFrom_congr_on_support
  intro elapsed _ later supported running observer
  by_cases own : observer = who
  · subst observer
    simp only [Function.update_self]
  · simp only [Function.update_of_ne own]
    obtain ⟨repaired, _, related, observed⟩ :=
      setup.deviation_history_values_representation admission who source target copies deviation
        start elapsed later supported
    exact setup.copied_foreign_law admission who observer source target copies later repaired
      related
      (observed observer own) running own

end Vegas.SourceProgram.Setup
