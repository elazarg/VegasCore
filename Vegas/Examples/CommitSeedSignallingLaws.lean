/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingAudit
import Interaction.ReactiveEquilibriumExistence

/-! # Realized settlement and honest zero-payoff laws

Preserving the actual public-result and realized-payoff joint law forces
every expected native payoff to be zero. The comparison retains the audit's
settlement kernel rather than replacing it by expected charges in the law.
-/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

def sourceJointLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    PMF (Option (PublicOutcome program) × (Player → ℝ)) :=
  (setup.intendedModel.runBehavioralTerminalFrom
    setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory).map
      fun final => ((setup.protocolReadout final.state).map (publicOutcome program),
        fun who => honestPayoff who final)

def nativeHistoryLaw (profile : ∀ who, rawModel.BehavioralPolicy who) :
    PMF rawProtocol.History :=
  rawModel.runBehavioralTerminalFrom canonicalCertificate profile rawProtocol.initHistory

def realizedSettlement (state : app.ProtocolState) : PMF (Player → ℝ) :=
  TerminalAudit.settlement basePayoff app.stateTraffic audit deposit state

def nativeJointLaw (profile : ∀ who, rawModel.BehavioralPolicy who) :
    PMF (Option (PublicOutcome program) × (Player → ℝ)) :=
  (nativeHistoryLaw profile).bind fun final =>
    (realizedSettlement final.state).map fun payoffs =>
      ((phaseSourceReadout setup .concurrentReveals runtime leaks final.state).map
        (publicOutcome program), payoffs)

theorem sourceJointLaw_payoff_projection
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (sourceJointLaw profile).map Prod.snd = PMF.pure (fun _ : Player => (0 : ℝ)) := by
  simp only [sourceJointLaw, PMF.map_comp, Function.comp_def, honestPayoff_eq_zero,
    ]
  exact PMF.map_const _ _

theorem nativeJointLaw_payoff_projection (profile : ∀ who, rawModel.BehavioralPolicy who) :
    (nativeJointLaw profile).map Prod.snd =
      (nativeHistoryLaw profile).bind fun final => realizedSettlement final.state := by
  simp only [nativeJointLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support
  intro final _
  exact PMF.map_id _

/-- The finite native game has genuine sequential equilibria, independently
of any preservation or service assertion. -/
theorem exists_native_sequentialEquilibrium :
    ∃ assessment : rawModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (rawMenu.decisionInformationAntichain initial horizon scheduler)
        canonicalCertificate rawPayoff := by
  exact rawMenu.exists_sequentialEquilibrium initial horizon scheduler rawPayoff

theorem settlementPayoff_integrable (law : PMF rawProtocol.History) (who : Player) :
    PayoffIntegrable (law.bind fun final => realizedSettlement final.state)
      (fun payoffs => payoffs who) := by
  have baseIntegrable : PayoffIntegrable law (fun final => basePayoff final.state who) :=
    payoffIntegrable_of_bounded _ _ (C := 3) fun final => by
      have bounds := basePayoff_mem_Icc final.state who
      exact abs_le.mpr ⟨by linarith [bounds.1], bounds.2⟩
  apply payoffIntegrable_bind_of_abs_le law (fun final => realizedSettlement final.state)
    (fun payoffs => payoffs who) (fun final => basePayoff final.state who) |deposit who|
    baseIntegrable
  intro final _ payoffs supported
  obtain ⟨verdict, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  split <;> simp

/-- The terminal audit's realized mean is the actual native utility. -/
theorem expectedPayoff_eq_settlementMean (law : PMF rawProtocol.History) (who : Player) :
    expect law (rawPayoff who) =
      expect (law.bind fun final => realizedSettlement final.state)
        (fun payoffs => payoffs who) := by
  rw [expect_bind_tower _ _ _ (settlementPayoff_integrable law who)]
  apply congrArg (expect law)
  funext final
  exact (TerminalAudit.settlement_expect basePayoff app.stateTraffic audit deposit
    final.state who).symm

/-- Exact preservation of the realized joint law forces the native mean to zero. -/
theorem preservation_implies_zero_payoff
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, rawModel.BehavioralPolicy who)
    (preserves : sourceJointLaw source = nativeJointLaw target) (who : Player) :
    expect (nativeHistoryLaw target) (rawPayoff who) = 0 := by
  have projection := congrArg (PMF.map Prod.snd) preserves
  rw [sourceJointLaw_payoff_projection, nativeJointLaw_payoff_projection] at projection
  rw [expectedPayoff_eq_settlementMean, ← projection]
  exact expect_pure _ _

end Vegas.Examples.CommitSeedSignalling
