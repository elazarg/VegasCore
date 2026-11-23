module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveAsyncContract
public import Vegas.Source.ConditionedInitialLaw

@[expose] public section

/-! # Ledger service under conditioning of the source prior -/

noncomputable section

namespace Interaction.ReactiveApplication

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
    {restricted initial : PMF app.State} {horizon : Nat} {scheduler : app.Scheduler}

/-- Restricting the initial support retains every legal execution of the restricted game
as an execution of the original game, with identical controls and actions. -/
def traceOfInitialSupportSubset (included : restricted.support ⊆ initial.support) :
    ∀ {state}, (app.protocol restricted horizon scheduler).Trace state →
      (app.protocol initial horizon scheduler).Trace state
  | _, .start => .start
  | _, @GameTheory.Protocol.ExecutionProtocol.Trace.extend _ _ state _ prior joint legal realized =>
      .extend (traceOfInitialSupportSubset included prior) joint legal (by
        cases state with
        | none =>
          obtain ⟨start, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨start, included member, rfl⟩
        | some control => exact realized)

end Interaction.ReactiveApplication

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support)
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {scheduler : (application setup timeouts leaks).Scheduler}

include supported

/-- Conditioning the source prior introduces no new initialized ledger state. -/
theorem conditionInitial_ledgerSupport :
    (Vegas.initialLaw (setup.conditionInitial signal value)).support ⊆
      (Vegas.initialLaw setup).support := by
  intro state member
  obtain ⟨draw, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨draw, setup.conditionInitial_support_subset signal value supported present, rfl⟩

/-- Finite nature descends to a supported component for the same scheduler and leak law. -/
theorem conditionInitial_finiteNature
    (finite : (application setup timeouts leaks).FiniteNature (Vegas.initialLaw setup) scheduler) :
    (application setup timeouts leaks).FiniteNature
      (Vegas.initialLaw (setup.conditionInitial signal value)) scheduler where
  toFiniteEnvironment := finite.toFiniteEnvironment
  initial_finite := finite.initial_finite.subset
    (setup.conditionInitial_ledgerSupport signal value supported)
  scheduler_finite := finite.scheduler_finite

/-- Every supported component inherits the actual builder's opportunity, inclusion and
completion guarantees on all its legal raw histories, with the original deadlines. -/
theorem conditionInitial_asyncContract {horizon : Nat}
    {delay bound : setup.informationGraph.EventId → Nat}
    (service : AsyncContract timeouts leaks (Vegas.initialLaw setup) horizon scheduler
      delay bound) :
    AsyncContract timeouts leaks (Vegas.initialLaw (setup.conditionInitial signal value))
      horizon scheduler delay bound where
  opportunity control trace := service.opportunity control
    (ReactiveApplication.traceOfInitialSupportSubset
      (setup.conditionInitial_ledgerSupport signal value supported) trace)
  inclusion control trace := service.inclusion control
    (ReactiveApplication.traceOfInitialSupportSubset
      (setup.conditionInitial_ledgerSupport signal value supported) trace)
  completes control trace := service.completes control
    (ReactiveApplication.traceOfInitialSupportSubset
      (setup.conditionInitial_ledgerSupport signal value supported) trace)

omit supported in
/-- Mixing actual ledger executions from the conditional initializers gives the entire
original execution law under any fixed physical policies, including every raw deviation. -/
theorem roundsFrom_conditionInitial_reconstruct
    (players : Player → (application setup timeouts leaks).Policy) (count : Nat) :
    (setup.initialLaw.map signal).bind (fun key =>
      (application setup timeouts leaks).roundsFrom
        (Vegas.initialLaw (setup.conditionInitial signal key)) scheduler players count) =
      (application setup timeouts leaks).roundsFrom (Vegas.initialLaw setup)
        scheduler players count := by
  let pack := fun draw : State L setup.context =>
    EventGraphRuntime.State.initial (graph := setup.informationGraph)
    (setup.eventInputs draw)
  let play := fun state => (application setup timeouts leaks).runRounds scheduler players count
    (ReactiveApplication.Execution.initial (application setup timeouts leaks) state)
  change (setup.initialLaw.map signal).bind
    (fun key => ((fiberPosterior setup.initialLaw signal key).map pack).bind play) =
    (setup.initialLaw.map pack).bind play
  simp_rw [PMF.bind_map (f := pack)]
  rw [← PMF.bind_bind, fiberPosterior_reconstruct]

end Vegas.SourceProgram.Setup
