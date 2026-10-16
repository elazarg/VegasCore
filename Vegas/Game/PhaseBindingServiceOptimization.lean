/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingServicePolicy
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheory.Protocol.FiniteInformation
import GameTheory.Protocol.DecisionPlan

/-! # Finite own-service optimization in actual phased continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "menu" => onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (onePacketMenu runtime leaks bounds) initial horizon scheduler

variable [Finite (ReactiveApplication.ResponseMenu.protocol
  (onePacketMenu runtime leaks bounds) initial horizon scheduler).History]
  (owner : Player) (coordinate : CommitAttemptEvent graph)

/-- Read the service word at a genuine decision site of the original model. -/
def phaseServiceSiteClocks (site : (N).InformationSite owner) : List Nat :=
  match site.1 with
  | none => []
  | some (past, view) => PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view

/-- The actual finite protocol supplies the clock words consulted by every
possible local deviation, rather than only by the proposed service policy. -/
def phaseServiceClockDomain : Finset (List Nat) := by
  classical
  let := Fintype.ofFinite ((N).InformationSite owner)
  exact Finset.univ.image (phaseServiceSiteClocks runtime leaks bounds initial horizon scheduler
    owner coordinate)

/-- A finite table chooses WAIT or a bounded prepared slot at each actual
clock word. Repeated clock values remain distinct entries in the word. -/
abbrev PhaseBindingServiceRule :=
  {clocks : List Nat // clocks ∈ phaseServiceClockDomain runtime leaks bounds initial horizon
    scheduler owner coordinate} → Option (Fin bounds.candidateCount)

open Classical in
def phaseServiceRuleChoice (rule : PhaseBindingServiceRule runtime leaks bounds initial horizon
    scheduler owner coordinate) (clocks : List Nat) : Option (Fin bounds.candidateCount) :=
  if present : clocks ∈ phaseServiceClockDomain runtime leaks bounds initial horizon scheduler
      owner coordinate then rule ⟨clocks, present⟩ else none

def phaseServiceRuleOfChoice (choose : List Nat → Option (Fin bounds.candidateCount)) :
    PhaseBindingServiceRule runtime leaks bounds initial horizon scheduler owner coordinate :=
  fun clocks => choose clocks.1

/-- The globally covered raw service policy is restricted by the existing
counted-menu embedding, with its source result kept separate from timing. -/
def phaseBindingServiceStrategy (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option (Fin bounds.candidateCount)) : (N).BehavioralPolicy owner :=
  (menu).restrictPolicy initial horizon scheduler owner
    (phaseBindingServicePolicy runtime leaks bounds owner coordinate payload result
      (fun clocks => (choose clocks).map Fin.val))

/-- Restricting an arbitrary pure bounded own-service rule to the actual finite
clock domain preserves its complete decision behavior, including off-path sites. -/
theorem phaseBindingServiceStrategy_finite_agreement
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option (Fin bounds.candidateCount)) :
    (phaseBindingServiceStrategy runtime leaks bounds initial horizon scheduler owner coordinate
      payload result (phaseServiceRuleChoice runtime leaks bounds initial horizon scheduler owner
        coordinate (phaseServiceRuleOfChoice runtime leaks bounds initial horizon scheduler owner
          coordinate choose))).AgreesAtDecisions
      (phaseBindingServiceStrategy runtime leaks bounds initial horizon scheduler owner coordinate
        payload result choose) := by
  classical
  let := Fintype.ofFinite ((N).InformationSite owner)
  funext site
  have member : phaseServiceSiteClocks runtime leaks bounds initial horizon scheduler owner
      coordinate site ∈ phaseServiceClockDomain runtime leaks bounds initial horizon scheduler
        owner coordinate := by
    exact Finset.mem_image.mpr ⟨site, Finset.mem_univ _, rfl⟩
  change (phaseBindingServiceStrategy runtime leaks bounds initial horizon scheduler owner
    coordinate payload result (phaseServiceRuleChoice runtime leaks bounds initial horizon scheduler
      owner coordinate (phaseServiceRuleOfChoice runtime leaks bounds initial horizon scheduler
        owner coordinate choose))) site.1 =
      phaseBindingServiceStrategy runtime leaks bounds initial horizon scheduler owner coordinate
        payload result choose site.1
  cases info : site.1 with
  | none => simp only [phaseBindingServiceStrategy,
      ReactiveApplication.ResponseMenu.restrictPolicy]
  | some data =>
    rcases data with ⟨past, view⟩
    have current : PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view ∈
        phaseServiceClockDomain runtime leaks bounds initial horizon scheduler owner
          coordinate := by
      simpa only [phaseServiceSiteClocks, info] using member
    apply pmf_map_injective (f := Subtype.val)
    · exact fun _ _ same => Subtype.ext same
    · change ((menu).restrictPolicy initial horizon scheduler owner _ (some (past, view))).map
        Subtype.val = ((menu).restrictPolicy initial horizon scheduler owner _
          (some (past, view))).map Subtype.val
      rw [(menu).restrictPolicy_map_val initial horizon scheduler owner _ past view
          (fun response supported => phaseBindingServicePolicy_covered runtime leaks bounds
            (supported := supported)),
        (menu).restrictPolicy_map_val initial horizon scheduler owner _ past view
          (fun response supported => phaseBindingServicePolicy_covered runtime leaks bounds
            (supported := supported))]
      apply congrArg (fun law : PMF (phaseApplication runtime leaks).Action => law.map some)
      apply phaseBindingServicePolicy_eq_of_clocks runtime leaks bounds
      simp only [phaseServiceRuleChoice, dite_eq_left current, phaseServiceRuleOfChoice]

/-- The actual assessment belief and original stopped runner evaluate the whole
service continuation. No source-value identity or success-factor premise is used. -/
def phaseBindingServiceValue (assessment : (N).BehavioralAssessment)
    (site : (N).InformationSite owner) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option (Fin bounds.candidateCount))
    (stopped : (E).History → Prop) (payoff : (E).History → ℝ) : ℝ :=
  expect ((assessment.belief owner site).bind fun history =>
    (N).runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories
      (Profile.update (sig := (N).behavioralSignature) assessment.strategy owner
        (phaseBindingServiceStrategy runtime leaks bounds initial horizon scheduler owner
          coordinate payload result choose)) stopped history.1) payoff

/-- The finite table retains the SAME native stopped continuation value for
every pure bounded service rule, not a freshly initialized or independent run. -/
theorem phaseBindingServiceValue_finite (assessment : (N).BehavioralAssessment)
    (site : (N).InformationSite owner) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option (Fin bounds.candidateCount))
    (stopped : (E).History → Prop) (payoff : (E).History → ℝ) :
    phaseBindingServiceValue runtime leaks bounds initial horizon scheduler owner coordinate
        assessment site payload result
        (phaseServiceRuleChoice runtime leaks bounds initial horizon scheduler owner coordinate
          (phaseServiceRuleOfChoice runtime leaks bounds initial horizon scheduler owner coordinate
            choose)) stopped payoff =
      phaseBindingServiceValue runtime leaks bounds initial horizon scheduler owner coordinate
        assessment site payload result choose stopped payoff := by
  apply congrArg (fun law => expect law payoff)
  apply bind_congr_on_support
  intro history _supported
  apply (N).runBehavioralUntil_congr
  intro later _reached nonterminal player
  by_cases same : player = owner
  · subst player
    simp only [Profile.update_same]
    exact (phaseBindingServiceStrategy_finite_agreement runtime leaks bounds initial horizon
      scheduler owner coordinate payload result choose).at_history later nonterminal
  · simp only [Profile.update_of_ne _ _ same]

/-- An actual native stopped objective has an optimal pure bounded own-service
rule. This supplies existence inside the concrete policy class; independence
from private types and comparison with richer policies remain separate. -/
theorem exists_optimal_phase_binding_service (assessment : (N).BehavioralAssessment)
    (site : (N).InformationSite owner) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (stopped : (E).History → Prop) (payoff : (E).History → ℝ) :
    ∃ choose : List Nat → Option (Fin bounds.candidateCount),
      ∀ alternative : List Nat → Option (Fin bounds.candidateCount),
        phaseBindingServiceValue runtime leaks bounds initial horizon scheduler owner coordinate
          assessment site payload result alternative stopped payoff ≤
        phaseBindingServiceValue runtime leaks bounds initial horizon scheduler owner coordinate
          assessment site payload result choose stopped payoff := by
  classical
  let score := fun rule : PhaseBindingServiceRule runtime leaks bounds initial horizon scheduler
      owner coordinate => phaseBindingServiceValue runtime leaks bounds initial horizon scheduler
        owner coordinate assessment site payload result (phaseServiceRuleChoice runtime leaks
          bounds initial horizon scheduler owner coordinate rule) stopped payoff
  obtain ⟨best, maximal⟩ := Finite.exists_max score
  refine ⟨phaseServiceRuleChoice runtime leaks bounds initial horizon scheduler owner coordinate
    best, fun alternative => ?_⟩
  rw [← phaseBindingServiceValue_finite runtime leaks bounds initial horizon scheduler owner
    coordinate assessment site payload result alternative stopped payoff]
  exact maximal (phaseServiceRuleOfChoice runtime leaks bounds initial horizon scheduler owner
    coordinate alternative)

end Vegas.EventGraphRuntime.PhaseCount
