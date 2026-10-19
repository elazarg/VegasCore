/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalQuery
import Vegas.Game.PhaseSourcePolicy
import Vegas.Game.PhaseRecoveryDomainValue
import Vegas.Game.ProposalRecoveryPrescription
import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhaseProposalResponseAliases
import Vegas.Pending.PhaseProposalInputSummary

/-! # Actual counted reference responses at enriched source queries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Independent native perturbations. The accepted-failed-preparation rate is
separate from ordinary source values, waiting, fresh-slot and syntax noise. -/
structure PhaseProposalRates where
  badPreparation : Set.Icc (0 : ℝ) 1
  waiting : Set.Icc (0 : ℝ) 1
  slots : Set.Icc (0 : ℝ) 1
  aliases : Set.Icc (0 : ℝ) 1

open Classical in
private def completeClassSupport {Class : Type*} [Finite Class] (law : PMF Class) : PMF Class := by
  let := Fintype.ofFinite Class
  let : Nonempty Class := ⟨law.support_nonempty.choose⟩
  exact if FullSupport law then law else PMF.uniformOfFintype Class

private theorem completeClassSupport_full {Class : Type*} [Finite Class] (law : PMF Class) :
    FullSupport (completeClassSupport law) := by
  classical
  let := Fintype.ofFinite Class
  let : Nonempty Class := ⟨law.support_nonempty.choose⟩
  unfold completeClassSupport
  dsimp only
  split
  · assumption
  · exact fun chosen => PMF.mem_support_uniformOfFintype chosen

private theorem completeClassSupport_eq {Class : Type*} [Finite Class] (law : PMF Class)
    (full : FullSupport law) : completeClassSupport law = law := by
  classical
  exact ite_eq_left full

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Read the SAME ordinary domain table as the enriched source perturbation.
The existing addressed source decoder is used before the independent native
accepted-failure atom. No physical WAIT is identified with a source omission. -/
def phaseProposalBindingResults
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PublicationResult (L.Val payload)) :=
  match phaseProposalQuery? setup mode runtime leaks plan who event past view with
  | none => PMF.pure .failure
  | some key => mix rates.badPreparation.val rates.badPreparation.property.1
      rates.badPreparation.property.2 (PMF.pure .failure)
      ((values who key).map fun value =>
        PublicationResult.success
          (phaseRecoveryDomainValue setup mode event who payload binding value.val.val))

/-- The complete public request dispatches actual covered encoders. Bindings
choose a source value only on SEND; all earlier WAITs retain future choices.
Openings use the actual accepted handle and truthful certificate. -/
def phaseProposalBasePolicy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) : (app).Policy :=
  phasePolicyDispatch setup mode runtime leaks
    (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
        (fun _ _ => mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
          (PMF.pure false) (PMF.pure true)))
    (fun owner event payload binding past view =>
      mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩)
        (PhaseCount.bindingResultEncoder runtime leaks bounds owner event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values rates owner event
            payload binding) rates.slots.val rates.slots.property.1 rates.slots.property.2
          past view))
    who

/-- The source lookup never overrides actual runtime availability. -/
theorem phaseProposalBasePolicy_covered
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who
        past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  unfold phaseProposalBasePolicy at supported
  refine phasePolicyDispatch_covered setup mode runtime leaks bounds _ ?_ _ ?_ who past view
    response supported
  · intro owner event payload binding before observed action offered
    exact PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event payload binding
      _ before observed action offered
  · intro owner event payload binding before observed action offered
    rcases support_mix_subset _ _ _ _ _ offered with silent | sending
    · cases (PMF.mem_support_pure_iff _ _).mp silent
      exact PhaseCount.silence_onePacket runtime leaks bounds owner before observed
    · exact PhaseCount.bindingResultEncoder_covered runtime leaks bounds owner event payload _
        rates.slots.val rates.slots.property.1 rates.slots.property.2 before observed action sending

/-- The actual dispatcher and every source/slot/opening component ignore
old inert private syntax once emitted traffic and the current view agree. -/
theorem phaseProposalBasePolicy_congr_input
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second) :
    phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who first view =
      phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who second
        view := by
  unfold phaseProposalBasePolicy
  apply phasePolicyDispatch_congr_input
  · intro owner event payload binding
    exact PhaseCount.phaseOpeningPolicy_congr_input runtime leaks bounds owner event payload
      binding _ first second view outputs serial rfl
  · intro owner event payload binding
    apply congrArg (mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
      (PMF.pure (⟨none⟩ : (app).Action)))
    apply PhaseCount.bindingResultEncoder_congr_input runtime leaks bounds owner event payload
      _ rates.slots.val rates.slots.property.1 rates.slots.property.2 first second view outputs
        serial
    have queried : phaseProposalQuery? setup mode runtime leaks plan owner event first view =
        phaseProposalQuery? setup mode runtime leaks plan owner event second view := by
      unfold phaseProposalQuery? PhaseProposal.observedSourceArchive
        ReactiveApplication.ResponseMenu.knownPackets
      rw [outputs]
    unfold phaseProposalBindingResults
    rw [queried]

/-- Attach actual menu membership to the covered canonical response law. -/
def phaseProposalBaseResponses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PhaseProposal.Response runtime leaks bounds who past view) :=
  let law := phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who past view
  law.bindOnSupport fun response supported => PMF.pure
      ⟨response, phaseProposalBasePolicy_covered setup mode runtime leaks bounds plan values rates
        who past view response supported⟩

/-- Attaching menu evidence changes neither the response nor its probability. -/
theorem phaseProposalBaseResponses_map_val
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseProposalBaseResponses setup mode runtime leaks bounds plan values rates who past view).map
        Subtype.val =
      phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who past view := by
  simp only [phaseProposalBaseResponses, map_bindOnSupport, PMF.pure_map]
  rw [bindOnSupport_eq_bind_of_eq_on_support _ (g := PMF.pure) (fun _ _ => rfl), PMF.bind_pure]

/-- Canonical choices projected to typed preparations and actually emitted
packets. Private syntax aliases have not yet been sampled. -/
def phaseProposalBaseClasses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PhaseProposal.ResponseClass runtime leaks bounds who past view) :=
  (phaseProposalBaseResponses setup mode runtime leaks bounds plan values rates who past view).map
    (PhaseProposal.projectResponse runtime leaks bounds who past view)

open Classical in
/-- Totalize only finite local inputs whose canonical class support is
incomplete. On genuine histories the shape/query adapters discharge this
finite support check; no extra raw noise changes their bad-preparation rate. -/
def phaseProposalReferenceClasses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PhaseProposal.ResponseClass runtime leaks bounds who past view) :=
  completeClassSupport
    (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view)

/-- All actual local response classes have positive probability. This support
statement uses only the concrete finite menu, not source-history existence. -/
theorem phaseProposalReferenceClasses_fullSupport
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    FullSupport (phaseProposalReferenceClasses setup mode runtime leaks bounds plan values rates who
      past view) :=
  completeClassSupport_full _

/-- The support totalization disappears as soon as actual class coverage is
derived. Later genuine-query consumers prove this premise from counted shapes. -/
theorem phaseProposalReferenceClasses_eq
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view)) :
    phaseProposalReferenceClasses setup mode runtime leaks bounds plan values rates who past view =
      phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view :=
  completeClassSupport_eq _ full

/-- Sample private aliases in their actual local preimages AFTER selecting the
source class and actual packet. The literal raw own action remains in recall. -/
def phaseProposalReferenceResponses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PhaseProposal.Response runtime leaks bounds who past view) :=
  PhaseProposal.splitResponseLaw runtime leaks bounds who past view
    (phaseProposalReferenceClasses setup mode runtime leaks bounds plan values rates who past view)
    rates.aliases.val rates.aliases.property.1 rates.aliases.property.2

/-- This is an actual ordinary runtime policy at every full local input. -/
def phaseProposalReferencePolicy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) : (app).Policy := fun past view =>
  let law := phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates who
    past view
  law.map Subtype.val

/-- The complete response law stays in the original counted menu. -/
theorem phaseProposalReferencePolicy_covered
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who past
        view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  obtain ⟨chosen, _positive, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact chosen.property

/-- Positive alias noise reaches EVERY actual counted response without
adding an independent uniform preparation tier on genuine inputs. -/
theorem phaseProposalReferencePolicy_fullSupport
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (aliases : 0 < rates.aliases.val) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (permitted : response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view) :
    response ∈
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who past
        view).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨⟨response, permitted⟩, ?_, rfl⟩
  exact PhaseProposal.splitResponseLaw_fullSupport runtime leaks bounds who past view _
    (phaseProposalReferenceClasses_fullSupport setup mode runtime leaks bounds plan values rates who
      past view) rates.aliases.val rates.aliases.property.1 rates.aliases.property.2 aliases _

/-- Summing all actual private aliases recovers the selected packet/preparation
law exactly. No equality of beliefs is inferred from this local identity. -/
theorem phaseProposalReferenceResponses_project
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates who past
        view).map (PhaseProposal.projectResponse runtime leaks bounds who past view) =
      phaseProposalReferenceClasses setup mode runtime leaks bounds plan values rates who past
        view :=
  PhaseProposal.splitResponseLaw_project runtime leaks bounds who past view _
    rates.aliases.val rates.aliases.property.1 rates.aliases.property.2

/-- The complete raw reference lottery, including finite support totalization
and syntax splitting, depends only on the current view and signed traffic
summary. This is equality of actual policies, with literal value tables/rates. -/
theorem phaseProposalReferencePolicy_congr_input
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second) :
    phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who first view =
      phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who second
        view := by
  classical
  have menus := PhaseCount.onePacketActions_congr_input runtime leaks bounds who first second view
    outputs serial
  have packets (material : WitnessedSubmission (serviceGraph setup mode)) :
      PhaseCount.localEnvelope runtime leaks who first view material =
        PhaseCount.localEnvelope runtime leaks who second view material := by
    unfold PhaseCount.localEnvelope ReactiveApplication.ResponseMenu.knownPackets
    rw [outputs, serial]
  have base := phaseProposalBasePolicy_congr_input setup mode runtime leaks bounds plan values
    rates who first second view outputs serial
  let compute (allowed : Finset (app).Action)
      (wire : WitnessedSubmission (serviceGraph setup mode) →
        CommitAttemptPacket (serviceGraph setup mode))
      (law : PMF (app).Action) (covered : ∀ response ∈ law.support, response ∈ allowed) :
      PMF (app).Action :=
    let classify (response : { response : (app).Action // response ∈ allowed }) :=
      (response.val.transmission.bind PhaseProposal.bindingPreparation,
        response.val.transmission.map wire)
    let project := fun response =>
      (⟨classify response, response, rfl⟩ : Set.range classify)
    let canonical := fun chosen : Set.range classify => Classical.choose chosen.property
    let retract : ∀ chosen, project (canonical chosen) = chosen :=
      fun chosen => Subtype.ext (Classical.choose_spec chosen.property)
    let selected := law.bindOnSupport fun response supported =>
      PMF.pure (⟨response, covered response supported⟩ :
        { response : (app).Action // response ∈ allowed })
    ((completeClassSupport (selected.map project)).bind
      (PMF.splitKernel project canonical retract rates.aliases.val
        rates.aliases.property.1 rates.aliases.property.2)).map Subtype.val
  change compute (PhaseCount.onePacketActions runtime leaks bounds who first view)
      (fun material => (PhaseCount.localEnvelope runtime leaks who first view material).payload)
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who first view)
      (phaseProposalBasePolicy_covered setup mode runtime leaks bounds plan values rates who
        first view) =
    compute (PhaseCount.onePacketActions runtime leaks bounds who second view)
      (fun material => (PhaseCount.localEnvelope runtime leaks who second view material).payload)
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who second view)
      (phaseProposalBasePolicy_covered setup mode runtime leaks bounds plan values rates who
        second view)
  congr 1
  funext material
  exact congrArg (fun packet => packet.payload) (packets material)

end Vegas
