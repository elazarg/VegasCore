/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompatibleImmediateAudit
import Vegas.Game.SourceServiceAuditableCollection
import Vegas.Game.SourceServiceRecordedCollection

/-! # Collection at compatible information in the full runtime

Compatible information supplies the authentic own-call provenance of every
actual hidden prefix. A classified forbidden packet or repeated submission
therefore has the backend's collection bound under arbitrary later policies,
including in the full effective game. The bound is on the existing one-time
charge, with partial final-record observation and conditional report delivery.
Private unusable bindings are outside these charged classes.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

open Classical in
/-- Both charged local classes have an actual collection bound at every
compatible hidden history of any response menu. Own-call resources are derived
from the compatible witness; the caller supplies no original risk-menu trace
or future response-support condition. -/
theorem sourceCompatibleInfo_charged_collection_committed
    (menu : (application service.setup service.leaks).ResponseMenu)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (profile : ∀ player, (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (history : (menu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).InfoState who)
    (compatible : service.sourceCompatibleInfo who info)
    (choice : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).Choice who info)
    (observed : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who history.trace = info)
    (classified : auditableServiceChoice service.setup service.leaks menu service.horizon
      service.scheduler who info choice ∨
        recordedServiceChoice service.setup service.leaks menu service.horizon
          service.scheduler who info choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (initialLaw service.setup) service.horizon
        service.scheduler).runBehavioralTerminalFrom
          (menu.bounded (initialLaw service.setup) service.horizon
            service.scheduler).wellFoundedHistories
          (Profile.update
            (sig := (menu.information (initialLaw service.setup) service.horizon
              service.scheduler).behavioralSignature)
            profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((runtime service.setup).serviceAuditObservation
          service.leaks) (sourceServiceAudit service.setup service.leaks backend.sample)
            final.state who) := by
  rcases classified with packet | recorded
  · exact auditableServiceChoice_collection_committed service.setup service.leaks menu
      service.horizon service.scheduler service.completes backend profile history who remaining
      execution current info choice observed packet observationRate deliveryRate
      delivery_nonnegative coverage
  · let app := application service.setup service.leaks
    have input : info = some (execution.recall who, execution.observe app who) := by
      have actual := observed.symm.trans
        (menu.info (initialLaw service.setup) service.horizon service.scheduler who history.trace)
      simpa only [current, ReactiveApplication.observe, ↓reduceIte] using actual
    have actualCompatible := input ▸ compatible
    have rawTrace := current ▸ menu.toRawTrace (initialLaw service.setup) service.horizon
      service.scheduler history.trace
    obtain ⟨_, _, _, calls, _, _, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
      ⟨remaining, some who, execution⟩ rawTrace who actualCompatible
    exact recordedServiceChoice_collection_committed menu service.horizon service.scheduler
      service.completes backend profile history who remaining execution current calls info choice
      observed recorded observationRate deliveryRate delivery_nonnegative coverage

end Vegas.AsyncServiceSpec
