/-
  Kevros Enforcement Kernel — Lean 4 Formalization
  Faithful translation of KevrosEnforcementKernel.tla (716 lines)
  TLC result: 1.94 billion states, 12 safety invariants, 4 liveness properties, 0 violations

  Source: github.com/taskhawk-systems/kevros-formal-verification
  Author: John McGraw, TaskHawk Systems, LLC
  Live API: governance.taskhawktech.com  •  pip install kevros  •  Free: 1,000 calls/month
  Date: March 2026

  Key design decisions:
    • KappaRegion abstraction eliminates IEEE 754 from the model.
    • All mode transitions require phase = IDLE (TLA+ line 201).
    • BootAccumulate has tick - boot_start <= BOOT_TIMEOUT guard (TLA+ line 283).
    • RunSafetyExit goes to INERT (TLA+ line 244).
    • AuthenticateRequest skips to EVIDENCE on auth fail (TLA+ line 363).
    • CheckMode skips to EVIDENCE on mode fail (TLA+ line 376).
    • ReceiveRequest defaults to DENY (TLA+ line 348, fail-closed).
    • Hash function is uninterpreted (chain integrity is boolean).
    • All proofs by induction on Reachable with case analysis on Next.
-/

-- No external dependencies. Lean 4.15.0+.
-- To verify: `lake build`

namespace Kevros

/-! ## Core Types -/

inductive Mode | inert | boot | run | fault deriving DecidableEq, Repr, BEq
inductive Phase | idle | auth | modeCheck | decide | evidence | token | respond deriving DecidableEq, Repr, BEq
inductive Decision | allow | clamp | deny | halt deriving DecidableEq, Repr, BEq
inductive KappaRegion | belowOff | between | aboveOn deriving DecidableEq, Repr, BEq
inductive Actuation | zero | applied deriving DecidableEq, Repr, BEq

/-! ## System State -/

structure State where
  mode : Mode
  modePrev : Mode
  consecutiveOk : Nat
  bootStart : Nat
  lastTransition : Nat
  tick : Nat
  kappaRegion : KappaRegion
  timeOracleOk : Bool
  integrityOk : Bool
  phase : Phase
  requestHmacOk : Bool
  decision : Decision
  actuation : Actuation
  tokenVerified : Bool
  tokenIssued : Bool
  evidenceWritten : Bool
  writeSucceeded : Bool
  chainLength : Nat
  chainIntact : Bool
  deriving Repr, BEq

/-! ## Initial State (TLA+ Init, line 172) -/

def IsInit (s : State) : Prop :=
  s.mode = .inert ∧ s.modePrev = .inert ∧ s.phase = .idle ∧
  s.decision = .deny ∧ s.actuation = .zero ∧
  s.tokenVerified = false ∧ s.tokenIssued = false ∧
  s.evidenceWritten = false ∧ s.writeSucceeded = true ∧
  s.consecutiveOk = 0 ∧ s.bootStart = 0 ∧ s.lastTransition = 0 ∧
  s.tick = 0 ∧ s.chainLength = 0 ∧ s.chainIntact = true ∧
  s.requestHmacOk = false

def canTransition (dwellTicks : Nat) (s : State) : Prop :=
  s.tick - s.lastTransition ≥ dwellTicks

/-! ## Next-State Relation (TLA+ Next, line 495)

    ALL mode transitions require phase = IDLE (TLA+ line 201).
    Every constructor fully constrains all fields of s'. -/

inductive Next (nP bT dT : Nat) : State → State → Prop
  -- INERT → BOOT (TLA+ InertToBoot, line 264)
  | inertToBoot (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .inert)
      (hK : s.kappaRegion = .aboveOn) (hO : s.timeOracleOk = true)
      (hG : s.integrityOk = true) (hD : canTransition dT s)
      (h1 : s'.mode = .boot) (h2 : s'.modePrev = .inert) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.tick) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- BOOT accumulate (TLA+ BootAccumulate, line 280, ELSE branch)
  | bootAccumulate (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .boot) (hK : s.kappaRegion = .aboveOn)
      (hTO : s.tick - s.bootStart ≤ bT) (hNP : s.consecutiveOk + 1 < nP)
      (h1 : s'.mode = .boot) (h2 : s'.modePrev = s.modePrev) (h3 : s'.consecutiveOk = s.consecutiveOk + 1)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.lastTransition) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- BOOT → RUN (TLA+ BootAccumulate, line 280, THEN branch)
  | bootToRun (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .boot) (hK : s.kappaRegion = .aboveOn)
      (hTO : s.tick - s.bootStart ≤ bT) (hProm : s.consecutiveOk + 1 ≥ nP)
      (hDw : canTransition dT s)
      (h1 : s'.mode = .run) (h2 : s'.modePrev = .boot) (h3 : s'.consecutiveOk = s.consecutiveOk + 1)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- BOOT confidence drop (TLA+ BootConfidenceDrop, line 295)
  | bootConfDrop (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .boot) (hK : s.kappaRegion ≠ .aboveOn)
      (h1 : s'.mode = s.mode) (h2 : s'.modePrev = s.modePrev) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.lastTransition)
      (h6 : s'.tick = s.tick)  -- TLA+ line 301: UNCHANGED <<tick, ...>>
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- RUN → INERT (TLA+ RunSafetyExit, line 239)
  | runExit (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .run) (hK : s.kappaRegion = .belowOff)
      (hDw : canTransition dT s)
      (h1 : s'.mode = .inert) (h2 : s'.modePrev = .run) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Any → FAULT (TLA+ IntegrityFault, line 227)
  | toFault (s s' : State)
      (hI : s.phase = .idle) (hBad : s.timeOracleOk = false ∨ s.integrityOk = false)
      (hNF : s.mode ≠ .fault)
      (h1 : s'.mode = .fault) (h2 : s'.modePrev = s.mode) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- FAULT → INERT (TLA+ ManualReset, line 314)
  | faultReset (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .fault)
      (h1 : s'.mode = .inert) (h2 : s'.modePrev = .fault) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- BOOT timeout (TLA+ BootTimeout, line 251)
  | bootTimeout (s s' : State)
      (hI : s.phase = .idle) (hM : s.mode = .boot) (hTO : s.tick - s.bootStart > bT)
      (hDw : canTransition dT s)
      (h1 : s'.mode = .inert) (h2 : s'.modePrev = .boot) (h3 : s'.consecutiveOk = 0)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.tick) (h6 : s'.tick = s.tick)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Receive request (TLA+ ReceiveRequest, line 344)
  | receive (s s' : State)
      (hP : s.phase = .idle)
      (h1 : s'.phase = .auth) (h2 : s'.decision = .deny) (h3 : s'.actuation = .zero)
      (h4 : s'.tokenVerified = false) (h5 : s'.tokenIssued = false) (h6 : s'.evidenceWritten = false)
      (h7 : s'.mode = s.mode) (h8 : s'.modePrev = s.modePrev) (h9 : s'.consecutiveOk = s.consecutiveOk)
      (h10 : s'.bootStart = s.bootStart) (h11 : s'.lastTransition = s.lastTransition)
      (h12 : s'.tick = s.tick)
      (h13 : s'.chainLength = s.chainLength) (h14 : s'.chainIntact = s.chainIntact)
      (h15 : s'.writeSucceeded = s.writeSucceeded)
      : Next nP bT dT s s'
  -- Auth pass (TLA+ AuthenticateRequest THEN, line 361)
  | authPass (s s' : State)
      (hP : s.phase = .auth) (hA : s.requestHmacOk = true)
      (h1 : s'.phase = .modeCheck) (h2 : s'.decision = s.decision) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Auth fail → EVIDENCE (TLA+ AuthenticateRequest ELSE, line 363)
  | authFail (s s' : State)
      (hP : s.phase = .auth) (hA : s.requestHmacOk = false)
      (h1 : s'.phase = .evidence) (h2 : s'.decision = .deny) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Mode check pass (TLA+ CheckMode THEN, line 374)
  | modePass (s s' : State)
      (hP : s.phase = .modeCheck) (hR : s.mode = .run)
      (h1 : s'.phase = .decide) (h2 : s'.decision = s.decision) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Mode check fail → EVIDENCE (TLA+ CheckMode ELSE, line 376)
  | modeFail (s s' : State)
      (hP : s.phase = .modeCheck) (hNR : s.mode ≠ .run)
      (h1 : s'.phase = .evidence) (h2 : s'.decision = .deny) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Decide ALLOW (TLA+ ComputeDecision, line 393)
  | decAllow (s s' : State)
      (hP : s.phase = .decide)
      (h1 : s'.phase = .evidence) (h2 : s'.decision = .allow) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Decide CLAMP
  | decClamp (s s' : State)
      (hP : s.phase = .decide)
      (h1 : s'.phase = .evidence) (h2 : s'.decision = .clamp) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Decide HALT
  | decHalt (s s' : State)
      (hP : s.phase = .decide)
      (h1 : s'.phase = .evidence) (h2 : s'.decision = .halt) (h3 : s'.actuation = s.actuation)
      (h4 : s'.tokenVerified = s.tokenVerified) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Write evidence OK (TLA+ WriteEvidence, line 410, success)
  | evidOk (s s' : State)
      (hP : s.phase = .evidence)
      (h1 : s'.phase = .token) (h2 : s'.evidenceWritten = true) (h3 : s'.writeSucceeded = true)
      (h4 : s'.decision = s.decision) (h5 : s'.actuation = s.actuation)
      (h6 : s'.tokenVerified = s.tokenVerified) (h7 : s'.tokenIssued = s.tokenIssued)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength + 1) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Write evidence FAIL (TLA+ WriteEvidence, line 410, failure)
  | evidFail (s s' : State)
      (hP : s.phase = .evidence)
      (h1 : s'.phase = .token) (h2 : s'.evidenceWritten = false) (h3 : s'.writeSucceeded = false)
      (h4 : s'.decision = .deny) (h5 : s'.actuation = s.actuation)
      (h6 : s'.tokenVerified = s.tokenVerified) (h7 : s'.tokenIssued = s.tokenIssued)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Issue token (TLA+ IssueToken, line 435, issued=true)
  | tokIssue (s s' : State)
      (hP : s.phase = .token) (hAC : s.decision = .allow ∨ s.decision = .clamp)
      (hEv : s.evidenceWritten = true)
      (h1 : s'.phase = .respond) (h2 : s'.tokenIssued = true) (h3 : s'.decision = s.decision)
      (h4 : s'.actuation = s.actuation) (h5 : s'.tokenVerified = s.tokenVerified)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Deny token (TLA+ IssueToken, line 435, issued=false)
  | tokDeny (s s' : State)
      (hP : s.phase = .token) (hD : s.decision = .deny ∨ s.decision = .halt ∨ s.evidenceWritten = false)
      (h1 : s'.phase = .respond) (h2 : s'.tokenIssued = false) (h3 : s'.decision = s.decision)
      (h4 : s'.actuation = s.actuation) (h5 : s'.tokenVerified = s.tokenVerified)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Respond APPLY (TLA+ Respond, line 454, token verified)
  | rspApply (s s' : State)
      (hP : s.phase = .respond) (hT : s.tokenIssued = true)
      (h1 : s'.phase = .idle) (h2 : s'.tokenVerified = true) (h3 : s'.actuation = .applied)
      (h4 : s'.decision = s.decision) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Respond VERIFY FAIL (token issued but verification fails)
  | rspFail (s s' : State)
      (hP : s.phase = .respond) (hT : s.tokenIssued = true)
      (h1 : s'.phase = .idle) (h2 : s'.tokenVerified = false) (h3 : s'.actuation = .zero)
      (h4 : s'.decision = s.decision) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Respond DENY (no token → zero)
  | rspDeny (s s' : State)
      (hP : s.phase = .respond) (hNT : s.tokenIssued = false)
      (h1 : s'.phase = .idle) (h2 : s'.tokenVerified = false) (h3 : s'.actuation = .zero)
      (h4 : s'.decision = s.decision) (h5 : s'.tokenIssued = s.tokenIssued)
      (h6 : s'.evidenceWritten = s.evidenceWritten) (h7 : s'.writeSucceeded = s.writeSucceeded)
      (h8 : s'.mode = s.mode) (h9 : s'.modePrev = s.modePrev) (h10 : s'.consecutiveOk = s.consecutiveOk)
      (h11 : s'.bootStart = s.bootStart) (h12 : s'.lastTransition = s.lastTransition) (h13 : s'.tick = s.tick)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'
  -- Environment tick (TLA+ TickAdvance, line 481)
  -- Guard: NoPendingModeTransition (TLA+ line 476-479)
  -- In particular: ¬(mode = BOOT ∧ tick - boot_start > BOOT_TIMEOUT ∧ CanTransition)
  | envTick (s s' : State)
      (hI : s.phase = .idle)
      (hNoBT : s.mode = .boot → s.tick - s.bootStart ≤ bT)
      (h1 : s'.mode = s.mode) (h2 : s'.modePrev = s.modePrev) (h3 : s'.consecutiveOk = s.consecutiveOk)
      (h4 : s'.bootStart = s.bootStart) (h5 : s'.lastTransition = s.lastTransition) (h6 : s'.tick = s.tick + 1)
      (h7 : s'.phase = s.phase) (h8 : s'.decision = s.decision) (h9 : s'.actuation = s.actuation)
      (h10 : s'.tokenVerified = s.tokenVerified) (h11 : s'.tokenIssued = s.tokenIssued)
      (h12 : s'.evidenceWritten = s.evidenceWritten) (h13 : s'.writeSucceeded = s.writeSucceeded)
      (h14 : s'.chainLength = s.chainLength) (h15 : s'.chainIntact = s.chainIntact)
      (h16 : s'.requestHmacOk = s.requestHmacOk)
      : Next nP bT dT s s'

/-! ## Reachability -/

inductive Reachable (nP bT dT : Nat) : State → Prop
  | init (s : State) (h : IsInit s) : Reachable nP bT dT s
  | step (s s' : State) (hR : Reachable nP bT dT s) (hN : Next nP bT dT s s') : Reachable nP bT dT s'

/-! ## Safety Invariant -/

def SafetyInv (s : State) (nP bT dT : Nat) : Prop :=
  (s.actuation = .applied → s.tokenVerified = true) ∧                                          -- SP1
  ((s.phase = .evidence ∨ s.phase = .token ∨ s.phase = .respond) →
    s.requestHmacOk = false → s.decision = .deny) ∧                                            -- SP2
  ((s.phase = .token ∨ s.phase = .respond) →
    s.evidenceWritten = false → s.writeSucceeded = false → s.decision = .deny) ∧                -- SP3
  (s.tokenIssued = true → s.evidenceWritten = true) ∧                                          -- SP4
  (s.actuation = .applied → s.tokenIssued = true) ∧                                            -- SP5
  ((s.phase = .evidence ∨ s.phase = .token ∨ s.phase = .respond) →
    (s.decision = .allow ∨ s.decision = .clamp) → s.mode = .run) ∧                             -- SP6
  (s.modePrev = .fault → s.mode = .fault ∨ s.mode = .inert) ∧                                  -- SP7
  (s.modePrev = .inert → s.mode ≠ .run) ∧                                                      -- SP8
  (s.mode = .run → s.modePrev = .boot → s.consecutiveOk ≥ nP) ∧                                -- SP9
  (s.mode = .boot → s.tick - s.bootStart ≤ bT + dT + 1) ∧                                     -- SP10
  ((s.decision = .deny ∨ s.decision = .halt) → s.actuation = .zero) ∧                          -- SP11
  (s.chainIntact = true)                                                                        -- SP12

/-! ## Strengthened invariant for inductive proof -/

def Inv (s : State) (nP bT dT : Nat) : Prop := SafetyInv s nP bT dT ∧
  (s.phase = .idle → s.tokenIssued = false → s.actuation = .zero) ∧  -- idle defaults
  (s.phase = .auth → s.decision = .deny) ∧                            -- receive sets deny
  (s.phase = .modeCheck → s.decision = .deny) ∧                       -- preserved from auth
  (s.phase = .decide → s.mode = .run) ∧                               -- checkModePass gate
  (s.phase = .auth → s.tokenIssued = false) ∧                         -- receive resets
  (s.phase = .auth → s.evidenceWritten = false) ∧
  (s.phase = .modeCheck → s.tokenIssued = false) ∧
  (s.phase = .modeCheck → s.evidenceWritten = false) ∧
  (s.phase = .decide → s.tokenIssued = false) ∧
  (s.phase = .decide → s.evidenceWritten = false) ∧
  (s.phase = .evidence → s.tokenIssued = false) ∧                     -- not yet issued
  (s.phase = .auth → s.actuation = .zero) ∧                           -- receive sets zero
  (s.phase = .decide → s.requestHmacOk = true) ∧                      -- path through authPass
  (s.phase = .respond → s.tokenIssued = true →
    (s.decision = .allow ∨ s.decision = .clamp)) ∧                     -- from tokIssue guard
  (s.phase = .evidence → s.requestHmacOk = false → s.decision = .deny) ∧ -- auth fail → deny
  (s.phase = .modeCheck → s.requestHmacOk = true) ∧                     -- path through authPass
  (s.phase = .token → s.requestHmacOk = false → s.decision = .deny) ∧   -- propagated from evidence
  (s.phase = .respond → s.requestHmacOk = false → s.decision = .deny) ∧ -- propagated from token
  (s.phase = .decide → s.actuation = .zero) ∧                            -- still zero at decide
  (s.phase = .decide → s.decision = .deny) ∧                             -- still deny at decide
  (s.mode = .boot → s.bootStart ≤ s.tick) ∧                               -- bootStart ≤ tick while booting
  (s.phase = .token → s.actuation = .zero) ∧                              -- actuation still zero at token
  (s.phase = .evidence → s.actuation = .zero) ∧                           -- actuation still zero at evidence
  (s.phase = .respond → s.actuation = .zero)                              -- actuation still zero at respond (pre-gate)

/-! ## Main theorem -/

-- Proof strategy: induction on Reachable, case analysis on Next.
-- Base case: IsInit satisfies all conjuncts (all fields fully constrained).
-- Inductive case: for each Next constructor, rewrite s' fields and appeal to IH.
-- Key insight: ALL mode transitions require phase=IDLE (TLA+ line 201),
-- so SP6 (mode-decision consistency) is preserved through pipeline phases.
--
-- Status: proof structure verified, 2 worked examples below.
-- Full proof requires ~24 cases × ~27 conjuncts = ~648 proof obligations.
-- Each is mechanical (rewrite + IH or contradiction).

theorem inv_holds (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) : Inv s nP bT dT := by
  induction hR with
  | init s hi =>
    obtain ⟨hm, hmp, hph, hd, ha, htv, hti, hew, hws, hco, hbs, hlt, ht, hcl, hci, hhm⟩ := hi
    simp only [Inv, SafetyInv]; simp_all
  | step s s' _ hN ih =>
    simp only [Inv, SafetyInv] at ih ⊢
    obtain ⟨⟨sp1,sp2,sp3,sp4,sp5,sp6,sp7,sp8,sp9,sp10,sp11,sp12⟩,
      si_idle, si_authD, si_mcD, si_decR, si_authTI, si_authEW,
      si_mcTI, si_mcEW, si_decTI, si_decEW, si_evTI, si_authA,
      si_decHmac, si_rspTok, si_evHmac, si_mcHmac, si_tokHmac,
      si_rspHmac, si_decA, si_decD, si_bt, si_tokA, si_evA, si_rspA⟩ := ih
    -- Save key IH components before simp_all rewrites/consumes them
    have sp10' := sp10; have si_bt' := si_bt; have si_rspTok' := si_rspTok
    have si_tokA' := si_tokA; have si_rspA' := si_rspA
    -- Main tactic: simp_all handles most of ~650 proof obligations.
    -- Remaining goals need: omega for SP10 (with Nat subtraction + bootStart ≤ tick),
    -- or decision case analysis for SP11 in rspApply.
    cases hN
    -- Handle envTick specially (SP10 needs careful Nat subtraction reasoning)
    case envTick hI hNoBT h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      -- SP10: tick+1 - bootStart ≤ bT + dT + 1
      -- From hNoBT: mode=boot → tick - bootStart ≤ bT
      -- From si_bt': mode=boot → bootStart ≤ tick
      -- So tick+1 - bootStart = (tick - bootStart) + 1 ≤ bT + 1 ≤ bT + dT + 1 ✓
      have key : s.mode = .boot → s.tick + 1 - s.bootStart ≤ bT + dT + 1 := by
        intro hb; have := hNoBT hb; have := si_bt' hb; omega
      have key2 : s.mode = .boot → s.bootStart ≤ s.tick + 1 := by
        intro hb; have := si_bt' hb; omega
      simp_all
    -- Handle rspApply specially (SP11 needs decision∈{allow,clamp} from si_rspTok)
    case rspApply hP hT h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      have hDec := si_rspTok hP hT  -- decision = allow ∨ clamp
      simp_all
      rcases hDec with h | h <;> simp_all [h]
    -- All other cases: simp_all handles everything (tick doesn't change)
    all_goals simp_all
    -- tokDeny: actuation=zero from si_tokA'
    all_goals (first
      | omega
      | exact si_tokA' (by assumption)
      | (exact fun h => absurd h (by rw [si_tokA' (by assumption)]; simp))
      | assumption)


/-! ## Safety Invariant follows from Strengthened Invariant -/

theorem safety_holds (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    SafetyInv s nP bT dT := (inv_holds nP bT dT s hR).1

theorem SP1  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.actuation = .applied → s.tokenVerified = true := (safety_holds nP bT dT s hR).1
theorem SP2  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    (s.phase = .evidence ∨ s.phase = .token ∨ s.phase = .respond) →
    s.requestHmacOk = false → s.decision = .deny := (safety_holds nP bT dT s hR).2.1
theorem SP3  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    (s.phase = .token ∨ s.phase = .respond) → s.evidenceWritten = false →
    s.writeSucceeded = false → s.decision = .deny := (safety_holds nP bT dT s hR).2.2.1
theorem SP4  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.tokenIssued = true → s.evidenceWritten = true := (safety_holds nP bT dT s hR).2.2.2.1
theorem SP5  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.actuation = .applied → s.tokenIssued = true := (safety_holds nP bT dT s hR).2.2.2.2.1
theorem SP6  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    (s.phase = .evidence ∨ s.phase = .token ∨ s.phase = .respond) →
    (s.decision = .allow ∨ s.decision = .clamp) → s.mode = .run :=
  (safety_holds nP bT dT s hR).2.2.2.2.2.1
theorem SP7  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.modePrev = .fault → s.mode = .fault ∨ s.mode = .inert :=
  (safety_holds nP bT dT s hR).2.2.2.2.2.2.1
theorem SP8  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.modePrev = .inert → s.mode ≠ .run := (safety_holds nP bT dT s hR).2.2.2.2.2.2.2.1
theorem SP9  (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.mode = .run → s.modePrev = .boot → s.consecutiveOk ≥ nP :=
  (safety_holds nP bT dT s hR).2.2.2.2.2.2.2.2.1
theorem SP10 (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.mode = .boot → s.tick - s.bootStart ≤ bT + dT + 1 :=
  (safety_holds nP bT dT s hR).2.2.2.2.2.2.2.2.2.1
theorem SP11 (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    (s.decision = .deny ∨ s.decision = .halt) → s.actuation = .zero :=
  (safety_holds nP bT dT s hR).2.2.2.2.2.2.2.2.2.2.1
theorem SP12 (nP bT dT : Nat) (s : State) (hR : Reachable nP bT dT s) :
    s.chainIntact = true := (safety_holds nP bT dT s hR).2.2.2.2.2.2.2.2.2.2.2

/-! ## Liveness Properties (LP1–LP4)

    TLA+ liveness uses temporal logic (leads-to ~>) under weak fairness.
    In Lean, we encode liveness as **bounded progress**: we define a variant
    (well-founded measure) for each LP and prove it strictly decreases on
    relevant transitions, giving an upper bound on steps to termination.

    The key structural insight enabling all four LPs:
      ALL mode transitions require phase = IDLE (TLA+ line 201).
    Therefore when the pipeline is active (phase ≠ idle), ONLY pipeline
    transitions can fire, and each strictly decreases phaseDist.

    Encoding: we use ReachN (reachability in exactly n steps) and prove
    existential liveness: from any state satisfying P, there EXISTS a
    finite sequence of Next steps leading to a state satisfying Q.

    This is the standard ITP encoding of liveness — weaker than TLA+'s
    universal quantification over fair traces, but sufficient for
    establishing that progress is structurally possible. -/

/-- Reflexive transitive closure of Next (reachability in 0 or more steps) -/
inductive NextStar (nP bT dT : Nat) : State → State → Prop
  | refl (s : State) : NextStar nP bT dT s s
  | step (s s₁ s₂ : State) (hN : Next nP bT dT s s₁) (hR : NextStar nP bT dT s₁ s₂) :
      NextStar nP bT dT s s₂

/-- Pipeline phase distance to IDLE (variant for LP4) -/
def phaseDist : Phase → Nat
  | .idle => 0 | .respond => 1 | .token => 2 | .evidence => 3
  | .decide => 4 | .modeCheck => 5 | .auth => 6

/-! ### LP4: Pipeline Eventually Completes

    Every non-idle phase has a Next transition that moves the phase
    strictly closer to idle. Since phaseDist is bounded by 6, the
    pipeline completes in at most 6 steps.

    This holds because:
    - auth → modeCheck or evidence (dist 6 → 5 or 3)
    - modeCheck → decide or evidence (dist 5 → 4 or 3)
    - decide → evidence (dist 4 → 3)
    - evidence → token (dist 3 → 2)
    - token → respond (dist 2 → 1)
    - respond → idle (dist 1 → 0)

    Proof: for each phase, construct a valid Next transition and show
    phaseDist decreases. The constructed transition uses arbitrary
    choices for nondeterministic fields (hmacOk, writeSucceeded, etc.)
    since ALL choices lead to phase progress. -/

/-- For any state with phase ≠ idle, there exists a Next step
    that strictly decreases phaseDist.
    Proof: for each phase, construct a valid Next transition.
    Nondeterministic choices (hmacOk, mode, tokenIssued) are
    resolved by case-splitting where needed. -/
theorem pipeline_progress (nP bT dT : Nat) (s : State) (hNI : s.phase ≠ .idle) :
    ∃ s', Next nP bT dT s s' ∧ phaseDist s'.phase < phaseDist s.phase := by
  -- For each phase, we construct a witness state s' and a Next proof.
  -- The witness is s with the phase (and sometimes decision) updated.
  -- All other fields are preserved, so frame conditions are trivially rfl.
  -- For each non-idle phase, construct a witness Next step that decreases phaseDist.
  -- The proof is purely mechanical: pick the appropriate constructor, provide rfl for
  -- all preserved fields, and show phaseDist decreases.
  -- Witnesses: auth→{modeCheck,evidence}, modeCheck→{decide,evidence},
  --   decide→evidence, evidence→token, token→respond, respond→idle
  -- State field order: mode modePrev consecutiveOk bootStart lastTransition tick
  --   kappaRegion timeOracleOk integrityOk phase requestHmacOk decision actuation
  --   tokenVerified tokenIssued evidenceWritten writeSucceeded chainLength chainIntact
  cases ha : s.phase <;> simp_all [phaseDist]
  case auth =>
    cases hr : s.requestHmacOk
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .evidence, s.requestHmacOk, .deny, s.actuation,
        s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.authFail s _ ha hr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .modeCheck, s.requestHmacOk, s.decision, s.actuation,
        s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.authPass s _ ha hr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case modeCheck =>
    by_cases hm : s.mode = .run
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .decide, s.requestHmacOk, s.decision,
        s.actuation, s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.modePass s _ ha hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .evidence, s.requestHmacOk, .deny,
        s.actuation, s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.modeFail s _ ha hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case decide =>
    refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
      s.kappaRegion, s.timeOracleOk, s.integrityOk, .evidence, s.requestHmacOk, .allow,
      s.actuation, s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
      s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
    exact Next.decAllow s _ ha rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case evidence =>
    refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
      s.kappaRegion, s.timeOracleOk, s.integrityOk, .token, s.requestHmacOk, .deny,
      s.actuation, s.tokenVerified, s.tokenIssued, false, false,
      s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
    exact Next.evidFail s _ ha rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case token =>
    cases hew : s.evidenceWritten <;> cases hd : s.decision
    -- All 8 sub-cases use s.field for preserved fields (s.evidenceWritten, s.tokenIssued replaced by cases)
    -- After `cases hew` and `cases hd`, use simp to propagate concrete values.
    -- Now s.evidenceWritten and s.decision are definitionally concrete values.
    -- tokDeny for evid=false, tokIssue/tokDeny for evid=true based on decision.
    -- Use simp [hew, hd] to rewrite s.evidenceWritten and s.decision to concrete values,
    -- then rfl works in constructor applications.
    -- hew and hd are now concrete equalities from `cases`
    all_goals (first
      | exact ⟨{ s with phase := .respond, tokenIssued := false },
          Next.tokDeny s _ ha (Or.inr (Or.inr hew)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          by simp [phaseDist]⟩
      | exact ⟨{ s with phase := .respond, tokenIssued := true },
          Next.tokIssue s _ ha (Or.inl hd) hew rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          by simp [phaseDist]⟩
      | exact ⟨{ s with phase := .respond, tokenIssued := true },
          Next.tokIssue s _ ha (Or.inr hd) hew rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          by simp [phaseDist]⟩
      | exact ⟨{ s with phase := .respond, tokenIssued := false },
          Next.tokDeny s _ ha (Or.inl hd) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          by simp [phaseDist]⟩
      | exact ⟨{ s with phase := .respond, tokenIssued := false },
          Next.tokDeny s _ ha (Or.inr (Or.inl hd)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          by simp [phaseDist]⟩)
  case respond =>
    cases ht : s.tokenIssued
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .idle, s.requestHmacOk, s.decision,
        .zero, false, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.rspDeny s _ ha ht rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · refine ⟨⟨s.mode, s.modePrev, s.consecutiveOk, s.bootStart, s.lastTransition, s.tick,
        s.kappaRegion, s.timeOracleOk, s.integrityOk, .idle, s.requestHmacOk, s.decision,
        .zero, false, s.tokenIssued, s.evidenceWritten, s.writeSucceeded,
        s.chainLength, s.chainIntact⟩, ?_, by simp [phaseDist]⟩
      exact Next.rspFail s _ ha ht rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- LP4: The pipeline eventually returns to IDLE.
    From any state with phase ≠ idle, there exists a finite chain of
    Next steps reaching a state with phase = idle.
    Proof by well-founded induction on phaseDist. -/
theorem LP4_PipelineCompletes (nP bT dT : Nat) (s : State) (hNI : s.phase ≠ .idle) :
    ∃ s', NextStar nP bT dT s s' ∧ s'.phase = .idle := by
  -- Well-founded induction on phaseDist
  have hPos : 0 < phaseDist s.phase := by
    cases h : s.phase <;> simp [phaseDist]
    exact absurd h hNI
  obtain ⟨s₁, hNext, hLt⟩ := pipeline_progress nP bT dT s hNI
  by_cases hIdle : s₁.phase = .idle
  · exact ⟨s₁, NextStar.step s s₁ s₁ hNext (NextStar.refl s₁), hIdle⟩
  · -- s₁ is closer to idle, recurse
    have : phaseDist s₁.phase < phaseDist s.phase := hLt
    have ⟨s₂, hStar, hIdle₂⟩ := LP4_PipelineCompletes nP bT dT s₁ hIdle
    exact ⟨s₂, NextStar.step s s₁ s₂ hNext hStar, hIdle₂⟩
termination_by phaseDist s.phase

/-! ### LP3: BOOT Eventually Completes

    From SP10, BOOT is bounded: tick - bootStart ≤ bT + dT + 1.
    Combined with LP4 (pipeline always returns to idle) and the
    bootTimeout transition (fires when tick - bootStart > bT),
    BOOT must eventually complete.

    We prove a weaker but clean statement: from any reachable BOOT
    state, there EXISTS a Next transition that exits BOOT
    (either bootToRun or bootTimeout), provided the pipeline is idle. -/

/-- LP3 (structural): From any reachable state in BOOT with phase=idle
    and tick - bootStart > bootTimeout, there exists a single step exiting BOOT. -/
theorem LP3_BootExits (nP bT dT : Nat) (s : State)
    (_hR : Reachable nP bT dT s) (hB : s.mode = .boot)
    (hI : s.phase = .idle) (hTO : s.tick - s.bootStart > bT)
    (hDw : canTransition dT s) :
    ∃ s', Next nP bT dT s s' ∧ s'.mode ≠ .boot := by
  refine ⟨⟨.inert, .boot, 0, s.bootStart, s.tick, s.tick, s.kappaRegion,
    s.timeOracleOk, s.integrityOk, s.phase, s.requestHmacOk, s.decision, s.actuation,
    s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded, s.chainLength,
    s.chainIntact⟩, ?_, ?_⟩
  · exact Next.bootTimeout s _ hI hB hTO hDw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · simp

/-! ### LP2: RUN Eventually Exits on Low Safety

    When safety confidence drops below THETA_OFF (kappaRegion = belowOff)
    and the dwell constraint is met, runSafetyExit fires immediately. -/

/-- LP2 (structural): From any RUN state with low kappa, idle phase,
    and dwell satisfied, there exists a single step exiting RUN. -/
theorem LP2_RunExits (nP bT dT : Nat) (s : State)
    (_hR : Reachable nP bT dT s) (hM : s.mode = .run)
    (hK : s.kappaRegion = .belowOff) (hI : s.phase = .idle)
    (hDw : canTransition dT s) :
    ∃ s', Next nP bT dT s s' ∧ s'.mode ≠ .run := by
  refine ⟨⟨.inert, .run, 0, s.bootStart, s.tick, s.tick, s.kappaRegion,
    s.timeOracleOk, s.integrityOk, s.phase, s.requestHmacOk, s.decision, s.actuation,
    s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded, s.chainLength,
    s.chainIntact⟩, ?_, ?_⟩
  · exact Next.runExit s _ hI hM hK hDw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · simp

/-! ### LP1: Eventually RUN Under Persistent Good Conditions

    If safety confidence is persistently high (aboveOn), oracles OK,
    and integrity OK, the system eventually reaches RUN through:
      INERT →(inertToBoot)→ BOOT →(bootAccumulate × nPromote)→ RUN

    We prove the BOOT→RUN sub-path: with persistent good conditions,
    each bootAccumulate step increments consecutiveOk, and after
    nPromote steps, bootToRun fires. -/

/-- LP1 (structural): From BOOT with good conditions and enough room,
    there exists a step that either promotes to RUN or accumulates
    toward promotion. -/
theorem LP1_BootProgress (nP bT dT : Nat) (s : State)
    (_hR : Reachable nP bT dT s) (hM : s.mode = .boot)
    (hK : s.kappaRegion = .aboveOn) (hI : s.phase = .idle)
    (hTO : s.tick - s.bootStart ≤ bT)
    (hDw : canTransition dT s) :
    ∃ s', Next nP bT dT s s' ∧
      (s'.mode = .run ∨ (s'.mode = .boot ∧ s'.consecutiveOk = s.consecutiveOk + 1)) := by
  by_cases hp : s.consecutiveOk + 1 ≥ nP
  · -- Enough consecutive OKs → promote to RUN
    refine ⟨⟨.run, .boot, s.consecutiveOk + 1, s.bootStart, s.tick, s.tick, s.kappaRegion,
      s.timeOracleOk, s.integrityOk, s.phase, s.requestHmacOk, s.decision, s.actuation,
      s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded, s.chainLength,
      s.chainIntact⟩, ?_, Or.inl rfl⟩
    exact Next.bootToRun s _ hI hM hK hTO hp hDw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · have : s.consecutiveOk + 1 < nP := by omega
    refine ⟨⟨.boot, s.modePrev, s.consecutiveOk + 1, s.bootStart, s.lastTransition, s.tick, s.kappaRegion,
      s.timeOracleOk, s.integrityOk, s.phase, s.requestHmacOk, s.decision, s.actuation,
      s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded, s.chainLength,
      s.chainIntact⟩, ?_, Or.inr ⟨rfl, rfl⟩⟩
    exact Next.bootAccumulate s _ hI hM hK hTO this rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- LP1 (entry): From INERT with good conditions and dwell satisfied,
    there exists a single step to BOOT. -/
theorem LP1_InertToBoot (nP bT dT : Nat) (s : State)
    (hM : s.mode = .inert) (hK : s.kappaRegion = .aboveOn)
    (hO : s.timeOracleOk = true) (hG : s.integrityOk = true)
    (hI : s.phase = .idle) (hDw : canTransition dT s) :
    ∃ s', Next nP bT dT s s' ∧ s'.mode = .boot := by
  refine ⟨⟨.boot, .inert, 0, s.tick, s.tick, s.tick, s.kappaRegion,
    s.timeOracleOk, s.integrityOk, s.phase, s.requestHmacOk, s.decision, s.actuation,
    s.tokenVerified, s.tokenIssued, s.evidenceWritten, s.writeSucceeded, s.chainLength,
    s.chainIntact⟩, ?_, ?_⟩
  · exact Next.inertToBoot s _ hI hM hK hO hG hDw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · rfl

end Kevros
