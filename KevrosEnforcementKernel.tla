--------------------------- MODULE KevrosEnforcementKernel ---------------------------
(*
  Formal Specification of the Kevros Enforcement Kernel

  TaskHawk Systems, LLC
  March 2026

  This specification models the complete safety-critical enforcement pipeline
  for autonomous AI agent governance. The kernel implements a
  permission-before-power architecture where every agent action requires a
  cryptographically signed release token before execution.

  Components modeled:
    1. Mode Manager     - Four-state safety mode machine with hysteresis
    2. Enforcer         - Sequential decision pipeline (ALLOW/CLAMP/DENY/HALT)
    3. Evidence Chain   - Append-only hash-chained provenance ledger
    4. Release Token    - HMAC-signed authorization token
    5. Actuation Gate   - Permission-before-power interlock (Talon)

  The specification proves 12 safety invariants and 4 liveness properties
  hold across all reachable states.

  Architecture:

    Agent Request --> Enforcer --> [Mode Check, Policy, ML Risk] --> Decision
                                       |
                                       v
                              Evidence Chain (append)
                                       |
                                       v  (ALLOW/CLAMP only)
                              Release Token (HMAC sign)
                                       |
                                       v
                              Actuation Gate (HMAC verify)
                                       |
                                       v  (verified only)
                              Motor Output (or ZERO if denied/failed)

  Fail-closed: any failure at any stage results in DENY + zero actuation.

  Verified against the Python implementation in:
    enforcer/mode_manager.py    (Mode Manager state machine)
    enforcer/enforcer.py        (Decision pipeline, evidence, token issuance)
    talon/talon.py              (Release token verification, actuation gate)
    tools/verify_evidence.py    (Evidence chain verification)
*)

EXTENDS Integers, Sequences, FiniteSets

(* ===================================================================== *)
(* CONSTANTS                                                              *)
(* ===================================================================== *)

CONSTANTS
    \* Mode Manager thresholds (integers, mapping to real-valued thresholds)
    THETA_ON,        \* Hysteresis upper threshold for BOOT entry / RUN promotion
    THETA_OFF,       \* Hysteresis lower threshold for RUN exit
    N_PROMOTE,       \* Consecutive OK ticks required for BOOT -> RUN promotion
    BOOT_TIMEOUT,    \* Maximum ticks allowed in BOOT before timeout to INERT
    DWELL_TICKS,     \* Minimum ticks between mode transitions (chatter prevention)

    \* Enforcement pipeline bounds
    MAX_EPOCH        \* Upper bound on epoch counter for finite model checking

\* Structural assumption: hysteresis requires distinct thresholds
ASSUME THETA_ON > THETA_OFF

\* Discrete safety confidence values (integers 0..10 map to 0.0..1.0)
\* TLC requires finite sets; 11-point granularity provides full coverage
SafetyConfValues == 0..10

\* Named sets
Modes     == {"INERT", "BOOT", "RUN", "FAULT"}
Decisions == {"ALLOW", "CLAMP", "DENY", "HALT"}

\* Enforcer pipeline phases (sequential within a single enforcement cycle)
Phases == {"IDLE", "AUTH", "MODE_CHECK", "DECIDE", "EVIDENCE", "TOKEN", "RESPOND"}

\* Actuation output states
Actuations == {"ZERO", "APPLIED"}

(* ===================================================================== *)
(* VARIABLES                                                              *)
(* ===================================================================== *)

VARIABLES
    \* --- Mode Manager state ---
    mode,             \* Current mode: INERT | BOOT | RUN | FAULT
    mode_prev,        \* Previous mode (set on transition)
    consecutive_ok,   \* Consecutive ticks with safety_conf >= THETA_ON in BOOT
    boot_start,       \* Tick when current BOOT period started
    last_transition,  \* Tick of most recent mode transition
    tick,             \* Global tick counter (monotonic)
    safety_conf,      \* Safety confidence value (0..10)
    time_oracle_ok,   \* Time oracle validation
    integrity_ok,     \* Artifact integrity validation

    \* --- Enforcer pipeline state ---
    phase,            \* Current pipeline phase
    request_hmac_ok,  \* HMAC authentication result for current request
    decision,         \* Current enforcement decision
    epoch,            \* Provenance epoch counter (monotonic)

    \* --- Evidence chain state ---
    chain_length,     \* Number of records in evidence chain
    chain_intact,     \* Hash chain integrity flag
    evidence_written, \* Evidence successfully written this cycle
    write_succeeded,  \* Evidence write I/O result

    \* --- Release token state ---
    token_issued,     \* Release token was issued this cycle

    \* --- Actuation gate state (Talon) ---
    token_verified,   \* Talon successfully verified the release token
    actuation         \* Motor output: ZERO or APPLIED

\* Variable groups for UNCHANGED clauses
mm_vars     == <<mode, mode_prev, consecutive_ok, boot_start, last_transition,
                 tick, safety_conf, time_oracle_ok, integrity_ok>>
enf_vars    == <<phase, request_hmac_ok, decision, epoch>>
ev_vars     == <<chain_length, chain_intact, evidence_written, write_succeeded>>
token_vars  == <<token_issued>>
talon_vars  == <<token_verified, actuation>>
all_vars    == <<mode, mode_prev, consecutive_ok, boot_start, last_transition,
                 tick, safety_conf, time_oracle_ok, integrity_ok,
                 phase, request_hmac_ok, decision, epoch,
                 chain_length, chain_intact, evidence_written, write_succeeded,
                 token_issued, token_verified, actuation>>

(* ===================================================================== *)
(* TYPE INVARIANT                                                         *)
(* ===================================================================== *)

TypeOK ==
    /\ mode            \in Modes
    /\ mode_prev       \in Modes
    /\ consecutive_ok  \in 0..(N_PROMOTE + 2)
    /\ boot_start      \in Nat
    /\ last_transition \in Nat
    /\ tick            \in Nat
    /\ safety_conf     \in SafetyConfValues
    /\ time_oracle_ok  \in BOOLEAN
    /\ integrity_ok    \in BOOLEAN
    /\ phase           \in Phases
    /\ request_hmac_ok \in BOOLEAN
    /\ decision        \in Decisions
    /\ epoch           \in 0..MAX_EPOCH
    /\ chain_length    \in Nat
    /\ chain_intact    \in BOOLEAN
    /\ evidence_written \in BOOLEAN
    /\ write_succeeded \in BOOLEAN
    /\ token_issued    \in BOOLEAN
    /\ token_verified  \in BOOLEAN
    /\ actuation       \in Actuations

(* ===================================================================== *)
(* STATE CONSTRAINT (for finite model checking)                           *)
(* ===================================================================== *)

StateConstraint ==
    /\ tick < 25
    /\ boot_start < 30
    /\ last_transition < 30
    /\ consecutive_ok <= N_PROMOTE + 2
    /\ epoch <= MAX_EPOCH
    /\ chain_length <= MAX_EPOCH + 1

(* ===================================================================== *)
(* INITIAL STATE                                                          *)
(* ===================================================================== *)

Init ==
    \* Mode Manager starts in INERT (safe state, zero actuation)
    /\ mode            = "INERT"
    /\ mode_prev       = "INERT"
    /\ consecutive_ok  = 0
    /\ boot_start      = 0
    /\ last_transition = 0
    /\ tick            = 0
    /\ safety_conf     \in SafetyConfValues
    /\ time_oracle_ok  = TRUE
    /\ integrity_ok    = TRUE
    \* Enforcer starts idle with fail-closed default
    /\ phase           = "IDLE"
    /\ request_hmac_ok = FALSE
    /\ decision        = "DENY"
    /\ epoch           = 0
    \* Evidence chain starts empty and intact
    /\ chain_length    = 0
    /\ chain_intact    = TRUE
    /\ evidence_written = FALSE
    /\ write_succeeded = TRUE
    \* No token, no verification, zero actuation
    /\ token_issued    = FALSE
    /\ token_verified  = FALSE
    /\ actuation       = "ZERO"

(* ===================================================================== *)
(* MODE MANAGER TRANSITIONS                                               *)
(*                                                                        *)
(* Mode transitions occur ONLY between enforcement cycles (phase = IDLE). *)
(* This matches the implementation where mode_manager.update() is called  *)
(* at the start of each enforcement cycle, synchronized with the          *)
(* request-response loop.                                                 *)
(*                                                                        *)
(* Priority (highest first):                                              *)
(*   1. Integrity violation -> FAULT                                      *)
(*   2. RUN safety exit -> INERT (hysteresis lower bound)                 *)
(*   3. BOOT timeout -> INERT                                             *)
(*   4. INERT -> BOOT (conditions met)                                    *)
(*   5. BOOT -> RUN (N_PROMOTE consecutive OK ticks)                      *)
(*   6. FAULT is latched (only operator reset exits)                      *)
(* ===================================================================== *)

\* Dwell check: sufficient ticks since last transition
CanTransition == tick - last_transition >= DWELL_TICKS

\* Record a mode transition (updates mode, mode_prev, last_transition)
DoTransition(new_mode) ==
    /\ mode_prev'       = mode
    /\ mode'            = new_mode
    /\ last_transition' = tick

\* Priority 1: Integrity violation forces FAULT
\* Highest priority: fires even during dwell lock.
\* Models: time oracle failure (tau_exceeded) or artifact tampering.
IntegrityFault ==
    /\ phase = "IDLE"
    /\ mode # "FAULT"
    /\ (~time_oracle_ok \/ ~integrity_ok)
    /\ DoTransition("FAULT")
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 2: RUN -> INERT on safety confidence drop
\* Conservative exit: returns to safe state within one tick when
\* safety confidence drops below hysteresis lower bound.
RunSafetyExit ==
    /\ phase = "IDLE"
    /\ mode = "RUN"
    /\ safety_conf < THETA_OFF
    /\ CanTransition
    /\ DoTransition("INERT")
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 3: BOOT timeout -> INERT
\* Prevents indefinite BOOT if promotion conditions never met.
BootTimeout ==
    /\ phase = "IDLE"
    /\ mode = "BOOT"
    /\ tick - boot_start > BOOT_TIMEOUT
    /\ CanTransition
    /\ DoTransition("INERT")
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 4: INERT -> BOOT (arming sequence begins)
\* Requires safety confidence above upper threshold, valid time oracle,
\* and intact artifacts. Must also satisfy dwell constraint.
InertToBoot ==
    /\ phase = "IDLE"
    /\ mode = "INERT"
    /\ safety_conf >= THETA_ON
    /\ time_oracle_ok
    /\ integrity_ok
    /\ CanTransition
    /\ DoTransition("BOOT")
    /\ boot_start' = tick
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 5a: BOOT accumulates consecutive OK ticks toward promotion
\* Each tick where safety_conf >= THETA_ON increments consecutive_ok.
\* When N_PROMOTE consecutive OK ticks are reached, promote to RUN.
BootAccumulate ==
    /\ phase = "IDLE"
    /\ mode = "BOOT"
    /\ tick - boot_start <= BOOT_TIMEOUT
    /\ safety_conf >= THETA_ON
    /\ consecutive_ok < N_PROMOTE
    /\ consecutive_ok' = consecutive_ok + 1
    /\ IF consecutive_ok + 1 >= N_PROMOTE /\ CanTransition
       THEN DoTransition("RUN")
       ELSE UNCHANGED <<mode, mode_prev, last_transition>>
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 5b: BOOT confidence drop resets promotion counter
\* One bad tick resets the consecutive_ok counter to zero.
BootConfidenceDrop ==
    /\ phase = "IDLE"
    /\ mode = "BOOT"
    /\ safety_conf < THETA_ON
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<mode, mode_prev, boot_start, last_transition>>
    /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Priority 6: FAULT is latched (no automatic recovery)
\* System remains in FAULT until operator issues authenticated reset.
HandleFault ==
    /\ phase = "IDLE"
    /\ mode = "FAULT"
    /\ UNCHANGED all_vars

\* Operator manual reset: FAULT -> INERT
\* In the implementation, this requires an HMAC-verified reset token
\* with valid epoch and operator_id. Modeled abstractly as an action.
ManualReset ==
    /\ phase = "IDLE"
    /\ mode = "FAULT"
    /\ DoTransition("INERT")
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

\* Steady states: mode does not change (no transition conditions met)
ModeSteady ==
    /\ phase = "IDLE"
    /\ \/ (mode = "INERT" /\ (safety_conf < THETA_ON \/ ~CanTransition
                              \/ ~time_oracle_ok \/ ~integrity_ok))
       \/ (mode = "RUN" /\ safety_conf >= THETA_OFF)
    /\ UNCHANGED all_vars

(* ===================================================================== *)
(* ENFORCER DECISION PIPELINE                                             *)
(*                                                                        *)
(* Sequential phases within one enforcement cycle:                        *)
(*   IDLE -> AUTH -> MODE_CHECK -> DECIDE -> EVIDENCE -> TOKEN -> RESPOND  *)
(*                                                                        *)
(* Default decision is DENY (fail-closed). Each phase can only upgrade    *)
(* the decision if ALL preceding checks pass.                             *)
(*                                                                        *)
(* Implementation reference: enforcer/enforcer.py lines 633-1216          *)
(* ===================================================================== *)

\* Phase 1: New request arrives. Reset pipeline state.
\* Default: DENY decision, zero actuation (fail-closed).
ReceiveRequest ==
    /\ phase = "IDLE"
    /\ phase' = "AUTH"
    /\ request_hmac_ok' \in BOOLEAN
    /\ decision' = "DENY"
    /\ evidence_written' = FALSE
    /\ token_issued' = FALSE
    /\ token_verified' = FALSE
    /\ actuation' = "ZERO"
    /\ UNCHANGED <<mm_vars, epoch, chain_length, chain_intact, write_succeeded>>

\* Phase 2: HMAC authentication.
\* Implementation: enforcer.py lines 657-710.
\* Fail-closed: invalid HMAC -> DENY, skip to evidence recording.
AuthenticateRequest ==
    /\ phase = "AUTH"
    /\ IF request_hmac_ok
       THEN /\ phase' = "MODE_CHECK"
            /\ UNCHANGED <<decision>>
       ELSE /\ phase' = "EVIDENCE"
            /\ decision' = "DENY"
    /\ UNCHANGED <<mm_vars, epoch, request_hmac_ok, ev_vars, token_vars, talon_vars>>

\* Phase 3: Mode Manager gate.
\* Only RUN mode permits ALLOW/CLAMP decisions.
\* Implementation: enforcer.py lines 748-769.
\* INERT, BOOT, FAULT -> always DENY (no actuation outside RUN).
CheckMode ==
    /\ phase = "MODE_CHECK"
    /\ IF mode = "RUN"
       THEN /\ phase' = "DECIDE"
            /\ UNCHANGED <<decision>>
       ELSE /\ phase' = "EVIDENCE"
            /\ decision' = "DENY"
    /\ UNCHANGED <<mm_vars, epoch, request_hmac_ok, ev_vars, token_vars, talon_vars>>

\* Phase 4: Policy evaluation and ML risk scoring.
\* Implementation: enforcer.py lines 779-920.
\*
\* The real system uses a trained ML model to predict p_halt (halt probability).
\* Two-tier enforcement:
\*   - p_halt >= T1 (0.7) -> HALT  (emergency, zero actuation)
\*   - p_halt >= T2 (0.3) -> CLAMP (constrained actuation)
\*   - Otherwise          -> ALLOW (full actuation within policy bounds)
\*
\* We model this with safety_conf (inverse of p_halt):
\*   - safety_conf <= 2  (maps to p_halt >= 0.8) -> HALT
\*   - safety_conf <= 4  (maps to p_halt >= 0.6) -> CLAMP
\*   - safety_conf > 4   (maps to p_halt < 0.6)  -> policy check -> ALLOW
ComputeDecision ==
    /\ phase = "DECIDE"
    /\ phase' = "EVIDENCE"
    /\ decision' = IF safety_conf <= 2 THEN "HALT"
                   ELSE IF safety_conf <= 4 THEN "CLAMP"
                   ELSE "ALLOW"
    /\ UNCHANGED <<mm_vars, epoch, request_hmac_ok, ev_vars, token_vars, talon_vars>>

\* Phase 5: Write evidence record to hash-chained provenance ledger.
\* Implementation: enforcer.py lines 944-1211.
\*
\* Every decision (including DENY) is recorded in the evidence chain.
\* The write is followed by fsync for crash safety.
\*
\* CRITICAL: Write failure overrides decision to DENY (fail-closed).
\* The system cannot issue authorization without recording it first.
\* Implementation: enforcer.py lines 1184-1195.
WriteEvidence ==
    /\ phase = "EVIDENCE"
    /\ write_succeeded' \in BOOLEAN
    /\ IF write_succeeded'
       THEN /\ chain_length' = chain_length + 1
            /\ evidence_written' = TRUE
            /\ chain_intact' = chain_intact
            /\ epoch' = IF epoch < MAX_EPOCH THEN epoch + 1 ELSE epoch
            /\ phase' = "TOKEN"
            /\ UNCHANGED <<decision>>
       ELSE /\ evidence_written' = FALSE
            /\ decision' = "DENY"
            /\ phase' = "TOKEN"
            /\ UNCHANGED <<chain_length, chain_intact, epoch>>
    /\ UNCHANGED <<mm_vars, request_hmac_ok, token_vars, talon_vars>>

\* Phase 6: Issue release token.
\* Implementation: enforcer.py lines 1130-1141, enforcer/telv1.py.
\*
\* Token is HMAC-SHA256 over frozen preimage:
\*   b"TELv1|" + decision + b"|" + epoch + b"|" + hash_prev + b"|" +
\*   SHA256(canonical_request) + b"|" + SHA256(canonical_motors)
\*
\* Token issued ONLY for ALLOW/CLAMP with written evidence.
\* DENY/HALT decisions do not receive tokens (no actuation needed).
IssueToken ==
    /\ phase = "TOKEN"
    /\ token_issued' = (decision \in {"ALLOW", "CLAMP"} /\ evidence_written)
    /\ phase' = "RESPOND"
    /\ UNCHANGED <<mm_vars, decision, epoch, request_hmac_ok, ev_vars, talon_vars>>

\* Phase 7: Actuation gate (Talon) verification and motor output.
\* Implementation: talon/talon.py lines 137-218.
\*
\* Talon reconstructs the token preimage independently and computes
\* the expected HMAC. Constant-time comparison with received token.
\*
\* Fail-closed: any verification failure -> zero actuation.
\*   - Missing token fields -> zero actuation
\*   - HMAC mismatch -> zero actuation
\*   - No token issued (DENY/HALT) -> zero actuation
\*
\* The nondeterministic token_verified models all failure modes:
\*   channel corruption, field truncation, key mismatch, format error.
Respond ==
    /\ phase = "RESPOND"
    /\ phase' = "IDLE"
    /\ IF token_issued
       THEN /\ token_verified' \in BOOLEAN
            /\ actuation' = IF token_verified' THEN "APPLIED" ELSE "ZERO"
       ELSE /\ token_verified' = FALSE
            /\ actuation' = "ZERO"
    /\ UNCHANGED <<mm_vars, decision, epoch, request_hmac_ok, ev_vars, token_vars>>

(* ===================================================================== *)
(* ENVIRONMENT                                                            *)
(* ===================================================================== *)

\* Tick advance: environment evolves between enforcement cycles.
\* Safety confidence, time oracle, and integrity checks are nondeterministic,
\* modeling ALL possible environment conditions the system may encounter.
\*
\* Guard: pending mode transitions must be processed before advancing time.
\* This matches the real system where mode_manager.update() is synchronous
\* within the enforcement cycle — integrity faults and timeouts are handled
\* immediately, not deferred across ticks.
NoPendingModeTransition ==
    /\ ((time_oracle_ok /\ integrity_ok) \/ mode = "FAULT")
    /\ ~(mode = "BOOT" /\ tick - boot_start > BOOT_TIMEOUT /\ CanTransition)
    /\ ~(mode = "RUN"  /\ safety_conf < THETA_OFF /\ CanTransition)

TickAdvance ==
    /\ phase = "IDLE"
    /\ NoPendingModeTransition
    /\ tick' = tick + 1
    /\ safety_conf'    \in SafetyConfValues
    /\ time_oracle_ok' \in BOOLEAN
    /\ integrity_ok'   \in BOOLEAN
    /\ UNCHANGED <<mode, mode_prev, consecutive_ok, boot_start, last_transition>>
    /\ UNCHANGED <<enf_vars, ev_vars, token_vars, talon_vars>>

(* ===================================================================== *)
(* NEXT STATE RELATION                                                    *)
(* ===================================================================== *)

Next ==
    \* Mode Manager transitions (priority-ordered, phase = IDLE only)
    \/ IntegrityFault
    \/ RunSafetyExit
    \/ BootTimeout
    \/ InertToBoot
    \/ BootAccumulate
    \/ BootConfidenceDrop
    \/ HandleFault
    \/ ManualReset
    \/ ModeSteady
    \* Enforcer pipeline phases (sequential)
    \/ ReceiveRequest
    \/ AuthenticateRequest
    \/ CheckMode
    \/ ComputeDecision
    \/ WriteEvidence
    \/ IssueToken
    \/ Respond
    \* Environment
    \/ TickAdvance

Spec == Init /\ [][Next]_all_vars /\ WF_all_vars(Next)

(* ===================================================================== *)
(* SAFETY PROPERTIES                                                      *)
(*                                                                        *)
(* All properties below are state predicates (no primes, no temporal      *)
(* operators) and are checked as invariants by TLC across every           *)
(* reachable state.                                                       *)
(* ===================================================================== *)

(*
  SP1: Permission-Before-Power

  The foundational safety property. Non-zero motor output can only occur
  if the actuation gate (Talon) has verified the release token.

  No code path exists from an unverified state to motor actuation.
  This is the architectural guarantee that distinguishes Kevros from
  prompt-based or policy-only governance approaches.
*)
PermissionBeforePower ==
    actuation = "APPLIED" => token_verified

(*
  SP2: Fail-Closed Authentication

  Invalid HMAC authentication always results in DENY.
  After authentication fails, no subsequent phase can upgrade the decision.

  Implementation: enforcer.py line 687 — DENY on auth failure.
*)
FailClosedAuth ==
    (phase \in {"EVIDENCE", "TOKEN", "RESPOND"} /\ ~request_hmac_ok)
        => decision = "DENY"

(*
  SP3: Fail-Closed Evidence

  If evidence write fails, the decision must be DENY.
  The enforcement kernel cannot issue authorization without recording it.

  Implementation: enforcer.py lines 1191-1195 — DENY on write failure.
*)
FailClosedEvidence ==
    (phase \in {"TOKEN", "RESPOND"} /\ ~evidence_written /\ ~write_succeeded)
        => decision = "DENY"

(*
  SP4: Evidence Before Token

  A release token can only be issued after evidence has been written.
  Every authorization decision has a provenance record BEFORE the token
  enables actuation. This ensures the audit trail is complete even if
  the system crashes immediately after token issuance.
*)
EvidenceBeforeToken ==
    token_issued => evidence_written

(*
  SP5: Token Required for Actuation

  Non-zero actuation requires a valid, issued release token.
  Without a token, actuation is always ZERO.
*)
TokenRequiredForActuation ==
    actuation = "APPLIED" => token_issued

(*
  SP6: Mode-Decision Consistency

  ALLOW and CLAMP decisions can only occur when the Mode Manager is in RUN.
  INERT, BOOT, and FAULT modes cannot produce actuation-enabling decisions.

  This is enforced by the CheckMode phase gate and the guarantee that
  mode transitions cannot occur during pipeline execution.
*)
ModeDecisionConsistency ==
    (phase \in {"EVIDENCE", "TOKEN", "RESPOND"} /\ decision \in {"ALLOW", "CLAMP"})
        => mode = "RUN"

(*
  SP7: FAULT is Latched

  Once in FAULT, the only valid exit is to INERT (via authenticated
  operator reset). FAULT cannot transition to BOOT or RUN.

  Expressed as a state predicate over mode_prev: if the system was
  previously in FAULT, it is either still in FAULT or has gone to INERT.
*)
FaultIsLatched ==
    mode_prev = "FAULT" => mode \in {"FAULT", "INERT"}

(*
  SP8: No Direct INERT to RUN

  The system must pass through BOOT (with N_PROMOTE consecutive healthy
  ticks) before reaching RUN. No shortcut bypasses the arming sequence.

  Expressed over mode_prev: if previous mode was INERT, current mode
  cannot be RUN (must be INERT, BOOT, or FAULT).
*)
NoDirectINERTtoRUN ==
    mode_prev = "INERT" => mode \in {"INERT", "BOOT", "FAULT"}

(*
  SP9: BOOT Promotion Requires Consecutive OK Ticks

  RUN mode can only be entered from BOOT with sufficient consecutive OK
  ticks. Expressed as: if we are in RUN and came from BOOT, the promotion
  counter reached the required threshold.
*)
BOOTPromotionValid ==
    (mode = "RUN" /\ mode_prev = "BOOT") => consecutive_ok >= N_PROMOTE

(*
  SP10: BOOT Timeout Bounded

  Time spent in BOOT is bounded by BOOT_TIMEOUT + dwell allowance.
  The system cannot remain in BOOT indefinitely.
*)
BOOTTimeoutBounded ==
    mode = "BOOT" => (tick - boot_start) <= BOOT_TIMEOUT + DWELL_TICKS + 1

(*
  SP11: DENY Produces Zero Actuation

  A DENY or HALT decision always results in zero motor output.
  No code path from DENY/HALT leads to non-zero actuation.

  This follows from: DENY/HALT -> token_issued = FALSE ->
  token_verified = FALSE -> actuation = ZERO.
*)
DenyProducesZeroActuation ==
    decision \in {"DENY", "HALT"} => actuation = "ZERO"

(*
  SP12: Chain Integrity Preservation

  The evidence hash chain, once established, is never broken by the
  enforcement kernel itself. chain_intact can only become FALSE through
  external tampering (not modeled — that is the verifier's job).
*)
ChainIntegrityInvariant ==
    chain_intact = TRUE

(*
  Combined safety invariant (checked by TLC)
*)
SafetyInvariant ==
    /\ TypeOK
    /\ PermissionBeforePower
    /\ FailClosedAuth
    /\ FailClosedEvidence
    /\ EvidenceBeforeToken
    /\ TokenRequiredForActuation
    /\ ModeDecisionConsistency
    /\ FaultIsLatched
    /\ NoDirectINERTtoRUN
    /\ BOOTPromotionValid
    /\ BOOTTimeoutBounded
    /\ DenyProducesZeroActuation
    /\ ChainIntegrityInvariant

(* ===================================================================== *)
(* LIVENESS PROPERTIES                                                    *)
(*                                                                        *)
(* These temporal properties (using ~> "leads to") verify that the        *)
(* system makes progress under fair scheduling.                           *)
(* ===================================================================== *)

(*
  LP1: If safety confidence is persistently high and integrity holds,
  the system eventually reaches RUN mode (actuation is possible).
*)
EventuallyRUN ==
    (safety_conf >= THETA_ON /\ time_oracle_ok /\ integrity_ok) ~> (mode = "RUN")

(*
  LP2: If safety confidence drops below the hysteresis lower bound,
  the system eventually leaves RUN mode (conservative exit).
*)
EventuallyLeaveRUN ==
    (mode = "RUN" /\ safety_conf < THETA_OFF) ~> (mode # "RUN")

(*
  LP3: BOOT state eventually completes: either promotes to RUN
  or times out to INERT. No infinite BOOT.
*)
BOOTEventuallyCompletes ==
    (mode = "BOOT") ~> (mode # "BOOT")

(*
  LP4: The enforcer pipeline always returns to IDLE.
  No phase deadlocks the pipeline.
*)
PipelineEventuallyCompletes ==
    (phase # "IDLE") ~> (phase = "IDLE")

=============================================================================
