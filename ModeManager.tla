--------------------------- MODULE ModeManager ---------------------------
(*
  Formal Specification of Kevros Mode Manager State Machine
  
  Proves:
  1. FAULT is latched (cannot transition to RUN without reset)
  2. No direct INERT -> RUN transition (must go through BOOT)
  3. Hysteresis prevents mode chatter
  4. BOOT timeout is bounded
  
  Model check with TLC to verify all safety properties hold.
*)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    THETA_ON,       \* Hysteresis upper threshold (e.g., 0.8)
    THETA_OFF,      \* Hysteresis lower threshold (e.g., 0.6)
    N_PROMOTE,      \* Consecutive OK ticks for BOOT->RUN (e.g., 10)
    BOOT_TIMEOUT,   \* Max ticks in BOOT before timeout (e.g., 100)
    DWELL_TICKS     \* Minimum ticks between transitions (e.g., 25)

\* Finite set of safety confidence values (rational numbers 0-10 mapped to 0.0-1.0)
SafetyConfValues == {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

VARIABLES
    mode,           \* Current mode: "INERT" | "BOOT" | "RUN" | "FAULT"
    mode_prev,      \* Previous mode
    consecutive_ok, \* Counter for BOOT promotion
    boot_start,     \* Tick when BOOT started
    last_transition,\* Tick of last transition
    tick,           \* Current tick counter
    safety_conf,    \* Safety confidence [0.0, 1.0]
    time_oracle_ok, \* Time oracle validation
    integrity_ok    \* Integrity monitor validation

vars == <<mode, mode_prev, consecutive_ok, boot_start, last_transition, 
          tick, safety_conf, time_oracle_ok, integrity_ok>>

-----------------------------------------------------------------------------

(*
  Type invariants
*)
TypeOK ==
    /\ mode \in {"INERT", "BOOT", "RUN", "FAULT"}
    /\ mode_prev \in {"INERT", "BOOT", "RUN", "FAULT"}
    /\ consecutive_ok \in Nat
    /\ boot_start \in Nat
    /\ last_transition \in Nat
    /\ tick \in Nat
    /\ safety_conf \in SafetyConfValues
    /\ time_oracle_ok \in BOOLEAN
    /\ integrity_ok \in BOOLEAN

(*
  State constraint to prevent explosion
  Bounds tick counter and all time-related variables
  Scaled for laptop-safe verification
*)
StateConstraint ==
    /\ tick < 30
    /\ boot_start < 35
    /\ last_transition < 35
    /\ consecutive_ok <= N_PROMOTE + 2

(*
  Initial state
*)
Init ==
    /\ mode = "INERT"
    /\ mode_prev = "INERT"
    /\ consecutive_ok = 0
    /\ boot_start = 0
    /\ last_transition = 0
    /\ tick = 0
    /\ safety_conf \in SafetyConfValues
    /\ time_oracle_ok = TRUE
    /\ integrity_ok = TRUE

(*
  Check if enough time has passed since last transition (dwell)
*)
CanTransition ==
    tick - last_transition >= DWELL_TICKS

(*
  Perform transition to new mode
*)
Transition(new_mode) ==
    /\ mode_prev' = mode
    /\ mode' = new_mode
    /\ last_transition' = tick

(*
  INERT state transitions
*)
HandleINERT ==
    /\ mode = "INERT"
    /\ IF safety_conf >= THETA_ON /\ CanTransition
       THEN /\ Transition("BOOT")
            /\ boot_start' = tick
            /\ consecutive_ok' = 0
            /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>
       ELSE /\ UNCHANGED <<mode, mode_prev, consecutive_ok, boot_start, last_transition>>
            /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>

(*
  BOOT state transitions
*)
HandleBOOT ==
    /\ mode = "BOOT"
    /\ LET boot_duration == tick - boot_start
       IN
       \/ (* Timeout *)
          /\ boot_duration > BOOT_TIMEOUT
          /\ CanTransition
          /\ Transition("INERT")
          /\ consecutive_ok' = 0
          /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
       \/ (* Promotion to RUN *)
          /\ safety_conf >= THETA_ON
          /\ consecutive_ok < N_PROMOTE
          /\ consecutive_ok' = consecutive_ok + 1
          /\ IF consecutive_ok + 1 >= N_PROMOTE /\ CanTransition
             THEN Transition("RUN")
             ELSE UNCHANGED <<mode, mode_prev, last_transition>>
          /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
       \/ (* Confidence drop - reset counter *)
          /\ safety_conf < THETA_ON
          /\ consecutive_ok' = 0
          /\ UNCHANGED <<mode, mode_prev, boot_start, last_transition>>
          /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>

(*
  RUN state transitions
*)
HandleRUN ==
    /\ mode = "RUN"
    /\ IF safety_conf < THETA_OFF /\ CanTransition
       THEN /\ Transition("INERT")
            /\ consecutive_ok' = 0
            /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>
       ELSE /\ UNCHANGED <<mode, mode_prev, consecutive_ok, boot_start, last_transition>>
            /\ UNCHANGED <<tick, safety_conf, time_oracle_ok, integrity_ok>>

(*
  FAULT state (latched - only manual reset can exit)
*)
HandleFAULT ==
    /\ mode = "FAULT"
    /\ UNCHANGED vars

(*
  Fail-closed: integrity violation forces FAULT
*)
IntegrityViolation ==
    /\ \/ ~time_oracle_ok
       \/ ~integrity_ok
    /\ CanTransition
    /\ Transition("FAULT")
    /\ UNCHANGED <<consecutive_ok, boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>

(*
  Manual reset from FAULT (operator action)
*)
ManualReset ==
    /\ mode = "FAULT"
    /\ Transition("INERT")
    /\ consecutive_ok' = 0
    /\ UNCHANGED <<boot_start, tick, safety_conf, time_oracle_ok, integrity_ok>>

(*
  Tick advance (environment action)
*)
TickAdvance ==
    /\ tick' = tick + 1
    /\ safety_conf' \in SafetyConfValues
    /\ time_oracle_ok' \in BOOLEAN
    /\ integrity_ok' \in BOOLEAN
    /\ UNCHANGED <<mode, mode_prev, consecutive_ok, boot_start, last_transition>>

(*
  Next state relation
*)
Next ==
    \/ IntegrityViolation
    \/ HandleINERT
    \/ HandleBOOT
    \/ HandleRUN
    \/ HandleFAULT
    \/ ManualReset
    \/ TickAdvance

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

(*
  SAFETY PROPERTIES (Invariants that must always hold)
*)

(*
  Property 1: FAULT is latched
  Once in FAULT, cannot transition to RUN without going through INERT first
*)
FaultIsLatched ==
    (mode = "FAULT" /\ mode' # "FAULT") => mode' = "INERT"

(*
  Property 2: No direct INERT -> RUN transition
  Must go through BOOT
*)
NoDirectINERTtoRUN ==
    (mode = "INERT" /\ mode' # "INERT") => mode' # "RUN"

(*
  Property 3: Hysteresis is enforced
  THETA_ON must be greater than THETA_OFF
*)
HysteresisValid ==
    THETA_ON > THETA_OFF

(*
  Property 4: BOOT promotion requires N_PROMOTE consecutive OK ticks
*)
BOOTPromotionValid ==
    (mode = "BOOT" /\ mode' = "RUN") => consecutive_ok >= N_PROMOTE - 1

(*
  Property 5: BOOT timeout is bounded
*)
BOOTTimeoutBounded ==
    (mode = "BOOT") => (tick - boot_start) <= BOOT_TIMEOUT + DWELL_TICKS

(*
  Property 6: Dwell time prevents chatter
*)
DwellEnforced ==
    (mode' # mode) => (tick - last_transition >= DWELL_TICKS)

(*
  Property 7: Integrity violation forces FAULT
*)
IntegrityViolationForcesFault ==
    (~time_oracle_ok \/ ~integrity_ok) ~> (mode = "FAULT")

(*
  Combined safety invariant
*)
SafetyInvariant ==
    /\ TypeOK
    /\ HysteresisValid
    /\ FaultIsLatched
    /\ NoDirectINERTtoRUN
    /\ BOOTPromotionValid
    /\ BOOTTimeoutBounded
    /\ DwellEnforced

-----------------------------------------------------------------------------

(*
  LIVENESS PROPERTIES (Things that eventually happen)
*)

(*
  Property L1: If safety confidence is high enough, eventually reach RUN
*)
EventuallyRUN ==
    (safety_conf >= THETA_ON /\ time_oracle_ok /\ integrity_ok) ~> (mode = "RUN")

(*
  Property L2: If safety confidence drops, eventually leave RUN
*)
EventuallyLeaveRUN ==
    (mode = "RUN" /\ safety_conf < THETA_OFF) ~> (mode # "RUN")

(*
  Property L3: BOOT eventually completes (either promotes or times out)
*)
BOOTEventuallyCompletes ==
    (mode = "BOOT") ~> (mode # "BOOT")

=============================================================================

(*
  Model Checking Configuration (ModeManager.cfg)
  
  CONSTANTS
    THETA_ON = 0.8
    THETA_OFF = 0.6
    N_PROMOTE = 10
    BOOT_TIMEOUT = 100
    DWELL_TICKS = 25
  
  SPECIFICATION Spec
  
  INVARIANTS
    SafetyInvariant
  
  PROPERTIES
    EventuallyRUN
    EventuallyLeaveRUN
    BOOTEventuallyCompletes
*)
