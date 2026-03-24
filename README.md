# Kevros Enforcement Kernel

**Six-Layer Formal Verification of a Safety-Critical AI Governance Kernel**

TaskHawk Systems, LLC — March 2026

---

## Overview

The Kevros Enforcement Kernel is a formally verified governance layer for autonomous AI agents. It enforces 12 safety invariants and 4 liveness properties through a deterministic pipeline: every agent action must pass authentication, mode checking, decision computation, evidence logging, and token gating before actuation occurs. A DENY verdict produces zero actuation. Always.

This repository contains the formal specifications, proofs, and runtime assertions that constitute the most comprehensive formal verification stack ever applied to a single product: **six independent verification layers, 71 total proofs, zero failures.**

## Six-Layer Verification Stack

| Layer | Tool | Domain | Scope | Result |
|-------|------|--------|-------|--------|
| 1 | **TLA+ / TLC 2.18** | System architecture | Bounded exhaustive (1.94B states, 171M distinct) | 12/12 invariants, 4/4 liveness |
| 2 | **Kani 0.66.0 / CBMC 6.5.0** | Rust implementation | Bounded model checking (72 vCPU, 145 GB) | 17/17 harnesses, 99 unit tests |
| 3 | **Verus / Z3** | Unbounded proof | SMT — all possible inputs | 22/22 proofs across 899 lines |
| 4 | **Python RAC** | Runtime assertions | Continuous — live production traffic | 1:1 property mapping with TLA+ |
| 5 | **Golden Vectors** | Cross-language equivalence | Byte identity — Python and Rust | Byte-identical outputs |
| 6 | **Lean 4** | Interactive theorem proving | Unbounded deductive — machine-checked proof | 20/20 theorems, 0 sorry |

No published organization — including AWS, Microsoft, or Google — has demonstrated six independent formal verification tools on a single product. AWS applies TLA+, CBMC, Dafny, and fuzzing across DynamoDB, S3, Firecracker, and the Encryption SDK respectively. Microsoft applies TLA+, Static Driver Verifier, and Verus across Cosmos DB, Windows, and research prototypes. Kevros applies all six to one kernel.

## Safety Properties (SP1–SP12)

| ID | Name | Invariant |
|----|------|-----------|
| SP1 | PermissionBeforePower | No actuation without valid release token |
| SP2 | FailClosedAuth | Any authentication error produces DENY |
| SP3 | FailClosedEvidence | Any evidence-write error produces DENY |
| SP4 | EvidenceBeforeToken | Token issued only after evidence appended |
| SP5 | TokenRequiredForActuation | Actuation gate rejects without valid token |
| SP6 | ModeDecisionConsistency | ALLOW/CLAMP decisions only in RUN mode |
| SP7 | FaultIsLatched | Once in FAULT, only resets to INERT |
| SP8 | NoDirectInertToRun | No single transition from INERT to RUN |
| SP9 | BootPromotionValid | BOOT→RUN requires nPromote consecutive OK readings |
| SP10 | BootTimeoutBounded | BOOT phase bounded by bootTimeout + dwellTicks + 1 |
| SP11 | DenyZeroActuation | DENY or HALT verdict produces zero actuation |
| SP12 | ChainIntegrityInvariant | Evidence chain hash-links are unbroken |

## Liveness Properties (LP1–LP4)

| ID | Name | Property |
|----|------|----------|
| LP1 | EventuallyRun | System reaches RUN under persistent good conditions |
| LP2 | RunExitsOnLowSafety | RUN exits when safety confidence drops below threshold |
| LP3 | BootEventuallyCompletes | BOOT completes within bounded time |
| LP4 | PipelineReturnsToIdle | Request pipeline returns to IDLE in at most 6 steps |

## Layer 6: Lean 4 Formalization

The Lean 4 formalization (`KevrosCorrect.lean`, 760 lines) is a faithful translation of the TLA+ specification. It provides machine-checked mathematical proof that all 12 safety invariants hold for every reachable state and all 4 liveness properties are structurally guaranteed.

**20 theorems, 0 sorry.**

The proof proceeds by induction on the `Reachable` relation with case analysis on all 24 constructors of the `Next` transition relation. A strengthened invariant with 27 conjuncts enables the inductive step to close mechanically. Key design decisions:

- **KappaRegion abstraction** eliminates IEEE 754 floating-point from the model, consistent with Layers 2 and 3.
- **Hash as uninterpreted function** — chain integrity proofs hold for any hash algorithm.
- **Well-founded variant (phaseDist)** — LP4 uses well-founded induction on pipeline phase distance, proving completion in at most 6 steps.
- **Zero dependencies** — pure Lean 4.15.0+, no Mathlib, no axioms beyond the Lean kernel.

### Theorem Catalog

**Core:**
- `inv_holds` — Strengthened inductive invariant (27 conjuncts) holds for all reachable states
- `safety_holds` — SafetyInv is a direct consequence of the strengthened invariant

**Safety (SP1–SP12):**
- `SP1` through `SP12` — Each safety property extracted as an individual theorem

**Liveness (LP1–LP4):**
- `pipeline_progress` — Every non-idle phase has a strictly closer successor
- `LP4_PipelineCompletes` — Pipeline returns to IDLE (well-founded induction on phaseDist)
- `LP3_BootExits` — BOOT exits when timeout exceeded
- `LP2_RunExits` — RUN exits when kappaRegion drops to belowOff
- `LP1_BootProgress` — BOOT accumulates toward RUN or promotes
- `LP1_InertToBoot` — INERT transitions to BOOT under good conditions

## Repository Structure

```
kevros-formal-verification/
├── KevrosEnforcementKernel.tla       Layer 1: TLA+ specification (716 lines)
├── KevrosEnforcementKernel.cfg       TLC configuration (12 invariants, bounded constants)
├── ModeManager.tla                   Standalone mode manager specification
├── ModeManager.cfg                   TLC configuration for ModeManager
├── KevrosCorrect.lean                Layer 6: Lean 4 formalization (760 lines)
├── lakefile.lean                     Lean 4 build configuration
├── lean-toolchain                    Lean 4 version pin (v4.15.0)
├── tlc-output.txt                    Complete TLC output (March 24, 2026)
├── kevros-verification-manifest.json Machine-readable verification results
├── timestamps/                       RFC 3161 timestamps (FreeTSA)
├── Five-Layer-Formal-Verification-AI-Governance-Kernel.pdf
└── README.md
```

## Reproducing the Verification

```bash
# Layer 1: TLA+ model checking (requires Java 11+)
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
java -XX:+UseParallelGC -Xmx8G -cp tla2tools.jar tlc2.TLC \
  -workers auto \
  -config KevrosEnforcementKernel.cfg \
  KevrosEnforcementKernel.tla

# Layer 6: Lean 4 theorem proving (requires elan)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
lake build
```

## Numbers

- **1,943,069,194** states generated by TLC
- **171,647,834** distinct states explored
- **118** search depth
- **71** total proofs across 6 layers
- **20** Lean 4 theorems with **0 sorry**
- **~648** proof obligations (24 constructors × 27 conjuncts)
- **12** safety invariants, **4** liveness properties
- **0** violations

## License

MIT

## Contact

John McGraw — Founder/CEO, TaskHawk Systems
admin@taskhawktech.com
