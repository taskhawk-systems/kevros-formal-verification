# Kevros Enforcement Kernel Public Assurance Capsule

TaskHawk Systems, LLC

## Purpose

This repository contains a sanitized, abstract Lean 4 model of selected
authorization and fail-closed safety properties associated with the Kevros
Enforcement Kernel. It is provided so that reviewers can inspect the theorem
statements and run the proof checker without access to TaskHawk production
software.

This repository is not the Kevros product source repository.

## Published Result

The public proof source currently contains:

- 20 theorem declarations;
- 12 named safety-property theorems;
- 6 structural-progress theorems;
- zero `sorry` declarations;
- zero `admit` declarations;
- zero project-defined `axiom` declarations; and
- zero `unsafe` declarations.

The proof builds with the pinned Lean 4.15.0 toolchain.

## Proof Inventory

| Category | Count | Scope |
| --- | ---: | --- |
| Core induction | 2 | Reachability and strengthened safety invariant |
| Safety properties | 12 | Properties SP1 through SP12 for modeled reachable states |
| Structural progress | 6 | Existential or bounded progress under stated premises |
| Total | 20 | Public theorem declarations in `KevrosCorrect.lean` |

## Reproduction

Install the pinned Lean toolchain, then run:

```bash
python3 verify_public_assurance.py
```

The verifier performs the following checks:

1. confirms the pinned Lean version;
2. builds the proof with `lake build`;
3. confirms the expected theorem count;
4. rejects `sorry`, `admit`, project-defined `axiom`, and `unsafe`
   declarations in executable Lean source;
5. checks the theorem dependency report against the documented allowance for
   standard Lean logical foundations; and
6. verifies the public file allowlist and manifest digest.

The direct build command is:

```bash
lake build
```

## Interpretation Boundary

The Lean checker establishes that the published theorem terms type-check for
the abstract model in `KevrosCorrect.lean`. The result is limited to the
definitions, transition relation, premises, and theorem statements in that
file.

In particular:

- `KappaRegion` is a finite abstraction of threshold regions. The proof does
  not reason over concrete floating-point execution.
- SP12 preserves an abstract `chainIntact` state predicate. It does not prove
  the security of a concrete hash function or verify a deployed evidence
  store.
- The structural-progress theorems establish the existence of progress paths
  under stated premises. They do not establish universal fair-trace liveness.
- The proof does not establish correspondence between this model and any
  compiled or deployed binary.

## Material Not Included

This repository does not contain or license:

- production source code;
- cryptographic keys, preimages, or protocol implementation details;
- deployment configuration or operational data;
- private verification harnesses;
- private test vectors;
- customer or partner information; or
- confidential implementation-correspondence evidence.

Those exclusions are intentional. Statements about private verification work
are outside the scope of this public repository.

## Non-Claims

Publication of this capsule is not:

- a product certification;
- a safety approval;
- an independent third-party assessment;
- a statement that every production behavior has been formally verified;
- a claim of deployed-binary equivalence;
- a claim about cryptographic primitive security;
- a claim of uniqueness or priority; or
- an endorsement by any external organization.

## Repository Contents

```text
KevrosCorrect.lean                 Public abstract model and proofs
AxiomAudit.lean                    Theorem dependency report
lakefile.lean                      Lean build definition
lean-toolchain                     Pinned Lean version
kevros-verification-manifest.json  Public capsule manifest
verify_public_assurance.py         Deterministic public verifier
PUBLIC_REPO_ALLOWLIST.txt          Permitted public files
NOTICE.md                          License and scope notice
LICENSE                            License for included material
```

## License and Scope

The repository license applies only to material included in this repository.
See [NOTICE.md](NOTICE.md) for the scope boundary.
