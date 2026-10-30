# Elementary qubit removal and logical lifting

`QubitRemoval.lean` implements an elementary X-check removal using the existing matrix specification and its proved QECLean homological bridge.
The retained code has binary checks `A,B` with `A*B^T=0`.
For any vector `s`, the old X checks are `(a_i,0)` and `(s,1)`; old Z checks are `(b_j,s dot b_j)`.
The last qubit and distinguished X generator are removed.
Applications must identify their actual physical matrices with this normal form.

## Formal results

The old X rank is the new X rank plus one; the Z rank is unchanged.
Encoded dimension is preserved.
New X logicals lift by appending zero, with unchanged physical Hamming weight.
New Z logicals have the unique lift `(z,s dot z)`, with weight unchanged or increased by one.
Both lifts preserve nontriviality, and the X/Z pairing is preserved.
The proof also describes all old X representatives and both exact distance minima.

With exact side minima supplied, the inequalities are

```text
d_X_old <= d_X_new
d_Z_new <= d_Z_old <= d_Z_new + 1
```

Given new X distance `D`, preservation is equivalent to `D <= weight(x+s)+1` for every new X logical `x`.
Given new Z distance `D`, preservation is equivalent to some shortest new Z logical having `s dot z=0`.
The old Z distance is `D+1` exactly when every shortest new Z logical has odd pairing with `s`.
These statements use actual cycles modulo matrix row spaces, not surrogate finite predicates.

## Kernel-checked examples

| Removal | Encoded dimension | Old `(d_X,d_Z)` | New `(d_X,d_Z)` |
| --- | --- | --- | --- |
| Five to four qubits, preserving | 2 | `(2,2)` | `(2,2)` |
| Four to three qubits, losing | 1 | `(2,2)` | `(2,1)` |
| Five to four qubits, increasing | 2 | `(1,2)` | `(2,2)` |

The losing old checks are literally `XXXX`, `ZZII`, and `IIZZ`, matching QECLean's small `[[4,1,2]]` construction.
The finite proofs establish exact minima and ranks and exercise the generic preservation/loss criteria.
A further regression proves that a canonical Z lift grows from weight 2 to 3 in the preserving example.
Exact distance preservation therefore does not require this particular lift to preserve every representative's weight.
These examples are separate from the nineteen submitted verified instances.

## Independent review and additional observations

An independent subagent found no correctness issues or missing hypotheses.
The standalone `independent-check.py` exhaustively checks 583 tiny orthogonal-subspace models and verifies all three examples numerically.
It runs with Python's standard library and is outside the Lean proof.

The reviewer also derived a stabilizer-correction condition: an odd-parity Z stabilizer can repair a lift without weight growth when its support overlap is at least half its weight.
An effective bound on X increase uses the least weight in `s+row(A)`.
These observations and accumulated bounds for repeated deletions are not additional Lean theorems in this milestone.
See `evaluation.json` for the distinction between formal results and derived observations.

The asymmetric puncturing bounds have prior coverage in [Grassl, Theorems 4–5](https://arxiv.org/html/2208.05353v2).
The broader [stabilizer puncturing framework](https://arxiv.org/html/2410.17754v3) provides related matrix constructions.
No mathematical novelty or first-formalization claim is made.

## Replay and resources

The two new proof modules and package root were rebuilt sequentially from cleared compiled outputs.
Other project outputs and dependency caches were retained.
All nine guarded audits passed, with 251 unique main targets and 70 focused lifting targets.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the new audited dependency closures.

The detached integration run took 51.14 seconds under a 5 GiB memory cap, 128 MiB swap cap, one CPU, and one Lean thread.
The wall limit was 300 seconds and the CPU limit 280 seconds.
Maximum child RSS was 3,852,696 KiB; the journal displayed a rounded charged-memory peak of 680.5M and 50.689 CPU seconds.
These memory measurements have different scopes and do not describe a cold build.
No cluster job was submitted.

With the pinned toolchain and caches ready, run inside a detached, resource-limited allocation:

```bash
bash data/lifting-evaluation/replay.sh
python data/lifting-evaluation/independent-check.py
```

`replay.sh` does not impose limits or clear compiled outputs itself.
Source hashes, commands, measurements, validation, and review scope are in `evaluation.json`.
Earlier proof records and datasets retain their original bytes.
