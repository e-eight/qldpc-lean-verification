# Literal Z-sector generation and pilot

Status: all seventeen focused emitter tests, Ruff checks, generation, exact byte
regeneration, and the seven-module kernel pilot passed. The source/test/data
handoff is frozen for emitter review. No new target-code distance theorem is
claimed by this evaluation.

Only `scripts/emit_distance566_sector.py` and its focused test file may receive
formatting or template fixes. The numerical certificate, independent validator,
original input revision, older generated inputs, approved generic prototype,
and mixed-class helper remain unchanged.

Generation uses a fresh temporary `--lean-root`. A separate staging check admits
only the new `Input/Distance566SectorZ*.lean` namespace, rejects existing source
destinations, and requires all destination directories to be real directories
inside the fresh workspace. Lean output checks also reject retained artifact
links and directory links. Prior source and artifact bytes remain read-only.

There are 59 generated modules, 29 used mixed bases, and seven references. Pruning
retained 1,138 good-family representatives and residual entry counts
`[31, 35, 32, 33, 30, 28, 33]`, drawn from 172 unique pool supports. Original
natural weights and row witnesses are retained; deletion preserves strict seven.

The pilot passed Data, BaseChecks0, RefChecks0, Good0Data/Checks, and
Residual0Data/Checks. It did not compile the complete generated certificate set
or a literal distance capstone. Every Lean call passes
`-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3` inside a detached
one-CPU, one-thread allocation with an enforced 8 GiB memory ceiling and zero
swap. The wall-time limit is twenty minutes. Pinned dependencies and approved
project imports are retained warm artifacts, not a cold full-project build.

The pilot took 547.59 seconds with GNU time maximum process RSS 3,330,704 KiB.
The whole successful allocation completed in 687 seconds. Sampled Slurm batch
MaxRSS was 5,523,612 KiB, a different aggregation scope. No generation allocation
remains active, and all 621 earlier preserved paths and the approved prototype
and helper manifests still match.

The [results](results.json), [commands](commands.json), [resources](resources.json),
[terminal allocation](allocations.json), and [dependency identities](dependencies.json)
record the exact scope. The [source manifest](source-sha256.txt) includes both
formatted Python files and every frozen numerical/source input. Formatting and
import ordering affected only the two authorized files; an unused import and
unnecessary f-string prefix were removed from the new emitter.

The [module inventory](module-inventory.json), [ordered module list](proof-modules.txt),
[declaration inventory](declaration-inventory.json), and
[generated source hashes](generated-source-sha256.txt) identify all 59 outputs.
[pilot-artifacts.json](pilot-artifacts.json) identifies the seven fresh objects.
[compact.json.gz](compact.json.gz) is the deterministic pruned artifact. Exact
regeneration checked every generated source byte and the compressed artifact.

The next gates are independent emitter/helper review, complete generated-module
replay, and the handwritten literal Z-sector adapter. Neither the full-set
replay nor that adapter ran in this evaluation. Earlier generation-v1 stopped
at Ruff before any tests or generation; its raw receipts remain private.
