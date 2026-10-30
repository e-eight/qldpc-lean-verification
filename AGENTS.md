# Repository Guidelines

## Project Structure and Module Organization

- `lean/QldpcVerification/` contains active Lean proofs built on QECLean. `Bicycle/` and `Lattice/` hold family theory; `Input/` contains matrix specifications and generated certificates.
- `scripts/` contains Python generators, numerical screens, and cluster helpers. `tests/` contains pytest regressions and `fixtures/`.
- `data/` stores dated evidence and evaluation records. `archive/QldpcCert/` preserves the independently audited earlier proof.

Use README.md for current capabilities and commands, RECOMMENDATIONS.md for research priorities, CHECKS_AND_RESULTS.md for historical evidence, and CERTIFICATES.md for packing mathematics.

## Build, Test, and Development Commands

Use Python 3.13 and `uv`. Clone [upstream qldpc-challenge](https://github.com/unitaryfoundation/qldpc-challenge) at `../qldpc-challenge`, or set `QLDPC_REPO` to another path.

```bash
uv sync --locked                         # Install pinned dependencies
uv run --locked ruff check .              # Lint Python
uv run --locked ruff format --check .     # Check formatting
uv run --locked pytest                    # Run regressions
```

For a full Lean build, submit from the staged cluster workspace:

```bash
bash scripts/cluster/submit.sh --cpus-per-task=2 --mem=48G
```

Run Lean only in detached allocations with enforced memory and swap limits. Local runs use one Lean thread. See `lean/README.md` for bounded replay instructions.

## Coding Style and Naming Conventions

Use four-space Python indentation, a 100-character line limit, and Ruff configuration from `pyproject.toml`. Keep scripts and functions in `snake_case`.

Use two-space Lean proof indentation and PascalCase module filenames. Follow surrounding namespace and declaration conventions. Build on QECLean definitions and preserve pinned dependencies. Regenerate input modules through their generators rather than editing certificate data manually.

## Testing Guidelines

Name pytest files `test_*.py` and functions `test_*`. Add focused regressions for changed behavior, including malformed certificates and integer-rounding boundaries. Preserve byte-for-byte regeneration checks.

For proof changes, run the guarded axiom audit and record source hashes and resource limits. Capstones must not depend on `sorryAx` or `native_decide`.

## Commit and Pull Request Guidelines

Use concise imperative subjects, such as “Retain integer rounding in packing candidate screening.” Describe the problem, resulting behavior, mathematical hypotheses, and validation in pull requests. Link relevant issues and identify upstream input revisions. Distinguish numerical evidence from kernel proofs.

## Configuration and Records

Keep cluster credentials, accounts, hosts, private paths, and raw logs under ignored `.local/`. Preserve historical datasets and logs; place new experiments in separate dated directories. Do not modify archived proof sources during routine development.
