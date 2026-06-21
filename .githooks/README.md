# Git hooks for this Lean project

`pre-commit` runs `lake build` as a hard gate when staged changes touch Lean
sources or build config — a red tree cannot be committed. Incremental, so it is
a no-op (seconds) when the project is already green.

Enabled per-clone via `core.hooksPath` (see below). Bypass a single commit with
`git commit --no-verify` (e.g. notes-only commits) — never to dodge a real failure.

Fresh clone / lean-yolo-box setup:

    git config core.hooksPath .githooks
