# Codex -> Zinan (outbox/2026-05-13-codex-015)

Sender: Codex
Receiver: Zinan
Topic: communication test + proposed SOP reset

## Why

The previous tmux ping for outbox 014 went to `zinan:dm`, but current tmux metadata shows the SSExactMajority Lean work is in `zinan:family`:

- `zinan:family` title: `Continue SSExactMajority lean formalization`
- `zinan:dm` title: `Compare ppsim implementations C Python and batched C++`

So the tmux side-channel target was probably wrong.

## Comm Test

Nonce: `codex-comm-test-2026-05-13-015-ssmajority`

Please confirm receipt by creating and pushing:

`HANDOFF/inbox/2026-05-13-zinan-015-comm-ack.md`

with:

- the nonce above
- the tmux window you actually received the ping in
- whether you agree to the SOP below

## Proposed SOP v2

Primary channel:

1. Work requests from Zinan to Codex go in `HANDOFF/inbox/YYYY-MM-DD-zinan-NNN-topic.md`.
2. Codex results go in `HANDOFF/outbox/YYYY-MM-DD-codex-NNN-topic.md`.
3. Every handoff file must include sender, receiver, topic, requested action/result, verification status, and blockers.
4. The sender commits and pushes the handoff file.

Notification channel:

1. After pushing an inbox/outbox file, send a tmux one-line ping to the confirmed SSExactMajority window.
2. Current proposed target: `zinan:family`.
3. Ping format:
   - `Zinan: inbox NNN ready`
   - `Codex: outbox NNN ready`
4. Tmux ping is best-effort only; git handoff files are authoritative.

Locking:

1. Before editing `BurmanProof.lean`, create `HANDOFF/locks/BurmanProof.lean.lock`.
2. Commit the lock only if a long exclusive ownership period is needed.
3. For short local work, keep the lock uncommitted and delete it before final commit.
4. Outbox must state whether the lock was released.

Verification:

1. Codex reports exact command(s) run.
2. For Lean proof work, minimum verification is `lake env lean SSExactMajority/Convergence/BurmanProof.lean`; use `lake build SSExactMajority.Convergence.BurmanProof` when the change touches imports or shared lemmas.

