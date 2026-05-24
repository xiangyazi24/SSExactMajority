# SSExactMajority HANDOFF SOP

Status: v2, active unless superseded by a later committed SOP.
Date: 2026-05-13

## Principle

Git handoff files are the authoritative communication channel.
Tmux messages are the notification channel. A tmux ping is considered
successfully notified once it is submitted or queued in Claude Code. The git
handoff file remains authoritative for task content.

## Channels

### Zinan -> Codex

Write requests to:

`HANDOFF/inbox/YYYY-MM-DD-zinan-NNN-topic.md`

Then commit and push.

### Codex -> Zinan

Write results/replies to:

`HANDOFF/outbox/YYYY-MM-DD-codex-NNN-topic.md`

Then commit and push.

## Required Handoff Fields

Every inbox/outbox file should include:

- sender
- receiver
- topic
- requested action or completed result
- verification command(s), if any
- remaining blockers
- lock status, if any project file was locked

## Notification

After pushing a handoff file, send a one-line tmux ping only as a nudge.

Current SSExactMajority target:

`zinan:family`

Reason: tmux metadata on 2026-05-13 showed `zinan:family` with title
`Continue SSExactMajority lean formalization`; `zinan:dm` was on an unrelated
ppsim task.

Ping format:

- `Zinan: inbox NNN ready`
- `Codex: outbox NNN ready`

Use explicit carriage return, not the symbolic `Enter` key name:

```bash
tmux send-keys -t zinan:family C-u 'Codex: outbox NNN ready' C-m
```

`C-u` clears any stale unsubmitted input in that pane. `C-m` is the intended
submit key, but Claude Code may still leave the message in the compose box or
queue it behind an active task.

Delivery states:

1. `typed`: text is visible in the input box. Not delivered.
2. `queued`: Claude Code shows "Press up to edit queued messages". Notification delivered.
3. `processed`: Claude writes a reply or an ack file. Content acknowledged.

State 2 is enough for the notification step. State 3 is required only when the
workflow needs explicit acknowledgement.

If text is left in the input box, a bare `tmux send-keys -t zinan:family Enter`
may move it to the queue. If the pane shows a queued-message marker, the
notification succeeded. Do not interrupt Claude's active task with `esc` unless
the handoff is urgent and Xiang explicitly asks for interruption.

For communication tests, include a nonce and require an ack file.

## Ack Rule

A handoff content is considered acknowledged only when one of these happens:

1. The receiver commits and pushes a reply file.
2. The receiver explicitly asks for the next action in the same git channel.

No ack means no content acknowledgement, even if tmux notification succeeded.
If Xiang manually forwards a ping, record that fact in the next outbox instead
of treating Codex's failed tmux attempt as delivered.

## Locking

Before editing a shared Lean file, create:

`HANDOFF/locks/<filename>.lock`

For short local work, the lock may stay uncommitted and must be deleted before
the final commit.

For long exclusive ownership, commit and push the lock, then remove it in the
final commit.

## Verification

## Lean Proof Integrity (2026-05-19 updated, 11-point standard)

A theorem is "proved" only when ALL of the following hold:

1. **0 sorry** — including nested in structure fields, have blocks, by blocks
2. **0 custom axiom** — only propext, Classical.choice, Quot.sound allowed. Verify with `#print axioms`
3. **0 assumption-structure escape** — don't package unproved conclusions as structure/hypothesis parameters
4. **0 trivially true** — conclusion cannot be True/trivial
5. **0 Prop-hypothesis escape** — don't use `def X : Prop` as a function parameter to avoid proving X internally
6. **End-to-end theorem required** — final theorem inputs are only primitive mathematical objects (protocol, process, initial data), no intermediate lemma conclusions
7. **Interface minimality** — hypothesis parameters must be a minimal set; derivable ones must be internalized
8. **Counterexample check** — if a sorry persists, check if the statement is FALSE before continuing
9. **Full repo build passes**
10. **Axiom audit** — `#print axioms` on final theorems
11. **Honest reporting** — distinguish "unconditionally proved", "conditional on X (X proved)", "conditional on X (X open)"

Forbidden substitutes:

- replacing a theorem by `def ... : Prop`
- weakening the theorem statement to make it trivially true
- adding `axiom`, `unsafe`, `admit`, or equivalent proof bypasses
- moving the mathematical burden into an input hypothesis, document, or handoff note instead of proving the stated theorem
- claiming "0 sorry" when sorry is hidden in assumption structures

If a theorem is too strong for the current hypotheses, record the precise
missing lemma or false hypothesis, then continue by proving honest supporting
lemmas. Do not report the `sorry` as cleared until the original theorem is
proved as a theorem.

For `BurmanProof.lean` work:

Minimum:

`lake env lean SSExactMajority/Convergence/BurmanProof.lean`

When touching imports, wrappers, or shared lemmas:

`lake build SSExactMajority.Convergence.BurmanProof`

Report exact commands in the outbox.

## Current Communication Test

Outbox test:

`HANDOFF/outbox/2026-05-13-codex-015-comm-test-and-sop.md`

Nonce:

`codex-comm-test-2026-05-13-015-ssmajority`

Result as of Codex local check: no ack commit found after a short wait.
Correction from Xiang: previous tmux attempts did not submit because the Enter
keystroke was not actually delivered; use `C-m` going forward.
Follow-up observation: a bare `Enter` moved the text from compose box to a queued
message while Claude was busy. Xiang confirmed that queued counts as successful
notification.
