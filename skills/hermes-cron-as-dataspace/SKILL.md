---
name: hermes-cron-as-dataspace
description: Replace Hermes' cron scheduler (jobs.py + scheduler.py) with scheduled facts in a Syndicate dataspace. Each scheduled job is an assertion `(scheduled ?id #:at ?time #:cap ?cap)`; an in-vat fiber observes due-time facts and fires the cap. Schedule is queryable, retractable, and persists via vat-snapshot.
type: bridge
parent: hermes-goblins-bridge
row: 12
proto: D
polarity: 0
status: stub
---

# hermes-cron-as-dataspace

Phase 2. Closes the witness-row triplet (mem + session + ctx + cron) all share vat-snapshot + dataspace.

## Hermes signature

`/Users/bob/i/hermes-agent/cron/`

- `scheduler.py` — APScheduler-style loop, due-time wake
- `jobs.py` — job definitions (cronjob_tools surface for the LLM to schedule new jobs)
- `__init__.py` — registry

Authority pattern: **scheduler thread holds direct callable references** (or shell command strings via `cronjob_tools`). Schedule state lives in a JSON file (or in-memory dict) read by the scheduler thread. LLM-scheduled jobs go through `tools/cronjob_tools.py` → `validate_within_dir` (path security) before write.

## Goblins signature

A `^cron-dataspace` actor publishes scheduled facts; an in-vat fiber observes `(scheduled ?id #:at ?t #:cap ?c)` facts and a clock fact `(now ?t)`. When `now ≥ at`, the fiber fires the cap.

```scheme
(define (^cron-dataspace bcom)
  (define ds (spawn ^dataspace))
  (methods
    ((schedule cap #:at when #:repeat (interval #f))
     (define id (mint-id))
     (assert! ds `(scheduled ,id #:at ,when #:cap ,cap
                             #:repeat ,interval))
     id)
    ((unschedule id) (retract! ds `(scheduled ,id . _)))
    ((list-due before)
     (filter (lambda (f) (<= (fact-at f) before))
             (query ds '(scheduled ?id . _)))))

  ;; In-vat fiber — Mandy syscaller-free for clock I/O
  (syscaller-free-fiber
    (lambda ()
      (let loop ()
        (define due (list-due (current-time)))
        (for-each fire! due)
        (sleep 1) (loop)))))

(define (fire! fact)
  (<- (fact-cap fact))
  (if (fact-repeat fact)
      (assert! ds `(scheduled ,(fact-id fact)
                              #:at ,(+ (current-time) (fact-repeat fact))
                              #:cap ,(fact-cap fact)
                              #:repeat ,(fact-repeat fact)))
      (retract! ds `(scheduled ,(fact-id fact) . _))))
```

Scheduled job = a *cap* + a time. LLM schedules by passing a cap it already holds (e.g. a `^revocable` wrapping a tool); cron has no special authority of its own, only the caps it was given.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `cron.add_job(fn, trigger, args)` | `(<- cron 'schedule (spawn ^job-cap fn args) #:at t)` | job is a cap, not a callable string |
| `cron.remove_job(id)` | `(<- cron 'unschedule id)` | retract fact |
| recurring job | `#:repeat seconds` | re-asserts after fire |
| `cronjob_tools` (LLM-facing) | LLM schedules via own caps | cron has no FS / shell authority |
| due-time check | observer in vat | not a thread |
| persistence | vat-snapshot of dataspace | survives crash |
| audit | dataspace query | full schedule + history if logged |

## Failure modes (closed by this bridge)

- **Cron holds shell-command strings = full ambient authority** — cron only holds caps the LLM (or user) handed it; lacks any authority of its own.
- **Scheduler thread = single point of stall** — `syscaller-free-fiber` (Mandy A) for clock; vat queue still drains.
- **Schedule file race on concurrent edit** — vat ordering serializes; no mid-write race.
- **Removed job that already fired this cycle** — fact retraction is atomic; fire-then-retract ordering visible in dataspace.
- **LLM-scheduled job that exceeds intended scope** — job is a cap; if the cap was `^revocable max-uses=1`, it fires once even if scheduled to repeat.

## Failure modes (introduced; must mitigate)

- **Wall-clock vs vat-clock skew on snapshot restore** — restored cron should re-evaluate due-times against current wall-clock, not snapshot-time; otherwise everything fires at restore.
- **Long-running job blocks the fire fiber** — fire via eventual send (`<-`), don't wait; observer pattern handles completion notification.

## Test vector

```python
cron = cron_dataspace()

# Schedule:
job_cap = make_cap(lambda: log.append('fired'))
jid = cron.schedule(job_cap, at=now() + 1, repeat=5)
sleep(2);  assert log == ['fired']
sleep(5);  assert log == ['fired', 'fired']

# Cap with max_uses limits repetition naturally:
once = revocable(job_cap, max_uses=1)
cron.schedule(once, at=now(), repeat=1)
sleep(3);  assert log[-3:] == ['fired', 'fired', 'fired']  # only 1 new fire post-revoke

# Unschedule:
cron.unschedule(jid)
sleep(10); assert no_new_fires_in(log)

# Survive restart:
snap = vat_snapshot(cron)
del cron;  cron2 = vat_restore(snap)
# Pending jobs continue from current wall-clock, not snapshot-time
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Job representation | callable / shell-string | cap |
| Cron's own authority | full (whatever it imports) | only caps it holds |
| Persistence | JSON / in-memory | vat-snapshot |
| Concurrency | scheduler thread | in-vat fiber + observers |
| Schedule audit | grep file | dataspace query, observable live |
| Retract atomicity | rm-from-list race | dataspace retraction |
| Failure mode | "fired with stale args" | cap revocation atomic |

## Test-harness location

`~/i/goblins-adapter/tests/cron-dataspace-bisim.scm` (todo). Probe: schedule + sleep + unschedule + snapshot + restore + verify post-restore behavior matches non-restart timeline (modulo wall-clock translation).

## Status: stub

Phase 2 priority. Closes the four-row D cluster (rows 9, 10, 11, 12). Once shipped, Hermes' time-shifted, persisted, observable surfaces all use one primitive: dataspace + vat-snapshot.
