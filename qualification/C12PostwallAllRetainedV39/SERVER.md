# Server execution

Host: sc01-ssh.gpuhome.cc, port 30388, user root. Workspace: /root/rivermind-data/shao-lean-20261021. Dedicated SSH key is configured; never print or copy it.

PowerShell connection: & C:/Windows/System32/OpenSSH/ssh.exe -F "C:/game/shao lean/tools/ssh_config" shao-server "<remote command>"

For structured exec/SFTP, run C:/Users/UIO/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe -X utf8 "C:/game/shao lean/tools/server.py" with a JSON request on stdin. No password field. Supported exec: {action:exec,command:<shell command>,timeout:120,stdin:<optional data>}; put/get: {action:put|get,files:[{local:<absolute>,remote:<absolute>}]}. Read script for schema. SSH banner failures are transient; bounded retry, then record if persistent.

Before Lean: source /root/rivermind-data/shao-lean-20261021/activate.sh, THEN cd your worktree (activation changes directory). Toolchain leanprover/lean4:v4.36.0-rc1; mathlib 807d3836b165983210ee2ecf3cd28f239436949c. Use the current accepted package view specified below; the old legacy package path is incomplete. Ask root for genuinely missing cache modules; do not run lake update/cache get yourself.

Current accepted package view (2026-10-23): new root worktrees should use the read-only `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages` view already used by accepted integration trees. It has the same pinned mathlib commit and the previously accepted Brownian/bump objects; the legacy `lean/.lake/packages` view lacks some of them. Do not fetch or rebuild modules merely because the legacy view is missing an object. Root-only targeted cache hydration runs from an already configured project worktree via `lake env .lake/packages/mathlib/.lake/build/bin/cache get <exact.module>`, not `lake exe cache` inside the standalone mathlib package, which may unnecessarily materialize its separate dependency directory. Preserve working in-flight environments; apply correct package links at a safe checkpoint.

Before GitHub: source /root/rivermind-data/shao-lean-20261021/github-env.sh. Authenticated randomcat4; private repo randomcat4/shao-lean. Do not inspect tokens. Git pushes currently work best with -c http.version=HTTP/2; bound network operations with timeout.

Source snapshot: /root/rivermind-data/shao-lean-20261021/sources/ (randomcat4/shao@35d4580b61e22e7145f47730045a09874ef93259); supplemental/ includes original paper excerpts. Local read-only source equivalent: C:/game/shao/current/.

Resource policy: server quota40 CPU/200GiB RAM, data disk335GB at setup. Start each lane with at most 4 concurrent Lean processes and 4-core affinity for builds. Total initial budget root+OQ56+OQ4 <=12 concurrent Lean processes; monitor aggregate memory before increasing. Measured ~3.54GiB maximum individual check process; this is not an aggregate peak. No local heavy computation.

## Preferred shared connection (active)

The tools/server.py JSON entry now uses transport_client.py and one persistent SSH connection, at most four concurrent channels across the team. Same exec/put/get request and success schemas; no password. This lowers repeated SSH handshakes. No command or transfer is automatically replayed. If broker_busy is returned, operation_may_have_started=false: wait briefly or do independent work before resubmitting. If operation_may_have_started=true, inspect effects before any retry. Endpoint token is private and must never be printed. The coordinator owns the hidden broker process. Direct native SSH and server_direct.py remain manual fallback only.

## Post-shutdown recovery, 2026-10-22

The coordinator restored the hidden shared broker with SHAO_SSH_CONNECT_IP=182.131.4.61 after the local resolver returned an unusable proxy address. The address was independently checked using Google and Cloudflare DNS over HTTPS; the established original host key remains strictly checked against sc01-ssh.gpuhome.cc, not the numeric route. transport_broker.py accepts this optional connection-address override without changing HOST identity or trust policy. Do not restart a functioning broker or expose its private endpoint token. On another restart, verify the route again rather than assuming this IP is permanent. Bound all network commands; GitHub API is available when Git transport times out. Check effects before replaying uncertain writes.

For this run, push authentication can otherwise wait indefinitely. After sourcing github-env.sh, use a bounded single command with GIT_TERMINAL_PROMPT=0 and git -c credential.helper="!gh auth git-credential". This reuses the existing trusted gh login without displaying credentials or changing global configuration. Verify the frozen remote head before publishing and inspect uncertain effects before any retry.

If inherited URL-scoped credential helpers still wait, clear only the current command helper chain and specify the existing GitHub helper: git -c credential.helper= -c credential.https://github.com.helper= -c credential.https://github.com.helper="!gh auth git-credential". Keep the command bounded. This worked for the accepted v25/v26 publications and does not alter repository/global Git config.

## Resource reservation — 2026-10-22 user instruction

User has a separate 10 CPU / 80 GiB workload. Read-only observation confirms its python/java process family is pinned to CPU0–9. Never terminate, renice, repin or change limits of that workload or unrelated processes. All new project commands avoid0–9: root integration10–13, OQ314–17, OQ418–21, OQ5622–25. Maximum one heavy Lean command per lane at a time, shared by its children; integration one sequential gate. Start conservatively with Lean native -M8192 -j4; do not use8GiB ulimit-v (observed startup thread failure due virtual address reservation). Budget8GiB per Lean process; requests to exceed require coordinator resource scheduling, never weaker proof settings. Preserve80GiB external allowance plus20GiB system headroom (project budgeting target<=100GiB, including concurrent project tasks). Cache is reclaimable and is reported separately. Do not interrupt existing in-flight lane commands merely to change affinity; apply to new commands.

## Current lane resource reassignment — 2026-10-24

User paused OQ3. Its exact writer/execution/no-inflight release was verified before C12 activation. OQ3 no longer executes. New C12 lane uses CPU14–17 and one heavy command under /root/rivermind-data/shao-lean-20261021/locks/c12-heavy.lock, native -M8192 -j4. Active child caps root3/C12 1/OQ4 3/OQ56 2=9; OQ3 prior1 is suspended, not additive. Root10–13/root-heavy.lock and OQ418–21/OQ5622–25 remain. External CPU0–9/80GiB unchanged. See c12-ACTIVATION.json and REGISTRY for exact active owner. All server-only/pinned/read-only-cache restrictions above remain.


## Recovery resource preflight — 2026-10-25 (prepared, not activated)

The human requested resource inspection before resumption. Exact observations and
pending allocation are in coordination/restart-20261025/RESOURCE-CHECKPOINT.json.
The external task now binds all observed threads to CPU0–39 (24 active screening
workers), so the older external0–9 / project10–25 map is invalid for new execution.
The prepared candidate is root40–43, C1244–47, OQ448–51, OQ5652–55; these physical
cores and their SMT siblings are disjoint from the external task's cores. This is
not an active reassignment. The shared quota remains40 CPU /200GiB, external
reservation80GiB and system headroom20GiB. Memory and total CPU usage must be
remeasured and heavy starts staggered; changing CPU IDs does not raise quota.
The shutdown pause, unchanged exclusive owners, lean-pr-90 PAUSED and separate
OQ3 PAUSED_BY_USER all remain in force. Before actual execution read the resource
checkpoint, verify live process/source effects, then activate a current resource
map for the same authorized owners. Do not use the stale10–25 CPU assignments.


## Bilateral resource agreement — 2026-10-25 (application receipt pending)

Verified human authorization in screening chat01a1714c-1d2d-7f70-877c-c15575d2bfe0
allows direct resource negotiation. Root agreed: screeningCPU0–23/24 workers,
Shao Lean reservedCPU40–55 with the lane split above; physical core/SMT groups
are disjoint. Each task has an80GiB process memory budget, with about40GiB
for system/shared cache/scheduling allowance; shared180GiB watchdog and200GiB
hard limit remain. Root never modifies screening configuration or processes.
The screening owner applies and verifies its binding, then Root independently
observes the effect. Until that receipt, its last actual observed affinity is
still0–39. See coordination/restart-20261025/RESOURCE-AGREEMENT.json.
All Shao Lean proof authors/checks and lean-pr-90 remain paused; OQ3's separate
human pause remains. Resource negotiation alone does not activate mathematics.


## Screening application independently verified — 2026-10-25

Resource negotiation is complete. Root's independent server observation at
2026-10-25T04:39:18.635098+00:00 found52 screening-related processes/340 threads
all constrained toCPU0–23,24 unchanged worker identities, persisted/running policy
in agreement,80GiB task and180GiB aggregate guards intact. Root reserved40–55
with the agreed four-lane split,80GiB project process budget, same40 CPU/200GiB
container quota. Exact receipt: coordination/restart-20261025/RESOURCE-AGREEMENT-VERIFIED.json.
This closes the pending application observation above. No Lean execution or
owner/heartbeat resumption occurred. Read current AGENTS.md before later resume.


## Explicit project resumption — 2026-10-25

The human resumed existing authorized lanes. Current activation and initial
resource phase are in coordination/restart-20261025/RESUMPTION-ACTIVATION.json:
Root40–43 and OQ5652–55 may each run one heavy command; C1244–47 first resumes
existing-evidence independent review without a new heavy command. OQ448–51
remains ready/idle, OQ3 remains separately paused. Root A/B share the original
root-heavy.lock. No new execution wrapper is needed. Prior CPU maps in shutdown
archives are historical; current AGENTS/REGISTRY activation governs new commands.


## Actual resumed runtime — 2026-10-25

The current compact state is coordination/restart-20261025/RUNTIME-CHECKPOINT.json.
Actual Lean application threads were observed atCPU40–43. Sleepingio_uring SQ
kernel I/O threads namediou-sqp-* expose0–255 affinity and0CPU seconds; one
owned-TID narrowing returnedEINVAL and is retained. Do not confuse that OS I/O
exception with proof-compute escape, retry it, or modify runtime/cgroups/system.
The observed check11 subsequently returnednaturalrc1; check12 is a new source
attempt, not an uncertain replay. The initial two-heavy phase remains because
current measured memory does not justify three8GiB allowances plus margin.
