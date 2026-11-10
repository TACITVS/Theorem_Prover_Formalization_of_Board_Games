# Mandatory Agent Execution Rules: Long-Running Jobs & State Checkpointing

## Rule 1: Zero Uncheckpointed Long-Running Computation
Any computational task, solver, verifier, or search script expected or observed to run for more than 60 seconds MUST strictly satisfy the following criteria:

1. **Granular Real-Time Progress Reporting:**
   - Must output frequent progress updates (every 1–5 seconds or at every major branch/depth increment).
   - Reports must include: current depth/ply, total states visited, states per second, active candidate branch, and elapsed time.
   - The user must never be left in the dark about how long a run will take or where it currently is in the state tree.

2. **Persistent Checkpointing & Resumption to Disk:**
   - Long-running searches must periodically serialize their state to disk (e.g., `checkpoint.bin`, `checkpoint.json`, or a persistent transposition cache) every 30–60 seconds and at the completion of every depth level.
   - The tool must support a `--resume` flag (or automatic resume from checkpoint) so that if interrupted, stopped, or killed by the user, **ZERO compute, CPU time, or progress is lost**.

3. **Upfront Runtime & State Complexity Estimates:**
   - Before launching any deep search or verification pass (e.g., depth > 6), provide an upfront estimate of the branching factor, anticipated node count, and expected wall-clock time.
   - Ask the user for confirmation if a run is projected to take more than a few minutes.

4. **Graceful Interruption & Resource Safety:**
   - Must handle termination signals cleanly without corrupting checkpoints or leaving orphaned background tasks.
   - Never tie up the user's CPU/RAM without full visibility and control.
