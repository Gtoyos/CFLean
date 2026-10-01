import Std

/-! Deterministic asynchronous atomic-register machine. A scheduler chooses one
process per transition; omission of a process forever models a crash. There is
no fairness assumption.

This generic machine has registers only.  The universal constructions are run
by the concrete machines `WeakUniversal.Forward.frun` and
`HelpingUniversal.Forward.frun`, which follow the same discipline — a local
computation followed by at most one atomic access per step — and add the
client's invocation inputs and Algorithm 2's atomic snapshot objects
(`ForwardGCA`).  Their runs are linked to `Execution`, and to the admitted
model, by `forward1_admitted` and `forward3_admitted`. -/
namespace ConflictFreedom.SharedMemory

/-- What a process does next: a local computation, a register read (continuing
with the value read), or a register write. -/
inductive Action (Register Value Local : Type) where
  | local (next : Local)
  | read (register : Register) (next : Value → Local)
  | write (register : Register) (value : Value) (next : Local)

/-- An algorithm: initial local states and memory, and each process's next
action as a function of its local state. -/
structure Algorithm (n : Nat) (Register Value Local : Type) where
  initialLocal : Fin n → Local
  initialMemory : Register → Value
  instruction : Fin n → Local → Action Register Value Local

/-- Every process's local state and the contents of every register. -/
structure Configuration (n : Nat) (Register Value Local : Type) where
  localState : Fin n → Local
  memory : Register → Value

variable {n : Nat} {Register Value Local : Type}

private def update {α β : Type} [DecidableEq α] (f : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else f j

/-- The algorithm's initial configuration. -/
def initial (a : Algorithm n Register Value Local) : Configuration n Register Value Local :=
  ⟨a.initialLocal, a.initialMemory⟩

/-- A local computation followed by at most one atomic register access. -/
def step [DecidableEq Register] (a : Algorithm n Register Value Local)
    (c : Configuration n Register Value Local) (p : Fin n) :
    Configuration n Register Value Local :=
  match a.instruction p (c.localState p) with
  | .local next => ⟨update c.localState p next, c.memory⟩
  | .read r next => ⟨update c.localState p (next (c.memory r)), c.memory⟩
  | .write r v next => ⟨update c.localState p next, update c.memory r v⟩

/-- The run in which `schedule t` takes step `t`. -/
def run [DecidableEq Register] (a : Algorithm n Register Value Local)
    (schedule : Nat → Fin n) : Nat → Configuration n Register Value Local
  | 0 => initial a
  | t + 1 => step a (run a schedule t) (schedule t)

theorem other_process_unchanged [DecidableEq Register]
    (a : Algorithm n Register Value Local) (c : Configuration n Register Value Local)
    (p q : Fin n) (h : q ≠ p) : (step a c p).localState q = c.localState q := by
  unfold step
  split <;> simp [update, h]

theorem read_memory_unchanged [DecidableEq Register]
    (a : Algorithm n Register Value Local) (c : Configuration n Register Value Local)
    (p : Fin n) (r : Register) (next : Value → Local)
    (h : a.instruction p (c.localState p) = .read r next) :
    (step a c p).memory = c.memory := by
  simp [step, h]

theorem write_other_register_unchanged [DecidableEq Register]
    (a : Algorithm n Register Value Local) (c : Configuration n Register Value Local)
    (p : Fin n) (r r' : Register) (v : Value) (next : Local)
    (h : a.instruction p (c.localState p) = .write r v next) (hne : r' ≠ r) :
    (step a c p).memory r' = c.memory r' := by
  simp [step, h, update, hne]

end ConflictFreedom.SharedMemory
