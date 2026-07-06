import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Cyclic tag systems
-/

namespace Rule110

structure CyclicTagSystem where
  appendants : List (List Bool)
  deriving Repr

namespace CyclicTagSystem

@[simp] def totalAppendantChars (cts : CyclicTagSystem) : ℕ :=
  (cts.appendants.map List.length).sum

@[simp] def cycleLen (cts : CyclicTagSystem) : ℕ :=
  cts.appendants.length

def cts_step (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) : List Bool × ℕ :=
  match w with
  | [] => ([], idx)
  | a :: rest =>
      let k := cts.cycleLen
      if hk : k = 0 then
        (rest, idx)
      else
        let idx' := (idx + 1) % k
        let hi : idx % k < cts.appendants.length :=
          Nat.mod_lt _ (Nat.pos_of_ne_zero hk)
        let app := cts.appendants[idx % k]'hi
        let w' := if a then rest ++ app else rest
        (w', idx')

/-- `n` CTS steps from `(w, idx)`. -/
def cts_steps (cts : CyclicTagSystem) : ℕ → List Bool → ℕ → List Bool × ℕ
  | 0,     w, idx => (w, idx)
  | n + 1, w, idx =>
    let (w₁, idx₁) := cts.cts_step idx w
    cts_steps cts n w₁ idx₁

def cts_eval (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) : List Bool :=
  (cts_steps cts n w₀ 0).1

/-- `n` CTS steps from `(w₀, idx₀)`; exposes appendant index for Stage 3 encoding hooks. -/
def cts_eval_with_idx (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ := 0) :
    List Bool × ℕ :=
  cts_steps cts n w₀ idx₀

@[simp] theorem cts_eval_with_idx_fst_zero (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) :
    (cts.cts_eval_with_idx n w₀ 0).1 = cts.cts_eval n w₀ := rfl

@[simp] theorem cts_eval_with_idx_zero (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ) :
    cts.cts_eval_with_idx 0 w₀ idx₀ = (w₀, idx₀) := rfl

def cts_halts (cts : CyclicTagSystem) (w₀ : List Bool) : Prop :=
  ∃ n : ℕ, cts.cts_eval n w₀ = []

def cts_computes (cts : CyclicTagSystem) (f : ℕ → ℕ) : Prop :=
  ∃ inputEncode : ℕ → List Bool,
    ∃ outputDecode : List Bool → ℕ,
      ∀ x : ℕ, ∃ steps : ℕ,
        outputDecode (cts.cts_eval steps (inputEncode x)) = f x

private theorem length_le_sum_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · cases ys <;> simp [List.sum_cons]
    · simp only [List.sum_cons]
      exact Nat.le_trans (ih hx') (Nat.le_add_left _ _)

theorem length_getElem_le_total (cts : CyclicTagSystem) {j : ℕ}
    (hj : j < cts.appendants.length) :
    (cts.appendants[j]'hj).length ≤ cts.totalAppendantChars := by
  refine length_le_sum_of_mem ?_
  rw [List.mem_map]
  exact ⟨_, List.getElem_mem hj, rfl⟩

@[simp] theorem cts_steps_zero (cts : CyclicTagSystem) (w : List Bool) (idx : ℕ) :
    cts_steps cts 0 w idx = (w, idx) :=
  rfl

theorem cts_steps_succ (cts : CyclicTagSystem) (n : ℕ) (w : List Bool) (idx : ℕ) :
    cts_steps cts (n + 1) w idx =
      let (w₁, idx₁) := cts.cts_step idx w
      cts_steps cts n w₁ idx₁ :=
  rfl

theorem cts_eval_with_idx_succ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) :
    cts.cts_eval_with_idx (n + 1) w₀ idx₀ =
      let (w₁, idx₁) := cts.cts_step idx₀ w₀
      cts.cts_eval_with_idx n w₁ idx₁ := by
  simp only [cts_eval_with_idx, cts_steps_succ]

@[simp] theorem cts_step_empty (cts : CyclicTagSystem) (idx : ℕ) :
    cts.cts_step idx [] = ([], idx) := by
  simp [cts_step]

/-- Empty CTS word stays empty under `cts_eval_with_idx` (appendant index may advance). -/
theorem cts_eval_with_idx_empty (cts : CyclicTagSystem) (n : ℕ) (idx₀ : ℕ) :
    (cts.cts_eval_with_idx n [] idx₀).1 = [] := by
  induction n with
  | zero => simp [cts_eval_with_idx_zero]
  | succ n ih =>
    rw [cts_eval_with_idx_succ]
    simp only [cts_step_empty]
    exact ih

private theorem cts_steps_fst (cts : CyclicTagSystem) (n : ℕ) (w : List Bool) (idx : ℕ) :
    (cts_steps cts n w idx).1 = (cts.cts_eval_with_idx n w idx).1 := rfl

theorem cts_steps_add (cts : CyclicTagSystem) (m n : ℕ) (w : List Bool) (idx : ℕ) :
    cts_steps cts (m + n) w idx =
      let (w', idx') := cts_steps cts m w idx
      cts_steps cts n w' idx' := by
  induction m generalizing n w idx with
  | zero => simp [cts_steps]
  | succ m ih =>
    rw [Nat.succ_add, cts_steps_succ]
    rcases hstep : cts.cts_step idx w with ⟨w₁, idx₁⟩
    simp only [hstep]
    rw [ih n w₁ idx₁]
    cases hm : cts.cts_steps m w₁ idx₁ with
    | mk w' idx' =>
      simp [hm, cts_steps_succ, hstep]

theorem cts_eval_with_idx_add (cts : CyclicTagSystem) (m n : ℕ) (w : List Bool) (idx : ℕ) :
    cts.cts_eval_with_idx (m + n) w idx =
      let (w', idx') := cts.cts_eval_with_idx m w idx
      cts.cts_eval_with_idx n w' idx' := by
  simp only [cts_eval_with_idx, cts_steps_add]

@[simp] theorem cts_eval_zero (cts : CyclicTagSystem) (w₀ : List Bool) :
    cts.cts_eval 0 w₀ = w₀ := by
  simp [cts_eval]

theorem cts_eval_succ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) :
    cts.cts_eval (n + 1) w₀ =
      let (w₁, idx₁) := cts.cts_step 0 w₀
      (cts_steps cts n w₁ idx₁).1 :=
  rfl

theorem cts_step_length_le (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) :
    (cts.cts_step idx w).1.length ≤ w.length + cts.totalAppendantChars := by
  cases w with
  | nil =>
    simp [cts_step]
  | cons ha ht =>
    rcases happ : cts.appendants with _ | ⟨x, xs⟩
    · simp [cts_step, cycleLen, happ, totalAppendantChars]
    · cases ha with
      | false =>
        simp [cts_step, cycleLen, happ, totalAppendantChars]
        omega
      | true =>
        have hpos : 0 < cts.appendants.length := by simp [happ]
        have hi := Nat.mod_lt idx hpos
        have hall := length_getElem_le_total cts hi
        have hs :
            (cts.cts_step idx (Bool.true :: ht)).1 =
              ht ++ cts.appendants[idx % cts.appendants.length]'hi := by
          simp [cts_step, cycleLen, happ]
        rw [hs, List.length_append, List.length_cons]
        have hsum :
            cts.totalAppendantChars =
              x.length + (List.map List.length xs).sum := by
          simp [totalAppendantChars, happ, List.map_cons, List.sum_cons]
        rw [hsum]
        omega

theorem cts_steps_length_bound (cts : CyclicTagSystem) (n : ℕ) (w : List Bool) (idx : ℕ) :
    (cts_steps cts n w idx).1.length ≤ w.length + n * cts.totalAppendantChars := by
  induction n generalizing w idx with
  | zero => simp [cts_steps]
  | succ n ih =>
    rcases hw : cts.cts_step idx w with ⟨w₁, idx₁⟩
    have hw' := cts_step_length_le cts idx w
    rw [hw] at hw'
    simp only [cts_steps_succ, hw]
    linarith [ih w₁ idx₁, hw']

theorem cts_eval_length_bound (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) :
    (cts.cts_eval n w₀).length ≤ w₀.length + n * cts.totalAppendantChars :=
  cts_steps_length_bound cts n w₀ 0

/-! ### Appendant index evolves predictably when the tape never empties -/

theorem cts_steps_succ_eq_tail (cts : CyclicTagSystem) (n : ℕ) (w : List Bool) (idx : ℕ) :
    cts_steps cts n.succ w idx =
      cts_steps cts n (cts.cts_step idx w).1 (cts.cts_step idx w).2 := by
  rfl

private theorem cts_step_snd_eq_mod_succ (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (hw : w ≠ []) (hk : 0 < cts.cycleLen) :
    (cts.cts_step idx w).2 = (idx + 1) % cts.cycleLen := by
  rcases w with _ | ⟨a, rest⟩
  · exact absurd rfl hw
  · rcases h : cts.appendants with _ | ⟨_, _⟩
    · simp [h, cycleLen] at hk
    · simp [cts_step, cycleLen, h]

/-- During any nonempty trace, each synchronous step advances the appendant cursor by one,
modulo `cycleLen`. -/
theorem cts_steps_snd_eq_idx_add_mod (cts : CyclicTagSystem) (n : ℕ) (w : List Bool) (idx : ℕ)
    (hk : 0 < cts.cycleLen) (hidx : idx < cts.cycleLen)
    (hne : ∀ i < n, (cts_steps cts i w idx).1 ≠ []) :
    (cts_steps cts n w idx).2 = (idx + n) % cts.cycleLen := by
  induction n generalizing w idx with
  | zero =>
    simp only [cts_steps, Nat.add_zero, Nat.mod_eq_of_lt hidx]
  | succ n ih =>
    have hw₀ : w ≠ [] := by
      specialize hne 0 (Nat.zero_lt_succ _)
      simpa [cts_steps] using hne
    rcases w with _ | ⟨a, rest⟩
    · exact absurd rfl hw₀
    · let p := cts.cts_step idx (a :: rest)
      have hsnd : p.2 = (idx + 1) % cts.cycleLen :=
        cts_step_snd_eq_mod_succ cts idx (a :: rest) hw₀ hk
      have idx₁_lt : p.2 < cts.cycleLen := by
        rw [hsnd]
        exact Nat.mod_lt _ hk
      have hchild : ∀ i < n, (cts_steps cts i p.1 p.2).1 ≠ [] := by
        intro i hi
        rw [← cts_steps_succ_eq_tail]
        exact hne (Nat.succ i) (Nat.succ_lt_succ hi)
      specialize ih p.1 p.2 idx₁_lt hchild
      calc
        (cts_steps cts n.succ (a :: rest) idx).2
            = (cts_steps cts n p.1 p.2).2 := by simp [cts_steps_succ_eq_tail, p]
        _ = (p.2 + n) % cts.cycleLen := ih
        _ = ((idx + 1) % cts.cycleLen + n) % cts.cycleLen := by simp [hsnd]
        _ = (idx + 1 + n) % cts.cycleLen := by rw [Nat.mod_add_mod]
        _ = (idx + n.succ) % cts.cycleLen := by
          simp only [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

/-- Starting from appendant index `0`, after `n` nonempty steps the cursor is `n mod cycleLen`. -/
theorem cts_steps_snd_zero_start_eq_mod (cts : CyclicTagSystem) (n : ℕ) (w : List Bool)
    (hk : 0 < cts.cycleLen)
    (hne : ∀ i < n, (cts_steps cts i w 0).1 ≠ []) :
    (cts_steps cts n w 0).2 = n % cts.cycleLen := by
  simpa using cts_steps_snd_eq_idx_add_mod cts n w 0 hk hk hne

end CyclicTagSystem

end Rule110
