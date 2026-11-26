import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact first-hitting times on C23 with chord {0,8}. Lean/mathlib v4.19.0.
The final theorem is about limits of partial sums of survival probabilities.
Certificate entries below are data. Their origin plays no role in the proof. -/
namespace Chord23
noncomputable section
open Filter
open scoped Topology BigOperators

abbrev V := Fin 23
-- The tag records the previous vertex: fresh, left, right, or chord.
abbrev State := V × Fin 4
def chord (v : V) : Option V := if v = 0 then some 8 else if v = 8 then some 0 else none
def previous (s : State) : Option V :=
  if s.2 = 0 then none else if s.2 = 1 then some (s.1 + 22)
  else if s.2 = 2 then some (s.1 + 1) else chord s.1

def moves (s : State) : List State :=
  [(s.1 + 1, 1), (s.1 + 22, 2)] ++ (chord s.1).toList.map (fun v => (v, 3))
def choices (nb : Bool) (s : State) : List State :=
  if nb then (moves s).filter (fun t => some t.1 != previous s) else moves s

-- A uniform six-way draw samples a list of length 1, 2 or 3 uniformly.
theorem choice_lengths : ∀ (b : Bool) (s : State),
    (choices b s).length = 1 ∨ (choices b s).length = 2 ∨ (choices b s).length = 3 := by decide
def next (b : Bool) (s : State) (k : Fin 6) : State :=
  let xs := choices b s
  xs[k.val % xs.length]!
def total {α : Type} [Add α] (f : Fin 6 → α) : α :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5
def alive (s : State) : ℝ := if s.1 = 1 then 0 else 1
def K (b : Bool) (f : State → ℝ) (s : State) : ℝ :=
  if s.1 = 1 then 0 else total (fun k => f (next b s k)) / 6

-- P(T > 0) is one precisely off the target. Each iteration adds one draw.
def survival (b : Bool) : ℕ → State → ℝ
  | 0 => alive
  | n+1 => K b (survival b n)

-- A word fixes every random draw through the prescribed time horizon.
def Word : ℕ → Type
  | 0 => Unit
  | n+1 => Fin 6 × Word n
def count : (n : ℕ) → (Word n → Bool) → ℕ
  | 0, p => if p () then 1 else 0
  | n+1, p => total (fun k => count n (fun w => p (k,w)))
def avoids (b : Bool) : (n : ℕ) → State → Word n → Bool
  | 0, s, _ => s.1 != 1
  | n+1, s, w => (s.1 != 1) && avoids b n (next b s w.1) w.2
theorem count_none (n : ℕ) : count n (fun _ => false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [count, total, ih]
theorem word_probability (b : Bool) (n : ℕ) : ∀ s,
    survival b n s = (count n (avoids b n s) : ℝ) / 6^n := by
  induction n with
  | zero => intro s; by_cases hs : s.1 = 1 <;> simp [survival, alive, count, avoids, hs]
  | succ n ih =>
    intro s
    by_cases hs : s.1 = 1
    · simp [survival, K, count, avoids, hs, total, count_none]
    · have hb : (s.1 != 1) = true := bne_iff_ne.mpr hs
      simp [survival, K, count, avoids, hs, hb, total, ih, pow_succ]
      ring

def den (b : Bool) : ℕ := if b then 6 else 143
def values (b : Bool) : Array ℕ :=
  if b then #[
    86, 52, 126, 80,
    0, 0, 0, 0,
    78, 150, 6, 78,
    78, 144, 12, 78,
    78, 138, 18, 78,
    78, 132, 24, 78,
    78, 126, 30, 78,
    78, 120, 36, 78,
    90, 114, 64, 92,
    103, 136, 70, 103,
    103, 130, 76, 103,
    103, 124, 82, 103,
    103, 118, 88, 103,
    103, 112, 94, 103,
    103, 106, 100, 103,
    103, 100, 106, 103,
    103, 94, 112, 103,
    103, 88, 118, 103,
    103, 82, 124, 103,
    103, 76, 130, 103,
    103, 70, 136, 103,
    103, 64, 142, 103,
    103, 58, 148, 103]
  else #[
    4735, 4735, 4735, 4735,
    0, 0, 0, 0,
    1843, 1843, 1843, 1843,
    3400, 3400, 3400, 3400,
    4671, 4671, 4671, 4671,
    5656, 5656, 5656, 5656,
    6355, 6355, 6355, 6355,
    6768, 6768, 6768, 6768,
    6895, 6895, 6895, 6895,
    8753, 8753, 8753, 8753,
    10325, 10325, 10325, 10325,
    11611, 11611, 11611, 11611,
    12611, 12611, 12611, 12611,
    13325, 13325, 13325, 13325,
    13753, 13753, 13753, 13753,
    13895, 13895, 13895, 13895,
    13751, 13751, 13751, 13751,
    13321, 13321, 13321, 13321,
    12605, 12605, 12605, 12605,
    11603, 11603, 11603, 11603,
    10315, 10315, 10315, 10315,
    8741, 8741, 8741, 8741,
    6881, 6881, 6881, 6881]
def num (b : Bool) (s : State) := (values b)[4*s.1.val+s.2.val]!
def h (b : Bool) (s : State) : ℝ := (num b s : ℝ) / den b

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem rows : ∀ (b : Bool) (s : State),
    6 * num b s = (if s.1 = 1 then 0 else
      6 * den b + total (fun k => num b (next b s k))) := by decide
theorem bounded : ∀ (b : Bool) (s : State), num b s ≤ 256 * den b := by decide
theorem den_pos (b : Bool) : 0 < (den b : ℝ) := by cases b <;> norm_num [den]

theorem bellman (b : Bool) (s : State) : h b s = alive s + K b (h b) s := by
  have hr := rows b s
  have hd := den_pos b
  by_cases hs : s.1 = 1
  · simp [hs] at hr
    simp [h, alive, K, hs, hr]
  · simp only [hs, if_false, total] at hr
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hr
    push_cast at hc
    simp only [h, alive, K, hs, if_false, total]
    field_simp
    nlinarith only [congrArg (fun x : ℝ => x * (den b : ℝ)) hc]

theorem h_le (b : Bool) (s : State) : h b s ≤ 256 := by
  apply (div_le_iff₀ (den_pos b)).2
  exact_mod_cast bounded b s
theorem h_nonneg (b : Bool) (s : State) : 0 ≤ h b s :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt (den_pos b))

theorem monoK (b : Bool) {f g : State → ℝ} (hh : ∀ t, f t ≤ g t) (s : State) :
    K b f s ≤ K b g s := by
  unfold K
  split
  · exact le_rfl
  · unfold total
    gcongr <;> apply hh

theorem scaleK (b : Bool) (c : ℝ) (f : State → ℝ) (s : State) :
    K b (fun t => c * f t) s = c * K b f s := by
  unfold K
  split <;> (simp [total]; try ring)

theorem subK (b : Bool) (f g : State → ℝ) (s : State) :
    K b (fun t => f t - g t) s = K b f s - K b g s := by
  unfold K
  split <;> (simp [total]; try ring)

def remn (b : Bool) : ℕ → State → ℝ
  | 0 => h b
  | n+1 => K b (remn b n)

theorem telescope (b : Bool) (n : ℕ) :
    ∀ s, survival b n s = remn b n s - remn b (n+1) s := by
  induction n with
  | zero => intro s; change alive s = h b s - K b (h b) s; linarith [bellman b s]
  | succ n ih =>
    intro s
    change K b (survival b n) s = K b (remn b n) s - K b (remn b (n+1)) s
    rw [funext ih, subK]

theorem tail_bound (b : Bool) (n : ℕ) :
    ∀ s, 0 ≤ remn b n s ∧ remn b n s ≤ (255/256 : ℝ)^n * h b s := by
  induction n with
  | zero => intro s; simp [remn, h_nonneg]
  | succ n ih =>
    intro s
    have hz := monoK b (f := fun _ => 0) (fun t => (ih t).1) s
    have hu := monoK b (fun t => (ih t).2) s
    have hk : K b (h b) s ≤ (255/256 : ℝ) * h b s := by
      have he := bellman b s
      by_cases hs : s.1 = 1
      · simp only [K, hs, if_true]
        exact mul_nonneg (by norm_num) (h_nonneg b s)
      · simp [alive, hs] at he
        linarith [h_le b s]
    constructor
    · simpa [K, total] using hz
    · change K b (remn b n) s ≤ _
      rw [scaleK] at hu
      rw [pow_succ, mul_assoc]
      exact hu.trans (mul_le_mul_of_nonneg_left hk (by positivity))

theorem partial_tail (b : Bool) (n : ℕ) (s : State) :
    (∑ k ∈ Finset.range n, survival b k s) = h b s - remn b n s := by
  induction n with
  | zero => simp [remn]
  | succ n ih => rw [Finset.sum_range_succ, ih, telescope b n s]; ring

-- E[T] = sum over n >= 0 of P(T > n) for a nonnegative integer hitting time.
def HasMean (b : Bool) (s : State) (a : ℝ) : Prop :=
  Tendsto (fun n => ∑ k ∈ Finset.range n, survival b k s) atTop (𝓝 a)
theorem mean (b : Bool) (s : State) : HasMean b s (h b s) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ)
    (r := 255/256) (by norm_num) (by norm_num)
  have hb := hp.mul_const (h b s)
  have hr : Tendsto (fun n => remn b n s) atTop (𝓝 0) :=
    squeeze_zero (fun n => (tail_bound b n s).1) (fun n => (tail_bound b n s).2) (by simpa using hb)
  unfold HasMean
  simp_rw [partial_tail]
  simpa using (tendsto_const_nhds (x := h b s)).sub hr

def start : State := (2, 0)
-- Verify the sampler against an independent edge predicate. Count all six
-- equally likely outcomes for each proposed next vertex.
def adjacent (v w : V) : Bool :=
  (w == v+1) || (v == w+1) || ((v == 0) && (w == 8)) || ((v == 8) && (w == 0))
theorem graph_checks :
    (∀ v : V, adjacent v v = false) ∧
    (∀ v w : V, adjacent v w = adjacent w v) ∧
    (∀ v : V, adjacent v (v+1) = true) := by decide
theorem connected (v w : V) :
    Relation.ReflTransGen (fun x y => adjacent x y = true) v w := by
  have along (n : ℕ) : Relation.ReflTransGen (fun x y => adjacent x y = true) v (v + (n : V)) := by
    induction n with
    | zero => simp only [Nat.cast_zero, add_zero]; exact .refl
    | succ n ih =>
      simpa [Nat.cast_succ, add_assoc] using ih.tail (graph_checks.2.2 (v + (n : V)))
  simpa using along (w-v).val
def legal (b : Bool) (s : State) (w : V) : Bool :=
  adjacent s.1 w && (!b || some w != previous s)
theorem uniform_moves : ∀ (b : Bool) (s : State) (w : V),
    (choices b s).length * total (fun k => if (next b s k).1 = w then 1 else 0) =
      (if legal b s w then 6 else 0) := by decide
theorem records_previous : ∀ (b : Bool) (s : State) (k : Fin 6),
    previous (next b s k) = some s.1 := by decide

theorem witness :
    HasMean true start 13 ∧ HasMean false start (1843/143) ∧
    (13 : ℝ) - 1843/143 = 16/143 ∧ (1843/143 : ℝ) < 13 := by
  have hn : num true start = 13 * den true := by decide
  have hs : 143 * num false start = 1843 * den false := by decide
  have nval : h true start = 13 := by rw [h, hn]; norm_num [den]
  have sval : h false start = 1843/143 := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hs
    push_cast at hcast
    unfold h
    have hd := den_pos false
    field_simp
    linarith
  exact ⟨nval ▸ mean true start, sval ▸ mean false start, by norm_num, by norm_num⟩

theorem refutes_pointwise : ¬ ∀ (v : V) (n r : ℝ),
    HasMean true (v,0) n → HasMean false (v,0) r → n ≤ r := by
  intro claim
  exact (not_le_of_gt witness.2.2.2) (claim 2 _ _ witness.1 witness.2.1)

-- The stationary-start experiment uses vertex mass degree/48, still with
-- an empty initial memory and the same fixed target.
def degree (v : V) := (moves (v,0)).length
theorem volume : ∑ v : V, degree v = 48 := by decide
def weightedNum (b : Bool) := ∑ v : V, degree v * num b (v,0)
def HasStationaryMean (b : Bool) (a : ℝ) : Prop :=
  Tendsto (fun n => (∑ v : V, (degree v : ℝ) *
    ∑ k ∈ Finset.range n, survival b k (v,0)) / 48) atTop (𝓝 a)
theorem averaged (b : Bool) :
    HasStationaryMean b ((weightedNum b : ℝ) / den b / 48) := by
  have hl : Tendsto (fun n => ∑ v : V, (degree v : ℝ) *
      ∑ k ∈ Finset.range n, survival b k (v,0)) atTop
      (𝓝 (∑ v : V, (degree v : ℝ) * h b (v,0))) :=
    tendsto_finset_sum _ (fun v _ => (mean b (v,0)).const_mul (degree v : ℝ))
  have eqn : (∑ v : V, (degree v : ℝ) * h b (v,0)) = (weightedNum b : ℝ) / den b := by
    simp [weightedNum, h, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rw [eqn] at hl
  exact hl.div_const 48
theorem stationary_witness :
    HasStationaryMean true (1087/72) ∧ HasStationaryMean false (51907/858) ∧
    (1087/72 : ℝ) < 51907/858 := by
  have hn : weightedNum true = 4348 := by decide
  have hs : weightedNum false = 415256 := by decide
  constructor
  · convert averaged true using 1; rw [hn]; norm_num [den]
  constructor
  · convert averaged false using 1; rw [hs]; norm_num [den]
  · norm_num

#print axioms uniform_moves
#print axioms connected
#print axioms records_previous
#print axioms witness
#print axioms refutes_pointwise
#print axioms word_probability
#print axioms stationary_witness
end
end Chord23
