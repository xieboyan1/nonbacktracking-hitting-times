import Branch
import Mathlib.Tactic.FinCases
namespace Theta
open Branch Filter
open scoped Topology
noncomputable section
-- The four corridors are A--target, target--B, A--B, and a second
-- A--B corridor. The eight directed corridors have indices 0,...,7.
-- Even indices point as just listed; the following odd index reverses them.
abbrev D := Fin 8
def rev : D → D := ![1,0,3,2,5,4,7,6]
def len (m n : ℕ) : D → ℕ := ![1,1,m+2,m+2,1,1,n+2,n+2]
def sz (m n : ℕ) (d : D) : 0 < len m n d := by fin_cases d <;> simp [len]
lemma revlen (m n : ℕ) (d : D) : len m n (rev d) = len m n d := by fin_cases d <;> rfl
abbrev S (m n : ℕ) := (d : D) × Fin (len m n d)
-- State (d,k) has already traversed k+1 edges after entering corridor d.
def enter (m n : ℕ) (d : D) : S m n := ⟨d,0,sz m n d⟩
def endpoint (m n : ℕ) (b : Bool) (d : D) : Row (S m n) :=
  let e := enter m n
  match d.val with
  | 0 | 3 => .hit
  | 1 => if b then .two (e 4) (e 6) else .three (e 0) (e 4) (e 6)
  | 5 => if b then .two (e 0) (e 6) else .three (e 0) (e 4) (e 6)
  | 7 => if b then .two (e 0) (e 4) else .three (e 0) (e 4) (e 6)
  | 2 => if b then .two (e 5) (e 7) else .three (e 3) (e 5) (e 7)
  | 4 => if b then .two (e 3) (e 7) else .three (e 3) (e 5) (e 7)
  | _ => if b then .two (e 3) (e 5) else .three (e 3) (e 5) (e 7)
def kernel (m n : ℕ) (b : Bool) (s : S m n) : Row (S m n) :=
  let d := s.1
  let k := s.2.val
  if h : k+1 < len m n d then
    let fwd : S m n := ⟨d,k+1,h⟩
    let back : S m n := ⟨rev d,len m n d-(k+1),by rw [revlen]; omega⟩
    if b then .one fwd else .two fwd back
  else endpoint m n b d
def delta (L Q : ℝ) := (Q+1)*L+2*Q+1
def A (L Q : ℝ) := ((Q+2)*((Q+1)*L+Q)+(Q+1)*L*(Q+L+1))/delta L Q
def B (L Q : ℝ) := ((2*Q+1)*L*(Q+L+1)+(Q+1)*L*(Q+2))/delta L Q
def left (L Q : ℝ) : D → ℝ := ![A L Q,0,0,B L Q,A L Q,B L Q,A L Q,B L Q]
def right (L Q : ℝ) (d : D) := left L Q (rev d)
def interp (U V l x : ℝ) := ((l-x)*U+x*V)/l + x*(l-x)
-- NB continuation at the terminal, conditional on the incoming corridor.
def ends (L Q : ℝ) : D → ℝ :=
  let ad := (3+L+2*Q)/3
  let aq := (L+Q+4)/3
  let bd := (L+Q+aq)/2
  let bq := (L+1+ad)/2
  ![0,(1+bd+Q+bq)/2,(1+ad+Q+aq)/2,0,bd,ad,bq,aq]
def value (m n : ℕ) (b : Bool) (s : S m n) : ℝ :=
  let l : ℝ := len m n s.1
  let x : ℝ := s.2.val+1
  let L : ℝ := m+2
  let Q : ℝ := n+2
  if b then l-x+ends L Q s.1 else interp (left L Q s.1) (right L Q s.1) l x
lemma delta_pos {L Q : ℝ} (l : 0<L) (q : 0<Q) : 0 < delta L Q := by unfold delta; positivity
lemma positive_val (m n : ℕ) (b : Bool) (s : S m n) : 0 ≤ value m n b s := by
  rcases s with ⟨d,k⟩
  have hk : (k.val : ℝ)+1 ≤ len m n d := by exact_mod_cast k.isLt
  have hh := sub_nonneg.mpr hk
  have dp : 0 < delta ((m:ℝ)+2) ((n:ℝ)+2) := delta_pos (by positivity) (by positivity)
  have lp (i : D) : 0 ≤ left ((m:ℝ)+2) ((n:ℝ)+2) i := by
    fin_cases i <;> simp [left,A,B] <;> positivity
  have ep (i : D) : 0 ≤ ends ((m:ℝ)+2) ((n:ℝ)+2) i := by
    fin_cases i <;> simp [ends] <;> positivity
  cases b
  · simp only [value,Bool.false_eq_true,if_false,interp,right]
    exact add_nonneg (div_nonneg (add_nonneg (mul_nonneg hh (lp _))
      (mul_nonneg (by positivity) (lp _))) (by positivity)) (mul_nonneg (by positivity) hh)
  · exact add_nonneg hh (ep d)
lemma sr_interior (U V l x : ℝ) (hl : l ≠ 0) :
    interp U V l x = 1+(interp U V l (x+1)+interp V U l (l-x+1))/2 := by
  unfold interp; field_simp; ring
lemma revrev (d : D) : rev (rev d) = d := by fin_cases d <;> rfl
lemma sr_end_eq (L Q : ℝ) (l : 0<L) (q : 0<Q) :
    A L Q = 1+(interp (A L Q) 0 1 1 + interp (A L Q) (B L Q) 1 1 +
      interp (A L Q) (B L Q) Q 1)/3 ∧
    B L Q = 1+(interp (B L Q) 0 L 1 + interp (B L Q) (A L Q) 1 1 +
      interp (B L Q) (A L Q) Q 1)/3 := by
  have d := (delta_pos l q).ne'
  unfold interp A B
  constructor <;> field_simp [l.ne',q.ne',d] <;> unfold delta <;> ring
set_option maxHeartbeats 2000000
lemma bellman (m n : ℕ) (b : Bool) (s : S m n) :
    value m n b s = (kernel m n b s).cost + (kernel m n b s).apply (value m n b) := by
  rcases s with ⟨d,k⟩
  by_cases inside : k.val+1 < len m n d
  · have subcast : ((len m n d - (k.val+1) : ℕ) : ℝ) =
        (len m n d : ℝ) - (k.val+1) := by push_cast [Nat.cast_sub inside.le]; rfl
    cases b
    · simp only [kernel,inside,dif_pos,Bool.false_eq_true,if_false,Row.apply,Row.cost,
        value,subcast,revlen,right,revrev,Nat.cast_add,Nat.cast_one]
      apply sr_interior
      exact_mod_cast (sz m n d).ne'
    · simp [kernel,inside,value,Row.cost,Row.apply]; ring
  · have eq : k.val+1 = len m n d := by have := k.isLt; omega
    have eq' : (k.val : ℝ)+1 = len m n d := by exact_mod_cast eq
    have sr := sr_end_eq ((m:ℝ)+2) ((n:ℝ)+2) (by positivity) (by positivity)
    have atEnd (U V t : ℝ) (ht : t ≠ 0) : interp U V t t = V := by simp [interp,ht]
    have ht : ((len m n d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (sz m n d).ne'
    simp only [kernel,inside,dif_neg,value,eq',sub_self,zero_add,atEnd _ _ _ ht]
    cases b <;> fin_cases d <;>
      simp [endpoint, enter, Row.cost, Row.apply, value, left, right, rev, ends, len] at * <;>
      first | exact sr.1 | exact sr.2 | ring

-- From x, one step along the arm hits the target, the other advances
-- to coordinate 2 on the target-to-B corridor of length L=m+2.
def second (m n : ℕ) : S m n := ⟨2,1,by simp [len]⟩
def fromX (m n : ℕ) (b : Bool) (t : ℕ) :=
  1 + trunc (kernel m n b) t (second m n) / 2
def ordinaryFormula (p q : ℝ) :=
  p-2+((2*q+1)*p+3*q^2+4*q+2)/((p+1)*q+p)
def nbFormula (p q : ℝ) := (4*p+3*q+1)/6
theorem means (m n : ℕ) (b : Bool) : Tendsto (fromX m n b) atTop
    (𝓝 (if b then nbFormula (m+3) (n+2) else ordinaryFormula (m+3) (n+2))) := by
  have lim := certificate (kernel m n b) (value m n b) (positive_val m n b) (bellman m n b) (second m n)
  have ans : 1+value m n b (second m n)/2 =
      (if b then nbFormula (m+3) (n+2) else ordinaryFormula (m+3) (n+2)) := by
    have dd := (delta_pos (L:=(m:ℝ)+2) (Q:=(n:ℝ)+2) (by positivity) (by positivity)).ne'
    cases b <;> simp [value,second,interp,left,right,rev,len,ends,A,B,ordinaryFormula,nbFormula] <;>
      field_simp [dd] <;> first | (unfold delta; ring) | ring
  rw [← ans]
  exact (lim.div_const 2).const_add 1
def scaled (t : ℝ) := (3+4*t+t^2)*(1+t+t^2)/(6*(4+t+3*t^2-t^3+2*t^4))
def ratio (p : ℝ) := nbFormula p (p^2) / ordinaryFormula p (p^2)
lemma normalize_ratio (p : ℝ) (hp : 3 ≤ p) : ratio p / p = scaled p⁻¹ := by
  have pp : 0 < p := by linarith
  have den : 0 < (p+1)*p^2+p := by positivity
  have hs : 0 < ordinaryFormula p (p^2) := by
    unfold ordinaryFormula
    have := div_pos (show 0 < (2*p^2+1)*p+3*(p^2)^2+4*p^2+2 by positivity) den
    linarith
  have invp : 0 < p⁻¹ := inv_pos.mpr pp
  have small : p⁻¹ ≤ 1 := (inv_le_one₀ pp).mpr (by linarith)
  have poly : 0 < 4+p⁻¹+3*p⁻¹^2-p⁻¹^3+2*p⁻¹^4 := by
    nlinarith [mul_nonneg (sq_nonneg p⁻¹) (sub_nonneg.mpr small), sq_nonneg (p⁻¹^2)]
  unfold scaled ratio
  apply (div_eq_div_iff pp.ne' (mul_pos (by norm_num) poly).ne').mpr
  apply (div_mul_eq_mul_div _ _ _).trans ?_
  apply (div_eq_iff hs.ne').mpr
  unfold ordinaryFormula nbFormula
  field_simp [pp.ne',den.ne']; ring
theorem ratio_asymptotic : Tendsto (fun m : ℕ => ratio ((m:ℝ)+3)/((m:ℝ)+3)) atTop (𝓝 (1/8)) := by
  have tp : Tendsto (fun m : ℕ => (m:ℝ)+3) atTop atTop :=
    tendsto_atTop_mono (show ∀ m : ℕ, (m:ℝ) ≤ (m:ℝ)+3 from fun m => by linarith) tendsto_natCast_atTop_atTop
  have cont : ContinuousAt scaled 0 := by unfold scaled; fun_prop (disch := norm_num)
  have t := cont.tendsto.comp (tendsto_inv_atTop_zero.comp tp)
  have eqn (m : ℕ) := normalize_ratio ((m:ℝ)+3) (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  simp_rw [eqn]
  simpa only [Function.comp_def, show scaled 0 = 1/8 by norm_num [scaled]] using t
theorem ratio_unbounded : Tendsto (fun m : ℕ => ratio ((m:ℝ)+3)) atTop atTop := by
  have tp : Tendsto (fun m : ℕ => (m:ℝ)+3) atTop atTop :=
    tendsto_atTop_mono (show ∀ m : ℕ, (m:ℝ) ≤ (m:ℝ)+3 from fun m => by linarith) tendsto_natCast_atTop_atTop
  have t := ratio_asymptotic.pos_mul_atTop (by norm_num) tp
  have eqn (m : ℕ) := div_mul_cancel₀ (ratio ((m:ℝ)+3)) (show (m:ℝ)+3 ≠ 0 by positivity)
  simpa only [eqn] using t
#print axioms means
#print axioms ratio_unbounded
-- n+2 is the length of the long bypass, p=m+3 is the other cycle path.
def squareLong (m : ℕ) := (m+3)^2-2
theorem square_family : ∃ N S : ℕ → ℝ,
    (∀ m, Tendsto (fromX m (squareLong m) true) atTop (𝓝 (N m)) ∧
          Tendsto (fromX m (squareLong m) false) atTop (𝓝 (S m))) ∧
    Tendsto (fun m => N m / S m / ((m:ℝ)+3)) atTop (𝓝 (1/8)) ∧
    Tendsto (fun m => N m / S m) atTop atTop := by
  refine ⟨fun m => nbFormula (m+3) ((m+3)^2),fun m => ordinaryFormula (m+3) ((m+3)^2),
    ?_,ratio_asymptotic,ratio_unbounded⟩
  intro m
  have hn : squareLong m+2=(m+3)^2 := by
    unfold squareLong; apply Nat.sub_add_cancel
    exact le_trans (by decide : 2 ≤ 3^2) (Nat.pow_le_pow_left (by omega) 2)
  have realLen : (squareLong m:ℝ)+2=((m:ℝ)+3)^2 := by exact_mod_cast hn
  constructor
  · simpa [realLen] using means m (squareLong m) true
  · simpa [realLen] using means m (squareLong m) false
#print axioms square_family
end
end Theta
