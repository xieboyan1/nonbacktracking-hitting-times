import Gap
namespace Gap
open Finset Stationary Walks Fundamental
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V) (a : V)
def hitPort : Port V := fun s => w G a s.1 s.2
def hitBar := fresh G a (w G a)
def meanIn (f : Port V) (i : V) := (∑ j ∈ G.N i,f (j,i))/deg G i
def err (i j : V) := if i=a then w G a j i-meanIn G (hitPort G a) i else 0
lemma bias_sum : es G (fun i _ => bias G a i)=0 := by
  have mid : es G (fun i _ => (if i=a then (1:ℝ) else 0)) = deg G a := by
    rw [show (fun (i _ : V) => if i=a then (1:ℝ) else 0) = (fun i j => indicator a (i,j)) from rfl]
    exact (div_left_inj' (vol_pos G a).ne').mp (indmass G a)
  have one := tot_const G 1
  change es G (fun _ _ => 1) = vol G*1 at one
  simp only [bias,es,div_eq_mul_inv,sum_sub_distrib,←sum_mul] at mid one ⊢
  rw [mid,one]; unfold piV; field_simp [(vol_pos G a).ne',(dp G a).ne']
lemma hit_bar : ∀ i, bar G (hitPort G a) i=hitBar G a i := by
  intro i
  have e := (from_bellman (raw G a)).center i
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul] at e
  apply (div_eq_iff (dp G i).ne').mpr
  change (∑ j ∈ G.N i, w G a i j) = fresh G a (w G a) i * deg G i
  unfold deg; linarith
lemma killed_row (i : V) :
    ∑ j ∈ G.N i,(hitBar G a i-w G a j i-bias G a i)=0 := by
  let r := fun i => ∑ j ∈ G.N i,(hitBar G a i-w G a j i-bias G a i)
  have off (i : V) (hi : i≠a) : r i=0 := by
    dsimp [r]; simp only [hitBar,fresh,hi,if_false,bias,zero_div,sub_zero,
      sum_sub_distrib,sum_const,nsmul_eq_mul]
    change deg G i * _ - _ - deg G i*1=0
    field_simp [(dp G i).ne']
  by_cases hi : i=a
  · subst i
    have e : ∑ i,r i=0 := by
      have eq₁ := flip G (fun i j => w G a i j)
      have eq₂ : es G (fun i _ => hitBar G a i) = es G (fun i j => w G a i j) := by
        apply sum_congr rfl; intro i _
        change (∑ _j ∈ G.N i,hitBar G a i) = _
        rw [←hit_bar G a i,sum_const,nsmul_eq_mul]
        exact (sumBar G (hitPort G a) i).symm
      have eq₃ := bias_sum G a
      simp only [r,es,sum_sub_distrib] at eq₁ eq₂ eq₃ ⊢
      linarith
    rw [sum_eq_single a (fun i _ hi => off i hi) (by simp)] at e; exact e
  · exact off i hi
lemma full_row (hd : Mindeg G) (hb : Branching G) (i : V) :
    ∑ j ∈ G.N i,(bar G (sol G hd hb a) i-sol G hd hb a (j,i)-bias G a i)=0 := by
  let f := sol G hd hb a
  have e := sum_congr (s₁:=G.N i) rfl (fun j _ => sol_poisson G hd hb a (i,j))
  change ∑ j ∈ G.N i,(f (i,j)-F G f (i,j)) = ∑ _j ∈ G.N i,bias G a i at e
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,balance G hd,sumBar G f i] at e ⊢
  exact sub_eq_zero.mpr e
def make (hd : Mindeg G) (hb : Branching G) : Data G a := by
  let f := sol G hd hb a
  let U := bar G f
  let z := central G f
  let u := hitBar G a
  let v := fun i j => w G a i j-u i
  have R := from_bellman (raw G a)
  have fr := full_row G a hd hb
  have fp (i j : V) (hj : j ∈ G.N i) : (deg G i-1)*z i j+f (j,i)-U i+bias G a i=0 := by
    have ep := at_port G hd f hj
    have ps := sol_poisson G hd hb a (i,j)
    have er := fr i
    simp only [sum_sub_distrib,sum_const,nsmul_eq_mul] at er
    change deg G i*U i - (∑ j ∈ G.N i,f (j,i)) - deg G i*bias G a i=0 at er
    change f (i,j)-F G f (i,j)=bias G a i at ps
    change (deg G i-1)*(f (i,j)-U i)+f (j,i)-U i+bias G a i=0
    rw [sub_eq_iff_eq_add.mp ps]; nlinarith only [ep,er]
  have ua : u a=0 := R.ua
  have Ua : U a=0 := by simp [U,f,solbar]
  refine { x := fun i => u i-U i, U := U, eta := fun i j => v i j-z i j, z := z,
           e := err G a, anchor := by rw [ua,Ua,sub_zero], cent := ?_, centZ := centered G f,
           harm := ?_, full := ?_, fullPort := ?_, source := ?_, support := ?_, stop := ?_ }
  · intro i
    rw [sum_sub_distrib,centered G f]; simpa [v,u,hitBar] using R.center i
  · intro i
    have eq₁ := killed_row G a i
    have eq₂ := fr i
    simp only [v,z,central,U,sum_sub_distrib] at *
    change _ = 0
    linarith only [eq₁,eq₂]
  · intro i
    simp only [z,central,U,sub_sub_sub_cancel_right]
    convert fr i using 2
  · intro i j hj
    have pe := fp i j hj
    dsimp only [z,U,central] at pe ⊢
    linarith only [pe]
  · intro i j hj
    by_cases hi : i=a
    · subst i
      have er := killed_row G a a
      simp only [sum_sub_distrib,sum_const,nsmul_eq_mul] at er
      change deg G a*u a - _ - deg G a*bias G a a=0 at er
      have mn : meanIn G (hitPort G a) a = -bias G a a := by
        apply (div_eq_iff (dp G a).ne').mpr
        change (∑ j ∈ G.N a,w G a j a)=_
        rw [ua] at er; nlinarith only [er]
      have va : v a j = 0 := R.va j hj
      simp only [err,if_pos rfl,mn,ua,Ua,sub_zero,sub_self,va,zero_sub]
      have pe := fp a j hj
      dsimp only [v,z,central,U,if_true] at pe ⊢
      have zero : bar G f a = 0 := Ua
      simp only [ite_true,neg_neg]
      nlinarith only [pe,zero]
    · have ep := R.port i hi j hj
      have ep' : (deg G i-1)*v i j+w G a j i-u i+1=0 := by
        dsimp [v,u,hitBar]; linarith only [ep]
      simp only [err,hi,if_false]
      have pe := fp i j hj
      simp only [bias,hi,if_false,zero_div,sub_zero] at pe
      dsimp only [v,z,central,U] at pe ep' ⊢
      linarith only [ep',pe]
  · intro i hi j _; simp [err,hi]
  · intro j hj; have va : v a j=0 := R.va j hj; rw [va,zero_sub]
end
end Gap
