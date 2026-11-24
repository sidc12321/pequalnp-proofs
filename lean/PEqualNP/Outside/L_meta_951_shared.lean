import PEqualNP.Outside.L_meta_951_private

/-!
# Gate lower bounds with heavily shared inputs

The ordinary data inputs can each occur in two rows. The remaining inputs
may occur arbitrarily often, provided each row contains at most one of them.
Restrict those remaining inputs to assignments of Hamming weight at most one.
Treat arbitrary functions of this restricted assignment as free input wires.

A paid binary gate masking a data input shared by two rows cannot be the sole
way that input reaches the outputs. Fix the masking operand at its absorbing
value. At least one of the two rows still has to distinguish the data input
being false from it being true. The projection lemma charges a second gate
along this distinction. Induction charges the incidences of all data inputs.
Padding handles rows without a distinguished input. The circuit simulation
below preserves the project's semantics for invalid and missing wire reads.

The main declarations are at_most_one_shared_per_row, six_rows_bound and
five_outputs. None of them requires an upper bound on the number of NOT gates.
-/ 
namespace Oracle951
open PEqualNP.CircuitLowerBounds
abbrev F (D : Type) := D → Bool

inductive Op
  | conj | disj | inv
  deriving DecidableEq

def Op.val (o : Op) (a b : Bool) : Bool :=
  match o with
  | .conj => a && b
  | .disj => a || b
  | .inv => !a

def gate {D : Type} (o : Op) (f g : F D) : F D := fun d => o.val (f d) (g d)

-- A straight-line proof of simultaneous availability. A NOT ignores its second argument.
inductive Run {D : Type} (T : Set (F D)) : Set (F D) → ℕ → Prop
  | stop {A} (done : T ⊆ A) : Run T A 0
  | step {A k} (o : Op) {f g} (hf : f ∈ A) (hg : g ∈ A) (tail : Run T (insert (gate o f g) A) k) :
      Run T A (k+1)

abbrev D (n : ℕ) (B : Type) := B × (Fin n → Bool)
def raw {n : ℕ} {B : Type} (p : Fin n) : F (D n B) := fun d => d.2 p
def base {n : ℕ} {B : Type} (b : B → Bool) : F (D n B) := fun d => b d.1
def start (n : ℕ) (B : Type) : Set (F (D n B)) :=
  Set.range raw ∪ Set.range base
def pin {n : ℕ} {B : Type} (p : Fin n) (d : D n B) : D n B :=
  (d.1,fun i => if i=p then false else d.2 i)
def cut {n : ℕ} {B : Type} (p : Fin n) (f : F (D n B)) : F (D n B) := fun d => f (pin p d)

private theorem cut_start {n : ℕ} {B : Type} (p : Fin n) {f : F (D n B)} (hf : f ∈ start n B) :
    cut p f ∈ start n B := by
  rcases hf with ⟨q,rfl⟩ | ⟨b,rfl⟩
  · by_cases eq : q=p
    · subst q; exact Or.inr ⟨fun _ => false,by funext d; simp [cut,pin,base,raw]⟩
    · exact Or.inl ⟨q,by funext d; simp [cut,pin,raw,eq]⟩
  · exact Or.inr ⟨b,rfl⟩

private theorem weaken {Ω : Type} {A A' T : Set (F Ω)} {k : ℕ}
    (run : Run T A k) (h : A ⊆ A') : Run T A' k := by
  induction run generalizing A' with
  | stop done => exact .stop (done.trans h)
  | step o hf hg tail ih => exact .step o (h hf) (h hg) (ih (Set.insert_subset_insert h))

-- Project a circuit to a smaller domain, optionally requiring one gate to vanish.
-- If a target separates d,e, that distinction must first arise from a wire
-- already in A or from a gate that reads such a wire.
private theorem project {n : ℕ} {B : Type} {A T A' : Set (F (D n B))} {k : ℕ}
    (run : Run T A k) (p : Fin n) (rep : ∀ f ∈ A, cut p f ∈ A')
    (constants : ∀ b : Bool, (fun _ => b) ∈ A')
    (extra : Bool) (d e : D n B)
    (diff : extra = true → ∃ f ∈ T, f d ≠ f e ∧ f ∉ A)
    (dead : extra = true → ∀ f ∈ A, f d ≠ f e → ∃ b : Bool, cut p f = fun _ => b) :
    ∃ j, Run (cut p '' T) A' j ∧ j + extra.toNat ≤ k := by
  classical
  induction run generalizing A' extra with
  | stop done =>
    have no : extra = false := by
      cases h : extra <;> simp
      obtain ⟨f,hf,_,hn⟩ := diff h; exact hn (done hf)
    refine ⟨0,.stop ?_,by simp [no]⟩
    rintro _ ⟨f,hf,rfl⟩; exact rep f (done hf)
  | @step A k o f g hf hg tail ih =>
    let v := gate o f g
    have proj : cut p v = gate o (cut p f) (cut p g) := rfl
    have keep : ∀ z ∈ insert v A, cut p z ∈ insert (cut p v) A' := by
      rintro _ (rfl | hz)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (rep _ hz)
    by_cases hv : cut p v ∈ A'
    · obtain ⟨j,r,hj⟩ := ih (A' := A') (fun z hz => by
        rcases hz with rfl | hz; exact hv; exact rep _ hz) constants false (by simp) (by simp)
      exact ⟨j,r,by simp at hj; cases extra <;> simp <;> omega⟩
    · have flat (z : F (D n B)) (hz : z ∈ A) (dif : z d ≠ z e) (ex : extra = true) :=
        dead ex z hz dif
      have propagate (ex : extra = true) : v d = v e := by
        by_contra ne
        have block (q : F (D n B)) (b : Bool) (eq : cut p q = fun _ => b)
            (other : F (D n B)) (mem : cut p other ∈ A') (ord : q = f ∧ other = g ∨ q = g ∧ other = f)
            (use : o ≠ .inv ∨ q = f) : False := by
          apply hv
          rw [proj]
          rcases ord with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · cases o <;> cases b <;> simp only [eq,gate,Op.val,Bool.false_and,
              Bool.true_and,Bool.false_or,Bool.true_or,Bool.not_false,Bool.not_true] <;> first | exact mem | apply constants
          · cases o with
            | inv =>
              have same : q = other := use.resolve_left (by simp)
              rw [← same,eq]; exact constants (!b)
            | conj | disj =>
              cases b <;> unfold gate <;> simp only [eq,Op.val,Bool.and_false,Bool.and_true,Bool.or_false,Bool.or_true] <;>
                first | exact mem | apply constants
        by_cases fd : f d = f e
        · have gd : g d ≠ g e := by intro ge; exact ne (by simp [v,gate,fd,ge])
          have notInv : o ≠ .inv := by rintro rfl; exact ne (by simp [v,gate,Op.val,fd])
          obtain ⟨b,hb⟩ := flat g hg gd ex
          exact block g b hb f (rep _ hf) (Or.inr ⟨rfl,rfl⟩) (.inl notInv)
        · obtain ⟨b,hb⟩ := flat f hf fd ex
          exact block f b hb g (rep _ hg) (Or.inl ⟨rfl,rfl⟩) (.inr rfl)
      obtain ⟨j,r,hj⟩ := ih keep (fun b => Set.mem_insert_of_mem _ (constants b)) extra
        (by intro ex; obtain ⟨z,hz,ne,na⟩ := diff ex; exact ⟨z,hz,ne,by
              rintro (rfl | old); exact ne (propagate ex); exact na old⟩)
        (by intro ex z hz ne; rcases hz with rfl | old
            · exact (ne (propagate ex)).elim
            · exact dead ex z old ne)
      rw [proj] at r
      exact ⟨j+1,.step o (rep _ hf) (rep _ hg) r,by omega⟩

def row {n : ℕ} {B : Type} (s : Finset (Fin n)) (h : B → Bool) : F (D n B) :=
  fun d => h d.1 || decide (∃ p ∈ s, d.2 p = true)
private def through {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i)

private theorem erase_sum {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) :
    ∑ i, (S i).card = (∑ i, ((S i).erase p).card) + (through S p).card := by
  classical
  have one i : (S i).card = ((S i).erase p).card + (if i ∈ through S p then 1 else 0) := by
    by_cases h : p ∈ S i
    · simpa [through,h] using (Finset.card_erase_add_one h).symm
    · simp [through,h,Finset.erase_eq_of_notMem h]
  simp [one,Finset.sum_add_distrib]

private theorem cut_row {n : ℕ} {B : Type} (s : Finset (Fin n)) (h : B → Bool) (p : Fin n) :
    cut p (row s h) = row (s.erase p) h := by
  funext d; simp [cut,row,pin,Finset.mem_erase]; grind

private theorem const_mem {n : ℕ} {B : Type} (b : Bool) : (fun _ => b) ∈ start n B :=
  Or.inr ⟨fun _ => b,rfl⟩

private theorem hit_pair {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n)
    (two : 2 ≤ (through S p).card) : ∃ i j, i ≠ j ∧ p ∈ S i ∧ p ∈ S j := by
  obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp two
  exact ⟨i,j,ne,by simpa [through] using hi,by simpa [through] using hj⟩

-- Two tests differ only at p. A target separates them, and the first gate
-- either agrees on the tests or becomes constant when p is set to false.
private def Witness {n m : ℕ} {B : Type} (S : Fin m → Finset (Fin n)) (H : Fin m → B → Bool)
    (p : Fin n) (v : F (D n B)) := ∃ (b : B) (x y : Fin n → Bool) (i : Fin m),
      (∀ j, j ≠ p → x j = y j) ∧
      row (S i) (H i) (b,x) ≠ row (S i) (H i) (b,y) ∧ row (S i) (H i) ≠ v ∧
      (v (b,x) = v (b,y) ∨ ∃ t : Bool, cut p v = fun _ => t)

private theorem masked {n m : ℕ} {B : Type} (S : Fin m → Finset (Fin n)) (H : Fin m → B → Bool)
    (p : Fin n) (v : F (D n B)) (i : Fin m) (b : B) (hb : H i b = false) (hp : p ∈ S i)
    (y : Fin n → Bool) (hy : ∀ q ∈ S i, y q = false)
    (mask : v (b,fun q => decide (q=p) || y q) = v (b,y)) : Witness S H p v := by
  let x := fun q => decide (q=p) || y q
  have ex : ∃ q ∈ S i, x q = true := ⟨p,hp,by simp [x]⟩
  have ey : ¬ ∃ q ∈ S i, y q = true := by grind
  have dif : row (S i) (H i) (b,x) ≠ row (S i) (H i) (b,y) := by simp [row,hb,ex,ey]
  exact ⟨b,x,y,i,by intro q hq; simp [x,hq],dif,by intro eq; exact dif (eq ▸ mask),Or.inl mask⟩

theorem guarded_bound {n m : ℕ} {B : Type} (S : Fin m → Finset (Fin n)) (H : Fin m → B → Bool)
    (zero : ∃ b, ∀ i, H i b = false) (pos : ∀ i, ∃ b, H i b = true)
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (deg : ∀ p, (through S p).card ≤ 2)
    (separate : ∀ p i j, i ≠ j → p ∈ S i → p ∈ S j → ∀ b, H i b = false ∨ H j b = false)
    (k : ℕ) (run : Run (Set.range (fun i => row (S i) (H i))) (start n B) k) :
    ∑ i, (S i).card ≤ k := by
  classical
  obtain ⟨z,hz⟩ := zero
  have noraw i (q : Fin n) : row (S i) (H i) ≠ raw q := by
    obtain ⟨b,hb⟩ := pos i
    intro eq; have t := congrFun eq (b,fun _ => false)
    simp [row,raw,hb] at t
  cases run with
  | stop done =>
    have empty i : S i = ∅ := by
      by_contra! ne
      obtain ⟨p,hp⟩ := ne
      rcases done (Set.mem_range_self i) with ⟨q,e⟩ | ⟨b,e⟩
      · exact noraw i q e.symm
      · have h1 := congrFun e (z,fun _ => true)
        have h2 := congrFun e (z,fun _ => false)
        simp [base,row,hz] at h1 h2; grind
    simp [empty]
  | @step _ k o f g hf hg tail =>
    let v := gate o f g
    have freeGate (ha : v ∈ start n B) : ∑ i, (S i).card ≤ k+1 := by
      have r := weaken tail (Set.insert_subset_iff.mpr ⟨ha,Set.Subset.rfl⟩)
      exact (guarded_bound S H ⟨z,hz⟩ pos lin deg separate k r).trans (by omega)
    have finish (p : Fin n) (ev : cut p v ∈ start n B)
        (wit : 2 ≤ (through S p).card → Witness S H p v) : ∑ i, (S i).card ≤ k+1 := by
      let T := Set.range (fun i => row (S i) (H i))
      let extra := decide (2 ≤ (through S p).card)
      have test : ∃ d e : D n B,
          (extra = true → ∃ a ∈ T, a d ≠ a e ∧ a ∉ insert v (start n B)) ∧
          (extra = true → ∀ a ∈ insert v (start n B), a d ≠ a e → ∃ s : Bool, cut p a = fun _ => s) := by
        by_cases two : 2 ≤ (through S p).card
        · obtain ⟨b,x,y,i,agree,dif,neq,stable⟩ := wit two
          refine ⟨(b,x),(b,y),fun _ => ⟨_,Set.mem_range_self i,dif,?_⟩,?_⟩
          · rintro (eq | ⟨q,eq⟩ | ⟨h,eq⟩)
            · exact neq eq
            · exact noraw i q eq.symm
            · exact dif (by rw [←eq]; rfl)
          · intro _ a ha change'
            rcases ha with rfl | ⟨q,rfl⟩ | ⟨b,rfl⟩
            · exact stable.resolve_left change'
            · by_cases eq : q = p
              · subst q; exact ⟨false,by funext t; simp [cut,raw,pin]⟩
              · exact (change' (agree _ eq)).elim
            · exact (change' rfl).elim
        · exact ⟨(z,fun _=>false),(z,fun _=>false),by simp [extra,two],by simp [extra,two]⟩
      obtain ⟨d,e,diff,dead⟩ := test
      obtain ⟨j,r,len⟩ := project tail p (A' := start n B)
        (by rintro _ (rfl | old); exact ev; exact cut_start p old) const_mem extra d e diff dead
      let S' := fun i => (S i).erase p
      have eqT : cut p '' T = Set.range (fun i => row (S' i) (H i)) := by
        ext a; simp [T,Set.mem_range,S',cut_row]
      change Run (cut p '' T) _ j at r
      rw [eqT] at r
      have lt : j < k+1 := by omega
      have sub i : S' i ⊆ S i := Finset.erase_subset _ _
      have low := guarded_bound S' H ⟨z,hz⟩ pos
        (fun i j ne => (Finset.card_le_card (Finset.inter_subset_inter (sub _) (sub _))).trans (lin i j ne))
        (fun q => (Finset.card_le_card (show through S' q ⊆ through S q by
          intro i hi; simpa [through] using sub i (by simpa [through] using hi : q ∈ S' i))).trans (deg q))
        (fun q i j ne hi hj => separate q i j ne (sub i hi) (sub j hj)) j r
      rw [erase_sum S p]
      change (∑ i, (S' i).card) + _ ≤ _
      have := deg p
      by_cases two : 2 ≤ (through S p).card <;> simp [extra,two] at len <;> omega
    have binary (p : Fin n) (h : F (D n B)) (src : h ∈ start n B) (t : Bool)
        (ev : ∀ d, v d = if t then (d.2 p || h d) else (d.2 p && h d)) :
        (∑ i, (S i).card) ≤ k+1 := by
      rcases src with ⟨q,rfl⟩ | ⟨b,rfl⟩
      · by_cases same : p = q
        · subst q
          apply freeGate; exact Or.inl ⟨p,by funext d; rw [ev]; cases t <;> simp [raw]⟩
        · apply finish p
          · cases t
            · exact Or.inr ⟨fun _ => false,by funext d; simp [cut,ev,pin,base]⟩
            · exact Or.inl ⟨q,by funext d; simp [cut,ev,pin,raw,Ne.symm same]⟩
          · intro two
            obtain ⟨i,j,ne,hi,hj⟩ := hit_pair S p two
            have away : q ∉ S i ∨ q ∉ S j := by
              by_contra! bad
              have lt : 1 < (S i ∩ S j).card := Finset.one_lt_card.mpr
                ⟨p,Finset.mem_inter.mpr ⟨hi,hj⟩,q,Finset.mem_inter.mpr bad,same⟩
              have := lin i j ne; omega
            obtain ⟨a,ap,aq⟩ : ∃ a, p ∈ S a ∧ q ∉ S a := by
              rcases away with h | h; exact ⟨i,hi,h⟩; exact ⟨j,hj,h⟩
            apply masked S H p v a z (hz a) ap (fun u => decide (u=q) && t)
            · intro u hu; have ne : u ≠ q := by rintro rfl; exact aq hu
              simp [ne]
            · rw [ev,ev]; cases t <;> simp [raw,same,Ne.symm same]
      · by_cases able : ∃ s, b s = t
        · obtain ⟨s,hs⟩ := able
          apply finish p
          · cases t
            · exact Or.inr ⟨fun _ => false,by funext d; simp [cut,ev,pin,base]⟩
            · exact Or.inr ⟨b,by funext d; simp [cut,ev,pin,base]⟩
          · intro two; obtain ⟨i,j,ne,hi,hj⟩ := hit_pair S p two
            obtain ⟨a,ap,an⟩ : ∃ a, p ∈ S a ∧ H a s = false := by
              rcases separate p i j ne hi hj s with h | h
              · exact ⟨i,hi,h⟩
              · exact ⟨j,hj,h⟩
            apply masked S H p v a s an ap (fun _ => false) (by simp)
            rw [ev,ev]; cases t <;> simp [base,hs]
        · push Not at able
          apply freeGate; exact Or.inl ⟨p,by
            funext d; rw [ev]; have hn := able d.1; cases t <;> cases hb : b d.1 <;> simp_all [base,raw]⟩
    cases o with
    | inv =>
      rcases hf with ⟨p,rfl⟩ | ⟨b,rfl⟩
      · apply finish p
        · exact Or.inr ⟨fun _ => true,by funext d; simp [cut,v,gate,Op.val,raw,pin,base]⟩
        · intro two
          obtain ⟨i,j,ne,hi,hj⟩ := hit_pair S p two
          refine ⟨z,fun q => decide (q=p),fun _ => false,i,by simp_all,?_,?_,?_⟩
          · simp [row,hz,hi]
          · intro eq; have h := congrFun eq (z,fun _ => false)
            simp [row,hz,v,gate,Op.val,raw] at h
          · exact Or.inr ⟨true,by funext d; simp [cut,raw,v,gate,Op.val,pin]⟩
      · exact freeGate (Or.inr ⟨fun x => !(b x),rfl⟩)
    | conj =>
      rcases hf with ⟨p,rfl⟩ | ⟨a,rfl⟩
      · exact binary p g hg false (by simp [v,gate,Op.val,raw])
      · rcases hg with ⟨p,rfl⟩ | ⟨b,rfl⟩
        · exact binary p (base a) (.inr ⟨a,rfl⟩) false (by simp [v,gate,Op.val,raw,Bool.and_comm])
        · exact freeGate (Or.inr ⟨fun x => a x && b x,rfl⟩)
    | disj =>
      rcases hf with ⟨p,rfl⟩ | ⟨a,rfl⟩
      · exact binary p g hg true (by simp [v,gate,Op.val,raw])
      · rcases hg with ⟨p,rfl⟩ | ⟨b,rfl⟩
        · exact binary p (base a) (.inr ⟨a,rfl⟩) true (by simp [v,gate,Op.val,raw,Bool.or_comm])
        · exact freeGate (Or.inr ⟨fun x => a x || b x,rfl⟩)
termination_by k

private def appendGate {Ω : Type} (w : List (F Ω)) (g : Gate) : List (F Ω) :=
  w ++ [fun d => g.op.eval (g.inputs.map fun k => (w.getD k (fun _ => false)) d)]

private theorem eval_list {Ω : Type} (gs : List Gate) (w : List (F Ω)) (d : Ω) :
    (gs.foldl appendGate w).map (fun f => f d) =
      gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun k => z.getD k false)]) (w.map (fun f => f d)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp only [appendGate,List.map_append,List.map_cons,List.map_nil]
    congr 3
    apply List.map_congr_left
    intro i _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? <;> rfl

private theorem available {Ω : Type} {T A : Set (F Ω)} (gs : List Gate) (w : List (F Ω))
    (ho : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hw : ∀ f ∈ w, f ∈ A) (c : ∀ b : Bool, (fun _ => b) ∈ A)
    (endOK : ∀ t ∈ T, ∃ k, t = (gs.foldl appendGate w).getD k (fun _ => false)) :
    ∃ j, Run T A j ∧ j ≤ gs.length := by
  classical
  have wire (i : ℕ) : w.getD i (fun _ => false) ∈ A := by
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact c false
  induction gs generalizing w A with
  | nil =>
    exact ⟨0,.stop (by intro t ht; obtain ⟨i,rfl⟩ := endOK t ht; exact wire i),by simp⟩
  | cons g gs ih =>
    let a (i : ℕ) := w.getD i (fun _ => false)
    let u : F Ω := fun d => g.op.eval (g.inputs.map fun i => a i d)
    let A' := insert u A
    have inw : ∀ f ∈ appendGate w g, f ∈ A' := by
      intro f hf
      change f ∈ w ++ [u] at hf
      rcases List.mem_append.mp hf with old | new
      · exact Set.mem_insert_of_mem _ (hw f old)
      · exact Or.inl (List.mem_singleton.mp new)
    obtain ⟨j,r,len⟩ := ih (A := A') (appendGate w g) (fun f hf => ho f (by simp [hf])) inw
      (fun b => Set.mem_insert_of_mem _ (c b)) endOK (by
        intro i; by_cases h : i < (appendGate w g).length
        · rw [List.getD_eq_getElem _ _ h]; exact inw _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (by omega)]; exact Set.mem_insert_of_mem _ (c false))
    have skipG (mem : u ∈ A) : ∃ j, Run T A j ∧ j ≤ (g::gs).length :=
      ⟨j,weaken r (Set.insert_subset_iff.mpr ⟨mem,Set.Subset.rfl⟩),by simp; omega⟩
    have useG (o : Op) (f h : F Ω) (mf : f ∈ A) (mh : h ∈ A) (e : u = gate o f h) :
        ∃ j, Run T A j ∧ j ≤ (g::gs).length := by
      change Run T (insert u A) j at r
      rw [e] at r; exact ⟨j+1,.step o mf mh r,by simp; omega⟩
    obtain ⟨ops,sz⟩ := ho g (by simp)
    rcases g with ⟨op,ins⟩
    change op = .and ∨ op = .or ∨ op = .not at ops
    change ins.length ≤ 2 at sz
    rcases ops with rfl | rfl | rfl <;> rcases ins with _ | ⟨i, _ | ⟨l, _ | ⟨b,bs⟩⟩⟩
    all_goals try simp at sz
    all_goals solve
      | exact skipG (c true)
      | exact skipG (c false)
      | apply skipG; convert wire i using 1; funext d; simp [u,a,GateOp.eval]
      | exact useG .inv (a i) (a i) (wire i) (wire i) rfl
      | apply useG .conj (a i) (a l) (wire i) (wire l); funext d; simp [u,gate,Op.val,GateOp.eval]
      | apply useG .disj (a i) (a l) (wire i) (wire l); funext d; simp [u,gate,Op.val,GateOp.eval]


private theorem after_run {Ω : Type} {A T U : Set (F Ω)} {j k : ℕ} (run : Run T A j)
    (cont : ∀ A', A ⊆ A' → T ⊆ A' → Run U A' k) : Run U A (k+j) := by
  induction run with
  | stop done => simpa using cont _ Set.Subset.rfl done
  | step o hf hg tail ih =>
    rw [←Nat.add_assoc]
    exact .step o hf hg (ih (fun A' sub ht => cont A' (fun x hx => sub (Set.mem_insert_of_mem _ hx)) ht))

private theorem pad {Ω : Type} {m : ℕ} (u v h : Fin m → F Ω) (I : Finset (Fin m))
    (eq : ∀ i ∉ I, v i = u i) (change' : ∀ i ∈ I, v i = gate .disj (u i) (h i))
    (A : Set (F Ω)) (orig : ∀ i, u i ∈ A) (gratis : ∀ i, h i ∈ A) :
    Run (Set.range v) A I.card := by
  classical
  suffices go : ∀ J ⊆ I, (∀ i ∉ J, v i ∈ A) → Run (Set.range v) A J.card by
    exact go I (Finset.Subset.refl _) (fun i hi => eq i hi ▸ orig i)
  intro J
  induction J using Finset.induction_on generalizing A with
  | empty => intro _ mem; exact .stop (by rintro _ ⟨i,rfl⟩; exact mem i (by simp))
  | @insert i J hi ih =>
    intro sub mem; rw [Finset.card_insert_of_notMem hi]
    apply Run.step .disj (orig i) (gratis i)
    apply ih _ (fun a => Set.mem_insert_of_mem _ (orig a)) (fun a => Set.mem_insert_of_mem _ (gratis a))
      (fun a ha => sub (Finset.mem_insert_of_mem ha))
    intro a ha
    by_cases e : a = i
    · subst a; rw [change' i (sub (Finset.mem_insert_self _ _))]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (mem a (by simp [e,ha]))

/-- Each nonempty row has at most one member of K. A variable outside K may occur in
up to two rows. The members of K have unrestricted incidence degrees. -/
theorem at_most_one_shared_per_row {n m : ℕ} (S : Fin m → Finset (Fin n)) (K : Finset (Fin n))
    (nonempty : ∀ i, (S i).Nonempty) (one : ∀ i, (S i ∩ K).card ≤ 1)
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (low : ∀ p ∉ K, (Finset.univ.filter (fun i => p ∈ S i)).card ≤ 2)
    (gs : List Gate) (out : Fin m → ℕ)
    (ho : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ i (x : Fin n → Bool), Circuit.eval ⟨gs,out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) : ∑ i, ((S i).card-1) ≤ gs.length := by
  classical
  let B := Option (Fin n ⊕ Fin m)
  let L := fun i => S i \ K
  let H (i : Fin m) (b : B) := decide (∃ q ∈ S i ∩ K, b = some (Sum.inl q))
  let enc (d : D n B) (q : Fin n) := if q ∈ K then decide (d.1 = some (Sum.inl q)) else d.2 q
  let w : List (F (D n B)) := List.ofFn (fun q : Fin n => fun d => enc d q)
  let T := Set.range (fun i => row (L i) (H i))
  have sub i : L i ⊆ S i := Finset.sdiff_subset
  obtain ⟨j,run,size⟩ := available (T := T) (A := start n B) gs w ho
    (by intro f hf; simp [w] at hf; obtain ⟨q,rfl⟩ := hf; by_cases qk : q ∈ K
        · exact Or.inr ⟨fun b => decide (b=some (Sum.inl q)),by funext d; simp [enc,base,qk]⟩
        · exact Or.inl ⟨q,by funext d; simp [enc,raw,qk]⟩)
    const_mem (by
      rintro t ⟨i,rfl⟩; refine ⟨out i,?_⟩; funext d
      have r := he i (enc d)
      have hw : w.map (fun f => f d) = List.ofFn (enc d) := by simp [w,List.map_ofFn,Function.comp_def]
      change (gs.foldl _ (List.ofFn (enc d))).getD (out i) false = _ at r
      rw [←hw,←eval_list gs w d] at r
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map] at r ⊢
      have unify (u : Option (F (D n B))) : ((u.map (fun f => f d)).getD false) = (u.getD (fun _ => false)) d := by cases u <;> rfl
      rw [unify] at r
      rw [r]; simp [row,H,L,enc,Finset.mem_sdiff]; grind)
  let I := Finset.univ.filter (fun i => S i ∩ K = ∅)
  let extra (i : Fin m) (b : B) := decide (i ∈ I ∧ b = some (.inr i))
  let G (i : Fin m) (b : B) := H i b || extra i b
  let U := Set.range (fun i => row (L i) (G i))
  have augmented : Run U (start n B) (I.card+j) := by
    apply after_run run
    intro A subA orig
    apply pad (fun i => row (L i) (H i)) (fun i => row (L i) (G i)) (fun i => base (extra i)) I
    · intro i hi; funext d; simp [G,extra,hi,row]
    · intro i hi; funext d; simp [G,gate,Op.val,row,base]; grind
    · exact fun i => orig (Set.mem_range_self _)
    · exact fun i => subA (Or.inr ⟨extra i,rfl⟩)
  have bound := guarded_bound L G ⟨none,by simp [G,extra,H]⟩
    (by intro i; by_cases mem : i ∈ I
        · exact ⟨some (.inr i),by simp [G,extra,mem]⟩
        · have hn : (S i ∩ K).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa [I] using mem)
          obtain ⟨q,hq⟩ := hn
          exact ⟨some (.inl q),by have h : H i (some (.inl q)) = true := decide_eq_true ⟨q,hq,rfl⟩
                                  simp [G,h]⟩)
    (fun i j ne => (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (lin i j ne))
    (by intro p; by_cases pk : p ∈ K
        · simp [through,L,pk]
        · simpa [through,L,pk] using low p pk)
    (by intro p i l ne pi pl b
        cases b with
        | none => simp [G,extra,H]
        | some arg =>
          cases arg with
          | inr i' => simp [G,extra,H]; grind
          | inl q =>
            have simplify (a : Fin m) : G a (some (.inl q)) = decide (q ∈ S a ∩ K) := by
              unfold G H extra
              have hx : ¬ (a ∈ I ∧ (some (.inl q) : B) = some (.inr a)) := by grind
              rw [decide_eq_false hx,Bool.or_false]; congr 1; apply propext; constructor
              · rintro ⟨r,hr,eq⟩
                have e : q = r := Sum.inl.inj (Option.some.inj eq)
                exact e ▸ hr
              · exact fun h => ⟨q,h,rfl⟩
            simp only [simplify,decide_eq_false_iff_not]
            by_contra! bad
            obtain ⟨qi,qk⟩ := Finset.mem_inter.mp bad.1
            obtain ⟨ql,_⟩ := Finset.mem_inter.mp bad.2
            have m1 : p ∈ S i ∧ p ∉ K := Finset.mem_sdiff.mp pi
            have m2 := Finset.mem_sdiff.mp pl
            have lt : 1 < (S i ∩ S l).card := Finset.one_lt_card.mpr
              ⟨p,Finset.mem_inter.mpr ⟨m1.1,m2.1⟩,q,Finset.mem_inter.mpr ⟨qi,ql⟩,by
                intro e; exact m1.2 (e ▸ qk)⟩
            have := lin i l ne; omega) (I.card+j) augmented
  have cost i : (L i).card = ((S i).card-1) + (if i ∈ I then 1 else 0) := by
    change (S i \ K).card = _
    rw [Finset.card_sdiff,Finset.inter_comm K (S i)]
    have hp := Finset.card_pos.mpr (nonempty i)
    have le := one i
    by_cases h : i ∈ I
    · have e : S i ∩ K = ∅ := by simpa [I] using h
      simp [e,h]; omega
    · have e : (S i ∩ K).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa [I] using h)
      have := Finset.card_pos.mpr e
      simp [h]; omega
  simp only [cost,Finset.sum_add_distrib] at bound
  simp at bound
  omega

-- Three row outputs and three column outputs, with a separate input shared
-- by the three rows and one shared by the three columns.
def sixRows : Fin 6 → Finset (Fin 11) :=
  ![{0,1,2,9},{3,4,5,9},{6,7,8,9},{0,3,6,10},{1,4,7,10},{2,5,8,10}]

theorem six_rows_bound (gs : List Gate) (out : Fin 6 → ℕ)
    (ho : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ i (x : Fin 11 → Bool), Circuit.eval ⟨gs,out i⟩ (List.ofFn x) =
      decide (∃ v ∈ sixRows i, x v = true)) : 18 ≤ gs.length := by
  have h := at_most_one_shared_per_row sixRows {9,10} (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) gs out ho he
  have cost : (∑ i, ((sixRows i).card-1)) = 18 := by decide +kernel
  rwa [cost] at h


-- With five outputs, a non-private row of size four already uses all four
-- other rows to cover its points. None of its points can have degree three.
private theorem avoids_heavy {n m : ℕ} (S : Fin m → Finset (Fin n)) (hm : m ≤ 5)
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (a : Fin m) (large : 4 ≤ (S a).card)
    (covered : ∀ x ∈ S a, ∃ i, i ≠ a ∧ x ∈ S i) (p : Fin n) (mp : p ∈ S a) :
    (through S p).card ≤ 2 := by
  classical
  obtain ⟨b,ba,bp⟩ := covered p ‹p ∈ S a›
  by_contra! high
  obtain ⟨c,hc,out⟩ : ∃ c ∈ through S p, c ∉ ({a,b} : Finset (Fin m)) := by
    by_contra! no
    have := Finset.card_le_card (show through S p ⊆ {a,b} from no)
    have h := Finset.card_insert_le a ({b} : Finset (Fin m)); simp at h; omega
  have cp : p ∈ S c := by simpa [through] using hc
  have cne : c ≠ a ∧ c ≠ b := by simpa using out
  let J := (Finset.univ : Finset (Fin m)) \ {a,b}
  have cover : S a ⊆ J.biUnion (fun i => S a ∩ S i) := by
    intro x hx
    obtain ⟨i,ia,ix⟩ := covered x hx
    by_cases ib : i=b
    · subst i
      have xp : x=p := by
        by_contra ne
        have big : 1 < (S a ∩ S b).card := Finset.one_lt_card.mpr
          ⟨x,Finset.mem_inter.mpr ⟨hx,ix⟩,p,Finset.mem_inter.mpr ⟨‹p ∈ S a›,bp⟩,ne⟩
        have := lin a b ba.symm; omega
      subst x; exact Finset.mem_biUnion.mpr ⟨c,by simp [J,cne.1,cne.2],Finset.mem_inter.mpr ⟨hx,cp⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨i,by simp [J,ia,ib],Finset.mem_inter.mpr ⟨hx,ix⟩⟩
  have cnt : (S a).card ≤ J.card := calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ i ∈ J, (S a ∩ S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ J, 1 := Finset.sum_le_sum (by
      intro i hi; have eq : i ≠ a ∧ i ≠ b := by simpa [J] using hi
      exact lin a i eq.1.symm)
    _ = _ := by simp
  have card : J.card = m-2 := by simp [J,Finset.card_sdiff_of_subset,ba.symm]
  omega

private theorem unique_heavy {n m : ℕ} (S : Fin m → Finset (Fin n)) (hm : m ≤ 5)
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (a : Fin m) (avoid : ∀ p ∈ S a, (through S p).card ≤ 2)
    (p q : Fin n) (hp : 3 ≤ (through S p).card) (hq : 3 ≤ (through S q).card) : p=q := by
  classical
  by_contra ne
  have small : ((through S p) ∩ (through S q)).card ≤ 1 := by
    by_contra! big
    obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp big
    have ei : p ∈ S i ∧ q ∈ S i := by simpa [through] using hi
    have ej : p ∈ S j ∧ q ∈ S j := by simpa [through] using hj
    have hh : 1 < (S i ∩ S j).card := Finset.one_lt_card.mpr
      ⟨p,Finset.mem_inter.mpr ⟨ei.1,ej.1⟩,q,Finset.mem_inter.mpr ⟨ei.2,ej.2⟩,ne⟩
    have := lin i j ij; omega
  have sub : through S p ∪ through S q ⊆ Finset.univ.erase a := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    rintro rfl
    rcases Finset.mem_union.mp hi with h | h
    · have := avoid p (by simpa [through] using h); omega
    · have := avoid q (by simpa [through] using h); omega
  have bound := Finset.card_le_card sub
  have er := Finset.card_erase_add_one (Finset.mem_univ a)
  have un := Finset.card_union_add_card_inter (through S p) (through S q)
  simp only [Finset.card_univ,Fintype.card_fin] at er
  omega

theorem five_outputs {n m : ℕ} (S : Fin m → Finset (Fin n)) (hm : m ≤ 5)
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (he : Pin951.Computes S gs out)
    (ho : ∀ g ∈ gs, Pin951.ok g.op ∧ g.inputs.length ≤ 2) :
    ∑ i, ((S i).card-1) ≤ gs.length := by
  classical
  by_cases sm : ∀ i, (S i).card ≤ 3
  · exact Mixed951.bound S hs sm lin gs ho out he
  push Not at sm
  obtain ⟨a,ha⟩ := sm
  by_cases priv : ∃ p ∈ S a, ∀ j, j ≠ a → p ∉ S j
  · obtain ⟨p,hp,only⟩ := priv
    let T := fun i => (S i).erase p
    have sub i : T i ⊆ S i := Finset.erase_subset _ _
    have ht i : 2 ≤ (T i).card := by
      by_cases e : i=a
      · subst i; have := Finset.card_erase_add_one hp; change 2 ≤ ((S a).erase p).card; omega
      · simpa [T,Finset.erase_eq_of_notMem (only i e)] using hs i
    obtain ⟨fs,o,comp,ops,cost⟩ := Pin951.restrict_input S gs out he ho p
      (fun i => Finset.card_pos.mp (show 0 < (T i).card by have := ht i; omega))
    obtain ⟨g,mem,used⟩ := Pin951.some_read S gs out he a (hs a) p hp
    have saved : 0 < (gs.filter (fun f => decide (Pin951.liveRead p.val f))).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨mem,decide_eq_true used⟩)
    have shorter : fs.length < gs.length := by omega
    have b := five_outputs T hm ht (fun i j ne =>
      (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (lin i j ne)) fs o comp ops
    have orig := Pin951.erase_cost S a p hp (hs a) only
    change (∑ i, ((T i).card-1)) + 1 = _ at orig
    omega
  · push Not at priv
    let K := Finset.univ.filter (fun p => 3 ≤ (through S p).card)
    have avoid := avoids_heavy S hm lin a ha priv
    have smallK : K.card ≤ 1 := by
      by_contra! h
      obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp h
      apply ne; exact unique_heavy S hm lin a avoid p q (by simpa [K] using hp) (by simpa [K] using hq)
    exact at_most_one_shared_per_row S K (fun i => Finset.card_pos.mp (by have := hs i; omega))
      (fun i => (Finset.card_le_card Finset.inter_subset_right).trans smallK) lin
      (fun p np => by have d : ¬3 ≤ (through S p).card := by simpa [K] using np
                      change (through S p).card ≤ 2; omega) gs out ho he
termination_by gs.length

end Oracle951
