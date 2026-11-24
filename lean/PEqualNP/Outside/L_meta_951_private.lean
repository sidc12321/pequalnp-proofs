import PEqualNP.Outside.L_meta_951_incidence
/-!
# Removing private inputs from the one-NOT Boolean sum problem

Let p belong to exactly one requested row, of size at least three, and assume
all other rows have size at least two. Set p to false. Scan the original
circuit in evaluation order, keeping for each old wire either a Boolean
constant or the index of a surviving wire. Missing references mean false at
the time the old gate is read. Apply foldGate below. An emitted gate has the
same operation as the old gate, and reads only surviving wires. An alias or
constant costs zero gates. Induction on the scan gives the old values on the
restricted inputs. All reduced rows are nonconstant, so each output has a
surviving wire (possibly a raw input). The number of NOT gates cannot increase.

At least one gate disappears. Otherwise, consider the first gate effectively
reading the raw input p. Here AND and OR effectively read all their listed
operands, and NOT reads only its head. Such a gate exists: absent any such
gate, every gate value is independent of p by induction. No raw input or
missing wire equals the OR of the original row of size at least three.
At that first read the reference for p is a literal. An AND or OR of at most
two operands with a literal always folds, and so does a NOT with literal head.
This contradicts emission of every gate. If the original format requires an
index in the gate list to witness the at-most-one-NOT budget, the restricted
circuit has a gate whenever any surviving row has at least two inputs.

Thus any lower bound for the reduced family lifts by one, precisely the
decrease in the target sum (erase_cost). Repeatedly choose a row larger than
three and delete one private input. For at most four total rows, has_private
always supplies such an input. Row sizes stay at least two and pairwise
intersection sizes cannot grow. The sum of the row sizes decreases, so the
process reaches a family of width at most three, covered by Mixed951.bound.
In particular the four-row profile (4,4,3,3) needs ten gates; this conclusion
does not assume any particular arrangement of its intersections.

More generally the same peeling works with any number of rows if every row
has at most three input points that are also used by another row.

The scan, restriction, and private-input induction are verified below.
The second proof, degree_two, also handles shared inputs: fixing an input
read by two separate gates eliminates both. In the first binary gate with
two distinct raw operands, one operand can mask the other. If the masked
input belongs to two nontrivial rows, one of them excludes the masking
input. That row distinguishes assignments the first gate cannot distinguish.
Some later gate must therefore read the masked input directly. A first NOT
can be charged together with a later read of its raw input or of its output.
The proof allows arbitrary numbers of inverters.
-/
namespace Pin951
open PEqualNP.CircuitLowerBounds

inductive Ref where
  | lit (b : Bool)
  | wire (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

def read (w : List Bool) : Ref → Bool
  | .lit b => b
  | .wire k => w.getD k false

-- A folded gate is either an alias or an actual gate to emit.
def binary (op : GateOp) (neutral : Bool) : Ref → Ref → Ref ⊕ Gate
  | .lit b, r | r, .lit b => .inl (if b = neutral then r else .lit b)
  | .wire i, .wire j => .inr ⟨op,[i,j]⟩

def foldGate (o : GateOp) (args : List Ref) : Ref ⊕ Gate :=
  match o with
  | .and | .or =>
    let e := (match o with | .and => true | _ => false)
    match args with
    | [] => .inl (.lit e)
    | [r] => .inl r
    | r::s::_ => binary o e r s
  | .not => match args with
    | [] => .inl (.lit true)
    | .lit b::_ => .inl (.lit (!b))
    | .wire i::_ => .inr ⟨.not,[i]⟩
  | _ => .inl (.lit false)

def val (w : List Bool) : Ref ⊕ Gate → Bool
  | .inl r => read w r
  | .inr g => g.op.eval (g.inputs.map fun i => w.getD i false)

def ok (o : GateOp) := o = .and ∨ o = .or ∨ o = .not

theorem fold_spec (w : List Bool) (o : GateOp) (args : List Ref)
    (ho : ok o) (hl : args.length ≤ 2) :
    val w (foldGate o args) = o.eval (args.map (read w)) ∧
    (∀ g, foldGate o args = .inr g → g.op = o ∧ g.inputs.length ≤ 2 ∧
      ∀ r ∈ args, (∀ b, r ≠ .lit b) ∨ (o = .not ∧ r ≠ args.head!)) := by
  obtain rfl | rfl | rfl := ho <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try cases a
  all_goals try cases b
  all_goals try casesm* Bool
  all_goals simp_all [foldGate,binary,val,read,GateOp.eval]
/-- Four outputs suffice to force a private input in every row of size at least four. -/
theorem has_private {n m : ℕ} (S : Fin m → Finset (Fin n)) (a : Fin m)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (hm : m ≤ (S a).card) :
    ∃ p ∈ S a, ∀ j, j ≠ a → p ∉ S j := by
  classical
  by_contra! bad
  let I := (Finset.univ : Finset (Fin m)).erase a
  have cover : S a ⊆ I.biUnion (fun j => S a ∩ S j) := by
    intro p hp
    obtain ⟨j,hj,hm⟩ := bad p hp
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,
      Finset.mem_inter.mpr ⟨hp,hm⟩⟩
  have lt : (S a).card ≤ I.card := calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ j ∈ I, (S a ∩ S j).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ I, 1 := Finset.sum_le_sum (fun j hj => h a j (Finset.mem_erase.mp hj).1.symm)
    _ = _ := by simp
  have eq : I.card + 1 = m := by simpa [I] using Finset.card_erase_add_one (Finset.mem_univ a)
  omega

/-- One deletion from a row of size at least two decreases the target by exactly one. -/
theorem erase_cost {n m : ℕ} (S : Fin m → Finset (Fin n)) (a : Fin m) (p : Fin n)
    (hp : p ∈ S a) (ha : 2 ≤ (S a).card) (priv : ∀ j, j ≠ a → p ∉ S j) :
    (∑ j, ((S j).erase p).card.sub 1) + 1 = ∑ j, ((S j).card - 1) := by
  classical
  have e (j : Fin m) : (S j).card - 1 = ((S j).erase p).card - 1 + (if j = a then 1 else 0) := by
    by_cases eq : j = a
    · subst j
      have := Finset.card_erase_add_one hp
      simp; omega
    · simp [eq,Finset.erase_eq_of_notMem (priv j eq)]
  simp [e,Finset.sum_add_distrib]


def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def liveRead (p : ℕ) (g : Gate) : Prop :=
  match g.op with
  | .not => g.inputs.head? = some p
  | _ => p ∈ g.inputs

instance (p : ℕ) (g : Gate) : Decidable (liveRead p g) := by
  unfold liveRead; split <;> infer_instance

def valid (bound : ℕ) : Ref → Prop
  | .lit _ => True
  | .wire k => k < bound

private theorem fold_valid (bound : ℕ) (o : GateOp) (args : List Ref) (ho : ok o)
    (hl : args.length ≤ 2) (hv : ∀ r ∈ args, valid bound r)
    {r : Ref} (eq : foldGate o args = .inl r) : valid bound r := by
  obtain rfl | rfl | rfl := ho <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try cases a
  all_goals try cases b
  all_goals try casesm* Bool
  all_goals simp_all [foldGate,binary,valid] <;> subst r <;> first | assumption | trivial

private theorem read_stable (w : List Bool) (b : Bool) (r : Ref) (h : valid w.length r) :
    read (w ++ [b]) r = read w r := by
  cases r with
  | lit => rfl
  | wire k =>
    change k < w.length at h
    simp [read,List.getD_eq_getElem?_getD,List.getElem?_append_left h]

def lookup (refs : List Ref) (i : ℕ) := refs.getD i (.lit false)

private theorem lookup_values (refs : List Ref) (w : List Bool) (i : ℕ) :
    (refs.map (read w)).getD i false = read w (lookup refs i) := by
  simp only [List.getD_eq_getElem?_getD,lookup,List.getElem?_map]
  cases refs[i]? <;> rfl

private theorem no_emit {p : ℕ} (refs : List Ref) {b : Bool} (hp : lookup refs p = .lit b)
    (g f : Gate) (ho : ok g.op) (hl : g.inputs.length ≤ 2)
    (eq : foldGate g.op (g.inputs.map (lookup refs)) = .inr f) : ¬liveRead p g := by
  have H := ((fold_spec [] _ _ ho (by simpa)).2 f eq).2.2
  intro live
  have mem : p ∈ g.inputs := by
    obtain ⟨o,ins⟩ := g
    cases o <;> simp_all [liveRead] <;>
      cases ins <;> simp_all
  obtain ha | ⟨op,neq⟩ := H _ (List.mem_map_of_mem mem)
  · exact ha b hp
  · have hd : g.inputs.head? = some p := by simpa [liveRead,op] using live
    rcases eqi : g.inputs with _ | ⟨i,is⟩ <;> simp_all

-- The old prefix is represented by refs. Each raw read of the pinned input
-- saves a distinct gate, including reads in nonconsecutive gates.
theorem scan {p K : ℕ} (saving : Bool) (gs : List Gate) (refs : List Ref)
    (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2)
    (hp : saving = true → p < refs.length) (hpin : saving = true → ∃ b, lookup refs p = .lit b)
    (hv : ∀ r ∈ refs, valid K r) :
    ∃ (fs : List Gate) (rs : List Ref),
      fs.length + (gs.filter (fun g => (saving && decide (liveRead p g)))).length ≤ gs.length ∧
      (∀ f ∈ fs, ok f.op ∧ f.inputs.length ≤ 2) ∧
      (∀ w : List Bool, w.length = K →
        gs.foldl advance (refs.map (read w)) = rs.map (read (fs.foldl advance w))) := by
  induction gs generalizing K refs with
  | nil => exact ⟨[],refs,by simp,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨op,sz⟩ := ho g (by simp)
    have tailok := fun f hf => ho f (List.mem_cons_of_mem g hf)
    let args := g.inputs.map (lookup refs)
    have vs (r) (hr : r ∈ args) : valid K r := by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      by_cases h : i < refs.length
      · unfold lookup; rw [List.getD_eq_getElem _ _ h]; exact hv _ (List.getElem_mem h)
      · unfold lookup; rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]; trivial
    have sem (w : List Bool) : advance (refs.map (read w)) g =
        refs.map (read w) ++ [val w (foldGate g.op args)] := by
      simp only [advance,(fold_spec w _ args op (by simpa [args])).1,args,List.map_map,
        Function.comp_def,lookup_values]
    have keep (r : Ref) (hsav : saving = true) : ∃ b, lookup (refs ++ [r]) p = .lit b := by
      obtain ⟨b,hb⟩ := hpin hsav
      refine ⟨b,?_⟩
      simpa only [lookup,List.getD_eq_getElem?_getD,List.getElem?_append_left (hp hsav)] using hb
    cases eq : foldGate g.op args with
    | inl r =>
      have vr := fold_valid K g.op args op (by simpa [args]) vs eq
      obtain ⟨fs,rs,len,ops,sem'⟩ := ih (K := K) (refs ++ [r]) tailok (by intro s; have := hp s; simp; omega) (keep r)
        (by intro t ht; simp at ht; rcases ht with ht | rfl; exact hv _ ht; exact vr)
      refine ⟨fs,rs,?_,ops,?_⟩
      · cases saving <;> by_cases h : liveRead p g <;> simp_all <;> omega
      · intro w hw
        simpa [sem,eq,val] using sem' w hw
    | inr f =>
      obtain ⟨of',sf,_⟩ := (fold_spec [] _ args op (by simpa [args])).2 f eq
      have ne : (saving && decide (liveRead p g)) = false := by
        cases h : saving <;> simp [h]
        obtain ⟨b,hb⟩ := hpin h
        exact no_emit refs hb g f op sz eq
      have inc r (hr : r ∈ refs) : valid (K+1) r := by
        have := hv r hr
        cases r <;> simp_all [valid] <;> omega
      obtain ⟨fs,rs,len,ops,sem'⟩ := ih (K := K+1) (refs ++ [Ref.wire K]) tailok
        (by intro s; have := hp s; simp; omega) (keep _) (by intro t ht; simp at ht; rcases ht with ht | rfl; exact inc _ ht; exact Nat.lt_succ_self _)
      refine ⟨f::fs,rs,?_,by simpa [of',op,sf] using ops,?_⟩
      · simp [List.filter_cons,ne]; omega
      · intro w hw
        let b := f.op.eval (f.inputs.map fun i => w.getD i false)
        have heq : (refs ++ [Ref.wire K]).map (read (advance w f)) =
            refs.map (read w) ++ [b] := by
          simp only [List.map_append,List.map_cons,List.map_nil]
          congr 1
          · exact List.map_congr_left (fun r hr => read_stable w b r (hw ▸ hv r hr))
          · simp [read,advance,←hw,b]
        have recur :=  sem' (advance w f) (by simp [advance,hw])
        rw [heq] at recur
        simpa [sem,eq,val,b] using recur

private theorem eval_ext (g : Gate) (a b : ℕ → Bool)
    (h : ∀ k, liveRead k g → a k = b k) : g.op.eval (g.inputs.map a) = g.op.eval (g.inputs.map b) := by
  obtain ⟨op,ks⟩ := g
  cases op <;> try (congr 1; exact List.map_congr_left (fun k hk => h k hk))
  cases ks <;> simp_all [GateOp.eval,liveRead]

private theorem no_reads {n : ℕ} (p : Fin n) (gs : List Gate)
    (h : ∀ g ∈ gs, ¬ liveRead p.val g) (x y : Fin n → Bool)
    (eq : ∀ i, i ≠ p → x i = y i) (u : List Bool) :
    ∃ v, gs.foldl advance (List.ofFn x ++ u) = List.ofFn x ++ v ∧
      gs.foldl advance (List.ofFn y ++ u) = List.ofFn y ++ v := by
  induction gs generalizing u with
  | nil => exact ⟨u,rfl,rfl⟩
  | cons g gs ih =>
    let a := fun i => (List.ofFn x ++ u).getD i false
    let b := fun i => (List.ofFn y ++ u).getD i false
    have ev := eval_ext g a b (by
      intro i hi
      have ne : i ≠ p.val := by rintro rfl; exact h g (by simp) hi
      by_cases lt : i < n
      · simp [a,b,List.getD_eq_getElem?_getD,List.getElem?_append_left (show i < (List.ofFn x).length by simpa),
          List.getElem?_append_left (show i < (List.ofFn y).length by simpa),lt,eq ⟨i,lt⟩ (by intro e; exact ne (congrArg Fin.val e))]
      · simp [a,b,List.getD_eq_getElem?_getD,List.getElem?_append_right,lt,Nat.le_of_not_lt lt])
    obtain ⟨v,hx,hy⟩ := ih (fun f hf => h f (by simp [hf])) (u ++ [g.op.eval (g.inputs.map a)])
    refine ⟨v,?_,?_⟩
    · simpa [advance,List.append_assoc,a] using hx
    · rw [ev] at hy; simpa [advance,List.append_assoc,b] using hy

def Computes {m n : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ) :=
  ∀ i (x : Fin n → Bool), Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)

private theorem gate_out {m n : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ)
    (he : Computes S gs out) (a : Fin m) (ha : 2 ≤ (S a).card) : n ≤ out a := by
  by_contra! lt
  let k : Fin n := ⟨out a,lt⟩
  have raw (x : Fin n → Bool) (u : List Bool) : (gs.foldl advance (List.ofFn x ++ u)).getD (out a) false = x k := by
    have ext (t : List Gate) (w : List Bool) : ∃ v, t.foldl advance w = w ++ v := by
      induction t generalizing w with
      | nil => exact ⟨[],by simp⟩
      | cons g t ih =>
        obtain ⟨v,hv⟩ := ih (advance w g)
        exact ⟨_ ,by simpa [advance,List.append_assoc] using hv⟩
    obtain ⟨v,hv⟩ := ext gs (List.ofFn x ++ u)
    rw [hv,List.append_assoc]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (show out a < (List.ofFn x).length by simpa),lt,k]
  have e := he a (fun v => decide (v ≠ k))
  change (gs.foldl advance _).getD _ _ = _ at e
  have r := raw (fun v => decide (v ≠ k)) []
  simp at r
  have pos : ((S a).erase k).Nonempty := Finset.card_pos.mp (by
    by_cases mem : k ∈ S a
    · have := Finset.card_erase_add_one mem; omega
    · rw [Finset.erase_eq_of_notMem mem]; omega)
  obtain ⟨v,hv⟩ := pos
  have yes : ∃ v ∈ S a, decide (v ≠ k) = true := ⟨v,(Finset.mem_erase.mp hv).2,by simp [(Finset.mem_erase.mp hv).1]⟩
  rw [decide_eq_true yes] at e
  exact Bool.noConfusion (r.symm.trans e)

theorem some_read {m n : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ)
    (he : Computes S gs out) (a : Fin m) (ha : 2 ≤ (S a).card) (p : Fin n) (hp : p ∈ S a) :
    ∃ g ∈ gs, liveRead p.val g := by
  by_contra! bad
  obtain ⟨v,hx,hy⟩ := no_reads p gs bad (fun j => decide (j = p)) (fun _ => false)
    (by intro i hi; simp [hi]) []
  simp only [List.append_nil] at hx hy
  have h1 := he a (fun j => decide (j = p))
  have h0 := he a (fun _ => false)
  change (gs.foldl advance _).getD _ _ = _ at h1 h0
  rw [hx] at h1
  rw [hy] at h0
  have bound := gate_out S gs out he a ha
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right,bound,hp] at h1 h0
  grind

theorem restrict_input {m n : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ)
    (he : Computes S gs out) (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2) (p : Fin n)
    (nonempty : ∀ i, ((S i).erase p).Nonempty) :
    ∃ fs out', Computes (fun i => (S i).erase p) fs out' ∧
      (∀ f ∈ fs, ok f.op ∧ f.inputs.length ≤ 2) ∧
      fs.length + (gs.filter (fun g => decide (liveRead p.val g))).length ≤ gs.length := by
  classical
  let refs := List.ofFn (fun i : Fin n => if i = p then Ref.lit false else .wire i.val)
  have len : refs.length = n := by simp [refs]
  obtain ⟨fs,rs,cost,ops,sem⟩ := scan (p := p.val) (K := n) true gs refs ho (by simp [len])
    (by intro _; exact ⟨false,by simp [refs,lookup,List.getD_eq_getElem?_getD,p.isLt]⟩) (by
      intro r hr; simp [refs] at hr; obtain ⟨i,rfl⟩ := hr
      split <;> simp [valid])
  have outsem (i : Fin m) (x : Fin n → Bool) :
      read (fs.foldl advance (List.ofFn x)) (lookup rs (out i)) =
          decide (∃ v ∈ (S i).erase p, x v = true) := by
    let y := fun v : Fin n => if v = p then false else x v
    have init : refs.map (read (List.ofFn x)) = List.ofFn y := by
      rw [show refs = _ from rfl,List.map_ofFn]
      congr 1; funext v; by_cases h : v = p <;> simp [read,y,h,Function.comp_def,List.getD_eq_getElem?_getD,v.isLt]
    have recu := sem (List.ofFn x) (by simp)
    rw [init] at recu
    have e := he i y
    change (gs.foldl advance _).getD _ _ = _ at e
    rw [recu,lookup_values] at e
    rw [e]; congr 1; simp [y,Finset.mem_erase]; grind
  have wires (i : Fin m) : ∃ k, lookup rs (out i) = .wire k := by
    cases e : lookup rs (out i) with
    | wire k => exact ⟨_,rfl⟩
    | lit b =>
      have ones := outsem i (fun _ => true)
      have zeros := outsem i (fun _ => false)
      simp [e,read,nonempty i,Finset.Nonempty] at ones zeros
      obtain ⟨p,hp⟩ := nonempty i
      grind [Finset.mem_erase]
  choose out' wire using wires
  refine ⟨fs,out',?_,ops,by simpa using cost⟩
  intro i x; have := outsem i x
  rw [wire i] at this; exact this


-- The quantified subfamilies allow the same induction to apply to different
-- sufficient criteria for the existence of a private input.
theorem peel_bound {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (peel : ∀ (T : Fin m → Finset (Fin n)), (∀ i, T i ⊆ S i) →
      ∀ a, 4 ≤ (T a).card → ∃ p ∈ T a, ∀ j, j ≠ a → p ∉ T j)
    (gs : List Gate) (out : Fin m → ℕ) (he : Computes S gs out)
    (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  by_cases sm : ∀ i, (S i).card ≤ 3
  · exact Mixed951.bound S hs sm lin gs ho out he
  push Not at sm
  obtain ⟨a,ha⟩ := sm
  obtain ⟨p,hp,priv⟩ := peel S (fun _ => Finset.Subset.refl _) a ha
  let T := fun i => (S i).erase p
  have sub (i) : T i ⊆ S i := Finset.erase_subset _ _
  have ht i : 2 ≤ (T i).card := by
    by_cases e : i = a
    · subst i; have := Finset.card_erase_add_one hp; change 2 ≤ ((S a).erase p).card; omega
    · simpa [T,Finset.erase_eq_of_notMem (priv i e)] using hs i
  have htlin i j (hij : i ≠ j) : (T i ∩ T j).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter (sub _) (sub _))).trans (lin i j hij)
  obtain ⟨fs,out',he',ho',hc⟩ := restrict_input S gs out he ho p (fun i =>
    Finset.card_pos.mp (by have := ht i; change 2 ≤ ((S i).erase p).card at this; omega))
  obtain ⟨g,hm,hread⟩ := some_read S gs out he a (hs a) p hp
  have saved : 0 < (gs.filter (fun g => decide (liveRead p.val g))).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hm,decide_eq_true hread⟩)
  have shorter : fs.length < gs.length := by omega
  have prev := peel_bound T ht htlin (fun U hU => peel U (fun i => (hU i).trans (sub i))) fs out' he' ho'
  have cost := erase_cost S a p hp (hs a) priv
  change (∑ i, ((T i).card - 1)) + 1 = _ at cost
  omega
termination_by gs.length

theorem four_outputs {m n : ℕ} (S : Fin m → Finset (Fin n)) (hm : m ≤ 4)
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (he : Computes S gs out)
    (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  apply peel_bound S hs lin _ gs out he ho
  intro T sub a ha
  exact has_private T a (fun i j hij =>
    (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (lin i j hij)) (by omega)



private theorem output_wires {m n : ℕ} (S : Fin m → Finset (Fin n))
    (fs : List Gate) (ref : Fin m → Ref)
    (sem : ∀ i (x : Fin n → Bool), read (fs.foldl advance (List.ofFn x)) (ref i) =
        decide (∃ v ∈ S i, x v = true)) :
    ∃ out, Computes S fs out := by
  classical
  let out i := match ref i with | .wire k => k | .lit _ => n+fs.length
  refine ⟨out,?_⟩
  intro i x
  change (fs.foldl advance (List.ofFn x)).getD (out i) false = _
  have h := sem i x
  cases eq : ref i with
  | wire k => simpa [out,eq,read] using h
  | lit b =>
    have zero := sem i (fun _ => false)
    simp [eq,read] at zero
    have length (t : List Gate) (w : List Bool) : (t.foldl advance w).length = w.length+t.length := by
      induction t generalizing w with
      | nil => simp
      | cons g t ih => simp [ih,advance]; omega
    have idx : out i = n+fs.length := by simp [out,eq]
    rw [idx,List.getD_eq_default _ _ (by simp [length])]
    simpa [eq,read,zero] using h

def pinned {n : ℕ} (p : Fin n) (x : Fin n → Bool) (j : Fin n) :=
  if j = p then false else x j

private theorem hits_pinned {n : ℕ} (p : Fin n) (x : Fin n → Bool) (A : Finset (Fin n)) :
    (∃ v ∈ A, pinned p x v = true) ↔ ∃ v ∈ A.erase p, x v = true := by
  simp [pinned,Finset.mem_erase]; grind

-- Fold the tail after specializing the first gate and the raw inputs.
private theorem restart {n m : ℕ} (S T : Fin m → Finset (Fin n))
    (g : Gate) (gs : List Gate) (out : Fin m → ℕ) (he : Computes S (g::gs) out)
    (ho : ∀ f ∈ gs, ok f.op ∧ f.inputs.length ≤ 2)
    (y : (Fin n → Bool) → Fin n → Bool) (refs : List Ref)
    (hv : ∀ r ∈ refs, valid n r)
    (init : ∀ x, advance (List.ofFn (y x)) g = refs.map (read (List.ofFn x)))
    (hit : ∀ i x, (∃ v ∈ S i, y x v = true) ↔ ∃ v ∈ T i, x v = true)
    (k : ℕ) (saving : Bool) (hk : saving = true → k < refs.length)
    (pin : saving = true → ∃ b, lookup refs k = .lit b) :
    ∃ fs out', Computes T fs out' ∧ (∀ f ∈ fs, ok f.op ∧ f.inputs.length ≤ 2) ∧
      fs.length + (gs.filter (fun f => saving && decide (liveRead k f))).length ≤ gs.length := by
  classical
  obtain ⟨fs,rs,hc,hops,recurs⟩ := scan saving gs refs ho hk pin hv
  obtain ⟨newout,hnew⟩ := output_wires T fs (fun i => lookup rs (out i)) (by
    intro i x
    have e := he i (y x)
    change (gs.foldl advance (advance (List.ofFn (y x)) g)).getD _ _ = _ at e
    rw [init,recurs _ (by simp),lookup_values] at e
    exact e.trans (decide_eq_decide.mpr (hit i x)))
  exact ⟨fs,newout,hnew,hops,hc⟩

private def rawrefs (n : ℕ) := List.ofFn (fun i : Fin n => Ref.wire i.val)
private def pinrefs {n : ℕ} (p : Fin n) := List.ofFn (fun i : Fin n => if i = p then Ref.lit false else .wire i.val)

private theorem rawrefs_val {n : ℕ} (x : Fin n → Bool) :
    (rawrefs n).map (read (List.ofFn x)) = List.ofFn x := by
  simp [rawrefs,List.map_ofFn,read,Function.comp_def,List.getD_eq_getElem?_getD]
private theorem pinrefs_val {n : ℕ} (p : Fin n) (x : Fin n → Bool) :
    (pinrefs p).map (read (List.ofFn x)) = List.ofFn (pinned p x) := by
  simp only [pinrefs,List.map_ofFn]
  congr 1; funext v; by_cases h : v = p <;> simp [pinned,Function.comp_def,h,read,List.getD_eq_getElem?_getD]

private theorem rawrefs_ok (n : ℕ) (r) (hr : r ∈ rawrefs n) : valid n r := by
  simp [rawrefs] at hr; obtain ⟨i,rfl⟩ := hr; exact i.isLt
private theorem pinrefs_ok {n : ℕ} (p : Fin n) (r) (hr : r ∈ pinrefs p) : valid n r := by
  simp [pinrefs] at hr; obtain ⟨i,rfl⟩ := hr; split <;> simp [valid]

private theorem remove_first {n m : ℕ} (S : Fin m → Finset (Fin n))
    (g : Gate) (gs : List Gate) (out : Fin m → ℕ) (he : Computes S (g::gs) out)
    (ho : ∀ f ∈ gs, ok f.op ∧ f.inputs.length ≤ 2) (r : Ref) (hr : valid n r)
    (ev : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
       = read (List.ofFn x) r) :
    ∃ fs out', Computes S fs out' ∧ (∀ f ∈ fs, ok f.op ∧ f.inputs.length ≤ 2) ∧
      fs.length ≤ gs.length := by
  obtain ⟨fs,o,h,ops,cost⟩ := restart S S g gs out he ho id (rawrefs n ++ [r])
    (by intro t ht; simp at ht; rcases ht with ht | rfl; exact rawrefs_ok _ _ ht; exact hr)
    (by intro x; simp only [id_eq,advance,List.map_append,List.map_cons,List.map_nil,rawrefs_val,ev]) (by simp) 0 false (by simp) (by simp)
  exact ⟨fs,o,h,ops,by simpa using cost⟩


private def active {m n : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i ∧ 2 ≤ (S i).card)

private theorem active_cost {m n : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) :
    ∑ i, ((S i).card - 1) =
      (∑ i, (((S i).erase p).card - 1)) + (active S p).card := by
  classical
  have e i : (S i).card - 1 = ((S i).erase p).card - 1 + (if i ∈ active S p then 1 else 0) := by
    by_cases h : p ∈ S i
    · have := Finset.card_erase_add_one h
      by_cases hc : 2 ≤ (S i).card <;> simp [active,h,hc] <;> omega
    · simp [active,h,Finset.erase_eq_of_notMem h]
  simp [e,Finset.sum_add_distrib]

private def firstVal {n : ℕ} (g : Gate) (x : Fin n → Bool) :=
  g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)

private theorem binary_tail_read {m n : ℕ} (S : Fin m → Finset (Fin n))
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (g : Gate) (gs : List Gate) (out : Fin m → ℕ) (he : Computes S (g::gs) out)
    (p q : Fin n) (ne : p ≠ q) (two : 2 ≤ (active S p).card) (t : Bool)
    (blocks : ∀ x : Fin n → Bool, x q = t → firstVal g x = t) :
    ∃ f ∈ gs, liveRead p.val f := by
  classical
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp two
  have A : p ∈ S a ∧ 2 ≤ (S a).card := by simpa [active] using ha
  have B : p ∈ S b ∧ 2 ≤ (S b).card := by simpa [active] using hb
  have sep : q ∉ S a ∨ q ∉ S b := by
    by_contra! bad
    have : 1 < (S a ∩ S b).card := Finset.one_lt_card.mpr ⟨p,Finset.mem_inter.mpr ⟨A.1,B.1⟩,
      q,Finset.mem_inter.mpr bad,ne⟩
    have := lin a b ab; omega
  obtain ⟨i,hip,hiq,size⟩ : ∃ i, p ∈ S i ∧ q ∉ S i ∧ 2 ≤ (S i).card := by
    rcases sep with e | e
    · exact ⟨a,A.1,e,A.2⟩
    · exact ⟨b,B.1,e,B.2⟩
  by_contra! none
  let x := fun j : Fin n => decide (j = p) || (decide (j = q) && t)
  let y := fun j : Fin n => decide (j = q) && t
  obtain ⟨v,hx,hy⟩ := no_reads p gs none x y (by intro j hj; simp [x,y,hj]) [t]
  have ex := he i x
  have ey := he i y
  change (gs.foldl advance (List.ofFn x ++ [firstVal g x])).getD (out i) false = _ at ex
  change (gs.foldl advance (List.ofFn y ++ [firstVal g y])).getD (out i) false = _ at ey
  rw [blocks x (by simp [x,ne.symm]),hx] at ex
  rw [blocks y (by simp [y]),hy] at ey
  have bound := gate_out S (g::gs) out he i size
  have pos : ∃ k ∈ S i, x k = true := ⟨p,hip,by simp [x]⟩
  have neg : ¬∃ k ∈ S i, y k = true := by simp [y]; grind
  rw [decide_eq_true pos] at ex
  rw [decide_eq_false neg] at ey
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simpa using bound :
    (List.ofFn x).length ≤ out i),List.getElem?_append_right (by simpa using bound :
    (List.ofFn y).length ≤ out i),List.length_ofFn] at ex ey
  grind

private theorem pin_first {n m : ℕ} (S : Fin m → Finset (Fin n))
    (g : Gate) (gs : List Gate) (out : Fin m → ℕ) (he : Computes S (g::gs) out)
    (ho : ∀ f ∈ gs, ok f.op ∧ f.inputs.length ≤ 2) (p : Fin n) (r : Ref) (hr : valid n r)
    (eval : ∀ x, firstVal g (pinned p x) = read (List.ofFn x) r)
    (k : ℕ) (hk : k < n+1) (hpin : ∃ b, lookup (pinrefs p ++ [r]) k = .lit b) :
    ∃ fs out', Computes (fun i => (S i).erase p) fs out' ∧
      (∀ f ∈ fs, ok f.op ∧ f.inputs.length ≤ 2) ∧
      fs.length + (gs.filter (fun f => decide (liveRead k f))).length ≤ gs.length := by
  obtain ⟨fs,o,he',ho',hc⟩ := restart S _ g gs out he ho (pinned p) (pinrefs p ++ [r])
    (by intro u hu; simp at hu; rcases hu with hu | rfl; exact pinrefs_ok _ _ hu; exact hr)
    (by intro x; simp only [List.map_append,List.map_cons,List.map_nil,pinrefs_val]
        change _ ++ [firstVal g (pinned p x)] = _; rw [eval])
    (fun i x => hits_pinned p x (S i)) k true (by simp [pinrefs]; omega) (by simp [hpin])
  exact ⟨fs,o,he',ho',by simpa using hc⟩

private theorem not_unused {m n : ℕ} (S : Fin m → Finset (Fin n))
    (g : Gate) (gs : List Gate) (out : Fin m → ℕ) (he : Computes S (g::gs) out)
    (p : Fin n) (hp : 0 < (active S p).card)
    (eval : ∀ x : Fin n → Bool, firstVal g x = !(x p))
    (only : ∀ f ∈ gs, ¬liveRead p.val f) :
    ∃ f ∈ gs, liveRead n f := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  obtain ⟨mem,size⟩ : p ∈ S a ∧ 2 ≤ (S a).card := by simpa [active] using ha
  by_contra! none
  let x := fun j : Fin n => decide (j = p)
  let y := fun _ : Fin n => false
  have skipWire (z : Fin n → Bool) (b : Bool) :
      ∃ v, gs.foldl advance (List.ofFn z ++ [b]) = (List.ofFn z ++ [b]) ++ v ∧
        gs.foldl advance (List.ofFn z ++ [false]) = (List.ofFn z ++ [false]) ++ v := by
    let xb : Fin (n+1) → Bool := Fin.lastCases b z
    let x0 : Fin (n+1) → Bool := Fin.lastCases false z
    have eq' (j : Fin (n+1)) (ne : j ≠ Fin.last n) : xb j = x0 j := by
      induction j using Fin.lastCases <;> simp_all [xb,x0]
    obtain ⟨v,h1,h2⟩ := no_reads (Fin.last n) gs none xb x0 eq' []
    simpa only [List.append_nil,xb,x0,List.ofFn_succ_last,Fin.lastCases_last,Fin.lastCases_castSucc] using
      (show ∃ v, gs.foldl advance (List.ofFn xb) = List.ofFn xb ++ v ∧
        gs.foldl advance (List.ofFn x0) = List.ofFn x0 ++ v from ⟨v,by simpa only [List.append_nil] using h1,by simpa only [List.append_nil] using h2⟩)
  have outgt : n < out a := by
    have lo := gate_out S (g::gs) out he a size
    by_contra! le
    have eqo : out a = n := by omega
    have ey := he a y
    change (gs.foldl advance (List.ofFn y ++ [firstVal g y])).getD (out a) false = _ at ey
    obtain ⟨v,hv,_⟩ := skipWire y (firstVal g y)
    rw [eqo,hv,eval] at ey
    simp [y,List.append_assoc,List.getD_eq_getElem?_getD,List.getElem?_append_right] at ey
  obtain ⟨v,hx,hy⟩ := no_reads p gs only x y (by intro j ne; simp [x,y,ne]) [false]
  have suffix (z : Fin n → Bool) (b : Bool) :
      (gs.foldl advance (List.ofFn z ++ [b])).getD (out a) false =
      (gs.foldl advance (List.ofFn z ++ [false])).getD (out a) false := by
    obtain ⟨v,h1,h2⟩ := skipWire z b
    rw [h1,h2]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show (List.ofFn z ++ [b]).length ≤ out a by simp; omega),
      List.getElem?_append_right (show (List.ofFn z ++ [false]).length ≤ out a by simp; omega),List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
  have h1 := he a x
  have h2 := he a y
  change (gs.foldl advance (List.ofFn x ++ [firstVal g x])).getD _ _ = _ at h1
  change (gs.foldl advance (List.ofFn y ++ [firstVal g y])).getD _ _ = _ at h2
  rw [suffix,hx] at h1; rw [suffix,hy] at h2
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right,outgt.le,x,y,mem] at h1 h2
  grind

private inductive Shape {n : ℕ} (g : Gate) : Prop
  | alias (r : Ref) (hr : valid n r) (ev : ∀ x : Fin n → Bool, firstVal g x = read (List.ofFn x) r)
  | neg (p : Fin n) (ev : ∀ x, firstVal g x = !(x p))
  | bin (p q : Fin n) (ne : p ≠ q) (t : Bool)
      (block : ∀ x, x q = t → firstVal g x = t)
      (ev : ∀ x, firstVal g (pinned p x) = if t then x q else false)

private theorem shape (n : ℕ) (g : Gate) (ho : ok g.op) (sz : g.inputs.length ≤ 2) : @Shape n g := by
  obtain ⟨o,ins⟩ := g
  change ok o at ho
  change ins.length ≤ 2 at sz
  let raw (k : ℕ) := if k < n then Ref.wire k else Ref.lit false
  have valid' k : valid n (raw k) := by unfold raw; split <;> simp_all [valid]
  have rex (x : Fin n → Bool) (k : ℕ) : (List.ofFn x).getD k false = read (List.ofFn x) (raw k) := by
    by_cases h : k < n <;> simp [raw,h,read,List.getD_eq_getElem?_getD]
  have binaryShape (o : GateOp) (a b : ℕ) (hop : o = .and ∨ o = .or) : @Shape n ⟨o,[a,b]⟩ := by
    by_cases ha : a < n <;> by_cases hb : b < n
    · by_cases eq : a = b
      · subst b; apply Shape.alias (raw a) (valid' a); intro x
        rcases hop with rfl | rfl <;> simp [firstVal,raw,read,ha,GateOp.eval]
      · let p : Fin n := ⟨a,ha⟩
        let q : Fin n := ⟨b,hb⟩
        have ne : p ≠ q := by intro e; exact eq (congrArg Fin.val e)
        rcases hop with rfl | rfl
        · apply Shape.bin p q ne false
          · intro x h; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,hb,q] at *; simp_all
          · intro x; simp [firstVal,GateOp.eval,pinned,p,List.getD_eq_getElem?_getD,ha]
        · apply Shape.bin p q ne true
          · intro x h; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,hb,q] at *; simp_all
          · intro x; simp [firstVal,GateOp.eval,pinned,p,q,List.getD_eq_getElem?_getD,ha,hb,Ne.symm eq]
    · rcases hop with rfl | rfl
      · apply Shape.alias (.lit false) trivial; intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,hb,read]
      · apply Shape.alias (raw a) (valid' a); intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,hb,ha,read,raw]
    · rcases hop with rfl | rfl
      · apply Shape.alias (.lit false) trivial; intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,read]
      · apply Shape.alias (raw b) (valid' b); intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,hb,read,raw]
    · rcases hop with rfl | rfl <;> apply Shape.alias (.lit false) trivial <;> intro x <;>
        simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,hb,read]
  obtain rfl | rfl | rfl := ho
  all_goals rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals first
    | solve | simp at sz
    | exact binaryShape _ _ _ (Or.inl rfl)
    | exact binaryShape _ _ _ (Or.inr rfl)
    | apply Shape.alias (.lit true) trivial; intro x; rfl
    | apply Shape.alias (.lit false) trivial; intro x; rfl
    | apply Shape.alias (raw a) (valid' a); intro x; simpa [firstVal,GateOp.eval] using rex x a
    | by_cases ha : a < n
      · apply Shape.neg ⟨a,ha⟩; intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha]
      · apply Shape.alias (.lit true) trivial; intro x; simp [firstVal,GateOp.eval,List.getD_eq_getElem?_getD,ha,read]


/-- Exact Boolean sum lower bound when each input belongs to at most two
nontrivial outputs. The circuit may use any number of inverters. -/
theorem degree_two {m n : ℕ} (S : Fin m → Finset (Fin n))
    (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (degree : ∀ p, (Finset.univ.filter (fun i => p ∈ S i ∧ 2 ≤ (S i).card)).card ≤ 2)
    (gs : List Gate) (out : Fin m → ℕ) (he : Computes S gs out)
    (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  cases gs with
  | nil =>
    have small i : (S i).card ≤ 1 := by
      by_contra! large
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (S i).card)
      obtain ⟨g,hm,_⟩ := some_read S [] out he i large p hp
      simp at hm
    have cost i : (S i).card - 1 = 0 := by have := small i; omega
    simp [cost]
  | cons g gs =>
    have hop := ho g (by simp)
    have tailok := fun f hf => ho f (List.mem_cons_of_mem g hf)
    have finish (p : Fin n) (r : Ref) (hr : valid n r)
        (eval : ∀ x, firstVal g (pinned p x) = read (List.ofFn x) r)
        (k : ℕ) (hk : k < n + 1) (pin : ∃ b, lookup (pinrefs p ++ [r]) k = .lit b)
        (more : 2 ≤ (active S p).card → ∃ f ∈ gs, liveRead k f) :
        ∑ i, ((S i).card - 1) ≤ (g::gs).length := by
      obtain ⟨fs,o,comp,ops,cost⟩ := pin_first S g gs out he tailok p r hr eval k hk pin
      let T := fun i => (S i).erase p
      have sub i : T i ⊆ S i := Finset.erase_subset _ _
      have lin' i j (ne : i ≠ j) : (T i ∩ T j).card ≤ 1 :=
        (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (lin i j ne)
      have deg' (u : Fin n) : (active T u).card ≤ 2 := by
        apply le_trans _ (degree u)
        apply Finset.card_le_card
        intro i hi
        obtain ⟨mem,size⟩ : u ∈ T i ∧ 2 ≤ (T i).card := by simpa [active] using hi
        simpa [active] using And.intro (sub _ mem) (size.trans (Finset.card_le_card (sub i)))
      have shorter : fs.length < (g::gs).length := by simp; omega
      have bound := degree_two T lin' deg' fs o comp ops
      have d : (active S p).card ≤ 2 := degree p
      rw [active_cost S p,List.length_cons]
      change (∑ i, ((T i).card-1)) + _ ≤ _
      by_cases two : 2 ≤ (active S p).card
      · obtain ⟨f,hm,hf⟩ := more two
        have saved : 0 < (gs.filter (fun f => decide (liveRead k f))).length :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨hm,decide_eq_true hf⟩)
        omega
      · omega
    have selfpin (p : Fin n) (r : Ref) :
        ∃ b, lookup (pinrefs p ++ [r]) p.val = .lit b := by
      exact ⟨false,by simp [lookup,pinrefs,List.getD_eq_getElem?_getD,List.getElem?_append_left
        (show p.val < (pinrefs p).length by simp [pinrefs]),p.isLt]⟩
    cases shape n g hop.1 hop.2 with
    | «alias» r hr ev =>
      obtain ⟨fs,o,c,ops,cost⟩ := remove_first S g gs out he tailok r hr ev
      have shorter : fs.length < (g::gs).length := by simp; omega
      exact (degree_two S lin degree fs o c ops).trans shorter.le
    | neg p ev =>
      have eval (x) : firstVal g (pinned p x) = read (List.ofFn x) (.lit true) := by simp [ev,pinned,read]
      by_cases use : ∃ f ∈ gs, liveRead p.val f
      · exact finish p (.lit true) trivial eval p.val (by omega) (selfpin _ _) (fun _ => use)
      · push Not at use
        apply finish p (.lit true) trivial eval n (by omega) (by exact ⟨true,by
          simp [lookup,pinrefs,List.getD_eq_getElem?_getD,List.getElem?_append_right]⟩)
        intro h
        exact not_unused S g gs out he p (by omega) ev use
    | bin p q ne t blocks ev =>
      let r := if t then Ref.wire q.val else .lit false
      have hr : valid n r := by cases t <;> simp [r,valid]
      have eval (x) : firstVal g (pinned p x) = read (List.ofFn x) r := by
        cases t <;> simp [ev,r,read,List.getD_eq_getElem?_getD]
      exact finish p r hr eval p.val (by omega) (selfpin _ _) (fun h =>
        binary_tail_read S lin g gs out he p q ne h t blocks)
termination_by gs.length


-- Vertices are outputs and the ten edges are inputs. Each star is an OR.
def fiveStars : Fin 5 → Finset (Fin 10) :=
  ![{0,1,2,3},{0,4,5,6},{1,4,7,8},{2,5,7,9},{3,6,8,9}]

theorem five_stars_bound (gs : List Gate) (out : Fin 5 → ℕ) (he : Computes fiveStars gs out)
    (ho : ∀ g ∈ gs, ok g.op ∧ g.inputs.length ≤ 2) : 15 ≤ gs.length := by
  have hh := degree_two fiveStars (by decide +kernel) (by decide +kernel) gs out he ho
  have exactCost : (∑ i, ((fiveStars i).card - 1)) = 15 := by decide +kernel
  rwa [exactCost] at hh


end Pin951
