import PEqualNP.Defs
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

The Lean declarations below check the individual gate rewrite, the private
input existence lemma and the exact change in the target. The circuit scan
induction and the resulting general lifting theorem above are written proofs.
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

end Pin951
