import PEqualNP.Outside.L_meta_951_partial

/-!
Rows have arbitrary sizes and any two share at most one input. If setting
one variable to false makes every inverter output true on that subcube,
the full gate lower bound follows. For rows containing that variable, use
the upper monotone circuit obtained by freezing each inverter to true.
For all other rows, additionally mask the distinguished variable. At each
gate index, the masked circuit is pointwise below the upper circuit. A gate
counted for two rows would witness two distinct singleton inputs in their
intersection. This argument puts no bound on the degrees of the inputs.
-/
namespace Pivot951
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_951_aux

private def pin {n : ℕ} (p : Fin n) (x : Fin n → Bool) (j : Fin n) :=
  if j = p then false else x j

private def mask (p N : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (fun k => if k=p then N else k)⟩

private theorem mask_val {n : ℕ} (p : Fin n) (N : ℕ) (gs : List Gate)
    (hn : n+gs.length ≤ N) (x : Fin n → Bool) (k : ℕ) (hk : k ≠ p.val) :
    val (gs.map (mask p.val N)) x k = val gs (pin p x) k := by
  induction gs using List.reverseRecOn generalizing k with
  | nil =>
    rw [List.map_nil,val_nil,val_nil]; split <;> simp_all [pin,Fin.ext_iff]
  | append_singleton gs g ih =>
    simp only [List.length_append,List.length_cons,List.length_nil] at hn
    simp only [List.map_append,List.map_cons,List.map_nil,val_snoc,List.length_map]
    split
    · simp only [mask,List.map_map,Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases e : i=p.val
      · rw [if_pos e,e,outside_gates _ x N (Or.inr (by simp; omega)),val_nil,
          outside_gates gs (pin p x) p.val (Or.inl p.isLt),val_nil]
        simp [show ¬N < n by omega,p.isLt,pin]
      · rw [if_neg e,ih (by omega) i e]
    · exact ih (by omega) k hk

private theorem mono_val {n : ℕ} (gs : List Gate)
    (pos : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (x y : Fin n → Bool) (h : ∀ j, x j ≤ y j) (k : ℕ) : val gs x k ≤ val gs y k := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => rw [val_nil,val_nil]; split <;> simp_all
  | append_singleton gs g ih =>
    rw [val_snoc,val_snoc]; split
    · exact eval_mono g (pos g (by simp)) _ _ (ih (fun f hf => pos f (by simp [hf])))
    · exact ih (fun f hf => pos f (by simp [hf])) _

-- This condition only concerns inverter outputs when the distinguished input
-- is false. Other inputs and the arrangement of the output rows are unrestricted.
def forced {n : ℕ} (p : Fin n) (gs : List Gate) :=
  ∀ (x : Fin n → Bool), x p = false → ∀ (j : Fin gs.length),
    (gs.get j).op = .not → val gs x (n+j.val) = true

private theorem agrees {n : ℕ} (p : Fin n) (gs : List Gate) (ctrl : forced p gs)
    (x : Fin n → Bool) (xp : x p = false) (hg : ∀ g ∈ gs, basis g) (k : ℕ) :
    val (gs.map (freeze true)) x k = val gs x k := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => rfl
  | append_singleton gs g ih =>
    have pre : forced p gs := by
      intro y hy j hj
      let j' : Fin (gs++[g]).length := ⟨j.val,by simp⟩
      have op : ((gs++[g]).get j').op = .not := by
        simpa [j',List.get_eq_getElem,List.getElem_append_left j.isLt] using hj
      have ok := ctrl y hy j' op
      simpa [j',val_snoc,show j.val ≠ gs.length by omega] using ok
    have old := ih pre (fun f hf => hg f (by simp [hf]))
    have hop := (hg g (by simp)).1
    simp only [List.map_append,List.map_cons,List.map_nil,val_snoc,List.length_map]
    split
    · rcases hop with op | op | op
      · simp [freeze,op,old]
      · simp [freeze,op,old]
      · let j : Fin (gs++[g]).length := ⟨gs.length,by simp⟩
        have h := ctrl x xp j (by simpa [j,List.get_eq_getElem] using op)
        simpa [j,val_snoc,freeze,op,GateOp.eval] using h.symm
    · exact old _

theorem pivot_tests_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (hg : ∀ g ∈ gs, basis g)
    (he : ∀ i (x : Fin n → Bool), val gs x (out i) = decide (∃ v ∈ S i, x v = true))
    (p : Fin n) (tests : ∀ i, val (gs.map (freeze true)) (Zof (insert p (S i))) (out i) = false) : ∑ i, ((S i).card-1) ≤ gs.length := by
  classical
  let F := gs.map (freeze true)
  let N := n + gs.length
  let L := F.map (mask p.val N)
  let C (i : Fin m) := if p ∈ S i then F else L
  have size i : (C i).length = gs.length := by simp [C,F,L]; split <;> simp
  have ph := freeze_basis true gs hg
  have pl (g) (mem : g ∈ L) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp mem
    simpa [mask] using ph f hf
  have pc i g (mem : g ∈ C i) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    by_cases e : p ∈ S i <;> simp [C,e] at mem
    · exact ph _ mem
    · exact pl _ mem
  have om i : out i ≠ p.val := by
    have hr := output_range (S i) (hs i) gs (out i) (by intro u; simp [he,eof])
    have := (Finset.mem_Ico.mp hr).1; omega
  have mv x k (ne : k ≠ p.val) : val L x k = val F (pin p x) k :=
    mask_val p N F (by simp [F,N]) x k ne
  have zl i : val (C i) (Zof (S i)) (out i) = false := by
    by_cases mem : p ∈ S i
    · simpa [C,mem,F,Finset.insert_eq_of_mem mem] using tests i
    · simp only [C,if_neg mem,mv _ _ (om i)]
      have e : pin p (Zof (S i)) = Zof (insert p (S i)) := by
        funext j; by_cases eq : j=p <;> simp [pin,Zof,eq]
      exact e ▸ tests i
  have ep i u (hu : u ∈ S i) : val (C i) (eof u) (out i) = true := by
    have yes : val gs (eof u) (out i) = true := by simp [he,eof,hu]
    by_cases mem : p ∈ S i
    · simpa [C,mem,F] using Bool.le_iff_imp.mp (sandwich gs (eof u) hg (out i)).2 yes
    · simp only [C,if_neg mem,mv _ _ (om i)]
      have eq : pin p (eof u) = eof u := by
        funext j; by_cases e : j=p <;> simp [pin,eof,e]; grind
      rw [eq]; exact Bool.le_iff_imp.mp (sandwich gs (eof u) hg (out i)).2 yes
  have ord (x : Fin n → Bool) k (ne : k ≠ p.val) : val L x k ≤ val F x k := by
    rw [mv _ _ ne]
    exact mono_val F (fun g h => (ph g h).1) _ _ (by intro j; by_cases e : j=p <;> simp [pin,e]) _
  let chargedSet i := D (S i) (C i)
  have disj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (chargedSet i) (chargedSet j) := by
    intro i _ j _ ne
    rw [Finset.disjoint_left]
    intro k h1 h2
    have lower (i j : Fin m) (ne : i ≠ j) (h1 : k ∈ chargedSet i) (h2 : k ∈ chargedSet j)
        (cmp : ∀ u : Fin n, val (C i) (eof u) k ≤ val (C j) (eof u) k) : False := by
      obtain ⟨_,_,hz,u,v,uv,hu,hv⟩ := Finset.mem_filter.mp h1
      obtain ⟨_,_,hz',_⟩ := Finset.mem_filter.mp h2
      obtain ⟨_,hI,_⟩ := main_inv (S i) (C i) (pc i)
      obtain ⟨_,hJ,_⟩ := main_inv (S j) (C j) (pc j)
      have both (q) (t : val (C i) (eof q) k = true) : q ∈ S i ∩ S j := by
        have t' := Bool.le_iff_imp.mp (cmp q) t
        exact Finset.mem_inter.mpr ⟨(hI k q q hz t t).1,(hJ k q q hz' t' t').1⟩
      have big : 1 < (S i ∩ S j).card := Finset.one_lt_card.mpr ⟨u,both _ hu,v,both _ hv,uv⟩
      have := lin i j ne; omega
    have kk := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).1
    have nk : k ≠ p.val := by omega
    by_cases pi : p ∈ S i <;> by_cases pj : p ∈ S j
    · exact lower i j ne h1 h2 (by simp [C,pi,pj])
    · exact lower j i ne.symm h2 h1 (by simp [C,pi,pj]; intro u; exact ord _ _ nk)
    · exact lower i j ne h1 h2 (by simp [C,pi,pj]; intro u; exact ord _ _ nk)
    · exact lower i j ne h1 h2 (by simp [C,pi,pj])
  calc
    _ ≤ ∑ i, (chargedSet i).card := Finset.sum_le_sum (fun i _ =>
      count_subset (S i) (S i) (Finset.Subset.refl _) (C i) (pc i) (out i) (zl i) (ep i))
    _ = (Finset.univ.biUnion chargedSet).card := (Finset.card_biUnion disj).symm
    _ ≤ (Finset.Ico n (n+gs.length)).card := Finset.card_le_card (by
      intro k hk; obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hk
      simpa [size i] using (show k ∈ Finset.Ico n (n+(C i).length) from (Finset.mem_filter.mp hi).1))
    _ = _ := by simp
theorem pivot_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (hg : ∀ g ∈ gs, basis g)
    (he : ∀ i (x : Fin n → Bool), val gs x (out i) = decide (∃ v ∈ S i, x v = true))
    (p : Fin n) (ctrl : forced p gs) : ∑ i, ((S i).card-1) ≤ gs.length := by
  apply pivot_tests_bound S hs lin gs out hg he p
  intro i
  rw [agrees p gs ctrl _ (by simp [Zof]) hg,he]
  simp [Zof]; grind

/-- In particular the NOT gate may directly negate a raw input, with arbitrary
downstream fan-out. Additional unused arguments of a NOT are allowed. -/
theorem raw_inverter {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (lin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (hg : ∀ g ∈ gs, basis g)
    (he : ∀ i (x : Fin n → Bool), val gs x (out i) = decide (∃ v ∈ S i, x v = true))
    (p : Fin n) (direct : ∀ g ∈ gs, g.op = .not → g.inputs.head? = some p.val) :
    ∑ i, ((S i).card-1) ≤ gs.length := by
  apply pivot_bound S hs lin gs out hg he p
  clear he hg
  induction gs using List.reverseRecOn with
  | nil => intro x hx j; exact Fin.elim0 j
  | append_singleton t g ih =>
    intro x hx j hop
    by_cases last : j.val = t.length
    · have op : g.op = .not := by simpa [List.get_eq_getElem,last] using hop
      have head := direct g (by simp) op
      rw [last,val_snoc,if_pos rfl,op]
      cases eq : g.inputs with
      | nil => simp [eq] at head
      | cons k ks =>
        have kp : k = p.val := by simpa [eq] using head
        simp [eq,kp,GateOp.eval,outside_gates t x p.val (.inl p.isLt),val_nil,p.isLt,hx]
    · have lt : j.val < t.length := by have := j.isLt; simp at this; omega
      let i : Fin t.length := ⟨j.val,lt⟩
      have op : (t.get i).op = .not := by
        simpa [i,List.get_eq_getElem,List.getElem_append_left lt] using hop
      have old := ih (fun f hf => direct f (by simp [hf])) x hx i op
      simpa [i,val_snoc,last] using old

end Pivot951
