import PEqualNP.Defs

-- Adapted from the invariant in the checked L-meta-529 proof.
-- The refined invariant counts only binary OR gates.
namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def binaryOr (g : Gate) : Bool :=
  match g.op with
  | .or => decide (g.inputs.length = 2)
  | _ => false

theorem single_parent {X : Type} (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (hlen : g.inputs.length ≤ 2) (hb : binaryOr g = false) (f : X → ℕ → Bool) (z : X)
    (hz : g.op.eval (g.inputs.map (f z)) = false) :
    ∃ j, (f z j = false ∧ ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y j = true)
    ∨ (∀ y, g.op.eval (g.inputs.map (f y)) = false) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz ⊢
  rcases hop with rfl | rfl
  · have hex : ∃ j ∈ ins, f z j = false := by
      simpa [GateOp.eval, List.all_map] using hz
    obtain ⟨j, hj, hjz⟩ := hex
    refine ⟨j, Or.inl ⟨hjz, ?_⟩⟩
    intro y hy
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hy
    exact hy j hj
  · match ins, hlen with
    | [], _ => exact ⟨0, Or.inr (by simp [GateOp.eval])⟩
    | [j], _ => exact ⟨j, Or.inl ⟨by simpa [GateOp.eval] using hz, by simp [GateOp.eval]⟩⟩
    | [_,_], _ => simp [binaryOr] at hb
    | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

def charged (n : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  (gs[i-n]?).any binaryOr

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => charged n gs i = true ∧ Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_, ?_⟩
  · simpa only [charged, List.getElem?_append_left (show i - n < gs.length by omega)] using hi.2.1
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, ite_eq_right hne]; exact hz
  · rw [val_snoc, ite_eq_right hne]; exact hu
  · rw [val_snoc, ite_eq_right hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, ?_, u0, v0, ?_, ?_, ?_⟩
          · have hb : binaryOr g = true := by
              by_contra! hbad
              have bad : binaryOr g = false := by cases h : binaryOr g <;> simp_all
              obtain ⟨j, hj | hall⟩ := single_parent g hop hlen bad
                (fun x j => val gs x j) (Zof S) hz
              · exact hne (hinv j u0 v0 hj.1 (hj.2 _ hu0) (hj.2 _ hv0)).2
              · exact Bool.noConfusion ((hall (eof u0)).symm.trans hu0)
            simp [charged, hN, hb]
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega


def basis (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def freeze (b : Bool) (g : Gate) : Gate :=
  match g.op with
  | .not => if b then ⟨.and, []⟩ else ⟨.or, []⟩
  | _ => g

theorem freeze_basis (b : Bool) (gs : List Gate) (hg : ∀ g ∈ gs, basis g) :
    ∀ g ∈ gs.map (freeze b), (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  obtain ⟨ha | ho | hn, hlen⟩ := hg k hk
  · simpa [freeze, ha] using hlen
  · simpa [freeze, ho] using hlen
  · cases b <;> simp [freeze, hn]

theorem eval_mono (g : Gate) (h : g.op = .and ∨ g.op = .or) (f f' : ℕ → Bool)
    (hff : ∀ i, f i ≤ f' i) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map f') := by
  rw [Bool.le_iff_imp]
  rcases h with h | h
  · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => (Bool.le_iff_imp.mp (hff i)) (hall i hi)
  · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, Bool.le_iff_imp.mp (hff i) hv⟩

theorem sandwich {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (hg : ∀ g ∈ gs, basis g) :
    ∀ i, val (gs.map (freeze false)) x i ≤ val gs x i ∧
         val gs x i ≤ val (gs.map (freeze true)) x i := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have prev := ih (fun k hk => hg k (by simp [hk]))
    obtain ⟨hop, -⟩ := hg g (by simp)
    intro i
    simp only [List.map_append, List.map_cons, List.map_nil, val_snoc, List.length_map]
    split_ifs with hi
    · rcases hop with ha | ho | hn
      · simp only [freeze, ha]
        rw [← ha]
        exact ⟨eval_mono g (Or.inl ha) _ _ (fun j => (prev j).1),
          eval_mono g (Or.inl ha) _ _ (fun j => (prev j).2)⟩
      · simp only [freeze, ho]
        rw [← ho]
        exact ⟨eval_mono g (Or.inr ho) _ _ (fun j => (prev j).1),
          eval_mono g (Or.inr ho) _ _ (fun j => (prev j).2)⟩
      · simp [freeze, hn, GateOp.eval]
    · exact prev i

theorem freeze_order {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, basis g)
    (a b : Bool) (hab : a ≤ b) (x : Fin n → Bool) (i : ℕ) :
    val (gs.map (freeze a)) x i ≤ val (gs.map (freeze b)) x i := by
  cases a <;> cases b
  · exact le_rfl
  · exact (sandwich gs x hg i).1.trans (sandwich gs x hg i).2
  · exact False.elim ((by decide : ¬(true ≤ false)) hab)
  · exact le_rfl

theorem count_subset {n : ℕ} (S U : Finset (Fin n)) (hU : U ⊆ S)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (o : ℕ) (hZ : val gs (Zof S) o = false) (hE : ∀ u ∈ U, val gs (eof u) o = true) :
    U.card - 1 ≤ (D S gs).card := by
  classical
  obtain ⟨l, hinv, hc⟩ := main_inv S gs hg
  have hu : (U.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hinv o u v hZ (hE u hu) (hE v hv)).2
  have hsum := Finset.card_union_le ((S \ U).image l) (U.image l)
  rw [← Finset.image_union, Finset.sdiff_union_of_subset hU] at hsum
  have hd : ((S \ U).image l).card ≤ (S \ U).card := Finset.card_image_le
  rw [Finset.card_sdiff_of_subset hU] at hd
  have := Finset.card_le_card hU
  omega

theorem separate {n : ℕ} (A B : Finset (Fin n)) (hAB : (A ∩ B).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (a b : Bool) (hab : a ≤ b) :
    Disjoint (D A (gs.map (freeze a))) (D B (gs.map (freeze b))) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hj
  obtain ⟨_, _, hza, u, v, huv, hu, hv⟩ := Finset.mem_filter.mp hi
  obtain ⟨_, _, hzb, _⟩ := Finset.mem_filter.mp hj
  obtain ⟨_, hA, _⟩ := main_inv A _ (freeze_basis a gs hg)
  obtain ⟨_, hB, _⟩ := main_inv B _ (freeze_basis b gs hg)
  have liftT (w : Fin n) := Bool.le_iff_imp.mp (freeze_order gs hg a b hab (eof w) i)
  have hsub : ({u,v} : Finset (Fin n)) ⊆ A ∩ B := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_inter.mpr ⟨(hA i _ _ hza hu hu).1,
          (hB i _ _ hzb (liftT _ hu) (liftT _ hu)).1⟩
    · obtain rfl := Finset.mem_singleton.mp hw
      exact Finset.mem_inter.mpr ⟨(hA i _ _ hza hv hv).1,
          (hB i _ _ hzb (liftT _ hv) (liftT _ hv)).1⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at h
  omega

theorem binaryOr_freeze (g : Gate) (b : Bool) : binaryOr (freeze b g) = binaryOr g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases b <;> simp [binaryOr, freeze] <;> rfl

def orIndices (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => charged n gs i

theorem mixed_bound {n m : ℕ} (S U : Fin m → Finset (Fin n))
    (hS : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) (hU : ∀ w, U w ⊆ S w)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (out : Fin m → ℕ) (b : Fin m → Bool)
    (hZ : ∀ w, val (gs.map (freeze (b w))) (Zof (S w)) (out w) = false)
    (hE : ∀ w, ∀ u ∈ U w, val (gs.map (freeze (b w))) (eof u) (out w) = true) :
    ∑ w, ((U w).card - 1) ≤ (orIndices n gs).card := by
  classical
  let C (w : Fin m) := D (S w) (gs.map (freeze (b w)))
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ c ∈ (Finset.univ : Finset (Fin m)),
      a ≠ c → Disjoint (C a) (C c) := by
    intro a _ c _ hne
    rcases le_total (b a) (b c) with h | h
    · exact separate _ _ (hS a c hne) _ hg _ _ h
    · exact (separate _ _ (hS c a hne.symm) _ hg _ _ h).symm
  calc ∑ w, ((U w).card - 1) ≤ ∑ w, (C w).card := Finset.sum_le_sum fun w _ =>
        count_subset _ _ (hU w) _ (freeze_basis (b w) gs hg) _ (hZ w) (hE w)
       _ = (Finset.univ.biUnion C).card := (Finset.card_biUnion hdisj).symm
       _ ≤ (orIndices n gs).card := by
         apply Finset.card_le_card
         intro i hi
         obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
         obtain ⟨hr, hc, _⟩ := Finset.mem_filter.mp hw
         refine Finset.mem_filter.mpr ⟨by simpa only [List.length_map] using hr, ?_⟩
         simp only [charged, List.getElem?_map] at hc ⊢
         cases e : gs[i - n]? <;> simp_all [binaryOr_freeze]

-- Choose the upper circuit when it rejects the maximal input outside the set.
def mode {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (o : ℕ) : Bool :=
  !(val (gs.map (freeze true)) (Zof S) o)

def covered {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (o : ℕ) : Finset (Fin n) :=
  S.filter fun u => val (gs.map (freeze (mode S gs o))) (eof u) o

theorem covered_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    ∑ w, ((covered (S w) gs (out w)).card - 1) ≤ (orIndices n gs).card := by
  apply mixed_bound S _ hS (fun _ => Finset.filter_subset _ _) gs hg out
    (fun w => mode (S w) gs (out w))
  · intro w
    have hz : val gs (Zof (S w)) (out w) = false := by
      change Circuit.eval ⟨gs, out w⟩ _ = false
      rw [hev]
      simp [Zof]
    cases h : val (gs.map (freeze true)) (Zof (S w)) (out w) with
    | false => simp [mode, h]
    | true =>
      have hlow := (sandwich gs (Zof (S w)) hg (out w)).1
      rw [hz] at hlow
      simpa [mode, h] using le_antisymm hlow (Bool.false_le _)
  · intro w u hu
    exact (Finset.mem_filter.mp hu).2

-- This small circuit computes the OR of the first two inputs on all eight inputs.
-- Freezing the inverter to either constant spoils at least one answer.
def exampleGates : List Gate :=
  [⟨.not, [2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩,
   ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩]

theorem example_correct : ∀ x : Fin 3 → Bool,
    Circuit.eval ⟨exampleGates, 8⟩ (List.ofFn x) = (x 0 || x 1) := by decide

theorem example_defect : (covered ({0, 1} : Finset (Fin 3)) exampleGates 8).card = 0 ∧
    (∀ b : Bool, ∃ x : Fin 3 → Bool,
      Circuit.eval ⟨exampleGates.map (freeze b), 8⟩ (List.ofFn x) ≠ (x 0 || x 1)) := by decide

-- The two outputs here require different choices to recover their full sets.
def twoOutputGates : List Gate :=
  [⟨.not, [0]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩,
   ⟨.and, [0, 3]⟩, ⟨.or, [6, 7]⟩]

theorem two_modes : (∀ x : Fin 3 → Bool,
    Circuit.eval ⟨twoOutputGates, 5⟩ (List.ofFn x) = (x 0 || x 1) ∧
    Circuit.eval ⟨twoOutputGates, 8⟩ (List.ofFn x) = (x 1 || x 2)) ∧
    mode ({0, 1} : Finset (Fin 3)) twoOutputGates 5 = true ∧
    mode ({1, 2} : Finset (Fin 3)) twoOutputGates 8 = false ∧
    covered ({0, 1} : Finset (Fin 3)) twoOutputGates 5 = {0, 1} ∧
    covered ({1, 2} : Finset (Fin 3)) twoOutputGates 8 = {1, 2} ∧
    (∀ b : Bool, ∃ x : Fin 3 → Bool,
      Circuit.eval ⟨twoOutputGates.map (freeze b), 5⟩ (List.ofFn x) ≠ (x 0 || x 1) ∨
      Circuit.eval ⟨twoOutputGates.map (freeze b), 8⟩ (List.ofFn x) ≠ (x 1 || x 2)) := by decide

-- Two inputs can be joined by any intermediate wire that rejects the complement.
def joinable {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (p q : Fin n) : Prop :=
  ∃ i : ℕ, val gs (Zof S) i = false ∧ val gs (eof p) i = true ∧ val gs (eof q) i = true

theorem connected_count {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hconn : ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (joinable S gs) p q) :
    S.card - 1 ≤ (D S gs).card := by
  classical
  obtain ⟨l, hi, hc⟩ := main_inv S gs hg
  have path {p q} (hh : Relation.ReflTransGen (joinable S gs) p q) : l p = l q := by
    induction hh with
    | refl => rfl
    | tail _ link ih =>
      obtain ⟨w, hz, ha, hb⟩ := link
      exact ih.trans (hi w _ _ hz ha hb).2
  have him : (S.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact path (hconn p hp q hq)
  omega

theorem connected_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (b : Fin m → Bool)
    (hconn : ∀ w, ∀ p ∈ S w, ∀ q ∈ S w, Relation.ReflTransGen
      (joinable (S w) (gs.map (freeze (b w)))) p q) :
    ∑ w, ((S w).card - 1) ≤ (orIndices n gs).card := by
  classical
  let C (w : Fin m) := D (S w) (gs.map (freeze (b w)))
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ c ∈ (Finset.univ : Finset (Fin m)),
      a ≠ c → Disjoint (C a) (C c) := by
    intro a _ c _ hne
    rcases le_total (b a) (b c) with h | h
    · exact separate _ _ (hS a c hne) _ hg _ _ h
    · exact (separate _ _ (hS c a hne.symm) _ hg _ _ h).symm
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (C w).card := Finset.sum_le_sum fun w _ =>
        connected_count _ _ (freeze_basis (b w) gs hg) (hconn w)
       _ = (Finset.univ.biUnion C).card := (Finset.card_biUnion hdisj).symm
       _ ≤ (orIndices n gs).card := by
         apply Finset.card_le_card
         intro i hi
         obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
         obtain ⟨hr, hc, _⟩ := Finset.mem_filter.mp hw
         refine Finset.mem_filter.mpr ⟨by simpa only [List.length_map] using hr, ?_⟩
         simp only [charged, List.getElem?_map] at hc ⊢
         cases e : gs[i - n]? <;> simp_all [binaryOr_freeze]

def overlapExample : List Gate :=
  [⟨.not, [3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩,
   ⟨.and, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [9, 10]⟩]

def triple : Finset (Fin 4) := {0, 1, 2}

theorem overlap_correct : ∀ x : Fin 4 → Bool,
    Circuit.eval ⟨overlapExample, 11⟩ (List.ofFn x) = (x 0 || x 1 || x 2) := by decide

theorem overlap_no_single_wire : ∀ (b : Bool) (i : Fin 12),
    ¬ (val (overlapExample.map (freeze b)) (Zof triple) i = false ∧
      ∀ p ∈ triple, val (overlapExample.map (freeze b)) (eof p) i = true) := by decide

theorem overlap_connected : ∀ p ∈ triple, ∀ q ∈ triple, Relation.ReflTransGen
    (joinable triple (overlapExample.map (freeze false))) p q := by
  let R := joinable triple (overlapExample.map (freeze false))
  have left (p : Fin 4) (hp : p ∈ triple) : R p 1 := by
    have h : ∀ p ∈ triple, ∃ i : Fin 12,
        val (overlapExample.map (freeze false)) (Zof triple) i = false ∧
        val (overlapExample.map (freeze false)) (eof p) i = true ∧
        val (overlapExample.map (freeze false)) (eof (1 : Fin 4)) i = true := by decide
    obtain ⟨i, hi⟩ := h p hp
    exact ⟨i, hi⟩
  intro p hp q hq
  obtain ⟨i, hz, hq', h1⟩ := left q hq
  exact (Relation.ReflTransGen.single (left p hp)).tail ⟨i, hz, h1, hq'⟩

-- An exact OR wire can never be charged to a different row in either shadow.
theorem reserve {n : ℕ} (A B : Finset (Fin n)) (hA : 2 ≤ A.card)
    (hAB : (A ∩ B).card ≤ 1) (gs : List Gate) (hg : ∀ g ∈ gs, basis g)
    (o : ℕ) (hev : ∀ p : Fin n, val gs (eof p) o = true ↔ p ∈ A) (b : Bool) :
    o ∉ D B (gs.map (freeze b)) := by
  classical
  intro hc
  obtain ⟨_, _, hz, u, v, huv, hu, hv⟩ := Finset.mem_filter.mp hc
  obtain ⟨_, hi, _⟩ := main_inv B _ (freeze_basis b gs hg)
  cases b with
  | false =>
    have ha (p : Fin n) (hp : val (gs.map (freeze false)) (eof p) o = true) : p ∈ A :=
      (hev p).mp ((Bool.le_iff_imp.mp (sandwich gs (eof p) hg o).1) hp)
    have hd : ({u,v} : Finset (Fin n)) ⊆ A ∩ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_inter.mpr ⟨ha _ hu, (hi o _ _ hz hu hu).1⟩
      · obtain rfl := Finset.mem_singleton.mp hx
        exact Finset.mem_inter.mpr ⟨ha _ hv, (hi o _ _ hz hv hv).1⟩
    have h := Finset.card_le_card hd
    rw [Finset.card_pair huv] at h
    omega
  | true =>
    have hd : A ⊆ A ∩ B := by
      intro p hp
      have hh := (Bool.le_iff_imp.mp (sandwich gs (eof p) hg o).2) ((hev p).mpr hp)
      exact Finset.mem_inter.mpr ⟨hp, (hi o p p hz hh hh).1⟩
    have := Finset.card_le_card hd
    omega

theorem outside_gates {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : i < n ∨ n + gs.length ≤ i) : val gs x i = val [] x i := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    rw [val_snoc, ite_eq_right (by omega)]
    exact ih (by omega)

theorem output_range {n : ℕ} (A : Finset (Fin n)) (hA : 2 ≤ A.card)
    (gs : List Gate) (o : ℕ) (hev : ∀ p : Fin n, val gs (eof p) o = true ↔ p ∈ A) :
    o ∈ Finset.Ico n (n+gs.length) := by
  by_contra hr
  simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hr
  have ho : ∀ p ∈ A, val [] (eof p) o = true := by
    intro p hp
    rw [← outside_gates gs (eof p) o hr]
    exact (hev p).mpr hp
  have hsmall : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    have h1 := ho p hp
    have h2 := ho q hq
    rw [val_nil] at h1 h2
    split at h1 <;> rename_i hm
    · simp [hm, eof] at h1 h2
      exact h1.symm.trans h2
    · contradiction
  omega

theorem reserved_total {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ w, 2 ≤ (S w).card) (hS : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (out : Fin m → ℕ)
    (hev : ∀ w p, val gs (eof p) (out w) = true ↔ p ∈ S w) (b : Fin m → Bool) :
    (∑ w, (insert (out w) (D (S w) (gs.map (freeze (b w))))).card) ≤ gs.length := by
  classical
  let C (w : Fin m) := insert (out w) (D (S w) (gs.map (freeze (b w))))
  have hinj : Function.Injective out := by
    intro a c hac
    by_contra hne
    have hsub : S a ⊆ S a ∩ S c := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨hp, (hev c p).mp (hac ▸ (hev a p).mpr hp)⟩
    have := Finset.card_le_card hsub
    have := hsize a
    have := hS a c hne
    omega
  have hd : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ c ∈ (Finset.univ : Finset (Fin m)),
      a ≠ c → Disjoint (C a) (C c) := by
    intro a _ c _ hne
    have h0 := reserve _ _ (hsize a) (hS a c hne) gs hg _ (hev a) (b c)
    have h1 := reserve _ _ (hsize c) (hS c a hne.symm) gs hg _ (hev c) (b a)
    have h2 : Disjoint (D (S a) (gs.map (freeze (b a)))) (D (S c) (gs.map (freeze (b c)))) := by
      rcases le_total (b a) (b c) with h | h
      · exact separate _ _ (hS a c hne) _ hg _ _ h
      · exact (separate _ _ (hS c a hne.symm) _ hg _ _ h).symm
    rw [Finset.disjoint_left]
    intro i hi hj
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rcases Finset.mem_insert.mp hj with hh | hh
      · exact hne (hinj hh)
      · exact h0 hh
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h1 hi
      · exact Finset.disjoint_left.mp h2 hi hj
  change (∑ w, (C w).card) ≤ gs.length
  rw [← Finset.card_biUnion hd]
  have hsub : Finset.univ.biUnion C ⊆ Finset.Ico n (n+gs.length) := by
    intro i hi
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_insert.mp hw with rfl | hor
    · exact output_range _ (hsize w) gs _ (hev w)
    · simpa only [List.length_map] using (Finset.mem_filter.mp hor).1
  simpa using Finset.card_le_card hsub

-- One designated representative per connected component suffices.
theorem roots_count {n : ℕ} (S T : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hroot : ∀ p ∈ S, ∃ q ∈ T, Relation.ReflTransGen (joinable S gs) p q) :
    S.card ≤ T.card + (D S gs).card := by
  classical
  obtain ⟨l, hi, hc⟩ := main_inv S gs hg
  have path {p q} (hh : Relation.ReflTransGen (joinable S gs) p q) : l p = l q := by
    induction hh with
    | refl => rfl
    | tail _ link ih =>
      obtain ⟨w, hz, ha, hb⟩ := link
      exact ih.trans (hi w _ _ hz ha hb).2
  have him : S.image l ⊆ T.image l := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨q, hq, hh⟩ := hroot p hp
    exact Finset.mem_image.mpr ⟨q, hq, (path hh).symm⟩
  have ht := (Finset.card_le_card him).trans (@Finset.card_image_le _ _ T l _)
  omega

-- If at most two components remain, an uncharged marked output pays for the second.
theorem two_components_bound {n m : ℕ} (S T : Fin m → Finset (Fin n))
    (hsize : ∀ w, 2 ≤ (S w).card) (hS : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, basis g) (out : Fin m → ℕ)
    (hev : ∀ w p, val gs (eof p) (out w) = true ↔ p ∈ S w) (b : Fin m → Bool)
    (hroot : ∀ w, ∀ p ∈ S w, ∃ q ∈ T w,
      Relation.ReflTransGen (joinable (S w) (gs.map (freeze (b w)))) p q)
    (htwo : ∀ w, (T w).card ≤ 2)
    (hone : ∀ w, out w ∈ D (S w) (gs.map (freeze (b w))) → (T w).card ≤ 1) :
    ∑ w, ((S w).card - 1) ≤ gs.length := by
  classical
  apply le_trans _ (reserved_total S hsize hS gs hg out hev b)
  apply Finset.sum_le_sum
  intro w _
  have hc := roots_count (S w) (T w) _ (freeze_basis (b w) gs hg) (hroot w)
  by_cases h : out w ∈ D (S w) (gs.map (freeze (b w)))
  · have := hone w h
    rw [Finset.insert_eq_of_mem h]
    omega
  · have := htwo w
    rw [Finset.card_insert_of_notMem h]
    omega

-- In this three-input OR, a fixed shadow can join the first two points, but its
-- test graph separates the third. The marked output accounts for the last gate.
def splitExample : List Gate :=
  [⟨.not, [3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 1]⟩,
   ⟨.and, [7, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 9]⟩]

theorem split_correct : ∀ x : Fin 4 → Bool,
    Circuit.eval ⟨splitExample, 10⟩ (List.ofFn x) = (x 0 || x 1 || x 2) := by decide

theorem split_cut : ∀ (b : Bool) (i : Fin 11),
    val (splitExample.map (freeze b)) (Zof triple) i = false →
    val (splitExample.map (freeze b)) (eof (2 : Fin 4)) i = true →
    val (splitExample.map (freeze b)) (eof (0 : Fin 4)) i = false ∧
    val (splitExample.map (freeze b)) (eof (1 : Fin 4)) i = false := by decide

theorem split_roots : ∀ p ∈ triple, ∃ q ∈ ({0,2} : Finset (Fin 4)),
    Relation.ReflTransGen (joinable triple (splitExample.map (freeze false))) p q := by
  intro p hp
  by_cases ht : p = 2
  · subst p
    exact ⟨2, by decide, .refl⟩
  · have hw : ∀ p ∈ triple, p ≠ 2 →
        val (splitExample.map (freeze false)) (eof p) 7 = true := by decide
    exact ⟨0, by decide, .single ⟨7, by decide, hw p hp ht, by decide⟩⟩

theorem split_output_unused : 10 ∉ D triple (splitExample.map (freeze false)) := by
  classical
  intro hh
  obtain ⟨_, _, _, u, v, huv, hu, hv⟩ := Finset.mem_filter.mp hh
  have ht : ∀ p : Fin 4, val (splitExample.map (freeze false)) (eof p) 10 = true →
      p = 2 := by decide
  exact huv ((ht u hu).trans (ht v hv).symm)

end PEqualNP.Outside.L_meta_951_aux
