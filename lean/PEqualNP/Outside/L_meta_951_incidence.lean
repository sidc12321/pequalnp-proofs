import PEqualNP.Defs

-- Monotone case from the checked upstream L-meta-529.

namespace Mixed951.MonotoneAux

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

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
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
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
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

end Mixed951.MonotoneAux

open Mixed951.MonotoneAux in
theorem Mixed951.monotone_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp


-- Adapted from the checked L-meta-1378 proof.
namespace Mixed951

open PEqualNP.CircuitLowerBounds

private def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

private lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih, Nat.add_comm, Nat.add_left_comm]

private lemma old (gs : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ h]
    exact List.getElem_append_left h

private def V {n : ℕ} (gs : List Gate) (k : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl step (List.ofFn x)).getD k false

private lemma eval_gate {n : ℕ} (gs : List Gate) (j : ℕ) (h : j < gs.length) (x : Fin n → Bool) :
    V gs (n+j) x = gs[j].op.eval
      (gs[j].inputs.map fun k => if k < n+j then V gs k x else false) := by
  unfold V
  let w := (gs.take j).foldl step (List.ofFn x)
  have hw : w.length = n+j := by simp [w, length_run, Nat.min_eq_left (Nat.le_of_lt h)]
  have split : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons h]
  have fold : gs.foldl step (List.ofFn x) = (gs.drop (j+1)).foldl step (step w gs[j]) := by
    conv_lhs => rw [split, List.foldl_append, List.foldl_cons]
  have old' (k : ℕ) (hk : k < n+j) : (gs.foldl step (List.ofFn x)).getD k false = w.getD k false := by
    conv_lhs => rw [split, List.foldl_append]
    exact old _ w _ (by rw [hw]; exact hk)
  calc
    _ = (step w gs[j]).getD w.length false := by
      rw [fold, old _ _ _ (by simp [step, hw]), hw]
    _ = gs[j].op.eval (gs[j].inputs.map fun k => w.getD k false) := by simp [step]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro k _
      by_cases hk : k < n+j
      · rw [ite_eq_left hk, old' k hk]
      · rw [ite_eq_right hk, List.getD_eq_default _ _ (by simpa [hw] using hk)]

private lemma raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (h : k < n) :
    V gs k x = x ⟨k,h⟩ := by
  unfold V
  rw [old _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private def point {n : ℕ} (p : Fin n) (v : Fin n) : Bool := decide (v = p)
private def off {n : ℕ} (s : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ s)
private def hit {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ v ∈ s, x v = true

private lemma hit_point {n : ℕ} (s : Finset (Fin n)) (p : Fin n) :
    hit s (point p) ↔ p ∈ s := by simp [hit, point]

private lemma hit_off_self {n : ℕ} (s : Finset (Fin n)) : ¬ hit s (off s) := by
  simp [hit, off]

private lemma pair_choice {n : ℕ} (s : Finset (Fin n)) (hs : 3 ≤ s.card)
    (ks : List ℕ) (hk : ks.length ≤ 2) (R : ℕ → Fin n → Prop)
    (h : ∀ p ∈ s, ∃ k ∈ ks, R k p) :
    ∃ k ∈ ks, ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ R k p ∧ R k q := by
  obtain ⟨p,hp,q,hq,r,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card.mp hs
  obtain ⟨a,ha,hap⟩ := h p hp
  obtain ⟨b,hb,hbq⟩ := h q hq
  obtain ⟨c,hc,hcr⟩ := h r hr
  have rep : a = b ∨ a = c ∨ b = c := by
    cases ks with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys =>
        cases ys with
        | nil => simp only [List.mem_cons] at ha hb hc; grind
        | cons z zs => simp at hk
  rcases rep with rfl | rfl | rfl
  · exact ⟨a,ha,p,hp,q,hq,hpq,hap,hbq⟩
  · exact ⟨a,ha,p,hp,r,hr,hpr,hap,hcr⟩
  · exact ⟨b,hb,q,hq,r,hr,hqr,hbq,hcr⟩

private def role {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (i : Fin m) (k : ℕ) : Prop :=
  ((∀ x, V gs k x = true → hit (S i) x) ∧
    ∃ p q : Fin n, p ≠ q ∧ V gs k (point p) = true ∧ V gs k (point q) = true) ∨
  ((∀ x, hit (S i) x → V gs k x = true) ∧ V gs k (off (S i)) = false) ∨
  ((∀ x, V gs k x = true ↔ ¬ hit (S i) x) ∧
   ∃ j : Fin gs.length, k < n + j.val ∧ (gs.get j).op = .not)

private lemma inter_small {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) {i j : Fin m} {p q : Fin n}
    (hpq : p ≠ q) (hp : p ∈ S i) (hq : q ∈ S i) (hp' : p ∈ S j) (hq' : q ∈ S j) : i = j := by
  by_contra hn
  have h1 := h i j hn
  have h2 := Finset.one_lt_card.mpr ⟨p, Finset.mem_inter.mpr ⟨hp,hp'⟩,
    q, Finset.mem_inter.mpr ⟨hq,hq'⟩, hpq⟩
  omega

private lemma diff {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j : Fin m} (hne : i ≠ j) : ∃ p ∈ S i, p ∉ S j := by
  by_contra! hh
  have hi := h i j hne
  rw [Finset.inter_eq_left.mpr hh] at hi
  have := hs i
  omega

private lemma roles_unique {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    {gs : List Gate} {k : ℕ} {i j : Fin m} (a : role S gs i k) (b : role S gs j k) : i = j := by
  by_contra ne
  obtain ⟨p,hp,hpj⟩ := diff S hs h ne
  obtain ⟨q,hq,hqi⟩ := diff S hs h (Ne.symm ne)
  have pi : hit (S i) (point p) := (hit_point _ _).mpr hp
  have qj : hit (S j) (point q) := (hit_point _ _).mpr hq
  have all_hit (a : Fin m) : hit (S a) (fun _ => true) :=
    let ⟨v,hv⟩ := Finset.card_pos.mp (by have := hs a; omega)
    ⟨v,hv,rfl⟩
  have none_hit (a : Fin m) : ¬ hit (S a) (fun _ => false) := by simp [hit]
  rcases a with ⟨a,u,v,huv,hu,hv⟩ | ⟨a,az⟩ | ⟨a,_⟩ <;> rcases b with ⟨b,_,_,_,_,_⟩ | ⟨b,bz⟩ | ⟨b,_⟩
  · exact ne (inter_small S h huv ((hit_point _ _).mp (a _ hu)) ((hit_point _ _).mp (a _ hv))
      ((hit_point _ _).mp (b _ hu)) ((hit_point _ _).mp (b _ hv)))
  · exact hqi ((hit_point _ _).mp (a _ (b _ qj)))
  · exact none_hit i (a _ ((b _).mpr (none_hit j)))
  · exact hpj ((hit_point _ _).mp (b _ (a _ pi)))
  · have hhit : hit (S j) (off (S i)) := ⟨q,hq,by simp [off,hqi]⟩
    exact Bool.noConfusion (az.symm.trans (b _ hhit))
  · exact (b _).mp (a _ (all_hit i)) (all_hit j)
  · exact none_hit j (b _ ((a _).mpr (none_hit i)))
  · exact (a _).mp (b _ (all_hit j)) (all_hit i)
  · exact (a _).mp ((b _).mpr (fun hj => hpj ((hit_point _ _).mp hj))) pi


private lemma no_raw {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (gs : List Gate) (i : Fin m) (k : ℕ) (hk : k < n) (a : role S gs i k) : False := by
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by have := hs i; omega : 1 < (S i).card)
  rcases a with ⟨_,p,q,hpq,hp,hq⟩ | ⟨a,_⟩ | ⟨a,_⟩
  · simp [raw gs _ k hk, point] at hp hq
    exact hpq (hp.symm.trans hq)
  · have up := a (point u) ((hit_point _ _).mpr hu)
    have vp := a (point v) ((hit_point _ _).mpr hv)
    simp [raw gs _ k hk, point] at up vp
    exact huv (up.symm.trans vp)
  · have zero := (a (fun _ => false)).mpr (by simp [hit])
    simp [raw gs _ k hk] at zero

private lemma out_valid {n : ℕ} (gs : List Gate) (o : ℕ) (s : Finset (Fin n))
    (hs : 2 ≤ s.card) (he : ∀ x, V gs o x = true ↔ hit s x) : n ≤ o ∧ o < n+gs.length := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have ap := (he (point p)).mpr ((hit_point s p).mpr hp)
  have aq := (he (point q)).mpr ((hit_point s q).mpr hq)
  constructor
  · by_contra! h
    simp [raw gs _ o h, point] at ap aq
    exact hpq (ap.symm.trans aq)
  · by_contra! h
    unfold V at ap
    rw [List.getD_eq_default _ _ (by simpa [length_run] using h)] at ap
    contradiction

private lemma parent {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (i : Fin m) (hthree : 3 ≤ (S i).card) (o : ℕ) (ho : n ≤ o ∧ o < n+gs.length)
    (he : ∀ x, V gs o x = true ↔ hit (S i) x) :
    ∃ k, n ≤ k ∧ k < o ∧ role S gs i k := by
  let j := o - n
  have hj : j < gs.length := by unfold j; omega
  have hjo : n+j = o := by unfold j; omega
  let g := gs[j]
  let R := fun (k : ℕ) (x : Fin n → Bool) => if k < o then V gs k x else false
  have ev (x : Fin n → Bool) : V gs o x = g.op.eval (g.inputs.map fun k => R k x) := by
    have this := eval_gate gs j hj x
    simpa [hjo, g, R] using this
  have hg' := hg g (List.getElem_mem hj)
  have allhit : hit (S i) (fun _ => true) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by have := hs i; omega : 0 < (S i).card)
    exact ⟨p,hp,rfl⟩
  have emp : ¬ hit (S i) (fun _ => false) := by simp [hit]
  have cond (k : ℕ) (x : Fin n → Bool) (h : R k x = true) : k < o := by
    by_contra! hn
    exact (Nat.not_lt.mpr hn) ((by simpa [R] using h : k < o ∧ V gs k x = true).1)
  suffices ∃ k, k < o ∧ role S gs i k by
    obtain ⟨k,hk,r⟩ := this
    exact ⟨k, Nat.le_of_not_gt (fun h => no_raw S hs gs i k h r), hk, r⟩
  rcases hg'.1 with hop | hop | hop
  · have hh (x : Fin n → Bool) : hit (S i) x ↔ ∀ k ∈ g.inputs, R k x = true := by
      rw [← he, ev, hop]
      simp [GateOp.eval,List.all_eq_true]
    have fail := mt (hh (off (S i))).mpr (hit_off_self (S i))
    push Not at fail
    obtain ⟨k,hk,hno⟩ := fail
    have hlt := cond k _ ((hh _).mp allhit k hk)
    refine ⟨k,hlt,Or.inr (Or.inl ⟨?_,?_⟩)⟩
    · intro x hx
      simpa [R,hlt] using (hh x).mp hx k hk
    · simpa [R,hlt] using hno
  · have hh (x : Fin n → Bool) : hit (S i) x ↔ ∃ k ∈ g.inputs, R k x = true := by
      rw [← he, ev, hop]
      simp [GateOp.eval,List.any_eq_true]
    obtain ⟨k,hk,p,_,q,_,hpq,hp,hq⟩ := pair_choice (S i) hthree g.inputs hg'.2
      (fun k p => R k (point p) = true) (fun p hp => (hh _).mp ((hit_point _ _).mpr hp))
    have hlt := cond k _ hp
    refine ⟨k,hlt,Or.inl ⟨?_,p,q,hpq,?_,?_⟩⟩
    · intro x hx
      exact (hh x).mpr ⟨k,hk,by simpa [R,hlt] using hx⟩
    · simpa [R,hlt] using hp
    · simpa [R,hlt] using hq
  · cases hargs : g.inputs with
    | nil =>
      have hz : V gs o (fun _ : Fin n => false) = true := by simp [ev,hop,hargs,GateOp.eval]
      exact (emp ((he _).mp hz)).elim
    | cons k ks =>
      have hh (x : Fin n → Bool) : hit (S i) x ↔ R k x = false := by
        rw [← he, ev, hop]
        simp [GateOp.eval,hargs]
      have hz : R k (fun _ => false) = true := by
        cases h : R k (fun _ => false)
        · exact (emp ((hh _).mpr h)).elim
        · rfl
      have hlt := cond k _ hz
      refine ⟨k,hlt,Or.inr (Or.inr ⟨fun x => ?_, ⟨j,hj⟩, by change k < n+j; omega, hop⟩)⟩
      have heq : hit (S i) x ↔ V gs k x = false := by simpa [R,hlt] using hh x
      cases hx : V gs k x <;> simp_all

private lemma count_reserved {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i x, V gs (out i) x = true ↔ hit (S i) x) (Z : Finset (Fin gs.length))
    (hZ : ∀ z ∈ Z, ∀ i, out i ≠ n+z.val ∧ ¬role S gs i (n+z.val)) :
    m + Fintype.card {i : Fin m // 3 ≤ (S i).card} + Z.card ≤ gs.length := by
  classical
  have valid i := out_valid gs (out i) (S i) (hs i) (he i)
  have outinj : Function.Injective out := by
    intro i j e
    by_contra ne
    obtain ⟨p,hp,hpn⟩ := diff S hs h ne
    have eq := (he i (point p)).mpr ((hit_point _ _).mpr hp)
    rw [e] at eq
    exact hpn ((hit_point _ _).mp ((he _ _).mp eq))
  choose dest hdlo hdhi hdrole using fun i : {i : Fin m // 3 ≤ (S i).card} =>
    parent S hs gs hg i.val i.property (out i.val) (valid i.val) (he i.val)
  have disj (i : {i : Fin m // 3 ≤ (S i).card}) (j : Fin m) : dest i ≠ out j := by
    intro e
    have nij : i.val ≠ j := by intro a; subst j; have := hdhi i; omega
    rcases hdrole i with ⟨a,_,_,_,_,_⟩ | ⟨a,_⟩ | ⟨a,_⟩
    · obtain ⟨p,hp,hpn⟩ := diff S hs h (Ne.symm nij)
      have hy := (he j (point p)).mpr ((hit_point _ _).mpr hp)
      rw [← e] at hy
      exact hpn ((hit_point _ _).mp (a _ hy))
    · obtain ⟨p,hp,hpn⟩ := diff S hs h nij
      have hy := a (point p) ((hit_point _ _).mpr hp)
      rw [e] at hy
      exact hpn ((hit_point _ _).mp ((he _ _).mp hy))
    · have hy := (a (fun _ => false)).mpr (by simp [hit])
      rw [e] at hy
      simpa [hit] using (he _ _).mp hy
  let F : Fin m ⊕ {i : Fin m // 3 ≤ (S i).card} → Fin gs.length :=
    Sum.elim (fun i => ⟨out i-n, by have := valid i; omega⟩)
      (fun i => ⟨dest i-n, by have := (valid i).2; have := hdhi i; have := hdlo i; omega⟩)
  have inj : Function.Injective F := by
    intro a b e
    have ev := congrArg Fin.val e
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        change out i - n = out j - n at ev
        have := (valid i).1
        have := (valid j).1
        exact congrArg Sum.inl (outinj (by omega))
      | inr j =>
        change out i - n = dest j - n at ev
        have := (valid i).1
        have := hdlo j
        exact ((disj j i) (by omega)).elim
    | inr i =>
      cases b with
      | inl j =>
        change dest i - n = out j - n at ev
        have := hdlo i
        have := (valid j).1
        exact ((disj i j) (by omega)).elim
      | inr j =>
        change dest i - n = dest j - n at ev
        have := hdlo i
        have := hdlo j
        have q : dest i = dest j := by omega
        exact congrArg Sum.inr (Subtype.ext (roles_unique S hs h (hdrole i) (q ▸ hdrole j)))
  have hn (v) : F v ∉ Z := by
    intro hz
    cases v with
    | inl i =>
      apply (hZ _ hz i).1
      change out i = n + (out i - n)
      have := (valid i).1
      omega
    | inr i =>
      apply (hZ _ hz i).2
      change role S gs i (n + (dest i - n))
      rw [Nat.add_sub_of_le (hdlo i)]
      exact hdrole i
  let A := Finset.univ.image F
  have hsub : A ⊆ Finset.univ \ Z := by
    intro k hk
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn v⟩
  have hh := Finset.card_le_card hsub
  have hz : Z.card ≤ gs.length := by simpa using Finset.card_le_card (Finset.subset_univ Z)
  simp [A, Finset.card_image_of_injective _ inj,Finset.card_sdiff_of_subset] at hh
  omega

private lemma prove {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i x, V gs (out i) x = true ↔ hit (S i) x) : m + Fintype.card {i : Fin m // 3 ≤ (S i).card} ≤ gs.length := by
  simpa using count_reserved S hs h gs hg out he ∅ (by simp)

theorem bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (hu : ∀ i, (S i).card ≤ 3)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  have he' : ∀ i x, V gs (out i) x = true ↔ hit (S i) x := by
    intro i x
    change Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = true ↔ _
    rw [he]
    simp [hit]
  have hh := prove S hs h gs hg out he'
  have one (i : Fin m) : (S i).card - 1 = 1 + (if 3 ≤ (S i).card then 1 else 0) := by
    have := hs i
    have := hu i
    split <;> omega
  simpa [one, Finset.sum_add_distrib, Fintype.card_subtype] using hh

-- Backward expansion counts each paid gate at most once, even with shared wires.
private lemma frontier {α : Type} [DecidableEq α] (d : ℕ → Finset α) (paid : Finset ℕ)
    (single : ∀ i, i ∉ paid → (d i).card ≤ 1)
    (step' : ∀ i ∈ paid, ∃ P : Finset ℕ, P ⊆ Finset.range i ∧ P.card ≤ 2 ∧
      d i ⊆ P.biUnion d) (t : ℕ) (Q : Finset ℕ) (hq : Q ⊆ Finset.range t) :
    (Q.biUnion d).card ≤ Q.card + (paid ∩ Finset.range t).card := by
  classical
  induction t generalizing Q with
  | zero =>
    have : Q = ∅ := Finset.subset_empty.mp (by simpa using hq)
    simp [this]
  | succ t ih =>
    by_cases ht : t ∈ Q
    · let R := Q.erase t
      have hr : R ⊆ Finset.range t := by
        intro x hx
        obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hx
        have := Finset.mem_range.mp (hq hmem)
        exact Finset.mem_range.mpr (by omega)
      have heq : insert t R = Q := Finset.insert_erase ht
      have hcard : R.card + 1 = Q.card := Finset.card_erase_add_one ht
      have hU : Q.biUnion d = d t ∪ R.biUnion d := by rw [← heq, Finset.biUnion_insert]
      by_cases hp : t ∈ paid
      · obtain ⟨P,hP,h2,hs⟩ := step' t hp
        have hsub : Q.biUnion d ⊆ (P ∪ R).biUnion d := by
          rw [hU, Finset.union_biUnion]
          exact Finset.union_subset_union hs (Finset.Subset.refl _)
        have h1 := (Finset.card_le_card hsub).trans (ih (P ∪ R) (Finset.union_subset hP hr))
        have h3 := Finset.card_union_le P R
        have h4 : paid ∩ Finset.range (t+1) = insert t (paid ∩ Finset.range t) := by
          ext x
          simp [Finset.range_add_one, hp]
        rw [h4, Finset.card_insert_of_notMem (by simp)]
        omega
      · have h1 := ih R hr
        have h2 := Finset.card_union_le (d t) (R.biUnion d)
        have h3 := single t hp
        have h4 := Finset.card_le_card (Finset.inter_subset_inter_left (s := paid)
          (Finset.range_mono (Nat.le_succ t)))
        change (paid ∩ Finset.range t).card ≤ (paid ∩ Finset.range (t+1)).card at h4
        rw [hU]
        omega
    · have hq' : Q ⊆ Finset.range t := by
        intro x hx
        have := Finset.mem_range.mp (hq hx)
        exact Finset.mem_range.mpr (by by_contra! hh; exact ht ((by omega : x = t) ▸ hx))
      have h1 := ih Q hq'
      have h2 := Finset.card_le_card (Finset.inter_subset_inter_left (s := paid)
        (Finset.range_mono (Nat.le_succ t)))
      change (paid ∩ Finset.range t).card ≤ (paid ∩ Finset.range (t+1)).card at h2
      omega

theorem row_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (a : Fin m)
    (hs : ∀ i, 2 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    (S a).card + m ≤ gs.length + 2 := by
  classical
  have he' (i) (x) : V gs (out i) x = decide (hit (S i) x) := by
    change Circuit.eval ⟨gs,out i⟩ _ = _
    rw [he]
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun hp => decide_eq_true (of_decide_eq_true hp : ∃ p ∈ S i, x p = true),
      fun hp => decide_eq_true (of_decide_eq_true hp : hit (S i) x)⟩
  have hv (i) := out_valid gs (out i) (S i) (hs i)
    (fun x => by rw [he']; simp)
  have inj : Function.Injective out := by
    intro i j e
    by_contra ne
    obtain ⟨p,hi,hj⟩ := diff S hs h ne
    have hh := he' i (point p)
    rw [e, he'] at hh
    simp [hit_point, hi, hj] at hh
  let marked := (Finset.univ.erase a).image out
  let gates := Finset.Ico n (n+gs.length)
  let paid := gates \ marked
  let d (i : ℕ) := (S a).filter fun p => V gs i (point p) ≠ V gs i (fun _ : Fin n => false)
  have ho (j) : d (out j) = S a ∩ S j := by
    ext p
    simp [d, he', hit, point]
  have hmarked : marked ⊆ gates := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (hv j)
  have hcmark : marked.card + 1 = m := by
    dsimp [marked]
    rw [Finset.card_image_of_injective _ inj, Finset.card_erase_add_one (Finset.mem_univ a)]
    simp
  have hcpaid : paid.card = gs.length - marked.card := by
    simp [paid, Finset.card_sdiff_of_subset hmarked, gates]
  have single (i) (hi : i ∉ paid) : (d i).card ≤ 1 := by
    by_cases hm : i ∈ marked
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
      rw [ho]; exact h a j (Finset.mem_erase.mp hj).1.symm
    · have hn : i ∉ gates := fun hi' => hi (Finset.mem_sdiff.mpr ⟨hi',hm⟩)
      by_cases hl : i < n
      · rw [Finset.card_le_one]
        intro p hp q hq
        simp [d,raw gs _ i hl, point] at hp hq
        exact hp.2.symm.trans hq.2
      · have hh : n+gs.length ≤ i := by
          simp only [gates, Finset.mem_Ico] at hn
          omega
        have hz (x : Fin n → Bool) : V gs i x = false := by
          unfold V; apply List.getD_eq_default; simpa [length_run] using hh
        simp [d, hz]
  have step' (i) (hi : i ∈ paid) : ∃ P : Finset ℕ, P ⊆ Finset.range i ∧
      P.card ≤ 2 ∧ d i ⊆ P.biUnion d := by
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hi).1
    let j := i-n
    have hj : j < gs.length := by dsimp [j]; omega
    have eq : n+j = i := by dsimp [j]; omega
    let g := gs[j]
    let P := g.inputs.toFinset ∩ Finset.range i
    refine ⟨P,Finset.inter_subset_right, ?_,?_⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans
        (g.inputs.toFinset_card_le.trans (hg g (List.getElem_mem hj)))
    · intro p hp
      obtain ⟨ha,hneq⟩ := Finset.mem_filter.mp hp
      by_contra hnone
      apply hneq
      have ev (x : Fin n → Bool) := eval_gate gs j hj x
      rw [← eq, ev, ev]
      congr 1
      apply List.map_congr_left
      intro k hk
      by_cases hki : k < n+j
      · simp only [ite_eq_left hki]
        by_contra hd
        exact hnone (Finset.mem_biUnion.mpr ⟨k,Finset.mem_inter.mpr
          ⟨List.mem_toFinset.mpr hk,Finset.mem_range.mpr (eq ▸ hki)⟩,
          Finset.mem_filter.mpr ⟨ha,hd⟩⟩)
      · simp [hki]
  have hh := frontier d paid single step' (out a+1) {out a} (by simp)
  simp only [Finset.singleton_biUnion,ho,Finset.inter_self,Finset.card_singleton] at hh
  have hle := Finset.card_le_card (Finset.inter_subset_left : paid ∩ Finset.range (out a+1) ⊆ paid)
  have hle' : marked.card ≤ gs.length := by simpa [gates] using Finset.card_le_card hmarked
  omega


theorem one_large_row {n m : ℕ} (S : Fin m → Finset (Fin n)) (a : Fin m)
    (hs : ∀ i, 2 ≤ (S i).card) (hpairs : ∀ j, j ≠ a → (S j).card = 2)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  have rb := row_bound S a hs h gs hg out he
  have hcard : (Finset.univ.erase a).card + 1 = m := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ a)
  have hsum : ∑ i ∈ Finset.univ.erase a, ((S i).card - 1) = (Finset.univ.erase a).card := by
    calc _ = ∑ _ ∈ Finset.univ.erase a, (1 : ℕ) := by
           apply Finset.sum_congr rfl
           intro i hi
           rw [hpairs i (Finset.mem_erase.mp hi).1]
         _ = _ := by simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),hsum]
  have := hs a
  omega
private theorem sole_not_antitone {n : ℕ} (gs : List Gate) (z : Fin gs.length)
    (hz : (gs.get z).op = .not)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hu : ∀ j : Fin gs.length, (gs.get j).op = .not → j = z) :
    Antitone (V gs (n+z.val) : (Fin n → Bool) → Bool) := by
  have pre (k : ℕ) : k < n+z.val → Monotone (V gs k : (Fin n → Bool) → Bool) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk x y hxy
      by_cases rawk : k < n
      · simpa only [raw gs _ k rawk] using hxy ⟨k,rawk⟩
      · let j := k-n
        have hj : j < gs.length := by have := z.isLt; dsimp [j]; omega
        have heq : n+j = k := by dsimp [j]; omega
        have hw (i : ℕ) : (if i < n+j then V gs i x else false) ≤
            (if i < n+j then V gs i y else false) := by
          split_ifs with hi
          · exact ih i (heq ▸ hi) (by omega) hxy
          · exact le_rfl
        rw [← heq,eval_gate gs j hj,eval_gate gs j hj,Bool.le_iff_imp]
        rcases hops _ (List.getElem_mem hj) with ha | ho | hn
        · simp only [ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          exact fun hh i hii => Bool.le_iff_imp.mp (hw i) (hh i hii)
        · simp only [ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨i,hii,hh⟩
          exact ⟨i,hii,Bool.le_iff_imp.mp (hw i) hh⟩
        · have eq := congrArg Fin.val (hu ⟨j,hj⟩ hn)
          change j = z.val at eq
          omega
  intro x y hxy
  rw [eval_gate gs z.val z.isLt,eval_gate gs z.val z.isLt]
  change gs[z.val].op = .not at hz
  rw [hz]
  cases hargs : gs[z.val].inputs with
  | nil => exact le_rfl
  | cons k ks =>
    simp only [GateOp.eval,List.map_cons,List.headD_cons]
    by_cases hk : k < n + z.val
    · simp only [ite_eq_left hk]
      have hh := pre k hk hxy
      cases h1 : V gs k x <;> cases h2 : V gs k y <;> simp_all [Bool.le_iff_imp]
    · simp [hk]

theorem one_not_count {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (z : Fin gs.length) (hz : (gs.get z).op = .not)
    (hu : ∀ j : Fin gs.length, (gs.get j).op = .not → j = z) :
    m + Fintype.card {i : Fin m // 3 ≤ (S i).card} + 1 ≤ gs.length := by
  classical
  have he' (i) (x) : V gs (out i) x = true ↔ hit (S i) x := by
    change Circuit.eval ⟨gs,out i⟩ _ = true ↔ _
    rw [he]; simp [hit]
  have ant := sole_not_antitone (n := n) gs z hz (fun g hg' => (hg g hg').1) hu
  have base (x : Fin n → Bool) : (fun _ : Fin n => false) ≤ x := fun _ => Bool.false_le _
  have top' (x : Fin n → Bool) : x ≤ (fun _ : Fin n => true) := fun _ => Bool.le_true _
  have reserved (i : Fin m) : out i ≠ n + z.val ∧ ¬role S gs i (n+z.val) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by have := hs i; omega : 0 < (S i).card)
    have ht : hit (S i) (fun _ => true) := ⟨p,hp,rfl⟩
    have hf : ¬hit (S i) (fun _ => false) := by simp [hit]
    constructor
    · intro eo
      have t := (he' i _).mpr ht
      rw [eo] at t
      have f := Bool.le_iff_imp.mp (ant (base _)) t
      rw [← eo] at f
      exact hf ((he' i _).mp f)
    · rintro (⟨small,p',_,_,hp',_⟩ | ⟨big,zero⟩ | ⟨_,j,hj,hop⟩)
      · exact hf (small _ (Bool.le_iff_imp.mp (ant (base _)) hp'))
      · have bad := Bool.le_iff_imp.mp (ant (top' (off (S i)))) (big _ ht)
        rw [zero] at bad
        contradiction
      · obtain rfl := hu j hop
        omega
  simpa using count_reserved S hs h gs hg out he' {z} (by simpa using reserved)


theorem width_four_with_one_not {n m : ℕ} (S : Fin m → Finset (Fin n)) (a : Fin m)
    (hs : ∀ i, 2 ≤ (S i).card) (ha : (S a).card ≤ 4)
    (hrest : ∀ j, j ≠ a → (S j).card ≤ 3)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (z : Fin gs.length) (hz : (gs.get z).op = .not)
    (hu : ∀ j : Fin gs.length, (gs.get j).op = .not → j = z) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  have hh := one_not_count S hs h gs hg out he z hz hu
  have cost (i : Fin m) : (S i).card - 1 ≤
      (1 + (if 3 ≤ (S i).card then 1 else 0)) + (if i = a then 1 else 0) := by
    have := hs i
    by_cases eq : i = a
    · subst i; split_ifs <;> omega
    · have := hrest i eq; split_ifs <;> omega
  apply le_trans (Finset.sum_le_sum (fun i _ => cost i))
  simpa [Finset.sum_add_distrib, Fintype.card_subtype] using hh

private lemma component_labels {α : Type} [DecidableEq α] (U : Finset α)
    (d : ℕ → Finset α) (paid : Finset ℕ) (single : ∀ i, i ∉ paid →
      (d i).card ≤ 1 ∨ ∃ k < i, d i ⊆ d k)
    (splitGate : ∀ i ∈ paid, ∃ P : Finset ℕ, P ⊆ Finset.range i ∧ P.card ≤ 2 ∧
      d i ⊆ P.biUnion d) (t : ℕ) :
    ∃ l : α → α, (∀ k < t, ∀ p ∈ d k, ∀ q ∈ d k, l p = l q) ∧
      U.card ≤ (U.image l).card + (paid ∩ Finset.range t).card := by
  classical
  induction t with
  | zero => exact ⟨id, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨l, mono, hc⟩ := ih
    by_cases same : ∀ p ∈ d t, ∀ q ∈ d t, l p = l q
    · refine ⟨l, ?_, hc.trans (Nat.add_le_add_left (Finset.card_le_card
        (Finset.inter_subset_inter_left (Finset.range_mono (Nat.le_succ t)))) _)⟩
      intro k hk
      by_cases eq : k = t
      · simpa [eq] using same
      · exact mono k (by omega)
    · push Not at same
      obtain ⟨p,hp,q,hq,hn⟩ := same
      have ht : t ∈ paid := by
        by_contra hnot
        rcases single _ hnot with small | ⟨k,hk,hsub⟩
        · exact hn (congrArg l (Finset.card_le_one.mp small _ hp _ hq))
        · exact hn (mono _ hk _ (hsub hp) _ (hsub hq))
      obtain ⟨P,hP,hP2,hcover⟩ := splitGate t ht
      have hcount : ((d t).image l).card ≤ 2 := by
        have hsub : (d t).image l ⊆ P.biUnion (fun k => (d k).image l) := by
          intro a ha
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨k,hk,hx⟩ := Finset.mem_biUnion.mp (hcover hx)
          exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image_of_mem l hx⟩
        calc _ ≤ _ := Finset.card_le_card hsub
             _ ≤ ∑ k ∈ P, ((d k).image l).card := Finset.card_biUnion_le
             _ ≤ ∑ _ ∈ P, 1 := by
               apply Finset.sum_le_sum
               intro k hk
               rw [Finset.card_le_one]
               intro a ha b hb
               obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
               obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
               exact mono k (Finset.mem_range.mp (hP hk)) x hx y hy
             _ ≤ 2 := by simpa using hP2
      let f (x : α) := if x = l q then l p else x
      have merge (x : α) (hx : x ∈ d t) : f (l x) = l p := by
        have lx := Finset.mem_image_of_mem l hx
        by_cases eq1 : l x = l p
        · simp [f,eq1]
        by_cases eq2 : l x = l q
        · simp [f,eq2]
        have sub : ({l x,l p,l q} : Finset α) ⊆ (d t).image l := by
          simp [Finset.insert_subset_iff,lx,Finset.mem_image_of_mem l hp,
            Finset.mem_image_of_mem l hq]
        have bound := Finset.card_le_card sub
        simp [Finset.card_insert_of_notMem,eq1,eq2,hn] at bound
        omega
      refine ⟨fun x => f (l x), ?_, ?_⟩
      · intro k hk x hx y hy
        by_cases eq : k = t
        · subst k; exact (merge x hx).trans (merge y hy).symm
        · exact congrArg f (mono k (by omega) x hx y hy)
      · have hsub : U.image l ⊆ insert (l q) (U.image fun x => f (l x)) := by
          intro a ha
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
          by_cases eq : l x = l q
          · simp [eq]
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,by simp [f,eq]⟩)
        have hbound := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have hw : paid ∩ Finset.range (t+1) = insert t (paid ∩ Finset.range t) := by
          ext x; simp [Finset.range_add_one,ht]
        rw [hw, Finset.card_insert_of_notMem (by simp)]
        omega

private def bump {n : ℕ} (A : Finset (Fin n)) (p : Fin n) (v : Fin n) : Bool :=
  decide (v ∉ A ∨ v = p)

-- I indexes the outputs whose full input sets we count. Other marked outputs
-- are constant along every test in this argument.
theorem simultaneous_free {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (T : Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (E : Finset ℕ)
    (free : ∀ k ∈ E, ∃ j : Fin gs.length, k = n+j.val ∧ (gs.get j).op = .not)
    (separate : ∀ k ∈ E, ∀ i ∉ I, out i ≠ k)
    (roots : ∀ p ∈ I.biUnion S, ∃ q ∈ T, Relation.ReflTransGen
      (fun u v => ∃ i ∈ I, u ∈ S i ∧ v ∈ S i) p q) :
    (I.biUnion S).card + (m-I.card) + E.card ≤ gs.length + T.card := by
  classical
  have hev (i) (x) : V gs (out i) x = true ↔ hit (S i) x := by
    change Circuit.eval ⟨gs,out i⟩ _ = true ↔ _
    rw [he]; simp [hit]
  have valid i := out_valid gs (out i) (S i) (hs i) (hev i)
  have inj : Function.Injective out := by
    intro i j eq
    by_contra ne
    obtain ⟨p,hp,hj⟩ := diff S hs h ne
    have good := (hev i _).mpr ((hit_point _ _).mpr hp)
    rw [eq] at good
    exact hj ((hit_point _ _).mp ((hev j _).mp good))
  let U := I.biUnion S
  let d (k : ℕ) := U.filter fun p => ∃ i ∈ I, p ∈ S i ∧
       V gs k (off (S i)) ≠ V gs k (bump (S i) p)
  have witness (i j) (p : Fin n) (hp : p ∈ S i) :
      V gs (out j) (off (S i)) ≠ V gs (out j) (bump (S i) p) ↔ j = i := by
    by_cases eq : j = i
    · subst j
      have lo : V gs (out i) (off (S i)) ≠ true := mt (hev i _).mp (hit_off_self _)
      have hi := (hev i (bump (S i) p)).mpr ⟨p,hp,by simp [bump]⟩
      simp [hi,lo]
    · obtain ⟨v,hv,hni⟩ := diff S hs h eq
      have lo := (hev j (off (S i))).mpr ⟨v,hv,by simp [off,hni]⟩
      have hi := (hev j (bump (S i) p)).mpr ⟨v,hv,by simp [bump,hni]⟩
      simp [lo,hi,eq]
  have mark (j) : ∀ p, p ∈ d (out j) ↔ j ∈ I ∧ p ∈ S j := by
    intro p
    constructor
    · intro hd
      obtain ⟨_,i,hi,hp,hd⟩ := Finset.mem_filter.mp hd
      obtain rfl := (witness i j p hp).mp hd
      exact ⟨hi,hp⟩
    · rintro ⟨hj,hp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j,hj,hp⟩,
        j,hj,hp,(witness j j p hp).mpr rfl⟩
  let skip := (Finset.univ \ I).image out
  let G := Finset.Ico n (n+gs.length)
  let paid := G \ (skip ∪ E)
  have subskip : skip ⊆ G := by
    intro k hk
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ico.mpr (valid j)
  have subE : E ⊆ G := by
    intro k hk
    obtain ⟨j,rfl,_⟩ := free k hk
    exact Finset.mem_Ico.mpr ⟨by omega,by have := j.isLt; omega⟩
  have dis : Disjoint skip E := by
    rw [Finset.disjoint_left]
    intro k hk he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact (separate _ he i (Finset.mem_sdiff.mp hi).2) rfl
  have one (k) (hk : k ∉ paid) :
      (d k).card ≤ 1 ∨ ∃ w < k, d k ⊆ d w := by
    by_cases ek : k ∈ E
    · obtain ⟨j,rfl,hnot⟩ := free _ ek
      change gs[j.val].op = .not at hnot
      cases hargs : gs[j.val].inputs with
      | nil =>
        have val (x : Fin n → Bool) : V gs (n+j.val) x = true := by
          rw [eval_gate gs j.val j.isLt,hnot,hargs]; rfl
        left; simp [d,val]
      | cons w ws =>
        have val (x : Fin n → Bool) :
            V gs (n+j.val) x = !(if w < n+j.val then V gs w x else false) := by
          rw [eval_gate gs j.val j.isLt,hnot,hargs]; rfl
        by_cases hw : w < n+j.val
        · right; refine ⟨w,hw,?_⟩
          intro p hp
          obtain ⟨ha,i,hi,hm,hne⟩ := Finset.mem_filter.mp hp
          refine Finset.mem_filter.mpr ⟨ha,i,hi,hm,?_⟩
          intro eq
          apply hne
          simp only [val,ite_eq_left hw,eq]
        · left; simp [d,val,hw]
    left
    by_cases sk : k ∈ skip
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp sk
      have : d (out j) = ∅ := by
        ext p; simp [mark, (Finset.mem_sdiff.mp hj).2]
      simp [this]
    · have nG : k ∉ G := fun hk' => hk (Finset.mem_sdiff.mpr ⟨hk',by simp [sk,ek]⟩)
      by_cases low : k < n
      · have only (p : Fin n) (hp : p ∈ d k) : p = ⟨k,low⟩ := by
          obtain ⟨_,i,_,_,hh⟩ := Finset.mem_filter.mp hp
          by_contra ne
          exact hh (by simp [raw gs _ k low,off,bump,Ne.symm ne])
        rw [Finset.card_le_one]
        exact fun p hp q hq => (only p hp).trans (only q hq).symm
      · have high : n+gs.length ≤ k := by simp only [G,Finset.mem_Ico] at nG; omega
        have bad (x : Fin n → Bool) : V gs k x = false := by
          unfold V; apply List.getD_eq_default; simpa [length_run] using high
        simp [d,bad]
  have expand (k) (hk : k ∈ paid) : ∃ P : Finset ℕ, P ⊆ Finset.range k ∧
      P.card ≤ 2 ∧ d k ⊆ P.biUnion d := by
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hk).1
    let j := k-n
    have hj : j < gs.length := by dsimp [j]; omega
    have eq : n+j = k := by dsimp [j]; omega
    let g := gs[j]
    let P := g.inputs.toFinset ∩ Finset.range k
    refine ⟨P,Finset.inter_subset_right, ?_,?_⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans
        (g.inputs.toFinset_card_le.trans (hg g (List.getElem_mem hj)))
    · intro p hp
      obtain ⟨ha,i,hi,hp',hneq⟩ := Finset.mem_filter.mp hp
      by_contra hnone
      apply hneq
      have ev (x : Fin n → Bool) := eval_gate gs j hj x
      rw [← eq,ev,ev]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases hwk : w < n+j
      · simp only [ite_eq_left hwk]
        by_contra hd
        exact hnone (Finset.mem_biUnion.mpr ⟨w,Finset.mem_inter.mpr
          ⟨List.mem_toFinset.mpr hw,Finset.mem_range.mpr (eq ▸ hwk)⟩,
          Finset.mem_filter.mpr ⟨ha,i,hi,hp',hd⟩⟩)
      · simp [hwk]
  obtain ⟨l,mono,hc⟩ := component_labels U d paid one expand (n+gs.length)
  have path {p q} (hh : Relation.ReflTransGen
      (fun u v => ∃ i ∈ I, u ∈ S i ∧ v ∈ S i) p q) : l p = l q := by
    induction hh with
    | refl => rfl
    | tail _ link ih =>
      obtain ⟨i,hi,hu,hv⟩ := link
      exact ih.trans (mono _ (valid i).2 _ ((mark _ _).mpr ⟨hi,hu⟩)
        _ ((mark _ _).mpr ⟨hi,hv⟩))
  have subimg : U.image l ⊆ T.image l := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q,hq,hh⟩ := roots p hp
    exact Finset.mem_image.mpr ⟨q,hq,(path hh).symm⟩
  have him := (Finset.card_le_card subimg).trans (@Finset.card_image_le _ _ T l _)
  have shr := Finset.card_le_card (Finset.inter_subset_left : paid ∩ Finset.range (n+gs.length) ⊆ paid)
  have hskip : skip.card = m-I.card := by
    simp [skip,Finset.card_image_of_injective _ inj,Finset.card_sdiff_of_subset]
  have suball := Finset.union_subset subskip subE
  have hcost : paid.card = gs.length-(skip.card + E.card) := by
    rw [Finset.card_sdiff_of_subset suball,Finset.card_union_of_disjoint dis]
    simp [G]
  have hle := Finset.card_le_card suball
  rw [Finset.card_union_of_disjoint dis] at hle
  simp only [G,Nat.card_Ico,Nat.add_sub_cancel_left] at hle
  change U.card + _ + E.card ≤ _
  omega

theorem simultaneous {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (T : Finset (Fin n)) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (roots : ∀ p ∈ I.biUnion S, ∃ q ∈ T, Relation.ReflTransGen
      (fun u v => ∃ i ∈ I, u ∈ S i ∧ v ∈ S i) p q) :
    (I.biUnion S).card + (m-I.card) ≤ gs.length + T.card := by
  simpa using simultaneous_free S I T hs h gs hg out he ∅ (by simp) (by simp) roots

theorem two_large_rows {n m : ℕ} (S : Fin m → Finset (Fin n)) (a b : Fin m) (hab : a ≠ b)
    (hs : ∀ i, 2 ≤ (S i).card) (pairs : ∀ i, i ≠ a → i ≠ b → (S i).card = 2)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  let I : Finset (Fin m) := {a,b}
  have ca : ∀ i, ((S i).card - 1) = 1 + (if i = a then (S a).card - 2 else 0)
      + (if i = b then (S b).card - 2 else 0) := by
    intro i
    by_cases ha : i = a
    · subst i; have := hs a; simp [hab]; omega
    by_cases hb : i = b
    · subst i; have := hs b; simp [Ne.symm hab]; omega
    · simp [ha,hb,pairs i ha hb]
  rw [Finset.sum_congr rfl (fun i _ => ca i)]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have ha := hs a
  have hb := hs b
  have hc := Finset.card_union_add_card_inter (S a) (S b)
  have hI : I.card = 2 := Finset.card_pair hab
  have hU : I.biUnion S = S a ∪ S b := by simp [I]
  have m2 : 2 ≤ m := by simpa [hI] using Finset.card_le_card (Finset.subset_univ I)
  by_cases nonempty : (S a ∩ S b).Nonempty
  · obtain ⟨v,hv⟩ := nonempty
    have hc1 := h a b hab
    have root : ∀ p ∈ I.biUnion S, ∃ q ∈ ({v} : Finset (Fin n)), Relation.ReflTransGen
        (fun u w => ∃ i ∈ I, u ∈ S i ∧ w ∈ S i) p q := by
      intro p hp
      refine ⟨v,Finset.mem_singleton_self _,.single ?_⟩
      rw [hU] at hp
      rcases Finset.mem_union.mp hp with h1 | h1
      · exact ⟨a, by simp [I], h1,(Finset.mem_inter.mp hv).1⟩
      · exact ⟨b, by simp [I], h1,(Finset.mem_inter.mp hv).2⟩
    have hh := simultaneous S I {v} hs h gs hg out he root
    rw [hI,hU,Finset.card_singleton] at hh
    omega
  · obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (S a).card)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (S b).card)
    have root : ∀ p ∈ I.biUnion S, ∃ q ∈ ({u,v} : Finset (Fin n)), Relation.ReflTransGen
        (fun u w => ∃ i ∈ I, u ∈ S i ∧ w ∈ S i) p q := by
      intro p hp
      rw [hU] at hp
      rcases Finset.mem_union.mp hp with h1 | h1
      · exact ⟨u,by simp,.single ⟨a,by simp [I],h1,hu⟩⟩
      · exact ⟨v,by simp,.single ⟨b,by simp [I],h1,hv⟩⟩
    have hh := simultaneous S I {u,v} hs h gs hg out he root
    rw [hI,hU] at hh
    have hpair := Finset.card_insert_le u ({v} : Finset (Fin n))
    rw [Finset.card_singleton] at hpair
    have hz : (S a ∩ S b).card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp nonempty)
    omega

private def paths {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m)) (p q : Fin n) :=
  Relation.ReflTransGen (fun u v => ∃ i ∈ I, u ∈ S i ∧ v ∈ S i) p q

private theorem small_core {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (I : Finset (Fin m)) (hI : I.card ≤ 3) :
    ∃ T : Finset (Fin n), (∀ p ∈ I.biUnion S, ∃ q ∈ T, paths S I p q) ∧
      (∑ i ∈ I, ((S i).card-1)) + T.card ≤ (I.biUnion S).card + (if I.card = 3 then 1 else 0) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a I ha ih =>
    rw [Finset.card_insert_of_notMem ha] at hI
    obtain ⟨T,hroot,hcost⟩ := ih (by omega)
    have ne3 : I.card ≠ 3 := by omega
    rw [ite_eq_right ne3,Nat.add_zero] at hcost
    have lift {p q} (e : paths S I p q) : paths S (insert a I) p q := by
      induction e with
      | refl => exact .refl
      | tail _ link ih =>
        obtain ⟨j,hj,hp,hq⟩ := link
        exact .tail ih ⟨j,Finset.mem_insert_of_mem hj,hp,hq⟩
    have hmeet : (S a ∩ I.biUnion S).card ≤ I.card := by
      have heq : S a ∩ I.biUnion S = I.biUnion (fun j => S a ∩ S j) := by
        ext p; simp; grind
      rw [heq]
      calc _ ≤ ∑ j ∈ I, (S a ∩ S j).card := Finset.card_biUnion_le
           _ ≤ ∑ _ ∈ I, 1 := Finset.sum_le_sum (fun j hj => h a j (fun eq => ha (eq ▸ hj)))
           _ = _ := by simp
    have hcard := Finset.card_union_add_card_inter (S a) (I.biUnion S)
    have hpos := hs a
    by_cases ov : (S a ∩ I.biUnion S).Nonempty
    · obtain ⟨v,hv⟩ := ov
      obtain ⟨r,hr,join⟩ := hroot v (Finset.mem_inter.mp hv).2
      refine ⟨T,?_,?_⟩
      · intro p hp
        rw [Finset.biUnion_insert] at hp
        rcases Finset.mem_union.mp hp with hi | hi
        · refine ⟨r,hr,Relation.ReflTransGen.head ?_ (lift join)⟩
          exact ⟨a,Finset.mem_insert_self _ _,hi,(Finset.mem_inter.mp hv).1⟩
        · obtain ⟨q,hq,hh⟩ := hroot p hi
          exact ⟨q,hq,lift hh⟩
      · rw [Finset.sum_insert ha,Finset.biUnion_insert,Finset.card_insert_of_notMem ha]
        split_ifs <;> omega
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (S a).card)
      have hz : (S a ∩ I.biUnion S).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ov)
      refine ⟨insert v T,?_,?_⟩
      · intro p hp
        rw [Finset.biUnion_insert] at hp
        rcases Finset.mem_union.mp hp with hi | hi
        · exact ⟨v,Finset.mem_insert_self _ _,Relation.ReflTransGen.single
            ⟨a,Finset.mem_insert_self _ _,hi,hv⟩⟩
        · obtain ⟨q,hq,hh⟩ := hroot p hi
          exact ⟨q,Finset.mem_insert_of_mem hq,lift hh⟩
      · rw [Finset.sum_insert ha,Finset.biUnion_insert]
        have := Finset.card_insert_le v T
        split_ifs <;> omega

-- The budget counts repeated intersection points beyond the first at each insertion.
inductive SparseCore {n m : ℕ} (S : Fin m → Finset (Fin n)) : Finset (Fin m) → ℕ → Prop
  | empty : SparseCore S ∅ 0
  | insert {I a b} (prev : SparseCore S I b) (ha : a ∉ I) :
      SparseCore S (insert a I) (b + ((S a ∩ I.biUnion S).card - 1))
  | weaken {I b c} (prev : SparseCore S I b) (le : b ≤ c) : SparseCore S I c

private theorem sparse_core_roots {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 2 ≤ (S i).card) {I : Finset (Fin m)} {b : ℕ} (e : SparseCore S I b) :
    ∃ T : Finset (Fin n), (∀ p ∈ I.biUnion S, ∃ q ∈ T, paths S I p q) ∧
      (∑ i ∈ I, ((S i).card-1)) + T.card ≤ (I.biUnion S).card + b := by
  classical
  induction e with
  | empty => exact ⟨∅, by simp, by simp⟩
  | weaken _ le ih =>
    obtain ⟨T,hr,hc⟩ := ih
    exact ⟨T,hr,by omega⟩
  | @insert I a b _ ha ih =>
    obtain ⟨T,hroot,hcost⟩ := ih
    have lift {p q} (e : paths S I p q) : paths S (insert a I) p q := by
      induction e with
      | refl => exact .refl
      | tail _ link ih =>
        obtain ⟨j,hj,hp,hq⟩ := link
        exact .tail ih ⟨j,Finset.mem_insert_of_mem hj,hp,hq⟩
    have hcard := Finset.card_union_add_card_inter (S a) (I.biUnion S)
    have hpos := hs a
    by_cases ov : (S a ∩ I.biUnion S).Nonempty
    · obtain ⟨v,hv⟩ := ov
      obtain ⟨r,hr,join⟩ := hroot v (Finset.mem_inter.mp hv).2
      refine ⟨T,?_,?_⟩
      · intro p hp
        rw [Finset.biUnion_insert] at hp
        rcases Finset.mem_union.mp hp with hi | hi
        · refine ⟨r,hr,Relation.ReflTransGen.head ?_ (lift join)⟩
          exact ⟨a,Finset.mem_insert_self _ _,hi,(Finset.mem_inter.mp hv).1⟩
        · obtain ⟨q,hq,hh⟩ := hroot p hi
          exact ⟨q,hq,lift hh⟩
      · rw [Finset.sum_insert ha,Finset.biUnion_insert]
        omega
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (S a).card)
      have hz : (S a ∩ I.biUnion S).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ov)
      refine ⟨insert v T,?_,?_⟩
      · intro p hp
        rw [Finset.biUnion_insert] at hp
        rcases Finset.mem_union.mp hp with hi | hi
        · exact ⟨v,Finset.mem_insert_self _ _,Relation.ReflTransGen.single
            ⟨a,Finset.mem_insert_self _ _,hi,hv⟩⟩
        · obtain ⟨q,hq,hh⟩ := hroot p hi
          exact ⟨q,Finset.mem_insert_of_mem hq,lift hh⟩
      · rw [Finset.sum_insert ha,Finset.biUnion_insert]
        have := Finset.card_insert_le v T
        omega

private theorem roots_one_not {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (hi : ∃ T : Finset (Fin n), (∀ p ∈ I.biUnion S, ∃ q ∈ T, paths S I p q) ∧
      (∑ i ∈ I, ((S i).card-1)) + T.card ≤ (I.biUnion S).card + 1) (pairs : ∀ i ∉ I, (S i).card = 2) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (z : Fin gs.length) (hz : (gs.get z).op = .not)
    (hu : ∀ j : Fin gs.length, (gs.get j).op = .not → j = z) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  obtain ⟨T,hr,hc⟩ := hi
  have ant := sole_not_antitone (n := n) gs z hz (fun g hg' => (hg g hg').1) hu
  have sep (i : Fin m) : out i ≠ n+z.val := by
    intro eq
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by have := hs i; omega : 0 < (S i).card)
    have t : V gs (out i) (fun _ : Fin n => true) = true := by
      change Circuit.eval ⟨gs,out i⟩ _ = _
      rw [he]; exact decide_eq_true ⟨p,hp,rfl⟩
    have f : V gs (out i) (fun _ : Fin n => false) = false := by
      change Circuit.eval ⟨gs,out i⟩ _ = _
      rw [he]; simp
    rw [eq] at t f
    have bad := Bool.le_iff_imp.mp (ant (show (fun _ : Fin n => false) ≤ (fun _ => true)
      from fun _ => Bool.false_le _)) t
    rw [f] at bad
    contradiction
  have hh := simultaneous_free S I T hs h gs (fun g hmem => (hg g hmem).2) out he {n+z.val}
    (by intro k hk; obtain rfl := Finset.mem_singleton.mp hk; exact ⟨z,rfl,hz⟩)
    (by intro k hk i _; obtain rfl := Finset.mem_singleton.mp hk; exact sep i) hr
  rw [Finset.card_singleton] at hh
  have rem : ∑ i ∈ Finset.univ \ I, ((S i).card-1) = m-I.card := by
    calc _ = ∑ _ ∈ Finset.univ \ I, 1 := Finset.sum_congr rfl (by
           intro i hmem; rw [pairs i (Finset.mem_sdiff.mp hmem).2])
         _ = _ := by simp [Finset.card_sdiff_of_subset]
  rw [← Finset.sum_sdiff (Finset.subset_univ I), rem]
  omega


private theorem roots_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (hi : ∃ T : Finset (Fin n), (∀ p ∈ I.biUnion S, ∃ q ∈ T, paths S I p q) ∧
      (∑ i ∈ I, ((S i).card-1)) + T.card ≤ (I.biUnion S).card + 1) (pairs : ∀ i ∉ I, (S i).card = 2) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (one : ∃ f : Fin 1 → Fin gs.length, ∀ j : Fin gs.length,
      (gs.get j).op = .not → ∃ k : Fin 1, f k = j)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  classical
  by_cases hinv : ∃ z : Fin gs.length, (gs.get z).op = .not
  · obtain ⟨z,hz⟩ := hinv
    obtain ⟨f,hf⟩ := one
    apply roots_one_not S I hi pairs hs h gs hg out he z hz
    intro j hj
    obtain ⟨k,rfl⟩ := hf j hj
    obtain ⟨l,rfl⟩ := hf z hz
    exact congrArg f (Subsingleton.elim _ _)
  · apply Mixed951.monotone_bound n m S h gs out _ he
    intro g hmem
    obtain ⟨hops,hsize⟩ := hg g hmem
    refine ⟨hops.imp_right (fun hor => hor.resolve_right ?_),hsize⟩
    intro hnot
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hmem
    apply hinv; refine ⟨⟨j,hj⟩,?_⟩; change gs[j].op = .not; rw [eq]; exact hnot

theorem three_large_rows {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (hi : I.card ≤ 3) (pairs : ∀ i ∉ I, (S i).card = 2) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (one : ∃ f : Fin 1 → Fin gs.length, ∀ j : Fin gs.length,
      (gs.get j).op = .not → ∃ k : Fin 1, f k = j)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  apply roots_bound S I _ pairs hs h gs hg one out he
  obtain ⟨T,hr,hc⟩ := small_core S hs h I hi
  exact ⟨T,hr,by split_ifs at hc <;> omega⟩

theorem sparse_large_rows {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (hi : SparseCore S I 1) (pairs : ∀ i ∉ I, (S i).card = 2) (hs : ∀ i, 2 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (one : ∃ f : Fin 1 → Fin gs.length, ∀ j : Fin gs.length,
      (gs.get j).op = .not → ∃ k : Fin 1, f k = j)
    (out : Fin m → ℕ) (he : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  exact roots_bound S I (sparse_core_roots S hs hi) pairs hs h gs hg one out he

end Mixed951
