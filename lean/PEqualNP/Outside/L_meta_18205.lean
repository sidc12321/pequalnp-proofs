import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18205_aux

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

private def evalOne (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem gate_eq {n : Nat} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) (j : Nat) (hj : j < C.gates.length) :
    wval C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have h := fw_getD_gate evalOne C.gates (List.ofFn x) j hj false
  simp only [List.length_ofFn] at h
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  change (fw evalOne C.gates (List.ofFn x)).getD (n+j) false = _
  rw [h]
  unfold evalOne
  rw [← hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_take', if_pos (ao.2.1 j hj i hi)]
  rfl

private def marked {n : Nat} (C : Circuit) (a b : Fin n) (i : Nat) : Prop :=
  wval C (indW n {a.val}) i = true ∧ wval C (indW n {b.val}) i = false

private def arc {n : Nat} (C : Circuit) (a b : Fin n) (i j : Nat) : Prop :=
  n ≤ j ∧ i ∈ (gateAt C (j-n)).inputs ∧ marked C a b i ∧ marked C a b j

private theorem path {n : Nat} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
    (a b : Fin n) (i : Nat) (hi : i < n+C.gates.length) (hm : marked C a b i) :
    Relation.ReflTransGen (arc C a b) a.val i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hn : i < n
    · obtain ⟨tail, he⟩ := fw_prefix evalOne C.gates (List.ofFn (indW n {a.val}))
      have hx := hm.1
      change (fw evalOne C.gates (List.ofFn (indW n {a.val}))).getD i false = true at hx
      rw [he, getD_append_left' _ _ _ _ (by simpa using hn)] at hx
      have heq : i = a.val := by simpa [indW,List.getD_eq_getElem?_getD,hn] using hx
      subst i
      exact .refl
    · let j := i-n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have eq : n+j=i := by dsimp [j]; omega
      have hh := hm
      unfold marked at hh
      rw [← eq, gate_eq ao _ _ hj, gate_eq ao _ _ hj] at hh
      have hg : gateAt C j ∈ C.gates := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
      have ex : ∃ t ∈ (gateAt C j).inputs, marked C a b t := by
        by_contra! he
        have imp : ∀ t ∈ (gateAt C j).inputs, wval C (indW n {a.val}) t = true → wval C (indW n {b.val}) t = true := by
          intro t ht h
          cases hb : wval C (indW n {b.val}) t
          · exact False.elim (he t ht ⟨h,hb⟩)
          · rfl
        have ht := hh.1
        have hf := hh.2
        rcases ao.1 _ hg with hop|hop
        · simp [hop, GateOp.eval] at ht hf
          obtain ⟨z,hz,hnz⟩ := hf
          simpa [hnz] using imp z hz (ht z hz)
        · simp [hop, GateOp.eval] at ht hf
          obtain ⟨z,hz,hzv⟩ := ht
          simpa [hf z hz] using imp z hz hzv
      obtain ⟨t,ht,hm'⟩ := ex
      have lt := ao.2.1 j hj t ht
      exact (ih t (by omega) (by omega) hm').tail ⟨by omega, ht, hm', hm⟩

end PEqualNP.Outside.L_meta_18205_aux

open PEqualNP.Outside.L_meta_18205_aux PEqualNP.ReadTwo PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18205 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1) (x6 : ℕ),       PEqualNP.ReadTwo.isAnd x2 x6 →         have x8 : Fin x1 → ℕ → Bool := fun (x8 : Fin x1) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {↑x8});         have x9 : ℕ → Prop := fun (x9 : ℕ) => x8 x4 x9 = Bool.true ∧ x8 x5 x9 = Bool.false;         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => x1 ≤ x11 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x11 - x1)).inputs ∧ x9 x10 ∧ x9 x11;         x8 x4 (x1 + x6) = Bool.true → (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x8 x5 x12 = Bool.false) → ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x9 x13 ∧ Relation.ReflTransGen x10 (↑x4) x13) := by
  intro n C ao a b j hj
  dsimp only
  intro htrue hfalse i hi
  rw [gate_eq ao _ _ hj.1] at htrue
  simp [hj.2, GateOp.eval] at htrue
  have h : marked C a b i := ⟨htrue i hi,hfalse i hi⟩
  exact ⟨h,path ao a b i (by have := ao.2.1 j hj.1 i hi; have := hj.1; omega) h⟩
