import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Defs.LratEncoding
-- Strip the first gate, then test its seventeen-gate suffix on the fifteen edge
-- inputs and the fifteen maximal independent sets. The fixed integer below
-- selects the orbit representatives for the unordered first-gate operands.
theorem PEqualNP.Outside.R_meta_5232_417
    (encode : ∀ (n s : ℕ) (C : Circuit) (σ : Equiv.Perm (Fin n)) (rows : List ℕ) (label : ℕ → Bool),
      Monotone2 C → C.size ≤ s → (∀ r ∈ rows, r < 2^n) →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin n => r.testBit (σ i).val)) = label r) →
      FormulaSat (enc n s label rows))
    (obstruction : ∀ (a b : Fin 11) (op : Fin 4),
      (1329228550382152642450328001106826591 : ℕ).testBit (11 * min a.val b.val + max a.val b.val) = true →
      let pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
      let lift := fun (r : ℕ) =>
        let w := r + if r.testBit 0 || r.testBit 2 then 1024 else 0
        let u := w.testBit a.val
        let v := w.testBit b.val
        w + if ([u && v, u || v, false, true] : List Bool).getD op.val false then 2048 else 0
      ¬ FormulaSat (enc 12 17 (fun r => decide (r % 1024 ∈ pos))
        ((pos ++ [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]).map lift))) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro C hm hr hs ho he
  by_contra! exactC
  have stripFirstGate (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 11 C)
      (hs : C.size ≤ 18) (ho : 11 ≤ C.output) (he : C.output < 11+C.size) :
      ∃ (g : Gate) (D : Circuit), (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 ∧
        (∀ i ∈ g.inputs, i < 11) ∧ Monotone2 D ∧ ReadsBack 12 D ∧ D.size ≤ 17 ∧
        11 ≤ D.output ∧ D.output < 12+D.size ∧
        ∀ x : List Bool, C.eval x = D.eval (x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))]) := by
    rcases C with ⟨gs,o⟩
    cases gs with
    | nil => change 11 ≤ o at ho; change o < 11 + 0 at he; omega
    | cons g gs =>
      let D : Circuit := ⟨gs,o⟩
      obtain ⟨op,arity⟩ := hm g (by simp)
      refine ⟨g,D,op,arity,?_,?_,?_,?_,ho,?_,?_⟩
      · intro i hi
        exact hr 0 (by simp) i hi
      · intro h hh
        exact hm h (List.mem_cons_of_mem _ hh)
      · intro j hj i hi
        have := hr (j+1) (by change j+1 < (g::gs).length; simpa [D] using hj) i
          hi
        omega
      · change gs.length ≤ 17
        change (g::gs).length ≤ 18 at hs
        simp at hs
        omega
      · change o < 12 + gs.length
        change o < 11 + (g::gs).length at he
        simp at he
        omega
      · intro x
        rfl
  have encodeFirstGate (g : Gate) (hop : g.op = .and ∨ g.op = .or) (hn : g.inputs.length ≤ 2)
      (hr : ∀ i ∈ g.inputs, i < 11) :
      ∃ a b : Fin 11, ∃ op : Fin 4, ∀ y : List Bool,
        g.op.eval (g.inputs.map fun i => y.getD i false) =
          ([y.getD a.val false && y.getD b.val false, y.getD a.val false || y.getD b.val false,
            false,true] : List Bool).getD op.val false := by
    rcases g with ⟨k,ins⟩
    change k = .and ∨ k = .or at hop
    change ins.length ≤ 2 at hn
    change ∀ i ∈ ins, i < 11 at hr
    rcases ins with _|⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
    · rcases hop with rfl|rfl
      · exact ⟨0,0,3,fun _ => rfl⟩
      · exact ⟨0,0,2,fun _ => rfl⟩
    · refine ⟨⟨a,hr a (by simp)⟩,⟨a,hr a (by simp)⟩,0,?_⟩
      intro y
      rcases hop with rfl|rfl
      · change (y.getD a false && true) = (y.getD a false && y.getD a false)
        simp
      · change (y.getD a false || false) = (y.getD a false && y.getD a false)
        simp
    · refine ⟨⟨a,hr a (by simp)⟩,⟨b,hr b (by simp)⟩,?_⟩
      rcases hop with rfl|rfl
      · refine ⟨0,?_⟩
        intro y
        change (y.getD a false && (y.getD b false && true)) = (y.getD a false && y.getD b false)
        simp
      · refine ⟨1,?_⟩
        intro y
        change (y.getD a false || (y.getD b false || false)) = (y.getD a false || y.getD b false)
        simp
    · simp at hn
  obtain ⟨g,D,gop,glen,gb,dm,_,ds,_,_,ev⟩ := stripFirstGate C hm hr hs ho he
  obtain ⟨i,j,op,hgate⟩ := encodeFirstGate g gop glen gb
  let p : Fin 4 → Fin 12 → Fin 12 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8, 10, 11], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8, 10, 11], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10, 11]]
  let perm (t : Fin 4) : Equiv.Perm (Fin 12) :=
    ⟨p t, p t, (by revert t; decide +kernel), (by revert t; decide +kernel)⟩
  let rep (t : Fin 4) (i : Fin 11) : Fin 11 := Fin.ofNat 11 (p t (Fin.castSucc i)).val
  have orbit : ∀ i j : Fin 11, ∃ t : Fin 4,
      (1329228550382152642450328001106826591 : ℕ).testBit (11 * min (rep t i).val (rep t j).val + max (rep t i).val (rep t j).val) = true := by decide +kernel
  obtain ⟨t,ht⟩ := orbit i j
  let a := rep t i
  let b := rep t j
  let pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
  let rows : List ℕ := pos ++ [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
  let f := fun (op : Fin 4) (u v : Bool) => ([u && v, u || v, false, true] : List Bool).getD op.val false
  let raw (r : ℕ) := r + if r.testBit 0 || r.testBit 2 then 1024 else 0
  let lift (r : ℕ) := raw r + if f op ((raw r).testBit a.val) ((raw r).testBit b.val) then 2048 else 0
  let x (r : ℕ) (v : Fin 10) := r.testBit (p t (Fin.ofNat 12 v.val)).val
  let base (r : ℕ) := List.ofFn (x r) ++ [x r 0 || x r 2]
  let pet := fun (x : Fin 10 → Bool) => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  have lab : ∀ t' : Fin 4, ∀ r ∈ rows,
      pet (fun (v : Fin 10) => r.testBit (p t' (Fin.ofNat 12 v.val)).val) = decide (r ∈ pos) := by decide +kernel
  have rawsmall : ∀ r ∈ rows, raw r < 2048 := by decide +kernel
  have rawmod : ∀ r ∈ rows, raw r % 1024 = r := by decide +kernel
  have small (r : ℕ) (h : r ∈ rows) : lift r < 4096 := by
    have := rawsmall r h; unfold lift; split <;> omega
  have lo (r : ℕ) (h : r ∈ rows) : lift r % 1024 = r := by
    have := rawmod r h; unfold lift; split <;> omega
  have basebits : ∀ t' : Fin 4, ∀ r ∈ rows, ∀ u : Fin 11,
      (List.ofFn (fun (v : Fin 10) => r.testBit (p t' (Fin.ofNat 12 v.val)).val) ++
        [r.testBit (p t' 0).val || r.testBit (p t' 2).val]).getD u.val false = (raw r).testBit (rep t' u).val := by decide +kernel
  have generalBits (w : ℕ) (h : w < 2048) (e : Bool) :
      (∀ l : Fin 11, (w + (if e then 2048 else 0)).testBit l.val = w.testBit l.val) ∧
      (w + (if e then 2048 else 0)).testBit 11 = e := by
    have off : w.testBit 11 = false := Nat.testBit_lt_two_pow (by exact h)
    cases e with
    | false => simp [off]
    | true =>
      simp only [ite_true]
      rw [Nat.add_comm w]
      exact ⟨fun l => Nat.testBit_two_pow_add_gt l.isLt w, by
        change (2^11+w).testBit 11 = true
        rw [Nat.testBit_two_pow_add_eq,off]; rfl⟩
  apply obstruction a b op ht
  apply encode 12 17 D (perm t) (rows.map lift) _ dm ds
  · intro v hv; obtain ⟨r,h,rfl⟩ := List.mem_map.mp hv; exact small r h
  · intro v hv; obtain ⟨r,h,rfl⟩ := List.mem_map.mp hv
    have bits := generalBits (raw r) (rawsmall r h) (f op ((raw r).testBit a.val) ((raw r).testBit b.val))
    have q (v : Fin 11) : (perm t (Fin.castSucc v)).val = (rep t v).val := by
      have H : ∀ t : Fin 4, ∀ v : Fin 11, (p t (Fin.castSucc v)).val = (rep t v).val := by decide +kernel
      exact H t v
    have last : (perm t 11).val = 11 := by
      have H : ∀ t : Fin 4, (p t 11).val = 11 := by decide +kernel
      exact H t
    have hg := hgate (base r)
    have hb (v : Fin 11) : (base r).getD v.val false = (raw r).testBit (rep t v).val := basebits t r h v
    rw [hb i,hb j] at hg
    have heq : List.ofFn (fun v : Fin 12 => (lift r).testBit ((perm t) v).val) =
        base r ++ [g.op.eval (g.inputs.map fun i => (base r).getD i false)] := by
      apply List.ext_getElem
      · simp [base]
      · intro k hk hl
        have kn : k < 12 := by simpa using hk
        by_cases u : k < 11
        · let v : Fin 11 := ⟨k,u⟩
          have qb := q v
          have bb := (bits.1 (rep t v)).trans (hb v).symm
          rw [List.getElem_ofFn, List.getElem_append_left (by simpa [base] using u)]
          rw [show (perm t ⟨k,kn⟩).val = (rep t v).val from qb]
          exact bb.trans (by simp [List.getD_eq_getElem?_getD,u,base,v])
        · have ek : k = 11 := by omega
          subst k
          rw [List.getElem_ofFn, show (perm t ⟨11,kn⟩).val = 11 from last]
          simpa [base,hg] using bits.2.trans hg.symm
    change D.eval _ = decide (lift r % 1024 ∈ pos)
    rw [heq, ← ev, lo r h]
    exact (exactC (x r)).trans (lab t r h)
