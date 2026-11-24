import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_4035_641
    (compile : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → C.output ≠ 0 →
    (let readers := fun (i : ℕ) => C.gates.filter fun g =>
       (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
     (readers 0).length = 0 ∧ (readers 10).length ≤ 2) →
    ∃ (p : List (Fin 3 × Fin 32 × Fin 32)) (o : Fin 32), p.length ≤ 18 ∧ (p.filter (fun g => decide (g.2.1 = 2 ∨ (g.1 ≠ 2 ∧ g.2.2 = 2)))).length ≤ 2 ∧
    ∀ k : Fin 1024, (p.foldl (fun w g => w ++ [if g.1 = 0 then w.getD g.2.1.val false && w.getD g.2.2.val false
        else if g.1 = 1 then w.getD g.2.1.val false || w.getD g.2.2.val false
        else !w.getD g.2.1.val false])
      ([false,true] ++ List.ofFn (fun i : Fin 10 => if i = 0 then !((k.val + 0).testBit 0) else (k.val + 0).testBit i.val))).getD o.val false =
      C.eval (List.ofFn (fun i : Fin 10 => (k.val + 0).testBit i.val) ++ [!((k.val + 0).testBit 0)]))
    (exclude : ∀ (p : List (Fin 3 × Fin 32 × Fin 32)) (o : Fin 32), p.length ≤ 18 → (p.filter (fun g => decide (g.2.1 = 2 ∨ (g.1 ≠ 2 ∧ g.2.2 = 2)))).length ≤ 2 →
    ∃ k : Fin 1024, (p.foldl (fun w g => w ++ [if g.1 = 0 then w.getD g.2.1.val false && w.getD g.2.2.val false
        else if g.1 = 1 then w.getD g.2.1.val false || w.getD g.2.2.val false
        else !w.getD g.2.1.val false])
      ([false,true] ++ List.ofFn (fun i : Fin 10 => if i = 0 then !((k.val + 0).testBit 0) else (k.val + 0).testBit i.val))).getD o.val false ≠ (179769313486231590772930519078902473361797697894230657273430081157732675805415574637631938330974342149254676239332264626717371455201768760401339708730060862467599309626786222646154322922921861021930833718980811068645458870467698626365512840652500019744054405992546613330590959325515380975353348937279334971592 : ℕ).testBit k.val) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  classical
  intro C fan size computes noZero limited
  obtain ⟨a,b,covered⟩ := limited
  let active (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have act (j : Fin C.gates.length) (i : ℕ) :
      i ∈ active (C.gates.get j) ↔
        (((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some i) ∨
         ((C.gates.get j).op ≠ GateOp.not ∧ i ∈ (C.gates.get j).inputs)) := by
    let g := C.gates.get j
    have hh := fan g (List.get_mem ..)
    change i ∈ active g ↔ _
    change i ∈ active g ↔ ((g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs))
    have hAnd : GateOp.and.eval [false] = false := rfl
    have hOr : GateOp.or.eval [false] = false := rfl
    have hNot : GateOp.not.eval [false] = true := rfl
    rcases hh.1 with ha | ho | hn
    · simp [active, ha, hAnd, List.take_of_length_le hh.2]
    · simp [active, ho, hOr, List.take_of_length_le hh.2]
    · have hn : g.op = .not := hn
      cases eq : g.inputs with
      | nil => simp [active, hn, eq, hNot]
      | cons w ws => simp [active, hn, eq, hNot] <;> exact eq_comm
  have occur (i : ℕ) : (C.gates.filter (fun g => (active g).contains i)).length =
      (Finset.univ.filter (fun j : Fin C.gates.length => i ∈ active (C.gates.get j))).card := by
    simpa only [List.ofFn_get, List.countP_eq_length_filter, List.contains_iff_mem] using
      List.countP_ofFn C.gates.get (fun g => (active g).contains i)
  have counts : (C.gates.filter (fun g => (active g).contains 0)).length = 0 ∧
      (C.gates.filter (fun g => (active g).contains 10)).length ≤ 2 := by
    rw [occur,occur]
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      rcases (act j 0).mp (Finset.mem_filter.mp hj).2 with ⟨h,hi⟩ | ⟨h,hi⟩
      · exact (noZero j).1 h hi
      · exact (noZero j).2 h hi
    · have sub : Finset.univ.filter (fun j : Fin C.gates.length => 10 ∈ active (C.gates.get j)) ⊆ {a,b} := by
        intro j hj
        rcases (act j 10).mp (Finset.mem_filter.mp hj).2 with ⟨h,hi⟩ | ⟨h,hi⟩
        · simpa using (covered j).1 h hi
        · simpa using (covered j).2 h hi
      exact (Finset.card_le_card sub).trans (Finset.card_le_two)
  have out : C.output ≠ 0 := by
    intro h
    let x : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have good := computes x
    have edge : C.eval (List.ofFn x ++ [!x 0]) = true := good.trans (by decide)
    have keep (gs : List Gate) (w : List Bool) (hw : 0 < w.length) :
        (Circuit.mk gs 0).eval w = w.getD 0 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        let v := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        change (Circuit.mk gs 0).eval v = _
        rw [ih v (by simp [v])]
        exact List.getD_append _ _ _ _ hw
    change (Circuit.mk C.gates C.output).eval _ = true at edge
    rw [h,keep _ _ (by simp)] at edge
    exact (by decide : (List.ofFn x ++ [!x 0]).getD 0 false ≠ true) edge
  obtain ⟨p,o,sz,deg,eq⟩ := compile C fan size out counts
  obtain ⟨k, hk⟩ := exclude p o sz deg
  apply hk
  rw [eq]
  apply (computes (fun i : Fin 10 => (k.val + 0).testBit i.val)).trans
  clear hk
  revert k
  decide +kernel
