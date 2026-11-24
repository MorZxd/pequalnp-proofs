import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3903_642
    (restricted : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → (∀ x : Fin 9 → Bool, x 0 = false →
      D.eval (List.ofFn x ++ [true]) = (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)) →
    D.gates.countP (fun g : Gate => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).any fun i => i == 0 || i == 9) ≤ 2)
    (remaining : ∀ pins : List ℕ, pins.length ≤ 2 → ∀ C : Circuit, FanInTwo C → C.size = 13 →
    (Gate.mk GateOp.or pins :: C.gates).countP (fun g : Gate => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).any fun i => i == 0 || i == 9) ≤ 2 →
    ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]
      C.eval (w ++ [GateOp.or.eval (pins.map fun i => w.getD i false)]) ≠ (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)) : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           (∃ x6 ∈ x3.gates, (10 : ℕ) ∈ x6.inputs) ∨ x3.output = (10 : ℕ) →             (∃ x7 ∈ x3.gates, (9 : ℕ) ∈ x7.inputs) ∨ (9 : ℕ) ∈ x1 ∨ x3.output = (9 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins hlen C fan size _ _
  classical
  by_contra! hn
  let D : Circuit := ⟨⟨.or,pins⟩ :: C.gates,C.output⟩
  have dFan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨by simp,hlen⟩
    · exact fan g h
  have dSize : D.size ≤ 14 := by
    change C.gates.length = 13 at size
    change C.gates.length + 1 ≤ 14
    omega
  have agree (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [!x 0]) = (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) := by
    have eq := Classical.byContradiction (hn x)
    apply eq.trans
    simp [Bool.or_assoc]
  have limit := restricted D dFan dSize (fun x h => by simpa only [h,Bool.not_false] using agree x)
  obtain ⟨x,hx⟩ := remaining pins hlen C fan size limit
  exact hx (agree x)
