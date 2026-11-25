import PEqualNP.Defs

-- The explicit monotone circuit gives the upper bound. The lower bound counts
-- binary gates with free complementation. On restrictions that identify or fix
-- inputs, the function becomes a smaller clique threshold. The finite search
-- accounts for each retained wire and each gate on the restricted inputs.
-- The live-circuit framework and the small clique bounds adapt the project
-- proofs L_meta_8449 and L_meta_8724 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩




end PEqualNP.Outside.L_meta_11763_aux.LiveCircuits

namespace PEqualNP.Outside.L_meta_11763_aux.FiveInputBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 512 rows at once, NOT gates cost nothing.
def ins_fffefee8 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082, 0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104, 0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208, 0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410, 0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]

theorem spec_fffefee8 : ∀ j : Fin 512, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (ins_fffefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

-- A live run mapped through a bitwise homomorphism is a build of the mapped goal; a wire
-- mapped to zero saves its gate.
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

-- Fixing input i to zero (restriction i) leaves the same four-input search, which fails at six.
def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4exact : search 6 k4inputs = false := by decide +kernel

def vinput (i : Fin 5) : W := ins_fffefee8.getD i.val 0

def pairIx : Fin 5 → List ℕ := ![[12, 14, 15, 16, 17, 30, 32, 33, 34, 35, 42, 44, 45, 46, 47, 54, 56, 57, 58, 59, 72, 74, 75, 76, 77, 84, 86, 87, 88, 89, 96, 98, 99, 100, 101, 108, 110, 111, 112, 113, 120, 122, 123, 124, 125, 132, 134, 135, 136, 137, 144, 146, 147, 148, 149],
[6, 7, 9, 10, 11, 24, 25, 27, 28, 29, 42, 43, 45, 46, 47, 48, 49, 51, 52, 53, 66, 67, 69, 70, 71, 84, 85, 87, 88, 89, 90, 91, 93, 94, 95, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 132, 133, 135, 136, 137, 138, 139, 141, 142, 143],
[0, 1, 2, 4, 5, 24, 25, 26, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 66, 67, 68, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131],
[0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 66, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 107],
[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64]]

def sourceRow (i : Fin 5) (j : Fin 512) : Fin 512 :=
  ⟨((if j.val < 256 then 0 else 256) + (pairIx i).getD ((j.val % 256) % 55) 0) % 512,
    Nat.mod_lt _ (by decide)⟩

def restriction (i : Fin 5) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(sourceRow i k).val]))).cast List.length_ofFn

theorem restriction_bit (i : Fin 5) (w : W) (j : ℕ) (hj : j < 512) :
    (restriction i w)[j] = w[(sourceRow i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [restriction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
theorem restriction_not (i : Fin 5) (u : W) : restriction i (~~~u) = ~~~restriction i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_not]

theorem restriction_ops (i : Fin 5) (a b z : W) (hz : z ∈ basicOps a b) :
    restriction i z ∈ basicOps (restriction i a) (restriction i b) := by
  have hand (u v : W) : restriction i (u &&& v) = (restriction i u &&& restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_and]
  have hor (u v : W) : restriction i (u ||| v) = (restriction i u ||| restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, restriction_not]

def remaining (i : Fin 5) : List W :=
  ((List.finRange 5).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 5, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 5, restriction i goal = goal := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_nd : ∀ i : Fin 5, (remaining i).Nodup := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_same : ∀ i : Fin 5, remaining i = k4inputs := by decide +kernel

theorem remaining_reject (i : Fin 5) : search 6 (remaining i) = false := by
  rw [remaining_same]
  exact k4exact

set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ ins_fffefee8, ∃ i : Fin 5, vinput i = w := by
  intro w hw
  simp only [ins_fffefee8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩

theorem restricted_available : ∀ i j : Fin 5, holds (remaining i).toFinset (restriction i (vinput j)) := by
  intro i j
  by_cases h : i = j
  · subst j
    exact Or.inl (projected_input i)
  · right; right
    exact ⟨_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, by simp [Ne.symm h],rfl⟩), Or.inl rfl⟩

-- The first gate, on inputs i and j, does not separate some pair that only input i separates,
-- so input i stays live after it.
def changes (w : W) (r : Fin 256) : Bool :=
  w.getLsbD (256+r.val) != w.getLsbD r.val

set_option maxRecDepth 8000 in
theorem separating_pair : ∀ i j : Fin 5, i ≠ j → ∀ op : Fin 4, ∃ r : Fin 256,
    changes ((ops (vinput i) (vinput j)).getD op.val 0) r = false ∧
    ∀ q : Fin 5, q ≠ i → changes (vinput q) r = false := by decide +kernel

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

theorem unchanged (w : W) (r : Fin 256) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem input_not_goal : ∀ i : Fin 5, vinput i ≠ goal ∧ vinput i ≠ ~~~goal := by decide +kernel

theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel

theorem restricted_new (i j : Fin 5) (z : W) (hz : z ∈ basicOps (vinput i) (vinput j)) :
    holds (remaining i).toFinset (restriction i z) := by
  exact mem_ops_zero (restricted_available i i) (restricted_available i j)
    (Or.inl (projected_input i))
    (restriction_ops i _ _ _ hz)

theorem raw_present {t : W} (ht : t = goal ∨ t = ~~~goal) (i j : Fin 5) (hij : i ≠ j)
    {z : W} (hz : z ∈ basicOps (vinput i) (vinput j)) (rest : Finset W)
    (hsub : rest ⊆ ins_fffefee8.toFinset)
    (h : live basicOps t 7 (insert z rest)) : vinput i ∈ rest := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  obtain ⟨r, hrz, hrq⟩ := separating_pair i j hij o
  rw [ho] at hrz
  have hd : differs r t := by
    rcases ht with rfl|rfl
    · exact (goal_changes r).1
    · exact (goal_changes r).2
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) h
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact False.elim (unchanged _ _ hrz hdw)
  · obtain ⟨q,rfl⟩ := input_index _ (List.mem_toFinset.mp (hsub hw))
    by_contra hn
    have qi : q ≠ i := by intro eq; exact hn (eq ▸ hw)
    exact unchanged _ _ (hrq q qi) hdw

set_option maxRecDepth 4000 in
theorem projected_impossible (i : Fin 5) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (h : SignedBuild 6 (remaining i).toFinset (restriction i t)) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have signs : restriction i t = goal ∨ restriction i t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact Or.inl (projected_goal i)
    · exact Or.inr (by rw [restriction_not, projected_goal])
  have opposite : ~~~restriction i t = goal ∨ ~~~restriction i t = ~~~goal := by
    rcases signs with h|h <;> simp [h]
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (run : build basicOps u 6 (remaining i).toFinset) : False := by
    have hit := search_complete hu 6 (remaining i) (remaining_nd i) run
    exact Bool.noConfusion ((remaining_reject i).symm.trans hit)
  rcases h with c | c | run | run
  · rcases signs with h|h
    · exact ne.1 (h.symm.trans c)
    · exact ne.2.2.1 (h.symm.trans c)
  · rcases signs with h|h
    · exact ne.2.1 (h.symm.trans c)
    · exact ne.2.2.2 (h.symm.trans c)
  · exact no signs run
  · exact no opposite run

theorem no_eight_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 ins_fffefee8.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl|rfl
    · exact (input_not_goal i).1 hi
    · exact (input_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput eq)
    have sub : rest ⊆ ins_fffefee8.toFinset := by
      intro u hu
      exact hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have keep := raw_present ht i j hij hz rest sub tail
    have pg : vinput i ≠ t := by rcases ht with rfl|rfl; exact (input_not_goal i).1; exact (input_not_goal i).2
    apply projected_impossible i t ht
    apply live_transport_save (restriction_ops i)
      tail (Finset.mem_insert_of_mem keep) pg (projected_input i)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact restricted_new i j w hz
    · obtain ⟨k,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hw))
      exact restricted_available i k


end PEqualNP.Outside.L_meta_11763_aux.FiveInputBounds

namespace PEqualNP.Outside.L_meta_11763_aux.CliqueBounds
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
open PEqualNP.Outside.L_meta_11763_aux.FiveInputBounds

theorem convert {T : Sig} {k : Nat} {S : Finset Sig}
    (h : Live true T k S) {av : Finset Sig} (sub : S ⊆ av) : build basicOps T k av := by
  induction h using Live.ind generalizing av with
  | stop hp => exact sub (Finset.mem_singleton_self T)
  | @binary k U a b d hd ha hb hab hf ht ih =>
    have op : bin d a b ∈ basicOps a b := by
      rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [bin,basicOps,ops,BitVec.and_comm]
    apply Or.inr
    refine ⟨a,sub (by simp),b,sub (by simp),hab,bin d a b,op,ih ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (sub (by simp [hw]))

theorem buildLift {T : Sig} {A : Finset Sig} {k l : Nat} (h : k ≤ l)
    (g : build basicOps T k A) : build basicOps T l A := by
  induction h with
  | refl => exact g
  | step _ ih => exact Or.inl ih

theorem packedLower5 : Lower true ins_fffefee8 goal 9 := by
  intro p bank h hit
  have pT : proper goal := by unfold proper; decide +kernel
  have gT : plainWord goal = true := by decide +kernel
  have pR : ins_fffefee8.all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,hs⟩ := reach_live pT gT pR h hit
  by_contra! hlow
  apply no_eight_binary goal (.inl rfl)
  apply buildLift (by omega : k ≤ 8)
  exact convert run (fun w hw => List.mem_toFinset.mpr (hs w hw))

def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def packedRow (j : Row) : Row :=
  ⟨(List.range 5 |>.foldl (fun acc q => acc + if bit j (ins_fffefee8.getD q 0) then 2^q else 0) 0) % 512, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4000 in
theorem rowTable : ∀ j : Row, bit (packedRow j) k5 = bit j goal := by decide +kernel

set_option maxRecDepth 4000 in
theorem rowInputs : ∀ q : Fin 5, ∀ j : Row, bit (packedRow j) (inputs.getD q.val 0) = bit j (ins_fffefee8.getD q.val 0) := by decide +kernel

set_option maxRecDepth 12000 in
theorem standardLower5 : Lower true (inputs.take 5) k5 9 := by
  have hT : proper k5 := by unfold proper; decide +kernel
  have hN : plainWord k5=true := by decide +kernel
  have hR : (inputs.take 5).all plainWord =true := by decide +kernel
  have pT : proper goal := by unfold proper; decide +kernel
  have eq : rename packedRow k5 = goal := bit_ext fun j => (bit_rename _ _ _).trans (rowTable j)
  have supp : ∀ a ∈ inputs.take 5, Available true (ins_fffefee8.map observe) (observe (rename packedRow a)) := by
    intro a ha
    have asList : inputs.take 5 = List.ofFn (fun q : Fin 5 => inputs.getD q.val 0) := rfl
    rw [asList, List.mem_ofFn] at ha
    obtain ⟨q,rfl⟩ := ha
    have same : rename packedRow (inputs.getD q.val 0) = ins_fffefee8.getD q.val 0 :=
      bit_ext fun j => (bit_rename _ _ _).trans (rowInputs q j)
    have mem : ∀ q : Fin 5, ins_fffefee8.getD q.val 0 ∈ ins_fffefee8 := by decide +kernel
    rw [same]
    exact Or.inl (List.mem_map_of_mem (mem q))
  simpa using lower_slice hT hN hR pT packedRow eq supp ∅ (by simp) (by simp) 9 packedLower5

theorem packedLower4 : Lower true k4inputs goal 7 := by
  intro p bank h hit
  have pT : proper goal := by unfold proper; decide +kernel
  have gT : plainWord goal = true := by decide +kernel
  have pR : k4inputs.all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,hs⟩ := reach_live pT gT pR h hit
  by_contra! hlow
  have hb := convert run (av := k4inputs.toFinset) (fun w hw => List.mem_toFinset.mpr (hs w hw))
  have hbad := search_complete (Or.inl (Eq.refl goal)) 6 k4inputs (by decide +kernel) (buildLift (by omega : k ≤ 6) hb)
  exact Bool.noConfusion (k4exact.symm.trans hbad)

def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def packedRow4 (j : Row) : Row :=
  ⟨(List.range 4 |>.foldl (fun acc q => acc + if bit j (k4inputs.getD q 0) then 2^q else 0) 0) % 512, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4000 in
theorem rowTable4 : ∀ j : Row, bit (packedRow4 j) k4 = bit j goal := by decide +kernel

set_option maxRecDepth 4000 in
theorem rowInputs4 : ∀ q : Fin 4, ∀ j : Row, bit (packedRow4 j) (inputs.getD q.val 0) = bit j (k4inputs.getD q.val 0) := by decide +kernel

set_option maxRecDepth 12000 in
theorem standardLower4 : Lower true (inputs.take 4) k4 7 := by
  have hT : proper k4 := by unfold proper; decide +kernel
  have hN : plainWord k4=true := by decide +kernel
  have hR : (inputs.take 4).all plainWord =true := by decide +kernel
  have pT : proper goal := by unfold proper; decide +kernel
  have eq : rename packedRow4 k4 = goal := bit_ext fun j => (bit_rename _ _ _).trans (rowTable4 j)
  have supp : ∀ a ∈ inputs.take 4, Available true (k4inputs.map observe) (observe (rename packedRow4 a)) := by
    intro a ha
    have asList : inputs.take 4 = List.ofFn (fun q : Fin 4 => inputs.getD q.val 0) := rfl
    rw [asList, List.mem_ofFn] at ha
    obtain ⟨q,rfl⟩ := ha
    have same : rename packedRow4 (inputs.getD q.val 0) = k4inputs.getD q.val 0 :=
      bit_ext fun j => (bit_rename _ _ _).trans (rowInputs4 q j)
    have mem : ∀ q : Fin 4, k4inputs.getD q.val 0 ∈ k4inputs := by decide +kernel
    rw [same]
    exact Or.inl (List.mem_map_of_mem (mem q))
  simpa using lower_slice hT hN hR pT packedRow4 eq supp ∅ (by simp) (by simp) 7 packedLower4

end PEqualNP.Outside.L_meta_11763_aux.CliqueBounds

namespace PEqualNP.Outside.L_meta_11763_aux.TriangleBound
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.CliqueBounds PEqualNP.Outside.L_meta_11763_aux.FiveInputBounds

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def blocked (T : Sig) : Nat → List Sig → Bool
  | 0, ws => !ws.contains T
  | k+1, ws => !ws.contains T && ws.all fun a => ws.all fun b =>
      if a.toNat < b.toNat then (ops a b).all fun z => blocked T k (z::ws) else true

theorem swapOps (a b z : Sig) (h : z ∈ ops a b) : z ∈ ops b a := by
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with h|h|h|h
  · exact Or.inl (h.trans (BitVec.and_comm a b))
  · exact Or.inr (Or.inl (h.trans (BitVec.or_comm a b)))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem blockedSound (T : Sig) (k) (ws : List Sig) (h : blocked T k ws = true) :
    ∀ l ≤ k, ¬build basicOps T l ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    intro l hl; have e : l=0 := by omega
    subst l
    simpa [blocked,build] using h
  | succ k ih =>
    simp only [blocked,Bool.and_eq_true,List.all_eq_true] at h
    intro l le
    induction l with
    | zero => simpa [build] using h.1
    | succ l hl =>
      rintro (prev|⟨a,ha,b,hb,ne,z,hz,htail⟩)
      · exact hl (by omega) prev
      · have next (a b : Sig) (ma : a ∈ ws) (mb : b ∈ ws) (lt : a.toNat < b.toNat) (hz : z ∈ ops a b) : blocked T k (z::ws) = true := by
          have ok := h.2 a ma b mb
          rw [if_pos lt] at ok
          exact List.all_eq_true.mp ok z hz
        have ne' : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
        have v : blocked T k (z::ws) = true := by
          rcases lt_or_gt_of_ne ne' with lt|gt
          · exact next a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) lt (List.mem_toFinset.mp hz)
          · exact next b a (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha) gt (swapOps a b z (List.mem_toFinset.mp hz))
        exact ih (z::ws) v l (by omega) (by simpa using htail)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem standardLower3 : Lower true (inputs.take 3) k3 4 := by
  intro p bank h hit
  have pT : proper k3 := by unfold proper; decide +kernel
  have gT : plainWord k3 = true := by decide +kernel
  have pR : (inputs.take 3).all plainWord=true := by decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT gT pR h hit
  by_contra! bad
  have no := blockedSound k3 3 (inputs.take 3) (by decide +kernel) k (by omega)
  exact no (convert run (fun w hw => List.mem_toFinset.mpr (sub w hw)))

end PEqualNP.Outside.L_meta_11763_aux.TriangleBound

namespace PEqualNP.Outside.L_meta_11763_aux.GraphTarget
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def full : Sig := 0xfffffffefffffefefffeffeefefcaa00fffffffefffffefefffeffeefefcaa00fffffffefffffefefffeffeefefcaa00fffffffefffffefefffeffeefefcaa00
def cols7 : List Sig := inputs.take 7
end PEqualNP.Outside.L_meta_11763_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit
open PEqualNP.CircuitLowerBounds

def upper : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [10, 4]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [13, 3]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.and, [16, 2]⟩,
    ⟨.or, [15, 17]⟩], 18⟩

def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem upperComputes : ∀ x : Fin 7 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel

theorem upperLegal : ∀ g ∈ upper.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem upperSize : upper.gates.length = 12 := rfl
end PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit

namespace PEqualNP.Outside.L_meta_11763_aux.GraphTarget
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def sample7 (r : Row) (j : Fin 7) := bit r (cols7.getD j.val zero)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenTable : ∀ r : Row, bit r full = PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.target (sample7 r) := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenList : List.ofFn (fun i : Fin 7 => cols7.getD i.val zero) = cols7 := rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenSampled (r : Row) : List.ofFn (sample7 r) = cols7.map (bit r) := by
  rw [←sevenList,List.map_ofFn]; rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem eval7 (C : Circuit) (h : FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cols7).getD i zero) =
      (C.wires (List.ofFn (sample7 r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem binaryLower (low : Lower true cols7 full 11) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.target x) :
    11 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have goalEq : (execute C.gates cols7).getD C.output zero = full := by
    apply bit_ext
    intro r
    exact (eval7 C legal C.output r).trans ((computes (sample7 r)).trans (sevenTable r).symm)
  have rep := get_rep (u:=true) (execute C.gates cols7) C.output
  rw [goalEq] at rep
  unfold PEqualNP.Outside.L_meta_11763_aux.LiveCircuits.Repr at rep
  have pg : bit 0 full = false := by decide +kernel
  have pfull : proper full := by unfold proper; decide +kernel
  rw [nrm_id pg] at rep
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates cols7 legal (by simp) pfull (rep.resolve_right (fun h => h pfull))
  have plain : cols7.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have rs := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hs : supply true (cols7.map observe) ((S.toList.map observe).map (restrictRows (id : Row → Row))) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  have b := projected_bound (id : Row → Row) rs (observe_proper pfull) Reach.start hs (L:=11) low
  omega
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem gateLower (low : Lower true cols7 full 11) (C : Circuit) (legal : FanInTwo C)
    (negUsed : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.target x) :
    12 ≤ C.gates.length := by
  obtain ⟨g,hg,ng⟩ := negUsed
  have hc := binaryLower low C legal computes
  by_contra! h
  have all := (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length (by omega : C.gates.length ≤ C.gates.countP (fun g => !isNot g)))) g hg
  simp [isNot,ng] at all


theorem finish (low : Lower true cols7 full 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _uniq computes
  change ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.target x at computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have hl : FanInTwo ⟨gates,o⟩ := by
      intro g hg
      obtain ⟨ht,hw⟩ := legal g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht, hw⟩
    have hs := gateLower low ⟨gates,o⟩ hl hn computes
    refine ⟨PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.upper.gates, PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.upper.output, PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.upperLegal, ?_, ?_⟩
    · exact hs
    · intro x
      exact PEqualNP.Outside.L_meta_11763_aux.ExplicitCircuit.upperComputes x
  · refine ⟨gates,o,?_,Nat.le_refl _,computes⟩
    intro g hg
    obtain ⟨hor,hw⟩ := legal g hg
    rcases hor with ha | ho | hnot
    · exact ⟨Or.inl ha,hw⟩
    · exact ⟨Or.inr ho,hw⟩
    · exact (hn ⟨g,hg,hnot⟩).elim
end PEqualNP.Outside.L_meta_11763_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_11763_aux.GraphSymmetry
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
abbrev T := PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full
abbrev ws0 := PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7

def low (s : Fin 1) : Sig :=
  match s.val with
  | _ => 0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222

def high (s : Fin 1) : Sig :=
  match s.val with
  | _ => 0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444

def shiftN (s : Fin 1) : Nat :=
  match s.val with
  | _ => 1

def groupSize : Nat := 1
def codes : Array Nat := #[0]

def decode : Nat → Nat → List (Fin 1)
  | 0, _ => []
  | n+1, code =>
    if code = 0 then [] else
      ⟨((code % 32 - 1) % 1), Nat.mod_lt _ (by decide)⟩ :: decode n (code / 32)

def plan (p : Fin groupSize) := decode 6 (codes[p.val]?.getD 0)

def stepWord (s : Fin 1) (w : Sig) : Sig :=
  (w &&& ~~~(low s ||| high s)) ||| ((w >>> shiftN s) &&& low s) |||
    ((w <<< shiftN s) &&& high s)

def stepRow (s : Fin 1) (r : Row) : Row :=
  if bit r (low s) then ⟨(shiftN s + r.val) % 512, Nat.mod_lt _ (by decide)⟩
  else if bit r (high s) then ⟨r.val - shiftN s, by have := r.isLt; omega⟩ else r

def permWord (p : Fin groupSize) (w : Sig) : Sig :=
  (plan p).foldl (fun v s => stepWord s v) w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem stepChecks : ∀ s : Fin 1, ∀ r : Row,
    (bit r (low s) = true → bit r (high s) = false ∧ shiftN s + r.val < 512) ∧
    (bit r (high s) = true → shiftN s ≤ r.val) ∧ stepRow s (stepRow s r) = r := by
  decide +kernel

theorem stepEq (s : Fin 1) (w : Sig) : stepWord s w = rename (stepRow s) w := by
  apply bit_ext
  intro r
  rw [bit_rename]
  obtain ⟨safeL,safeH,inv⟩ := stepChecks s r
  cases hL : bit r (low s)
  · cases hH : bit r (high s)
    · simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, BitVec.getLsbD_or, BitVec.getLsbD_and]
    · have cut := safeH hH
      have left : r.val - shiftN s < 512 := Nat.lt_of_le_of_lt (Nat.sub_le ..) r.isLt
      simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, Nat.not_lt.mpr cut, left, BitVec.getLsbD_or, BitVec.getLsbD_and]
  · obtain ⟨hH,lt⟩ := safeL hL
    simp [bit] at hL hH
    simp only [bit]
    simp [stepWord,stepRow,bit,hL,hH,lt,r.isLt,Nat.mod_eq_of_lt lt, BitVec.getLsbD_or, BitVec.getLsbD_and]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem permTarget : ∀ p : Fin groupSize, permWord p T = T := by decide +kernel

theorem stepLive {target k ws} (s : Fin 1) (h : Live true target k (List.toFinset ws)) :
    Live true (stepWord s target) k (ws.map (stepWord s)).toFinset := by
  have hr := live_rename h (stepRow s) (fun y => ⟨stepRow s y,(stepChecks s y).2.2⟩)
  have e : rename (stepRow s) = stepWord s := funext (fun w => (stepEq s w).symm)
  rw [e] at hr
  have he : ws.toFinset.image (stepWord s) = (ws.map (stepWord s)).toFinset := by
    ext t
    simp
  exact he ▸ hr

theorem planLive {target : Sig} {k : Nat} (ss : List (Fin 1)) {ws : List Sig} (h : Live true target k ws.toFinset) :
    Live true (ss.foldl (fun v s => stepWord s v) target) k (ws.map fun w => ss.foldl (fun v s => stepWord s v) w).toFinset := by
  induction ss generalizing target ws with
  | nil => simpa using h
  | cons s ss ih =>
    have v := ih (stepLive s h)
    simpa only [List.map_map,List.foldl_cons,Function.comp_def] using v

theorem isoTransfer (p : Fin groupSize) (ws : List Sig) (k : Nat)
    (h : Impossible true T k (ws.map (permWord p)).toFinset) : Impossible true T k ws.toFinset := by
  intro n hn bad
  have moved := planLive (plan p) bad
  change Live true (permWord p T) n (ws.map (permWord p)).toFinset at moved
  rw [permTarget] at moved
  exact h n hn moved

theorem isoTransferOf (p : Fin groupSize) (ws rep : List Sig) (k : Nat)
    (equal : (ws.map (permWord p)).toFinset = rep.toFinset)
    (h : Impossible true T k rep.toFinset) : Impossible true T k ws.toFinset :=
  isoTransfer p ws k (equal.symm ▸ h)

end PEqualNP.Outside.L_meta_11763_aux.GraphSymmetry

namespace PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def masks : List Nat := [41, 82, 84]
def cliqueDomain : Nat → Sig
  | 41 => 0x30300000303000000000000000000000303000003030000000000000000000003030000030300000000000000000000030300000303
  | 82 => 0x500050000000000050005000000000005000500000000000500050000000000050005000000000005000500000000000500050000000000050005
  | 84 => 0x1100110000000000110011000000000011001100000000001100110000000000110011000000000011001100000000001100110000000000110011
  | _ => 0

def cliqueSize : Nat → Nat
  | 41 => 3
  | 82 => 3
  | 84 => 3
  | _ => 0

def cliqueBound (m : Nat) := match cliqueSize m with | 5 => 9 | 4 => 7 | 3 => 4 | _ => 0
def embeds : Nat → List Row
  | 41 => [0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41]
  | 82 => [0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82]
  | 84 => [0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84]
  | _ => []

def ranks : Nat → List Nat
  | 41 => [0, 7, 7, 1, 7, 2, 7]
  | 82 => [7, 0, 7, 7, 1, 7, 2]
  | 84 => [7, 7, 0, 7, 1, 7, 2]
  | _ => []

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def standard : Nat → Sig | 5 => k5 | 4 => k4 | _ => k3
def embed (m : Nat) (r : Fin 32) : Row := (embeds m).getD r.val 0
def arg (m : Nat) (i : Fin 7) := (inputs.take (cliqueSize m)).getD ((ranks m).getD i.val 7) zero
def low (r : Row) : Fin 32 := ⟨r.val % 32,Nat.mod_lt _ (by decide)⟩
def toRow (j : Fin 32) : Row := ⟨j.val,by omega⟩
def ref (m : Nat) (r : Row) : Row := embed m (low r)

def cert (m : Nat) : Bool := decide (∀ j : Fin 32,
  bit (embed m j) (cliqueDomain m) = true ∧
    bit (embed m j) PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full = bit (toRow j) (standard (cliqueSize m)) ∧
    ∀ i : Fin 7, bit (embed m j) (PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero) = bit (toRow j) (arg m i))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem certs : masks.all cert = true := by decide +kernel

end PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def smalls := zero :: k3 :: k4 :: k5 :: inputs.take 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem periods : smalls.all (fun w => decide (∀ r : Row, bit (toRow (low r)) w = bit r w)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem facts : masks.all (fun m => decide (
    (cliqueSize m=3 ∨ cliqueSize m=4 ∨ cliqueSize m=5) ∧ standard (cliqueSize m) ∈ smalls ∧
    ∀ i : Fin 7, arg m i ∈ smalls)) = true := by decide +kernel

theorem fromWord {xs : List Sig} (j : Nat) :
    Available true (xs.map observe) (observe (xs.getD j zero)) := by
  by_cases h : j < xs.length
  · apply Or.inl
    apply List.mem_map_of_mem
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using (List.getElem_mem h)
  · have hz : xs.getD j zero = zero := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [hz]; exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem validParam (m : Nat) (hm : m ∈ masks)
    (lower : Lower true (inputs.take (cliqueSize m)) (standard (cliqueSize m)) (cliqueBound m)) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  have tbl0 := List.all_eq_true.mp certs m hm
  unfold cert at tbl0
  have tbl := of_decide_eq_true tbl0
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  have periodic (x : Sig) (hx : x ∈ smalls) : ∀ r, bit (toRow (low r)) x = bit r x :=
    of_decide_eq_true (List.all_eq_true.mp periods x hx)
  have tgt : restrictRows (ref m) (observe PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full) = observe (standard (cliqueSize m)) :=
    funext fun r => ((tbl (low r)).2.1).trans (periodic _ info.2.1 r)
  refine ⟨ref m,inputs.take (cliqueSize m),fun r => (tbl (low r)).1,?_,?_,?_⟩
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 7 := ⟨j,by exact hj⟩
    have eq : restrictRows (ref m) (observe (PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero)) = observe (arg m i) :=
      funext fun r => ((tbl (low r)).2.2 i).trans (periodic _ (info.2.2 i) r)
    have same : PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero = PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [← same,eq]; exact fromWord _
  · rw [tgt]
    apply observe_proper
    rcases info.1 with e|e|e <;> rw [e] <;> unfold proper <;> decide +kernel
  · rw [tgt]; exact lower
theorem validWithBounds
    (h3 : Lower true (inputs.take 3) k3 4)
    (h4 : Lower true (inputs.take 4) k4 7)
    (h5 : Lower true (inputs.take 5) k5 9)
    (m : Nat) (hm : m ∈ masks) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  apply validParam m hm
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  unfold cliqueBound
  rcases info.1 with h | h | h <;> rw [h]
  · exact h3
  · exact h4
  · exact h5

end PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def full : Sig := 0xfffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0
def cols7 : List Sig := inputs.take 7
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target

abbrev Entry := Nat × List Nat × Nat × List Nat
def Entry.cap (x : Entry) : Nat := x.1
def Entry.program (x : Entry) : List Nat := x.2.1
def Entry.livingMask (x : Entry) : Nat := x.2.2.1
def Entry.codes (x : Entry) : List Nat := x.2.2.2

def unpackGates (ws : List Sig) : List Nat → List Choice
  | [] => []
  | g :: gs =>
    let c : Choice := (g / 256, ws.getD (g % 16) 0, ws.getD ((g / 16) % 16) 0)
    c :: unpackGates (ws ++ [choiceVal c]) gs

def selectMask {α : Type} (m : Nat) (ws : List α) : List α :=
  (ws.zipIdx.filter fun p => m.testBit p.2).map Prod.fst

def choicesOf (e : Entry) := unpackGates cols7 e.program

def stateOf (e : Entry) : List Sig :=
  selectMask e.livingMask (cols7 ++ (choicesOf e).map choiceVal)

def negativeRows : List Row := [0,1,2,3,4,5,8,10,12,16,17,32,33,34,35,36,37,40,42,44,48,49,64,65,66,67,68,69,72,74,76,80,81,96,97,98,99,100,101,104,106,108,112,113]

def candidates (r : Row) : List Sig → Sig
  | [] => full
  | w :: ws => (if bit r w then w else ~~~w) &&& candidates r ws

def indist (ws : List Sig) := negativeRows.any fun r => candidates r ws != 0

def pop (x : Nat) : Nat := (BitVec.ofNat 16 x).cpop.toNat

def readCode (e : Entry) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Nat :=
  let ia := ws.idxOf a
  let ib := ws.idxOf b
  let lo := min ia ib
  let hi := max ia ib
  let block := e.codes.getD (hi*(hi-1)/2+lo) 0
  let dir := ia < ib
  let slot := 4 * (if dir then d else flipOp d) +
    (if dir then ka.toNat + 2*kb.toNat else kb.toNat + 2*ka.toNat)
  if block.testBit slot then
    let rank := pop (block % (2^slot))
    (block >>> (16+20*rank)) % (2^20)
  else 0

theorem candBit (r s : Row) (ws : List Sig) :
    bit s (candidates r ws) = true ↔ bit s full = true ∧ ∀ w ∈ ws, bit r w = bit s w := by
  induction ws with
  | nil => simp [candidates]
  | cons a ws ih =>
    have ba (x y : Sig) : bit s (x &&& y) = (bit s x && bit s y) := BitVec.getLsbD_and
    have bn (x : Sig) : bit s (~~~x) = !bit s x := by
      simp only [bit,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and]
    cases hr : bit r a <;> cases hs : bit s a <;>
      simp only [candidates,hr,Bool.false_eq_true,ite_false,ite_true,ba,bn,hs,Bool.and_eq_true,
        ih,List.forall_mem_cons] <;> simp_all

set_option maxRecDepth 8192 in
theorem indistSound {ws : List Sig} (bad : indist ws = true) (k : Nat) :
    Impossible true full k ws.toFinset := by
  obtain ⟨s,hs,hbad⟩ := List.any_eq_true.mp bad
  have hn : bit s full = false := (by decide +kernel : ∀ r ∈ negativeRows, bit r full = false) s hs
  intro l _ run
  have z : candidates s ws = 0 := by
    apply bit_ext
    intro r
    cases e : bit r (candidates s ws)
    · exact (bit_zero _).symm
    · obtain ⟨yes,all⟩ := (candBit _ _ _).mp e
      obtain ⟨w,hw,sep⟩ := live_row_difference run (show bit r full ≠ bit s full by simp [yes,hn])
      exact False.elim (sep (all w (List.mem_toFinset.mp hw)).symm)
  simp [z] at hbad
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Auto
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
abbrev T := PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.full
abbrev ws0 := PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7

def low (s : Fin 2) : Sig :=
  match s.val with
  | 0 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | _ => 0xffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff00000000

def high (s : Fin 2) : Sig :=
  match s.val with
  | 0 => 0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030
  | _ => 0xffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff0000000000000000

def shiftN (s : Fin 2) : Nat :=
  match s.val with
  | 0 => 2
  | _ => 32

def groupSize : Nat := 4
def codes : Array Nat := #[0, 2, 1, 65]

def decode : Nat → Nat → List (Fin 2)
  | 0, _ => []
  | n+1, code =>
    if code = 0 then [] else
      ⟨((code % 32 - 1) % 2), Nat.mod_lt _ (by decide)⟩ :: decode n (code / 32)

def plan (p : Fin groupSize) := decode 6 (codes[p.val]?.getD 0)

def stepWord (s : Fin 2) (w : Sig) : Sig :=
  (w &&& ~~~(low s ||| high s)) ||| ((w >>> shiftN s) &&& low s) |||
    ((w <<< shiftN s) &&& high s)

def stepRow (s : Fin 2) (r : Row) : Row :=
  if bit r (low s) then ⟨(shiftN s + r.val) % 512, Nat.mod_lt _ (by decide)⟩
  else if bit r (high s) then ⟨r.val - shiftN s, by have := r.isLt; omega⟩ else r

def permWord (p : Fin groupSize) (w : Sig) : Sig :=
  (plan p).foldl (fun v s => stepWord s v) w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem stepChecks : ∀ s : Fin 2, ∀ r : Row,
    (bit r (low s) = true → bit r (high s) = false ∧ shiftN s + r.val < 512) ∧
    (bit r (high s) = true → shiftN s ≤ r.val) ∧ stepRow s (stepRow s r) = r := by
  decide +kernel

theorem stepEq (s : Fin 2) (w : Sig) : stepWord s w = rename (stepRow s) w := by
  apply bit_ext
  intro r
  rw [bit_rename]
  obtain ⟨safeL,safeH,inv⟩ := stepChecks s r
  cases hL : bit r (low s)
  · cases hH : bit r (high s)
    · simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, BitVec.getLsbD_or, BitVec.getLsbD_and]
    · have cut := safeH hH
      have left : r.val - shiftN s < 512 := Nat.lt_of_le_of_lt (Nat.sub_le ..) r.isLt
      simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, Nat.not_lt.mpr cut, left, BitVec.getLsbD_or, BitVec.getLsbD_and]
  · obtain ⟨hH,lt⟩ := safeL hL
    simp [bit] at hL hH
    simp only [bit]
    simp [stepWord,stepRow,bit,hL,hH,lt,r.isLt,Nat.mod_eq_of_lt lt, BitVec.getLsbD_or, BitVec.getLsbD_and]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem permTarget : ∀ p : Fin groupSize, permWord p T = T := by decide +kernel

theorem stepLive {target k ws} (s : Fin 2) (h : Live true target k (List.toFinset ws)) :
    Live true (stepWord s target) k (ws.map (stepWord s)).toFinset := by
  have hr := live_rename h (stepRow s) (fun y => ⟨stepRow s y,(stepChecks s y).2.2⟩)
  have e : rename (stepRow s) = stepWord s := funext (fun w => (stepEq s w).symm)
  rw [e] at hr
  have he : ws.toFinset.image (stepWord s) = (ws.map (stepWord s)).toFinset := by
    ext t
    simp
  exact he ▸ hr

theorem planLive {target : Sig} {k : Nat} (ss : List (Fin 2)) {ws : List Sig} (h : Live true target k ws.toFinset) :
    Live true (ss.foldl (fun v s => stepWord s v) target) k (ws.map fun w => ss.foldl (fun v s => stepWord s v) w).toFinset := by
  induction ss generalizing target ws with
  | nil => simpa using h
  | cons s ss ih =>
    have v := ih (stepLive s h)
    simpa only [List.map_map,List.foldl_cons,Function.comp_def] using v

theorem isoTransfer (p : Fin groupSize) (ws : List Sig) (k : Nat)
    (h : Impossible true T k (ws.map (permWord p)).toFinset) : Impossible true T k ws.toFinset := by
  intro n hn bad
  have moved := planLive (plan p) bad
  change Live true (permWord p T) n (ws.map (permWord p)).toFinset at moved
  rw [permTarget] at moved
  exact h n hn moved

theorem isoTransferOf (p : Fin groupSize) (ws rep : List Sig) (k : Nat)
    (equal : (ws.map (permWord p)).toFinset = rep.toFinset)
    (h : Impossible true T k rep.toFinset) : Impossible true T k ws.toFinset :=
  isoTransfer p ws k (equal.symm ▸ h)

end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Auto

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def masks : List Nat := [22]
def cliqueDomain : Nat → Sig
  | 22 => 0x550055000000000000000000000000005500550000000000000000000000000055005500000000000000000000000000550055
  | _ => 0

def cliqueSize : Nat → Nat
  | 22 => 3
  | _ => 0

def cliqueBound (m : Nat) := match cliqueSize m with | 5 => 9 | 4 => 7 | 3 => 4 | _ => 0
def embeds : Nat → List Row
  | 22 => [0, 2, 4, 6, 16, 18, 20, 22, 0, 2, 4, 6, 16, 18, 20, 22, 0, 2, 4, 6, 16, 18, 20, 22, 0, 2, 4, 6, 16, 18, 20, 22]
  | _ => []

def ranks : Nat → List Nat
  | 22 => [7, 0, 1, 7, 2, 7, 7]
  | _ => []

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def standard : Nat → Sig | 5 => k5 | 4 => k4 | _ => k3
def embed (m : Nat) (r : Fin 32) : Row := (embeds m).getD r.val 0
def arg (m : Nat) (i : Fin 7) := (inputs.take (cliqueSize m)).getD ((ranks m).getD i.val 7) zero
def low (r : Row) : Fin 32 := ⟨r.val % 32,Nat.mod_lt _ (by decide)⟩
def toRow (j : Fin 32) : Row := ⟨j.val,by omega⟩
def ref (m : Nat) (r : Row) : Row := embed m (low r)

def cert (m : Nat) : Bool := decide (∀ j : Fin 32,
  bit (embed m j) (cliqueDomain m) = true ∧
    bit (embed m j) PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.full = bit (toRow j) (standard (cliqueSize m)) ∧
    ∀ i : Fin 7, bit (embed m j) (PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7.getD i.val zero) = bit (toRow j) (arg m i))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem certs : masks.all cert = true := by decide +kernel

end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Auto

def verifyCut (cap : Nat) (cs : List Choice) (ch : List Sig) (code : Nat) : Bool :=
  let m := (code-1) / 256
  let witness := selectMask ((code-1) % 256) cs
  let mask := cliqueDomain m
  masks.contains m &&
    match makePool true mask cols7 witness with
    | none => false
    | some pool => poolCut true mask (cliqueBound m) cap witness.length pool ch

def verifyIso (db : Array Entry) (cap : Nat) (ch : List Sig) (code : Nat) : Bool :=
  let key := code-65536
  let j := key/4
  let p : Fin 4 := Fin.ofNat 4 (key % 4)
  let dest := db[j]?.getD default
  decide (j < db.size) && (dest.cap==cap) &&
    decide ((ch.map (permWord p)).toFinset = (stateOf dest).toFinset)

def verifyChild (db : Array Entry) (e : Entry) (steps : List Choice) (ws : List Sig)
    (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  let y := bin d a b
  let ch := childTwo ws a b d ka kb
  if b.toNat ≤ a.toNat then true else
  if a == b || ws.contains y || y == zero || y == one || decide (e.cap < ch.length) then true
  else if indist ch then true
  else
    let code := readCode e ws a b d ka kb
    if code==0 then false else if 65536 ≤ code then verifyIso db (e.cap-1) ch code
      else verifyCut (e.cap-1) (steps++[(d,a,b)]) ch code

def verify (db : Array Entry) (e : Entry) : Bool :=
  let ws := stateOf e
  let cs := choicesOf e
  if e.cap = 0 then !ws.contains full else
  decide (0 < e.cap) && decide ws.Nodup && !ws.contains full &&
    ws.all fun a => ws.all fun b => [0,1,2,3].all fun d =>
      [false,true].all fun ka => [false,true].all fun kb => verifyChild db e cs ws a b d ka kb
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
def n0 : Entry := ⟨6, [], 31, [0x016010160101601016018888,0x016010160101601016018888,0x1002e1002c100281000c8888,0x016010160101601016010160101601c88c,0x016010160101601016018888,0x016010160101601016018888,0x0160101601016010160110004016018cc8,0x100541005010044100308888,0x100561005210046100328888,0x016010160101601016018888]⟩
def n1 : Entry := ⟨5, [320], 158, [0x0000,0x0000,0x0000,0x0000,0x0000,0x01601016012020,0x0000,0x0000,0x10008016010160101601016014207,0x01601016016000]⟩
def n2 : Entry := ⟨4, [320,883], 406, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x016010100]⟩
def n3 : Entry := ⟨5, [33], 159, [0x0000,0x0000,0x100140010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601100100110,0x0000,0x0000,0x016011001c0110,0x10024100200110]⟩
def n4 : Entry := ⟨4, [33,368], 286, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n5 : Entry := ⟨4, [33,289], 409, [0x0000,0x0000,0x0000,0x0000,0x0000,0x100180010,0x0000,0x0000,0x0000,0x0000]⟩
def n6 : Entry := ⟨3, [33,289,372], 777, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n7 : Entry := ⟨4, [33,371], 279, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n8 : Entry := ⟨4, [33,372], 271, [0x0000,0x0000,0x100180010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n9 : Entry := ⟨4, [33,628], 271, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n10 : Entry := ⟨5, [289], 159, [0x0000,0x0000,0x100140001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n11 : Entry := ⟨5, [545], 159, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n12 : Entry := ⟨5, [65], 159, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601100340110,0x0000,0x1003c100380110,0x01601100400110,0x0000]⟩
def n13 : Entry := ⟨4, [65,368], 286, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n14 : Entry := ⟨4, [65,370], 283, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n15 : Entry := ⟨4, [65,626], 283, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n16 : Entry := ⟨4, [65,371], 279, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n17 : Entry := ⟨5, [321], 159, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1004c100481001,0x0000,0x0000]⟩
def n18 : Entry := ⟨4, [321,114], 283, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n19 : Entry := ⟨4, [321,882], 283, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n20 : Entry := ⟨5, [577], 159, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n21 : Entry := ⟨5, [833], 159, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601100580110,0x0000,0x0000,0x0000,0x0000]⟩
def n22 : Entry := ⟨4, [833,368], 286, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x016010001,0x0000]⟩
def nodes : Array Entry := #[n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13,n14,n15,n16,n17,n18,n19,n20,n21,n22]
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok0 : verify nodes n0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok1 : verify nodes n1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok2 : verify nodes n2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok3 : verify nodes n3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok4 : verify nodes n4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok5 : verify nodes n5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok6 : verify nodes n6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok7 : verify nodes n7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok8 : verify nodes n8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok9 : verify nodes n9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok10 : verify nodes n10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok11 : verify nodes n11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok12 : verify nodes n12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok13 : verify nodes n13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok14 : verify nodes n14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok15 : verify nodes n15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok16 : verify nodes n16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok17 : verify nodes n17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok18 : verify nodes n18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok19 : verify nodes n19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok20 : verify nodes n20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok21 : verify nodes n21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok22 : verify nodes n22 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits

theorem childSwap {u : Bool} {d : Nat} (hd : allowed u d) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip hd a b, List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem enumStepOrdered {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb ne fresh pr sz
  rcases lt_or_gt_of_ne (fun eq => ne (BitVec.toNat_inj.mp eq)) with lt | gt
  · exact twoStep a ha b hb d hd ka kb lt fresh pr sz
  · have eq := bin_flip hd a b
    have perm := childSwap hd ws a b ka kb
    have hs := twoStep b hb a ha (flipOp d) (flip_flip hd).1 kb ka gt
      (eq ▸ fresh) (eq ▸ pr) (perm.length_eq ▸ sz)
    have eqSet : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext x
      simpa only [List.mem_toFinset] using (perm.mem_iff : x ∈ _ ↔ x ∈ _)
    exact eqSet.symm ▸ hs

end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Auto

theorem verifiedCut {cap cs ch code} (validSlice : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (nd : ch.Nodup) (ok : verifyCut cap cs ch code = true) : Impossible true full cap ch.toFinset := by
  let m := (code-1) / 256
  let witness := selectMask ((code-1) % 256) cs
  unfold verifyCut at ok
  simp only [Bool.and_eq_true,List.contains_iff_mem] at ok
  obtain ⟨hm,h⟩ := ok
  change (match makePool true (cliqueDomain m) cols7 witness with
    | none => false
    | some pool => poolCut true (cliqueDomain m) (cliqueBound m) cap witness.length pool ch) = true at h
  cases hp : makePool true (cliqueDomain m) cols7 witness with
  | none => rw [hp] at h; contradiction
  | some pool =>
    apply poolCut_sound (validSlice m hm) witness hp nd
    rw [hp] at h
    exact h

theorem verifiedIso {db cap ch code} (ok : verifyIso db cap ch code = true)
    (prev : ∀ j, j < db.size →
      (db[j]?.getD default).cap = cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full cap ch.toFinset := by
  let j := (code-65536)/4
  let p : Fin 4 := Fin.ofNat 4 ((code-65536) % 4)
  let dest := db[j]?.getD default
  simp only [verifyIso,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨hj,hcap⟩,eq⟩ := ok
  apply isoTransferOf p ch (stateOf dest) cap eq
  exact hcap ▸ prev j hj hcap

set_option maxRecDepth 8192 in
theorem nodeSound {db e}
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (ok : verify db e = true)
    (prev : ∀ j, j < db.size → (db[j]?.getD default).cap < e.cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full e.cap (stateOf e).toFinset := by
  let ws := stateOf e
  let cs := choicesOf e
  by_cases zeroCap : e.cap = 0
  · have missing : full ∉ ws := by simpa [verify,zeroCap,ws] using ok
    intro k hk run
    have ez : k = 0 := by omega
    subst k
    have singleton : ws.toFinset = {full} := run.1
    exact missing (List.mem_toFinset.mp (singleton.symm ▸ Finset.mem_singleton_self _))
  simp only [verify,zeroCap,ite_false,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
  obtain ⟨⟨⟨pos,nd⟩,notout⟩,all⟩ := ok
  apply enumStepOrdered nd (by simpa using notout)
  intro a ha b hb d hd ka kb lt fresh prop len
  have reverse : ¬b.toNat ≤ a.toNat := Nat.not_le.mpr lt
  have ne : a ≠ b := fun eq => (Nat.lt_irrefl _) (eq ▸ lt)
  have op : d ∈ [0,1,2,3] := by rcases allowed_four hd with h|h|h|h <;> simp_all
  have ka' : ka ∈ [false,true] := by cases ka <;> simp
  have kb' : kb ∈ [false,true] := by cases kb <;> simp
  have chk := all a ha b hb d op ka ka' kb kb'
  have nz := prop.1
  have no := prop.2
  simp only [verifyChild,beq_iff_eq,List.contains_iff_mem,Bool.or_eq_true,decide_eq_true_eq,
    reverse,ne,fresh,nz,no,Nat.not_lt.mpr len,or_self,ite_false] at chk
  split at chk
  next bad => exact indistSound bad _
  next =>
    split at chk
    next => contradiction
    next =>
      split at chk
      next =>
        have dec : e.cap-1 < e.cap := by omega
        exact verifiedIso chk (fun j hj heq => prev j hj (heq.trans_lt dec))
      next =>
        apply verifiedCut slices _ chk
        unfold childTwo kept
        have nodup := nd
        have rn : ((ws.erase a).erase b).Nodup := (nodup.erase a).erase b
        have notA : a ∉ (ws.erase a).erase b := fun h => ((nodup.mem_erase_iff).mp (List.mem_of_mem_erase h)).1 rfl
        have notB : b ∉ (ws.erase a).erase b := fun h => (((nodup.erase a).mem_erase_iff).mp h).1 rfl
        have old : ∀ x ∈ (ws.erase a).erase b, x ∈ ws := fun _ h => List.mem_of_mem_erase (List.mem_of_mem_erase h)
        have ya : bin d a b ≠ a := by intro eq; apply fresh; rw [eq]; exact ha
        have yb : bin d a b ≠ b := by intro eq; apply fresh; rw [eq]; exact hb
        have yr : bin d a b ∉ (ws.erase a).erase b := fun h => fresh (old _ h)
        change (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))).Nodup
        cases ka <;> cases kb <;> simp [kept,ya,yb,yr,notA,notB,rn,ne]


theorem forestSound (db : Array Entry)
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (good : ∀ j, j < db.size → verify db (db[j]?.getD default) = true)
    (j : Nat) (hj : j < db.size) :
    Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset := by
  suffices ∀ k i, i < db.size → (db[i]?.getD default).cap = k →
      Impossible true full (db[i]?.getD default).cap (stateOf (db[i]?.getD default)).toFinset from this _ j hj rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hi hc
    apply nodeSound slices (good i hi)
    intro j hj lt
    exact ih _ (hc ▸ lt) j hj rfl
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def smalls := zero :: k3 :: k4 :: k5 :: inputs.take 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem periods : smalls.all (fun w => decide (∀ r : Row, bit (toRow (low r)) w = bit r w)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem facts : masks.all (fun m => decide (
    (cliqueSize m=3 ∨ cliqueSize m=4 ∨ cliqueSize m=5) ∧ standard (cliqueSize m) ∈ smalls ∧
    ∀ i : Fin 7, arg m i ∈ smalls)) = true := by decide +kernel

theorem fromWord {xs : List Sig} (j : Nat) :
    Available true (xs.map observe) (observe (xs.getD j zero)) := by
  by_cases h : j < xs.length
  · apply Or.inl
    apply List.mem_map_of_mem
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using (List.getElem_mem h)
  · have hz : xs.getD j zero = zero := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [hz]; exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem validParam (m : Nat) (hm : m ∈ masks)
    (lower : Lower true (inputs.take (cliqueSize m)) (standard (cliqueSize m)) (cliqueBound m)) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7 PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.full (cliqueDomain m) (cliqueBound m) := by
  have tbl0 := List.all_eq_true.mp certs m hm
  unfold cert at tbl0
  have tbl := of_decide_eq_true tbl0
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  have periodic (x : Sig) (hx : x ∈ smalls) : ∀ r, bit (toRow (low r)) x = bit r x :=
    of_decide_eq_true (List.all_eq_true.mp periods x hx)
  have tgt : restrictRows (ref m) (observe PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.full) = observe (standard (cliqueSize m)) :=
    funext fun r => ((tbl (low r)).2.1).trans (periodic _ info.2.1 r)
  refine ⟨ref m,inputs.take (cliqueSize m),fun r => (tbl (low r)).1,?_,?_,?_⟩
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 7 := ⟨j,by exact hj⟩
    have eq : restrictRows (ref m) (observe (PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7.getD i.val zero)) = observe (arg m i) :=
      funext fun r => ((tbl (low r)).2.2 i).trans (periodic _ (info.2.2 i) r)
    have same : PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7.getD i.val zero = PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [← same,eq]; exact fromWord _
  · rw [tgt]
    apply observe_proper
    rcases info.1 with e|e|e <;> rw [e] <;> unfold proper <;> decide +kernel
  · rw [tgt]; exact lower
theorem validWithBounds
    (h3 : Lower true (inputs.take 3) k3 4)
    (h4 : Lower true (inputs.take 4) k4 7)
    (h5 : Lower true (inputs.take 5) k5 9)
    (m : Nat) (hm : m ∈ masks) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.cols7 PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target.full (cliqueDomain m) (cliqueBound m) := by
  apply validParam m hm
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  unfold cliqueBound
  rcases info.1 with h | h | h <;> rw [h]
  · exact h3
  · exact h4
  · exact h5

end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target

def activeRoots : List Sig := selectMask 31 cols7

private def clamp (r : Row) : Row := ⟨(r.val &&& 31) % 512, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem clampTarget : ∀ r : Row, bit (clamp r) full = bit r full := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem clampColumns : ∀ i : Fin 7, let w := cols7.getD i.val zero
    (w ∈ activeRoots ∧ ∀ r : Row, bit (clamp r) w = bit r w) ∨
    (∀ r : Row, bit (clamp r) w = false) := by decide +kernel

theorem restoreInputs {n : Nat} (h : Lower true activeRoots full n) : Lower true cols7 full n := by
  have hp : proper full := by unfold proper; decide +kernel
  have target : rename clamp full = full := bit_ext fun r => (bit_rename _ _ _).trans (clampTarget r)
  have covered : ∀ a ∈ cols7, Available true (activeRoots.map observe) (observe (rename clamp a)) := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 7 := ⟨j,by exact hj⟩
    have same : cols7.getD i.val zero = cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [←same]
    rcases clampColumns i with ⟨hm,hs⟩ | hs
    · have eq : rename clamp (cols7.getD i.val zero) = cols7.getD i.val zero :=
        bit_ext fun r => (bit_rename _ _ _).trans (hs r)
      rw [eq]
      exact Or.inl (List.mem_map_of_mem hm)
    · exact Or.inr (Or.inl ⟨false,funext fun r => (bit_rename _ _ _).trans (hs r)⟩)
  simpa using lower_slice hp (by decide +kernel) (by decide +kernel) hp clamp target covered
    (∅ : Finset Sig) (by simp) (by simp) n h

end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Target
set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem allChecks : ∀ j : Nat, j < nodes.size → verify nodes (nodes[j]?.getD default) = true
  | 0, _ => ok0
  | 1, _ => ok1
  | 2, _ => ok2
  | 3, _ => ok3
  | 4, _ => ok4
  | 5, _ => ok5
  | 6, _ => ok6
  | 7, _ => ok7
  | 8, _ => ok8
  | 9, _ => ok9
  | 10, _ => ok10
  | 11, _ => ok11
  | 12, _ => ok12
  | 13, _ => ok13
  | 14, _ => ok14
  | 15, _ => ok15
  | 16, _ => ok16
  | 17, _ => ok17
  | 18, _ => ok18
  | 19, _ => ok19
  | 20, _ => ok20
  | 21, _ => ok21
  | 22, _ => ok22
  | j+23,h => by change j+23 < 23 at h; omega

set_option maxRecDepth 16384 in
theorem complete
    (h3 : Lower true (inputs.take 3) PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices.k3 4)
    (h4 : Lower true (inputs.take 4) PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices.k4 7)
    (h5 : Lower true (inputs.take 5) PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices.k5 9) : Lower true cols7 full 7 := by
  have impossible := forestSound nodes (PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Slices.validWithBounds h3 h4 h5) allChecks 0 (by decide +kernel)
  apply restoreInputs
  have home : stateOf n0 = activeRoots := by decide +kernel
  change Impossible true full 6 (stateOf n0).toFinset at impossible
  rw [home] at impossible
  let xs : List (Sig × Row × Row) := [(cols7.getD 0 zero,8,9),(cols7.getD 1 zero,4,6),(cols7.getD 2 zero,2,6),(cols7.getD 3 zero,1,9),(cols7.getD 4 zero,2,18)]
  have er := essential_ok (T:=full) (raw:=activeRoots) (xs:=xs) (by decide +kernel)
  have eq : (xs.map Prod.fst).toFinset = activeRoots.toFinset := by decide +kernel
  rw [eq] at er
  exact lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun a h => er a (List.mem_toFinset.mpr h)) impossible
end PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest

namespace PEqualNP.Outside.L_meta_11763_aux.Boost
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
def masks : List Nat := [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48]
def cliqueDomain : Nat → Sig
  | 1 => 0x500050000500050050005000050005005000500005000500500050000500050050005000050005005000500005000500500050000500050050005000050005
  | 2 => 0x40104010040104014010401004010401401040100401040140104010040104014010401004010401401040100401040140104010040104014010401004010401
  | 3 => 0x50000050050000055000005005000005500000500500000550000050050000055000005005000005500000500500000550000050050000055000005005000005
  | 4 => 0x50005000050005000050005000050005500050000500050000500050000500055000500005000500005000500005000550005000050005000050005000050005
  | 5 => 0x30030000000030033003000000003003300300000000300330030000000030033003000000003003300300000000300330030000000030033003000000003003
  | 6 => 0x30000030030000033000003003000003300000300300000330000030030000033000003003000003300000300300000330000030030000033000003003000003
  | 8 => 0x900990090000000090099009000000009009900900000000900990090000000090099009000000009009900900000000900990090000000090099009
  | 9 => 0x90090000000090099009000000009009900900000000900990090000000090099009000000009009900900000000900990090000000090099009000000009009
  | 10 => 0x90099009000000000000000090099009900990090000000000000000900990099009900900000000000000009009900990099009000000000000000090099009
  | 11 => 0xc03000000000c030c03000000000c030c03000000000c030c03000000000c030c03000000000c030c03000000000c030c03000000000c030c03000000000c03
  | 12 => 0xa0005000a000500000a0005000a00050a0005000a000500000a0005000a00050a0005000a000500000a0005000a00050a0005000a000500000a0005000a0005
  | 13 => 0x842184210000000084218421000000008421842100000000842184210000000084218421000000008421842100000000842184210000000084218421
  | 14 => 0x84218421000000000000000084218421842184210000000000000000842184218421842100000000000000008421842184218421000000000000000084218421
  | 16 => 0xa00050000a000500a00050000a000500a00050000a000500a00050000a000500a00050000a000500a00050000a000500a00050000a000500a00050000a0005
  | 17 => 0xc03000000c030000c03000000c030000c03000000c030000c03000000c030000c03000000c030000c03000000c030000c03000000c030000c03000000c03
  | 18 => 0x1100110000000000110011000000000011001100000000001100110000000000110011000000000011001100000000001100110000000000110011
  | 19 => 0x110000000000110011000000000011001100000000001100110000000000110011000000000011001100000000001100110000000000110011000000000011
  | 20 => 0x110011000000000000000000110011001100110000000000000000001100110011001100000000000000000011001100110011000000000000000000110011
  | 21 => 0x110000110000000011000011000000001100001100000000110000110000000011000011000000001100001100000000110000110000000011000011
  | 22 => 0x110011000000000000110011000000001100110000000000001100110000000011001100000000000011001100000000110011000000000000110011
  | 23 => 0x500050000000000050005000000000005000500000000000500050000000000050005000000000005000500000000000500050000000000050005
  | 25 => 0x500000005000000000500000005000005000000050000000005000000050000050000000500000000050000000500000500000005000000000500000005
  | 26 => 0x500000505000005000000000000000005000005050000050000000000000000050000050500000500000000000000000500000505000005
  | 27 => 0x50000000050000005000000005000000500000000500000050000000050000005000000005000000500000000500000050000000050000005000000005
  | 28 => 0x50005000050005000000000000000000500050000500050000000000000000005000500005000500000000000000000050005000050005
  | 29 => 0x30000000000030003000000000003000300000000000300030000000000030003000000000003000300000000000300030000000000030003000000000003
  | 30 => 0x30300000303000000000000000000000303000003030000000000000000000003030000030300000000000000000000030300000303
  | 31 => 0x303000000000000000000000303000003030000000000000000000003030000030300000000000000000000030300000303000000000000000000000303
  | 32 => 0x303000000000303000000000000000003030000000003030000000000000000030300000000030300000000000000000303000000000303
  | 33 => 0x212100002121000000000000000000002121000021210000000000000000000021210000212100000000000000000000212100002121
  | 34 => 0x30000000030000003000000003000000300000000300000030000000030000003000000003000000300000000300000030000000030000003000000003
  | 35 => 0x2200110000000000220011000000000022001100000000002200110000000000220011000000000022001100000000002200110000000000220011
  | 36 => 0x30030000000000003003000000000000300300000000000030030000000000003003000000000000300300000000000030030000000000003003
  | 37 => 0x300300003003000000000000000000003003000030030000000000000000000030030000300300000000000000000000300300003003
  | 38 => 0x303000000303000000000000000000003030000003030000000000000000000030300000030300000000000000000000303000000303
  | 39 => 0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505
  | 41 => 0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303
  | 42 => 0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033
  | 43 => 0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333
  | 44 => 0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333
  | 46 => 0x9999999999999999000000000000000099999999999999990000000000000000999999999999999900000000000000009999999999999999
  | 47 => 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
  | 48 => 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
  | _ => 0

def cliqueSize : Nat → Nat
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | 11 => 4
  | 12 => 4
  | 13 => 4
  | 14 => 4
  | 16 => 4
  | 17 => 4
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | 21 => 3
  | 22 => 3
  | 23 => 3
  | 25 => 3
  | 26 => 3
  | 27 => 3
  | 28 => 3
  | 29 => 3
  | 30 => 3
  | 31 => 3
  | 32 => 3
  | 33 => 3
  | 34 => 3
  | 35 => 3
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 7
  | 41 => 7
  | 42 => 7
  | 43 => 7
  | 44 => 7
  | 46 => 7
  | 47 => 7
  | 48 => 7
  | _ => 0

def cliqueBound (m : Nat) := match cliqueSize m with | 7 => 7 | 5 => 9 | 4 => 7 | 3 => 4 | _ => 0
def embeds : Nat → List Row
  | 1 => [0, 2, 36, 38, 16, 18, 52, 54, 64, 66, 100, 102, 80, 82, 116, 118, 0, 2, 36, 38, 16, 18, 52, 54, 64, 66, 100, 102, 80, 82, 116, 118]
  | 2 => [0, 10, 36, 46, 16, 26, 52, 62, 64, 74, 100, 110, 80, 90, 116, 126, 0, 10, 36, 46, 16, 26, 52, 62, 64, 74, 100, 110, 80, 90, 116, 126]
  | 3 => [0, 2, 36, 38, 24, 26, 60, 62, 64, 66, 100, 102, 88, 90, 124, 126, 0, 2, 36, 38, 24, 26, 60, 62, 64, 66, 100, 102, 88, 90, 124, 126]
  | 4 => [0, 2, 36, 38, 72, 74, 108, 110, 16, 18, 52, 54, 88, 90, 124, 126, 0, 2, 36, 38, 72, 74, 108, 110, 16, 18, 52, 54, 88, 90, 124, 126]
  | 5 => [0, 1, 12, 13, 48, 49, 60, 61, 64, 65, 76, 77, 112, 113, 124, 125, 0, 1, 12, 13, 48, 49, 60, 61, 64, 65, 76, 77, 112, 113, 124, 125]
  | 6 => [0, 1, 36, 37, 24, 25, 60, 61, 64, 65, 100, 101, 88, 89, 124, 125, 0, 1, 36, 37, 24, 25, 60, 61, 64, 65, 100, 101, 88, 89, 124, 125]
  | 8 => [0, 3, 12, 15, 16, 19, 28, 31, 64, 67, 76, 79, 80, 83, 92, 95, 0, 3, 12, 15, 16, 19, 28, 31, 64, 67, 76, 79, 80, 83, 92, 95]
  | 9 => [0, 3, 12, 15, 48, 51, 60, 63, 64, 67, 76, 79, 112, 115, 124, 127, 0, 3, 12, 15, 48, 51, 60, 63, 64, 67, 76, 79, 112, 115, 124, 127]
  | 10 => [0, 3, 12, 15, 16, 19, 28, 31, 96, 99, 108, 111, 112, 115, 124, 127, 0, 3, 12, 15, 16, 19, 28, 31, 96, 99, 108, 111, 112, 115, 124, 127]
  | 11 => [0, 1, 10, 11, 48, 49, 58, 59, 64, 65, 74, 75, 112, 113, 122, 123, 0, 1, 10, 11, 48, 49, 58, 59, 64, 65, 74, 75, 112, 113, 122, 123]
  | 12 => [0, 17, 2, 19, 72, 89, 74, 91, 32, 49, 34, 51, 104, 121, 106, 123, 0, 17, 2, 19, 72, 89, 74, 91, 32, 49, 34, 51, 104, 121, 106, 123]
  | 13 => [0, 5, 10, 15, 16, 21, 26, 31, 64, 69, 74, 79, 80, 85, 90, 95, 0, 5, 10, 15, 16, 21, 26, 31, 64, 69, 74, 79, 80, 85, 90, 95]
  | 14 => [0, 5, 10, 15, 16, 21, 26, 31, 96, 101, 106, 111, 112, 117, 122, 127, 0, 5, 10, 15, 16, 21, 26, 31, 96, 101, 106, 111, 112, 117, 122, 127]
  | 16 => [0, 17, 2, 19, 36, 53, 38, 55, 64, 81, 66, 83, 100, 117, 102, 119, 0, 17, 2, 19, 36, 53, 38, 55, 64, 81, 66, 83, 100, 117, 102, 119]
  | 17 => [0, 1, 10, 11, 36, 37, 46, 47, 64, 65, 74, 75, 100, 101, 110, 111, 0, 1, 10, 11, 36, 37, 46, 47, 64, 65, 74, 75, 100, 101, 110, 111]
  | 18 => [0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84]
  | 19 => [0, 4, 48, 52, 64, 68, 112, 116, 0, 4, 48, 52, 64, 68, 112, 116, 0, 4, 48, 52, 64, 68, 112, 116, 0, 4, 48, 52, 64, 68, 112, 116]
  | 20 => [0, 4, 16, 20, 96, 100, 112, 116, 0, 4, 16, 20, 96, 100, 112, 116, 0, 4, 16, 20, 96, 100, 112, 116, 0, 4, 16, 20, 96, 100, 112, 116]
  | 21 => [0, 4, 24, 28, 64, 68, 88, 92, 0, 4, 24, 28, 64, 68, 88, 92, 0, 4, 24, 28, 64, 68, 88, 92, 0, 4, 24, 28, 64, 68, 88, 92]
  | 22 => [0, 4, 72, 76, 16, 20, 88, 92, 0, 4, 72, 76, 16, 20, 88, 92, 0, 4, 72, 76, 16, 20, 88, 92, 0, 4, 72, 76, 16, 20, 88, 92]
  | 23 => [0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82]
  | 25 => [0, 2, 72, 74, 32, 34, 104, 106, 0, 2, 72, 74, 32, 34, 104, 106, 0, 2, 72, 74, 32, 34, 104, 106, 0, 2, 72, 74, 32, 34, 104, 106]
  | 26 => [0, 2, 24, 26, 32, 34, 56, 58, 0, 2, 24, 26, 32, 34, 56, 58, 0, 2, 24, 26, 32, 34, 56, 58, 0, 2, 24, 26, 32, 34, 56, 58]
  | 27 => [0, 2, 36, 38, 64, 66, 100, 102, 0, 2, 36, 38, 64, 66, 100, 102, 0, 2, 36, 38, 64, 66, 100, 102, 0, 2, 36, 38, 64, 66, 100, 102]
  | 28 => [0, 2, 36, 38, 16, 18, 52, 54, 0, 2, 36, 38, 16, 18, 52, 54, 0, 2, 36, 38, 16, 18, 52, 54, 0, 2, 36, 38, 16, 18, 52, 54]
  | 29 => [0, 1, 48, 49, 64, 65, 112, 113, 0, 1, 48, 49, 64, 65, 112, 113, 0, 1, 48, 49, 64, 65, 112, 113, 0, 1, 48, 49, 64, 65, 112, 113]
  | 30 => [0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41]
  | 31 => [0, 1, 8, 9, 96, 97, 104, 105, 0, 1, 8, 9, 96, 97, 104, 105, 0, 1, 8, 9, 96, 97, 104, 105, 0, 1, 8, 9, 96, 97, 104, 105]
  | 32 => [0, 1, 8, 9, 48, 49, 56, 57, 0, 1, 8, 9, 48, 49, 56, 57, 0, 1, 8, 9, 48, 49, 56, 57, 0, 1, 8, 9, 48, 49, 56, 57]
  | 33 => [0, 5, 8, 13, 32, 37, 40, 45, 0, 5, 8, 13, 32, 37, 40, 45, 0, 5, 8, 13, 32, 37, 40, 45, 0, 5, 8, 13, 32, 37, 40, 45]
  | 34 => [0, 1, 36, 37, 64, 65, 100, 101, 0, 1, 36, 37, 64, 65, 100, 101, 0, 1, 36, 37, 64, 65, 100, 101, 0, 1, 36, 37, 64, 65, 100, 101]
  | 35 => [0, 17, 4, 21, 64, 81, 68, 85, 0, 17, 4, 21, 64, 81, 68, 85, 0, 17, 4, 21, 64, 81, 68, 85, 0, 17, 4, 21, 64, 81, 68, 85]
  | 36 => [0, 1, 12, 13, 64, 65, 76, 77, 0, 1, 12, 13, 64, 65, 76, 77, 0, 1, 12, 13, 64, 65, 76, 77, 0, 1, 12, 13, 64, 65, 76, 77]
  | 37 => [0, 1, 12, 13, 32, 33, 44, 45, 0, 1, 12, 13, 32, 33, 44, 45, 0, 1, 12, 13, 32, 33, 44, 45, 0, 1, 12, 13, 32, 33, 44, 45]
  | 38 => [0, 1, 36, 37, 8, 9, 44, 45, 0, 1, 36, 37, 8, 9, 44, 45, 0, 1, 36, 37, 8, 9, 44, 45, 0, 1, 36, 37, 8, 9, 44, 45]
  | 39 => [0, 8, 16, 24, 64, 72, 80, 88, 32, 40, 48, 56, 96, 104, 112, 120, 2, 10, 18, 26, 66, 74, 82, 90, 34, 42, 50, 58, 98, 106, 114, 122]
  | 41 => [0, 16, 8, 24, 32, 48, 40, 56, 64, 80, 72, 88, 96, 112, 104, 120, 1, 17, 9, 25, 33, 49, 41, 57, 65, 81, 73, 89, 97, 113, 105, 121]
  | 42 => [0, 32, 4, 36, 16, 48, 20, 52, 1, 33, 5, 37, 17, 49, 21, 53, 64, 96, 68, 100, 80, 112, 84, 116, 65, 97, 69, 101, 81, 113, 85, 117]
  | 43 => [0, 4, 8, 12, 32, 36, 40, 44, 64, 68, 72, 76, 96, 100, 104, 108, 1, 5, 9, 13, 33, 37, 41, 45, 65, 69, 73, 77, 97, 101, 105, 109]
  | 44 => [0, 8, 4, 12, 16, 24, 20, 28, 1, 9, 5, 13, 17, 25, 21, 29, 64, 72, 68, 76, 80, 88, 84, 92, 65, 73, 69, 77, 81, 89, 85, 93]
  | 46 => [0, 4, 8, 12, 32, 36, 40, 44, 16, 20, 24, 28, 48, 52, 56, 60, 3, 7, 11, 15, 35, 39, 43, 47, 19, 23, 27, 31, 51, 55, 59, 63]
  | 47 => [0, 8, 2, 10, 16, 24, 18, 26, 1, 9, 3, 11, 17, 25, 19, 27, 64, 72, 66, 74, 80, 88, 82, 90, 65, 73, 67, 75, 81, 89, 83, 91]
  | 48 => [0, 16, 1, 17, 8, 24, 9, 25, 2, 18, 3, 19, 10, 26, 11, 27, 32, 48, 33, 49, 40, 56, 41, 57, 34, 50, 35, 51, 42, 58, 43, 59]
  | _ => []

def ranks : Nat → List Nat
  | 1 => [7, 0, 1, 7, 2, 1, 3]
  | 2 => [7, 0, 1, 0, 2, 1, 3]
  | 3 => [7, 0, 1, 2, 2, 1, 3]
  | 4 => [7, 0, 1, 2, 3, 1, 2]
  | 5 => [0, 7, 1, 1, 2, 2, 3]
  | 6 => [0, 7, 1, 2, 2, 1, 3]
  | 8 => [0, 0, 1, 1, 2, 7, 3]
  | 9 => [0, 0, 1, 1, 2, 2, 3]
  | 10 => [0, 0, 1, 1, 2, 3, 3]
  | 11 => [0, 1, 7, 1, 2, 2, 3]
  | 12 => [0, 1, 7, 2, 0, 3, 2]
  | 13 => [0, 1, 0, 1, 2, 7, 3]
  | 14 => [0, 1, 0, 1, 2, 3, 3]
  | 16 => [0, 1, 2, 7, 0, 2, 3]
  | 17 => [0, 1, 2, 1, 7, 2, 3]
  | 18 => [7, 7, 0, 7, 1, 7, 2]
  | 19 => [7, 7, 0, 7, 1, 1, 2]
  | 20 => [7, 7, 0, 7, 1, 2, 2]
  | 21 => [7, 7, 0, 1, 1, 7, 2]
  | 22 => [7, 7, 0, 1, 2, 7, 1]
  | 23 => [7, 0, 7, 7, 1, 7, 2]
  | 25 => [7, 0, 7, 1, 7, 2, 1]
  | 26 => [7, 0, 7, 1, 1, 2, 7]
  | 27 => [7, 0, 1, 7, 7, 1, 2]
  | 28 => [7, 0, 1, 7, 2, 1, 7]
  | 29 => [0, 7, 7, 7, 1, 1, 2]
  | 30 => [0, 7, 7, 1, 7, 2, 7]
  | 31 => [0, 7, 7, 1, 7, 2, 2]
  | 32 => [0, 7, 7, 1, 2, 2, 7]
  | 33 => [0, 7, 0, 1, 7, 2, 7]
  | 34 => [0, 7, 1, 7, 7, 1, 2]
  | 35 => [0, 7, 1, 7, 0, 7, 2]
  | 36 => [0, 7, 1, 1, 7, 7, 2]
  | 37 => [0, 7, 1, 1, 7, 2, 7]
  | 38 => [0, 7, 1, 2, 7, 1, 7]
  | 39 => [7, 4, 7, 0, 1, 3, 2]
  | 41 => [4, 7, 7, 1, 0, 2, 3]
  | 42 => [3, 7, 1, 7, 2, 0, 4]
  | 43 => [4, 7, 0, 1, 7, 2, 3]
  | 44 => [3, 7, 1, 0, 2, 7, 4]
  | 46 => [4, 4, 0, 1, 3, 2, 7]
  | 47 => [3, 1, 7, 0, 2, 7, 4]
  | 48 => [1, 3, 7, 2, 0, 4, 7]
  | _ => []

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def auxGraph : Sig := 0xfffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0
def standard : Nat → Sig | 7 => auxGraph | 5 => k5 | 4 => k4 | _ => k3
def embed (m : Nat) (r : Fin 32) : Row := (embeds m).getD r.val 0
def arg (m : Nat) (i : Fin 7) := (inputs.take (cliqueSize m)).getD ((ranks m).getD i.val 7) zero
def low (r : Row) : Fin 32 := ⟨r.val % 32,Nat.mod_lt _ (by decide)⟩
def toRow (j : Fin 32) : Row := ⟨j.val,by omega⟩
def ref (m : Nat) (r : Row) : Row := embed m (low r)

def cert (m : Nat) : Bool := decide (∀ j : Fin 32,
  bit (embed m j) (cliqueDomain m) = true ∧
    bit (embed m j) PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full = bit (toRow j) (standard (cliqueSize m)) ∧
    ∀ i : Fin 7, bit (embed m j) (PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero) = bit (toRow j) (arg m i))


end PEqualNP.Outside.L_meta_11763_aux.Boost

namespace PEqualNP.Outside.L_meta_11763_aux.Boost
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem certs : masks.all cert = true := by decide +kernel


def smalls := auxGraph :: zero :: k3 :: k4 :: k5 :: inputs.take 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem periods : smalls.all (fun w => decide (∀ r : Row, bit (toRow (low r)) w = bit r w)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem facts : masks.all (fun m => decide (
    (cliqueSize m=3 ∨ cliqueSize m=4 ∨ cliqueSize m=5 ∨ cliqueSize m=7) ∧ standard (cliqueSize m) ∈ smalls ∧
    ∀ i : Fin 7, arg m i ∈ smalls)) = true := by decide +kernel

theorem fromWord {xs : List Sig} (j : Nat) :
    Available true (xs.map observe) (observe (xs.getD j zero)) := by
  by_cases h : j < xs.length
  · apply Or.inl
    apply List.mem_map_of_mem
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using (List.getElem_mem h)
  · have hz : xs.getD j zero = zero := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [hz]; exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem validParam (m : Nat) (hm : m ∈ masks)
    (lower : Lower true (inputs.take (cliqueSize m)) (standard (cliqueSize m)) (cliqueBound m)) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  have tbl0 := List.all_eq_true.mp certs m hm
  unfold cert at tbl0
  have tbl := of_decide_eq_true tbl0
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  have periodic (x : Sig) (hx : x ∈ smalls) : ∀ r, bit (toRow (low r)) x = bit r x :=
    of_decide_eq_true (List.all_eq_true.mp periods x hx)
  have tgt : restrictRows (ref m) (observe PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full) = observe (standard (cliqueSize m)) :=
    funext fun r => ((tbl (low r)).2.1).trans (periodic _ info.2.1 r)
  refine ⟨ref m,inputs.take (cliqueSize m),fun r => (tbl (low r)).1,?_,?_,?_⟩
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 7 := ⟨j,by exact hj⟩
    have eq : restrictRows (ref m) (observe (PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero)) = observe (arg m i) :=
      funext fun r => ((tbl (low r)).2.2 i).trans (periodic _ (info.2.2 i) r)
    have same : PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7.getD i.val zero = PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [← same,eq]; exact fromWord _
  · rw [tgt]
    apply observe_proper
    rcases info.1 with e|e|e|e <;> rw [e] <;> unfold proper <;> decide +kernel
  · rw [tgt]; exact lower
theorem validWithBounds
    (h3 : Lower true (inputs.take 3) k3 4)
    (h4 : Lower true (inputs.take 4) k4 7)
    (h5 : Lower true (inputs.take 5) k5 9)
    (m : Nat) (hm : m ∈ masks) :
    Slice true PEqualNP.Outside.L_meta_11763_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_11763_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  apply validParam m hm
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  unfold cliqueBound
  rcases info.1 with h | h | h | h <;> rw [h]
  · exact h3
  · exact h4
  · exact h5
  · exact PEqualNP.Outside.L_meta_11763_aux.Subgraph908.Forest.complete h3 h4 h5

end PEqualNP.Outside.L_meta_11763_aux.Boost

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.GraphTarget

abbrev Entry := Nat × List Nat × Nat × List Nat
def Entry.cap (x : Entry) : Nat := x.1
def Entry.program (x : Entry) : List Nat := x.2.1
def Entry.livingMask (x : Entry) : Nat := x.2.2.1
def Entry.codes (x : Entry) : List Nat := x.2.2.2

def unpackGates (ws : List Sig) : List Nat → List Choice
  | [] => []
  | g :: gs =>
    let c : Choice := (g / 256, ws.getD (g % 16) 0, ws.getD ((g / 16) % 16) 0)
    c :: unpackGates (ws ++ [choiceVal c]) gs

def selectMask {α : Type} (m : Nat) (ws : List α) : List α :=
  (ws.zipIdx.filter fun p => m.testBit p.2).map Prod.fst

def choicesOf (e : Entry) := unpackGates cols7 e.program

def stateOf (e : Entry) : List Sig :=
  selectMask e.livingMask (cols7 ++ (choicesOf e).map choiceVal)

def negativeRows : List Row := [0,1,2,3,4,5,6,7,8,10,12,14,16,17,24,32,36,48,64,72,96]

def candidates (r : Row) : List Sig → Sig
  | [] => full
  | w :: ws => (if bit r w then w else ~~~w) &&& candidates r ws

def indist (ws : List Sig) := negativeRows.any fun r => candidates r ws != 0

def pop (x : Nat) : Nat := (BitVec.ofNat 16 x).cpop.toNat

def readCode (e : Entry) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Nat :=
  let ia := ws.idxOf a
  let ib := ws.idxOf b
  let lo := min ia ib
  let hi := max ia ib
  let block := e.codes.getD (hi*(hi-1)/2+lo) 0
  let dir := ia < ib
  let slot := 4 * (if dir then d else flipOp d) +
    (if dir then ka.toNat + 2*kb.toNat else kb.toNat + 2*ka.toNat)
  if block.testBit slot then
    let rank := pop (block % (2^slot))
    (block >>> (16+20*rank)) % (2^20)
  else 0

theorem candBit (r s : Row) (ws : List Sig) :
    bit s (candidates r ws) = true ↔ bit s full = true ∧ ∀ w ∈ ws, bit r w = bit s w := by
  induction ws with
  | nil => simp [candidates]
  | cons a ws ih =>
    have ba (x y : Sig) : bit s (x &&& y) = (bit s x && bit s y) := BitVec.getLsbD_and
    have bn (x : Sig) : bit s (~~~x) = !bit s x := by
      simp only [bit,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and]
    cases hr : bit r a <;> cases hs : bit s a <;>
      simp only [candidates,hr,Bool.false_eq_true,ite_false,ite_true,ba,bn,hs,Bool.and_eq_true,
        ih,List.forall_mem_cons] <;> simp_all

set_option maxRecDepth 8192 in
theorem indistSound {ws : List Sig} (bad : indist ws = true) (k : Nat) :
    Impossible true full k ws.toFinset := by
  obtain ⟨s,hs,hbad⟩ := List.any_eq_true.mp bad
  have hn : bit s full = false := (by decide +kernel : ∀ r ∈ negativeRows, bit r full = false) s hs
  intro l _ run
  have z : candidates s ws = 0 := by
    apply bit_ext
    intro r
    cases e : bit r (candidates s ws)
    · exact (bit_zero _).symm
    · obtain ⟨yes,all⟩ := (candBit _ _ _).mp e
      obtain ⟨w,hw,sep⟩ := live_row_difference run (show bit r full ≠ bit s full by simp [yes,hn])
      exact False.elim (sep (all w (List.mem_toFinset.mp hw)).symm)
  simp [z] at hbad
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.GraphTarget
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits

theorem childSwap {u : Bool} {d : Nat} (hd : allowed u d) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip hd a b, List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem enumStepOrdered {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb ne fresh pr sz
  rcases lt_or_gt_of_ne (fun eq => ne (BitVec.toNat_inj.mp eq)) with lt | gt
  · exact twoStep a ha b hb d hd ka kb lt fresh pr sz
  · have eq := bin_flip hd a b
    have perm := childSwap hd ws a b ka kb
    have hs := twoStep b hb a ha (flipOp d) (flip_flip hd).1 kb ka gt
      (eq ▸ fresh) (eq ▸ pr) (perm.length_eq ▸ sz)
    have eqSet : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext x
      simpa only [List.mem_toFinset] using (perm.mem_iff : x ∈ _ ↔ x ∈ _)
    exact eqSet.symm ▸ hs

end PEqualNP.Outside.L_meta_11763_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.GraphTarget PEqualNP.Outside.L_meta_11763_aux.Boost PEqualNP.Outside.L_meta_11763_aux.GraphSymmetry

def verifyCut (cap : Nat) (cs : List Choice) (ch : List Sig) (code : Nat) : Bool :=
  let m := (code-1) / 256
  let witness := selectMask ((code-1) % 256) cs
  let mask := cliqueDomain m
  masks.contains m &&
    match makePool true mask cols7 witness with
    | none => false
    | some pool => poolCut true mask (cliqueBound m) cap witness.length pool ch

def verifyIso (db : Array Entry) (cap : Nat) (ch : List Sig) (code : Nat) : Bool :=
  let key := code-65536
  let j := key/1
  let p : Fin 1 := Fin.ofNat 1 (key % 1)
  let dest := db[j]?.getD default
  decide (j < db.size) && (dest.cap==cap) &&
    decide ((ch.map (permWord p)).toFinset = (stateOf dest).toFinset)

def verifyChild (db : Array Entry) (e : Entry) (steps : List Choice) (ws : List Sig)
    (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  let y := bin d a b
  let ch := childTwo ws a b d ka kb
  if b.toNat ≤ a.toNat then true else
  if a == b || ws.contains y || y == zero || y == one || decide (e.cap < ch.length) then true
  else if indist ch then true
  else
    let code := readCode e ws a b d ka kb
    if code==0 then false else if 65536 ≤ code then verifyIso db (e.cap-1) ch code
      else verifyCut (e.cap-1) (steps++[(d,a,b)]) ch code

def verify (db : Array Entry) (e : Entry) : Bool :=
  let ws := stateOf e
  let cs := choicesOf e
  if e.cap = 0 then !ws.contains full else
  decide (0 < e.cap) && decide ws.Nodup && !ws.contains full &&
    ws.all fun a => ws.all fun b => [0,1,2,3].all fun d =>
      [false,true].all fun ka => [false,true].all fun kb => verifyChild db e cs ws a b d ka kb
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
def n0 : Entry := ⟨10, [], 127, [0x029010010110001001018888,0x027010010102701001018888,0x027011003e02901029011003c02701a8a8,0x001010010100101001018888,0x001010290102a01001018888,0x001010270110040001018888,0x02b010010110008001018888,0x02b010290102b01029018888,0x02b010270110043027018888,0x02b010010110044001018888,0x02c010010110022001018888,0x02c010290102c01029018888,0x001010010102f01027018888,0x02c01001011005d001018888,0x02c0102b011007002b018888,0x03001001011002d001018888,0x03001029011003f029018888,0x030010270103001027018888,0x030010010110064001018888,0x0300102b011008302b018888,0x0300102c011008502c018888]⟩
def n1 : Entry := ⟨9, [272], 255, [0x00101005010010100101001010010100101ca0e,0x001010010100101001018888,0x012010120100501012010120102701012011000400501acf8,0x001010010100101001010010100101c88c,0x0010100101001010010100101001018cc8,0x001010010100101001018888,0x0010100101001010010102b01001018cc8,0x0120102b0100501012010050101201c88c,0x01e010170101e01017018888,0x001010010100101001018888,0x0010100101001010010101201001018cc8,0x0080100501012010120101201005018cc8,0x001010010100101001018888,0x001010010100101001018888,0x005010050101201008018888,0x0010100101001010010110002001018cc8,0x0120100501012010120110006005018cc8,0x01e010170101e01017018888,0x001010010100101001018888,0x01e0101e0101e0101e018888,0x012010080101201008018888,0x001010050100101e000,0x001010010100101e000,0x01201012010120100b0101201027010120100b01aaaa,0x0010100101001010010100101001010010100101aaaa,0x01201012010120100c010120102b010120101101aaaa,0x0120101201008010080101201012010080100801aaaa,0x01201012010120101e0101201100070120101201aaaa]⟩
def n2 : Entry := ⟨8, [272,352], 510, [0x012010120101e0101201100032470,0x00101001010440,0x0000,0x01e01012014004,0x0000,0x0000,0x01201012010440,0x0000,0x0000,0x0000,0x0120101e010440,0x0000,0x00101001012020,0x0000,0x01201012012020,0x00101001016000,0x0120101e012020,0x0000,0x0120101e012020,0x0000,0x0120101a0101201012014206,0x01a010050101201005014206,0x0000,0x00101001010202,0x01e0101e012020,0x01201012012020,0x00101001016000,0x01a01005010120100501005014207]⟩
def n3 : Entry := ⟨7, [272,352,289], 1016, [0x0000,0x0000,0x0000,0x00105001052020,0x0000,0x01201012012020,0x0000,0x0120101e012020,0x0000,0x01201012014004,0x00105001050202,0x01e0101e012020,0x01201012012020,0x00105001056000,0x00501005010202,0x0000,0x0000,0x0000,0x0000,0x0000,0x01d0101d014004]⟩
def n4 : Entry := ⟨8, [272,289], 505, [0x001030010300103001030010300103c88c,0x0010300103001030010302b01001038cc8,0x001030010300103001038888,0x0010300103001030010301201001038cc8,0x001030010300103001038888,0x005010050101201008038888,0x0010300103001030010310003001038cc8,0x001030010300103001038888,0x01e0101e0101e0101e018888,0x012010080301201008038888,0x001030050100103e000,0x001030010300103001030010300103a8a8,0x0120101201012010120102b0101201a8a8,0x0120100803008030010300803008038a8a,0x012010120101201012011000501201a8a8,0x0010301e0100103001030010300103c88c,0x001030010300103001038888,0x01e0101e0101e0101e018888,0x006010010300103001038888,0x01e0101e0101e0101e018888,0x00d0200b0100103001030010300103c88c]⟩
def n5 : Entry := ⟨7, [272,289,374], 889, [0x0000,0x0010701e010440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e01001076000,0x00107001072020,0x01e0101e012020,0x00803008030202,0x01201012016000,0x00b0100b010202]⟩
def n6 : Entry := ⟨8, [272,353], 509, [0x0000,0x00103001034004,0x0000,0x0010301e010440,0x0000,0x0000,0x00103012010440,0x0000,0x0000,0x0000,0x0010301e010440,0x0000,0x0000,0x01e0101e012020,0x01201012012020,0x00501001036000,0x0120101e012020,0x0000,0x0120101e012020,0x0000,0x0120101a0101201012014206,0x01e010010100103001014206,0x01e0101e012020,0x00103001032020,0x01102011020202,0x01201012012020,0x00501005016000,0x01a01001010010300101001014207]⟩
def n7 : Entry := ⟨8, [272,374], 383, [0x0000,0x0000,0x012010120101e0101201100052470,0x0000,0x0000,0x0000,0x0010301e010440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01201012012020,0x01e01001036000,0x01a01012016000,0x01e0100b0101e0100b012222,0x001030010100103001012222,0x01e0100c0101e0100c012222,0x012010080101201008012222,0x01201012016000]⟩
def n8 : Entry := ⟨9, [320], 255, [0x0010100101001010010102b01001018cc8,0x0010100101001010010102701001018cc8,0x00c01027010120101e0102b0100c01a8a8,0x001010010100101001018888,0x001010010100101001018888,0x001010010100101001018888,0x0010100c010010100101001010010100101ca0e,0x011010120101e01011018888,0x0110100c010190100c018888,0x001010010100101001010010100101a8a8,0x001010010100101001018888,0x012010120101201012018888,0x001010010100101001018888,0x001010010100101001018888,0x012010110102b0102b011000d011018cc8,0x0010100101001010010110009001018cc8,0x01e010120101e01012018888,0x01e0100c0101e0100c018888,0x001010010100101001018888,0x01e010110102b0101e0110011011018cc8,0x01e010120110012012018888,0x0010100c0100101e000,0x0190102b01012010050102b0102b010120100501aaaa,0x019010270100c0100b01019010270100c0100b01aaaa,0x0010100101001010010100101001010010100101aaaa,0x001010010100101e000,0x019011001b01201005011001a100180120100801aaaa,0x019011002001e0101e011001f1001d0190101e01aaaa]⟩
def n9 : Entry := ⟨8, [320,352], 510, [0x01e0101e012020,0x0000,0x0000,0x0000,0x0000,0x00101001012020,0x0000,0x0000,0x0000,0x01e011000a0440,0x0000,0x0000,0x00101001012020,0x01e0101e010440,0x01e011000c2020,0x01e0101e012020,0x01e0101e012020,0x0000,0x00101001016000,0x0000,0x0190101a010190101a014206,0x01e0101e012020,0x01e0101e012020,0x0000,0x01a0100c0101a0100c014206,0x0000,0x00101001016000,0x01a0100c0101a0100c0100c014207]⟩
def n10 : Entry := ⟨7, [320,352,340], 1006, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000b0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n11 : Entry := ⟨6, [320,352,340,357], 1934, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n12 : Entry := ⟨7, [320,352,357], 958, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000b0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n13 : Entry := ⟨8, [320,340], 495, [0x00103012010440,0x00103017010440,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x01201012012020,0x00103001032020,0x0000,0x001031000a0440,0x0000,0x0000,0x0000,0x012011000e0440,0x00c03001036000,0x01201012012020,0x0000,0x00103001032020,0x013010050101201005014206,0x0000,0x023010010100103001014206,0x0000,0x0000,0x00103001032020,0x00502005026000,0x100101000f2020,0x00501001010010300101001014207]⟩
def n14 : Entry := ⟨7, [320,340,357], 975, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000b0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n15 : Entry := ⟨7, [320,340,390], 751, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010001]⟩
def n16 : Entry := ⟨7, [320,340,902], 751, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n17 : Entry := ⟨8, [320,356], 495, [0x0010301e010440,0x0010301e010440,0x01e0101e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0010301e010440,0x01e0101e012020,0x01e0101e012020,0x0000,0x0000,0x00c03001036000,0x01e0101e012020,0x01e0101e012020,0x0000,0x0000,0x0190101a010190101a0101e014207,0x01e010010100103001014206,0x0000,0x01e0101e014004,0x00103001032020,0x01e011000f2020,0x01101011016000,0x01a01001010010300101001014207]⟩
def n18 : Entry := ⟨8, [320,357], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000e0010,0x1000c0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00503100130110,0x0000,0x0000,0x0000,0x0000,0x0000,0x005021000f0110,0x0000,0x0000,0x020010130110014019011111]⟩
def n19 : Entry := ⟨7, [320,357,373], 863, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030001,0x0000,0x0000,0x00a010001]⟩
def n20 : Entry := ⟨7, [320,357,391], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10015005011001,0x10016001011001,0x10017001011001,0x0000,0x0000,0x0000]⟩
def n21 : Entry := ⟨6, [320,357,391,913], 1149, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n22 : Entry := ⟨6, [320,357,391,914], 1147, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n23 : Entry := ⟨6, [320,357,391,915], 1143, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n24 : Entry := ⟨8, [320,373], 383, [0x00103012010440,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01201100130440,0x02301001036000,0x012010050101201005012222,0x017010010100103001012222,0x01501001030150100101001030010300101001017227,0x01201012016000,0x01301012016000,0x1001900a011001401a012222]⟩
def n25 : Entry := ⟨7, [320,373,902], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n26 : Entry := ⟨8, [320,373], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01301012011001,0x0000,0x023011000,0x0000,0x0000,0x01501001011001,0x012011000,0x0000,0x0000,0x005011000]⟩
def n27 : Entry := ⟨8, [320,885], 383, [0x00103012010440,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x00103001032020,0x0000,0x0000,0x0000,0x01201013012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030010100103001012222,0x009010050101201005012222,0x001030010101701001012222,0x001030010100103001012222,0x001010050100101001032222,0x01301012010060,0x0130101a011001c00a012222]⟩
def n28 : Entry := ⟨7, [320,885,390], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n29 : Entry := ⟨8, [320,374], 383, [0x0010301e010440,0x0010301e010440,0x01e0101e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e01001036000,0x01e010050101e01005012222,0x0210101e010210100b0101e0101e0100b0100b017227,0x001030010100103001012222,0x01a0101a016000,0x1001e0050110014005012222,0x01901019016000]⟩
def n30 : Entry := ⟨7, [320,374,901], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n31 : Entry := ⟨8, [320,374], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01901019011001,0x01e011000,0x0000,0x0210100c011001,0x0000,0x01a011000,0x0000,0x0000,0x01a011000]⟩
def n32 : Entry := ⟨8, [320,886], 383, [0x0010301e010440,0x00103019010440,0x0190101e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x01901019012020,0x0000,0x001030010100103001012222,0x019010050101e01005012222,0x0190100b010190100b012222,0x001030010100103001012222,0x001010110100101001032222,0x013010080110021008012222,0x0190101e010060]⟩
def n33 : Entry := ⟨7, [320,886,389], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01501001011001,0x0000,0x0000,0x0000]⟩
def n34 : Entry := ⟨9, [336], 255, [0x0010100101001010010101201001018cc8,0x001010010100101001018888,0x012010120101201012010120101201a8a8,0x0010100101001010010100101001018cc8,0x001010010100101001018888,0x001010010100101001018888,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x001010010100101001018888,0x00101008010010100101001010010100101ca0e,0x008010120101201008018888,0x001010010100101001018888,0x001010010100101001010010100101a8a8,0x008010120101201008018888,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x001010010100101001018888,0x0300202b021002602b028888,0x0120100801012010120110028008018cc8,0x001010080100101e000,0x0080100801008010050101201012010120100501aaaa,0x0010100101001010010100101001010010100101aaaa,0x001010120100101100230010100101001010010100101001010010100101faaf,0x0120101201012010050101201100180120101101aaaa,0x001010010100101e000,0x01201012010120101e01012011002a0120101201aaaa]⟩
def n35 : Entry := ⟨8, [336,883], 375, [0x001010010100101001018888,0x001010010100101001018888,0x012010120101201012010120101201a8a8,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x001010010100101001018888,0x008030120101201008038888,0x001010010100101001018888,0x008030120101201008038888,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x0300402b041002402b048888,0x012010080301201008038888,0x001010010100101001018888,0x008030120101201002038888,0x001010010100101001018888,0x012010120101201003038888,0x001010010100101001018888,0x012010120101201004038888]⟩
def n36 : Entry := ⟨7, [336,883,356], 887, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10025017011001,0x0000,0x0000,0x0000,0x0000]⟩
def n37 : Entry := ⟨6, [336,883,356,914], 1395, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n38 : Entry := ⟨8, [336,356], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10024001031001,0x0000,0x0000,0x0000,0x0000,0x0000,0x10027017011001,0x0000,0x0000,0x0000,0x0000,0x01e010120110014012011111]⟩
def n39 : Entry := ⟨7, [336,356,898], 763, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10025001071001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n40 : Entry := ⟨8, [336,357], 479, [0x00103012010440,0x0000,0x01201012012020,0x00103001030440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x01201012012020,0x0000,0x00103001032020,0x0000,0x00801001036000,0x00801012012020,0x00103001032020,0x01201001030010300103001034207,0x01201100132020,0x0120100a0101201012014206,0x100290010100103001014206,0x0000,0x0000,0x00103001032020,0x0000,0x00801008016000,0x00a01001010010300101001014207]⟩
def n41 : Entry := ⟨7, [336,357,896], 990, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n42 : Entry := ⟨8, [336,374], 383, [0x00103012010440,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x1002b001036000,0x012010050101201005012222,0x017010010100103001012222,0x01601001030160100101001030010300101001017227,0x1002c0050110014005012222,0x01401012016000,0x01201012016000]⟩
def n43 : Entry := ⟨7, [336,374,896], 894, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010100]⟩
def n44 : Entry := ⟨7, [336,374,900], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n45 : Entry := ⟨9, [352], 255, [0x0010100101001010010110002001018cc8,0x0010100101001010010102701001018cc8,0x01701027010120101e011002e01201a8a8,0x001010010100101001018888,0x001010010100101001018888,0x001010010100101001018888,0x0010100101001010010110009001018cc8,0x01e010120101e01012018888,0x01e010170101e01017018888,0x001010010100101001018888,0x001010010100101001018888,0x012010120101201012018888,0x001010010100101001018888,0x001010010100101001018888,0x0120101e0110031012018888,0x0010101e010010100101001010010100101ca0e,0x01a010120101e01012018888,0x01a010170101a01017018888,0x001010010100101001010010100101a8a8,0x01a0101e0101e0101a018888,0x01a010300101201030011003601201a8a8,0x0010101e0100101e000,0x01a0102e01012010050110030100070120100501aaaa,0x01a01027010170100b0101a01027010170100b01aaaa,0x0010100101001010010100101001010010100101aaaa,0x01a011003401e0100c01100331001d01a0101101aaaa,0x01a011003a0120100801100381002a0120100801aaaa,0x001010010100101e000]⟩
def n46 : Entry := ⟨8, [352,289], 507, [0x00103001030120100103100032470,0x0000,0x00103001030440,0x0010301e010440,0x0120101e010440,0x0000,0x0000,0x01201012014004,0x0000,0x0000,0x01e010010300103001034206,0x0120101e010440,0x00103001032020,0x0000,0x01201012012020,0x01e01001036000,0x012010120100501005011002f0120110005005012772,0x001030010300103001032222,0x01e0100c0101e01011032222,0x012010080301201008032222,0x00103001036000,0x0010301e010440,0x01701012016000,0x0000,0x0000,0x0000,0x0000,0x01d0101e0101e0101d014444]⟩
def n47 : Entry := ⟨7, [352,289,369], 1017, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e011000,0x0000,0x0000,0x0000,0x012011000,0x005011000,0x0000]⟩
def n48 : Entry := ⟨8, [352,369], 511, [0x0000,0x0000,0x1002f0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a01012011001,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e011000,0x0000,0x0000,0x0000,0x0000,0x0000,0x012011000,0x005011000]⟩
def n49 : Entry := ⟨8, [352,340], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000a0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100320010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01f01014011001401a011111]⟩
def n50 : Entry := ⟨7, [352,340,357], 927, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1000b0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n51 : Entry := ⟨8, [352,372], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a0101a011001,0x0000,0x0000,0x01e011000,0x0000,0x02101017011001,0x0000,0x0000,0x0000,0x019011000,0x00c011000]⟩
def n52 : Entry := ⟨8, [352,884], 383, [0x0010301e010440,0x0010301a010440,0x01a0101e012020,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a0101a010440,0x0000,0x001030010100103001012222,0x01a010050101e01005012222,0x01a0100b0101a0100b012222,0x001030010100103001012222,0x01a0101e010060,0x014010050110035005012222,0x001010110100101001032222]⟩
def n53 : Entry := ⟨7, [352,884,389], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n54 : Entry := ⟨8, [352,357], 447, [0x00103012010440,0x00103017010440,0x01201012012020,0x0000,0x0000,0x0000,0x001031000c0440,0x0000,0x0000,0x0000,0x00103001032020,0x01201012012020,0x00103001032020,0x00103001030202,0x01201100322020,0x01e01001036000,0x01201012012020,0x0000,0x00103001032020,0x0000,0x014010080101201008014206,0x100370010100103001014206,0x0000,0x0000,0x00103001032020,0x0000,0x01401012016000,0x00801001010010300101001014207]⟩
def n55 : Entry := ⟨7, [352,357,896], 958, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n56 : Entry := ⟨8, [352,373], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01401012011001,0x0000,0x100391000,0x0000,0x0000,0x01601001011001,0x0000,0x0000,0x012011000,0x008011000]⟩
def n57 : Entry := ⟨7, [352,373,896], 766, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010100]⟩
def n58 : Entry := ⟨8, [352,885], 383, [0x00103012010440,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x01201014010440,0x001030010100103001012222,0x00a010050101201005012222,0x001030010101701001012222,0x001030010100103001012222,0x01401005011003b005012222,0x01401012010060,0x001010080100101001032222]⟩
def n59 : Entry := ⟨7, [352,885,388], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n60 : Entry := ⟨9, [289], 251, [0x005010290100102012011000400102a8a8,0x001020010200102001028888,0x0010200501029010120102a01001028cc8,0x01e010010202b01001028888,0x01e01005010290101e0102b01005018cc8,0x006010010202a01001028888,0x012010010201201001028888,0x0120102c0100501012010050102901c88c,0x012010010201201001028888,0x005010050102b01012018888,0x01e01001021002e001028888,0x01e01005010290101e011003d005018cc8,0x01e010010202a01001028888,0x01e0101e0101e0101e018888,0x01e010120102c01012018888,0x01e010010202901001028888,0x01e010270102701e000,0x005010010202901001028888,0x01e0101e0101e0101e018888,0x006010010202901012018888,0x01e0101e0101e0101e018888]⟩
def n61 : Entry := ⟨8, [289,353], 505, [0x001040010400104001048888,0x01e010010401e01001048888,0x006010010401e01001048888,0x012010010401201001048888,0x012010010401201001048888,0x005010050101e01012018888,0x01e010010401e01001048888,0x01e010010401e01001048888,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e0101e010120101e0102c0101201a8a8,0x01e010010401e01001048888,0x005010010401e01001048888,0x01e0101e0101e0101e018888,0x006010010401e01012018888,0x01e0101e0101e0101e0101e0101e01c88c,0x01e0101e010010401e011000500104a8a8,0x01e0101e010010401e0102a0100104a8a8,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e01012010080201e0101201008028a8a,0x005010050100501e000,0x01e0101e0100b0101e0101e0101e018a8a]⟩
def n62 : Entry := ⟨9, [801], 251, [0x005010010201201001028888,0x001020010200102001028888,0x001020050101201001028888,0x00c010010202701001028888,0x01e010050101e01005018888,0x006010010202a01001028888,0x012010010201201001028888,0x012010050101201005018888,0x012010010201201001028888,0x005010050102b01012018888,0x01e010010202701001028888,0x01e010050101e01005018888,0x00c010010202a01001028888,0x01e0101e0101e0101e018888,0x01e010120102c01012018888,0x00b010010201701001028888,0x01e01027010290100e0,0x005010010201701001028888,0x00b0101e0101e0100b018888,0x00102006010170100b018888,0x00b0101e0101e0100b018888]⟩
def n63 : Entry := ⟨9, [353], 255, [0x0050101e0100102012011000600102a8a8,0x01e010010201e01001028888,0x01e0101e010050101e0101e0101e0101e011003d00501acf8,0x001020010200102001028888,0x001020050101201001028888,0x001020050101e01001028888,0x01e010010201e01001028888,0x01e010050101e0101e0101e01005018cc8,0x01e0101e0101e0101e018888,0x006010010201e01001028888,0x012010010201201001028888,0x012010050101201005018888,0x001020010201e01012018888,0x012010010201201001028888,0x005010050101e01012018888,0x01e010010201e01001028888,0x01e0101e0100501005010050101e0100501ca0e,0x01e0101e0101e0101e018888,0x01e010010201e01001028888,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e0101e010120101e0102c0101201a8a8,0x01e0101e01001020010101e01100070010200101aaaa,0x01e0101e0101e01e000,0x01e0101e0101e0100b0101e0101e0101e0100b01aaaa,0x01e0101e01001020010101e0102a010010200101aaaa,0x01e0101e0101e010110101e0101e0101e0101101aaaa,0x01e0101e01012010080101e0102c010120100801aaaa,0x005010050100501e000]⟩
def n64 : Entry := ⟨9, [306], 255, [0x001010010100101001018888,0x001010010100101001010010100101a8a8,0x00b010170100501017010290100501a8a8,0x001010010100101001018888,0x001010010100101001018888,0x00101001010010100501001010010100101ca0e,0x001010010100101001018888,0x01e010050101e01005018888,0x0170100b010170100b018888,0x0010100101001010010110041001018cc8,0x001010010100101001018888,0x008010050101201005018888,0x0010100101001010010100101001018cc8,0x001010010100101001018888,0x005010050101701008018888,0x001010010100101001018888,0x01e010050101e01005018888,0x0170100b010170100b018888,0x0010100101001010010103001001018cc8,0x01e0101e0101e0101e018888,0x017010080101701008018888,0x0010100101001010010100101001010010100101aaaa,0x00b0100b01005010020101701029010050100501aaaa,0x001010010100101e000,0x001010050100101e000,0x0170101701017010030101701100420170101101aaaa,0x0010100101001010010100101001010010100101aaaa,0x00c0100c0100c010040101701030010170101701aaaa]⟩
def n65 : Entry := ⟨8, [306,323], 503, [0x0000,0x00101001012020,0x0170101e012020,0x00101001012020,0x0000,0x0000,0x0000,0x0000,0x00101001010440,0x00503017010440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00b0301e012020,0x00101001016000,0x017010030101701003014206,0x0000,0x00c0301e012020,0x0000,0x0000,0x01b010050101701005014206,0x00101001016000,0x0000,0x0190101e012020,0x00301005010030100501003014207]⟩
def n66 : Entry := ⟨8, [306,372], 383, [0x0000,0x0000,0x0170101e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0010301e010440,0x0000,0x0000,0x001030010100103001012222,0x01e010020101e01002012222,0x01b01017016000,0x01901001036000,0x01701017016000,0x017010010100103001012222,0x019010040101e01004012222]⟩
def n67 : Entry := ⟨9, [322], 255, [0x01e010010201e01001028888,0x00b010010201701001028888,0x00b0101e0101e0101e0101e0100b01a8a8,0x001020010200102001028888,0x0010200b0101e01001028888,0x0010200b0101701001028888,0x00c010010201901001028888,0x0110101e0101e01011018888,0x011010110100b0100b0100b010110100b01ca0e,0x011010010201e01001028888,0x017010010201701001028888,0x0170101e0101e01017018888,0x00102001020170100b018888,0x017010010201701001028888,0x00b0100b0101e01011018888,0x01e010010201e01001028888,0x01e0101e0101e0101e018888,0x01e0100b0101e0101e0101e0100b018cc8,0x00c010010201e01001028888,0x01e010110101e0101e0101e01011018cc8,0x01e010170101e01017018888,0x00c0100c01001020010101901027010010200101aaaa,0x0190101e0101e010050101e0101e010190100501aaaa,0x011010110101101e000,0x0190101e01001020010101e01100420010200101aaaa,0x00b0100b0100b01e000,0x00b0100b01001020010101e0102f010170100101aaaa,0x0190101e0101e0101e0101e0101e010190101e01aaaa]⟩
def n68 : Entry := ⟨9, [323], 255, [0x001010010100101001018888,0x001010010100101001018888,0x0170102a010060101e0102a0100601a8a8,0x001010010100101001018888,0x0010100101001010010102a0100101a8a8,0x001010010100101001011004100101a8a8,0x001010010100101001010010100101a8a8,0x011010060101e01006018888,0x011010170101e01011018888,0x00101003010010100101001010010100101ca0e,0x001010010100101001018888,0x012010060101201006018888,0x001010010100101001018888,0x001010010100101001018888,0x012010110102b0102b011004b011018cc8,0x001010010100101001018888,0x01e010060101e01006018888,0x01e010170101e01017018888,0x0010100101001010010110047001018cc8,0x01e010110101e01011018888,0x01e01012011004d012018888,0x0010100101001010010100101001010010100101aaaa,0x011010110100601002010220102a010060100501aaaa,0x01b0110046017010050110045100420170100b01aaaa,0x001010030100101e000,0x001010010100101e000,0x01b0110056012010050110055100530120100801aaaa,0x01b011005b01e01004011005a1005801b0101e01aaaa]⟩
def n69 : Entry := ⟨8, [323,370], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01b01017011001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x019011000,0x017011000,0x0000,0x0000,0x005011000]⟩
def n70 : Entry := ⟨8, [323,882], 383, [0x0000,0x00103001032020,0x0170101e012020,0x0000,0x0000,0x00103001030440,0x0000,0x0000,0x0170101b010440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e01017014004,0x0010301e010440,0x0000,0x0000,0x001030010100103001012222,0x011010050101101005012222,0x01b01017010060,0x001030010100103001012222,0x0010100b0100101001032222,0x001030010100501001012222,0x0190100c0101e0100c012222]⟩
def n71 : Entry := ⟨8, [323,355], 503, [0x0000,0x0000,0x01e0101e012020,0x00101001012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e01100480440,0x00101001012020,0x0000,0x0000,0x0000,0x01e011004a2020,0x00101001012020,0x0110301e012020,0x01e0101e012020,0x00101001016000,0x00503008030202,0x019010040101b01004014206,0x0000,0x01e0101e012020,0x01e0101e012020,0x01a010030101c01003014206,0x0000,0x00101001016000,0x00401003010040100301003014207]⟩
def n72 : Entry := ⟨7, [323,355,340], 999, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100490010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010001,0x0000]⟩
def n73 : Entry := ⟨6, [323,355,340,357], 1927, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001090001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n74 : Entry := ⟨7, [323,355,357], 951, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100490010,0x0000,0x0000,0x0000,0x0000,0x008030001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n75 : Entry := ⟨8, [323,340], 495, [0x0000,0x0000,0x01201012012020,0x0000,0x00103012012020,0x00103017012020,0x0000,0x01201012012020,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x00103100480440,0x012011004c0440,0x00103001032020,0x01101012012020,0x0000,0x00303001036000,0x013010050101201005014206,0x0000,0x00103001032020,0x0000,0x0000,0x015010010100103001014206,0x00502005026000,0x0000,0x00501001010010300101001014207]⟩
def n76 : Entry := ⟨7, [323,340,357], 975, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100490010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001050001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n77 : Entry := ⟨8, [323,357], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1004c0010,0x0000,0x0000,0x0000,0x1004a0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1004e008011001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601013011004f01b011111]⟩
def n78 : Entry := ⟨7, [323,357,885], 863, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x004010100]⟩
def n79 : Entry := ⟨7, [323,357,391], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10050001011001,0x10051002011001,0x10052001011001,0x0000,0x0000,0x0000,0x0000]⟩
def n80 : Entry := ⟨6, [323,357,391,912], 1150, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n81 : Entry := ⟨6, [323,357,391,913], 1149, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n82 : Entry := ⟨6, [323,357,391,914], 1147, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n83 : Entry := ⟨8, [323,373], 383, [0x0000,0x0000,0x01201012012020,0x0000,0x00103012012020,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030010100103001012222,0x012010020101201002012222,0x017010010100103001012222,0x01501001036000,0x01201012016000,0x01301012016000,0x10054004011004f004012222]⟩
def n84 : Entry := ⟨7, [323,373,902], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n85 : Entry := ⟨8, [323,373], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01301012011001,0x0000,0x0000,0x0000,0x0000,0x015011000,0x012011000,0x0000,0x0000,0x005011000]⟩
def n86 : Entry := ⟨8, [323,885], 383, [0x0000,0x0000,0x01201012012020,0x0000,0x00103012012020,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x01201013012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x012011004e0440,0x001030010100103001012222,0x00b010050100b01005012222,0x001030010100501001012222,0x001030010100103001012222,0x001010050100101001032222,0x01301012010060,0x01301016011005700a012222]⟩
def n87 : Entry := ⟨7, [323,885,390], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n88 : Entry := ⟨8, [323,374], 383, [0x0000,0x0000,0x01e0101e012020,0x0000,0x0010301e012020,0x0010301e012020,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030010100103001012222,0x01e010020101e01002012222,0x0250101e01025010050101e0101e0100501005017227,0x01901001036000,0x01a0101a016000,0x10059005011004f005012222,0x01901019016000]⟩
def n89 : Entry := ⟨7, [323,374,901], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n90 : Entry := ⟨8, [323,374], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0190101b011001,0x0000,0x0000,0x02501017011001,0x019011000,0x01a011000,0x0000,0x0000,0x004011000]⟩
def n91 : Entry := ⟨8, [323,886], 383, [0x0000,0x0000,0x0190101e012020,0x0000,0x0010301e012020,0x00103019012020,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x01901019012020,0x0000,0x001030010100103001012222,0x011010050101101005012222,0x0190100b010190100b012222,0x001030010100103001012222,0x001010110100101001032222,0x01301008011005c008012222,0x0190101e010060]⟩
def n92 : Entry := ⟨7, [323,886,389], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010001,0x0000,0x0000,0x0000]⟩
def n93 : Entry := ⟨9, [339], 255, [0x001010010100101001018888,0x001010010100101001018888,0x012010120101201012010120101201a8a8,0x001010010100101001010010100101a8a8,0x001010010100101001010120100101a8a8,0x001010010100101001018888,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x001010010100101001018888,0x001010010100101001010010100101a8a8,0x008010120101201008018888,0x001010010100101001018888,0x00101008010010100101001010010100101ca0e,0x008010120101201008018888,0x001010010100101001018888,0x012010120101201012018888,0x017010170101701017018888,0x001010010100101001018888,0x0300202b021005e02b028888,0x012010080101201008018888,0x0010100101001010010100101001010010100101aaaa,0x00d0100d0100d010020101201012010120100501aaaa,0x0010100101001010010100101001010010100101aaaa,0x001010080100101e000,0x0120101201012010030101201100530120101101aaaa,0x001010010100101e000,0x0120101201012010040101201100600120101201aaaa]⟩
def n94 : Entry := ⟨8, [339,356], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1005f017011001,0x0000,0x0000,0x0000,0x0000,0x01901012011004f012011111]⟩
def n95 : Entry := ⟨7, [339,356,898], 763, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n96 : Entry := ⟨8, [339,374], 383, [0x0000,0x0000,0x01201012012020,0x00103001032020,0x00103012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x008030010300103001034206,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x10062001031006100101001030010300101001017227,0x012010020101201002012222,0x017010010100103001012222,0x01601001036000,0x10063003011004f003012222,0x01401012016000,0x01201012016000]⟩
def n97 : Entry := ⟨7, [339,374,896], 638, [0x01201012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n98 : Entry := ⟨7, [339,374,896], 894, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001010100]⟩
def n99 : Entry := ⟨7, [339,374,900], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n100 : Entry := ⟨9, [355], 255, [0x001010010100101001018888,0x001010010100101001018888,0x00c0102a010120101e0102a0100c01a8a8,0x001010010100101001010010100101a8a8,0x0010100101001010010102a0100101a8a8,0x001010010100101001010300100101a8a8,0x001010010100101001018888,0x01e010120101e01012018888,0x01e0100c0101e0100c018888,0x0010100101001010010110047001018cc8,0x001010010100101001018888,0x012010120101201012018888,0x001010010100101001018888,0x0010102c0200101001010010100101c88c,0x0120101e0110065012018888,0x001010010100101001010010100101a8a8,0x01c010120101e01012018888,0x01c0100c0101e0100c018888,0x00101004010010100101001010010100101ca0e,0x01c0101e0101e0101c018888,0x01c010300101201030011006b01201a8a8,0x0010100101001010010100101001010010100101aaaa,0x01c0102a01012010020102a0102a010120100501aaaa,0x01c010300100c0100501030010300100c0100b01aaaa,0x001010040100101e000,0x01c011006901e0100301100681005801c0101101aaaa,0x01c011006e01201008011006c100600120100801aaaa,0x001010010100101e000]⟩
def n101 : Entry := ⟨8, [355,340], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100480010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100670010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10066001011001,0x0000,0x0000,0x0000,0x01501014011004f01c011111]⟩
def n102 : Entry := ⟨7, [355,340,899], 759, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x004010100]⟩
def n103 : Entry := ⟨7, [355,340,357], 927, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100490010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001050001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n104 : Entry := ⟨8, [355,372], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a0101c011001,0x0000,0x0000,0x0000,0x0000,0x0250100c011001,0x019011000,0x0000,0x0000,0x019011000,0x003011000]⟩
def n105 : Entry := ⟨8, [355,884], 383, [0x0000,0x0000,0x01a0101e012020,0x0000,0x0010301e012020,0x0010301a012020,0x0000,0x0000,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a0101a010440,0x0000,0x001030010100103001012222,0x01a010050101e01005012222,0x01a0100b0101a0100b012222,0x001030010100103001012222,0x01a0101e010060,0x01401005011006a005012222,0x001010110100101001032222]⟩
def n106 : Entry := ⟨7, [355,884,389], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n107 : Entry := ⟨8, [355,357], 447, [0x0000,0x0000,0x01201012012020,0x00103001032020,0x00103012012020,0x00103017012020,0x0000,0x0000,0x0000,0x001031004a0440,0x00103001032020,0x01201012012020,0x00103001032020,0x00802001030010300103001034207,0x01201100672020,0x00103001032020,0x01201012012020,0x0000,0x00403001036000,0x0000,0x014010080101201008014206,0x00103001032020,0x0000,0x0000,0x016010010100103001014206,0x0000,0x01401012016000,0x00801001010010300101001014207]⟩
def n108 : Entry := ⟨8, [355,373], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001030001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01401012011001,0x0000,0x1006d001011001,0x0000,0x0000,0x016011000,0x0000,0x0000,0x012011000,0x008011000]⟩
def n109 : Entry := ⟨7, [355,373,896], 766, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n110 : Entry := ⟨8, [355,885], 383, [0x0000,0x0000,0x01201012012020,0x00103001032020,0x00103012012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x008020010300103001036024,0x0000,0x00103001032020,0x0000,0x0000,0x0000,0x0000,0x01201014010440,0x001030010100103001012222,0x00e010050101201005012222,0x001030010101701001012222,0x001030010300101014010010300401001012672,0x01401005011006f005012222,0x01401012010060,0x001010080100101001032222]⟩
def n111 : Entry := ⟨7, [355,885,388], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n112 : Entry := ⟨9, [340], 255, [0x005010010201201001028888,0x00b010010201701001028888,0x00b0102b010050101e0102b0100501a8a8,0x001020010200102001028888,0x001020050101201001028888,0x001020050101701001028888,0x0110102b010010202b011000d00102a8a8,0x0110102b010050101e0102b0100501a8a8,0x0110100b0101e0100b018888,0x0110102b010010202b011004b00102a8a8,0x008010010201201001028888,0x0080102b01005010120102b0100501a8a8,0x0010200102001020170102f0100801a8a8,0x008010010201201001028888,0x00501005010050100501008010080101101ca0e,0x01e010010210031001028888,0x01e010050101e01005018888,0x01e0100b0101e0100b018888,0x01e010010210065001028888,0x01e010110101e01011018888,0x01e010080102c0102c0110078008018cc8,0x0240110072001020010110071100180010200101aaaa,0x0240102b0100501005010240102b010050100501aaaa,0x0110101101001020010102f0102f0100b0100101aaaa,0x0240110076001020010110075100530010200101aaaa,0x005010050100501e000,0x005010050100501e000,0x024011008001e0101e011007e1007901e0101e01aaaa]⟩
def n113 : Entry := ⟨8, [340,368], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x02301001021001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01501001021001,0x012011000,0x013011000,0x0000,0x001011000]⟩
def n114 : Entry := ⟨8, [340,880], 383, [0x0000,0x0000,0x01201012012020,0x0000,0x0000,0x0000,0x00102023010440,0x0000,0x0000,0x00102001022020,0x00102012010440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01201100730440,0x02301001020060,0x012010050101201005012222,0x010010010100102001012222,0x001020010100102001012222,0x005010010100102001012222,0x005010010100102001012222,0x01f01014011007401a012222]⟩
def n115 : Entry := ⟨7, [340,880,357], 863, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n116 : Entry := ⟨7, [340,880,390], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n117 : Entry := ⟨8, [340,371], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01501001021001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x012011000,0x013011000,0x0000,0x001011000]⟩
def n118 : Entry := ⟨8, [340,883], 383, [0x0000,0x0000,0x01201012012020,0x00102001020202,0x0000,0x0000,0x00102001022020,0x0000,0x0000,0x00102015010440,0x0000,0x0000,0x0000,0x00102012010440,0x0000,0x0000,0x0000,0x0000,0x00102100660440,0x0000,0x0000,0x001020010100102001012222,0x012010020101201002012222,0x003010010100102001012222,0x01501001020060,0x005010010100102001012222,0x003010010100102001012222,0x015010040110077004012222]⟩
def n119 : Entry := ⟨7, [340,883,390], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n120 : Entry := ⟨8, [340,357], 479, [0x0000,0x0000,0x01e0101e012020,0x0000,0x0000,0x0000,0x01e011000e2020,0x01e0101e012020,0x0000,0x01e011004c2020,0x01e01100322020,0x01e0101e012020,0x0000,0x01e01100672020,0x0000,0x10073100132020,0x01e0101e012020,0x0110301e012020,0x00103001030202,0x00503005036000,0x01f0100a0101e0101a014206,0x0000,0x01e0101e012020,0x01e0101e012020,0x0000,0x020010050101e01005014206,0x00801008016000,0x00a010050101e0100501005014207]⟩
def n121 : Entry := ⟨8, [340,374], 383, [0x0000,0x0000,0x01e0101e012020,0x0000,0x0000,0x0000,0x01e011000f2020,0x01e0101e012020,0x0000,0x0000,0x0000,0x01e0101e012020,0x0010401e012020,0x0000,0x0000,0x0000,0x01e0101e012020,0x0000,0x0000,0x0000,0x0000,0x1007a0010110014001012222,0x1007c01e011007b0050101e0101e0100501005017227,0x0260101e01026010010101e0101e0100101001017227,0x1007d001011004f001012222,0x0200101e016000,0x01e0101e016000,0x01f0101e016000]⟩
def n122 : Entry := ⟨7, [340,374,896], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n123 : Entry := ⟨7, [340,374,897], 637, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0260101e014004,0x0000,0x0000,0x0000,0x0000]⟩
def n124 : Entry := ⟨7, [340,374,897], 893, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0260101e011001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x005010100]⟩
def n125 : Entry := ⟨7, [340,374,899], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n126 : Entry := ⟨8, [340,374], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01f0101e011001,0x0000,0x1007f005011001,0x02601001021001,0x0000,0x020011000,0x01e011000,0x0000,0x00a011000]⟩
def n127 : Entry := ⟨7, [340,374,897], 765, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n128 : Entry := ⟨8, [340,886], 383, [0x0000,0x0000,0x01e0101e012020,0x0000,0x0000,0x0000,0x01e01100102020,0x01e0101e012020,0x0000,0x0000,0x0000,0x01e0101e012020,0x0010401e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e0101e012020,0x01e0101f012020,0x01f010010110081001012222,0x01e010050101e01005012222,0x0110100b010110100b012222,0x015010010110082001012222,0x005010110100501011012222,0x005010080100501008012222,0x01f0101e010060]⟩
def n129 : Entry := ⟨7, [340,886,384], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n130 : Entry := ⟨7, [340,886,387], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x004010001,0x0000]⟩
def n131 : Entry := ⟨9, [356], 255, [0x01e010010201e01001028888,0x01e010010201e01001028888,0x01e0101e0101e0101e0101e0101e01a8a8,0x001020010200102001028888,0x001020110101e01001028888,0x0010201e0101e01001028888,0x0110101e010010201e011001100102a8a8,0x0110101e0101e0101e0101e0101101a8a8,0x0110101e0101e0101e0101e0101101a8a8,0x011010010201e01001028888,0x02c020010210026001028888,0x01e0101e0101e0101e018888,0x001020010201e0101e018888,0x02c02001021005e001028888,0x01e010110101e01011018888,0x01e010010201e01001028888,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e010010201e01001028888,0x01e0101e0101101011010110101e0101101ca0e,0x01e0101e0101e0101e018888,0x01e0101e01001020010101e011001d0010200101aaaa,0x01e0101e0101e010050101e0101e0101e0100501aaaa,0x01e0101e0101e011008401e0100b0101e0101e0101e0101e0100b0102701faaf,0x01e0101e01001020010101e01100580010200101aaaa,0x01e0101e0101e01e000,0x01e0101e0101e010050101e011007901e0100801aaaa,0x011010110101101e000]⟩
def n132 : Entry := ⟨8, [356,882], 379, [0x01e010010401e01001048888,0x001040010400104001048888,0x001040110301e01001048888,0x011030010401e01001048888,0x0110301e0101e01011038888,0x011030010401e01001048888,0x02c040010410027001048888,0x01e0101e0101e0101e018888,0x02c04001041005f001048888,0x01e010110301e01011038888,0x01e010010401e01001048888,0x01e0101e0101e0101e018888,0x01e010010401e01001048888,0x01e010110301e01011038888,0x01e0101e0101e0101e018888,0x01e010010401e01001048888,0x01e0101e0101e0101e0101e0101e01a8a8,0x01e010010401e01001048888,0x01e010110301e01011038888,0x01e0101e0101e01001048888,0x0110301e0101e0101e018888]⟩
def n133 : Entry := ⟨9, [357], 255, [0x008010010201201001028888,0x00d010010201701001028888,0x0170102c010120101e0102c0101201a8a8,0x001020010200102001028888,0x0010200d0101201001028888,0x001020080101701001028888,0x01e010010210012001028888,0x01e010120101e01012018888,0x01e010170101e01017018888,0x01e01001021004d001028888,0x0080102c0100102012011002800102a8a8,0x0080102c01012010120102c0100801a8a8,0x0010200102001020170102f0100801a8a8,0x0080100102001020120100102001028a8a,0x0080102c0101e0102c011007800801a8a8,0x01e010300100102030011003600102a8a8,0x01e0102c010120101e0102c0101201a8a8,0x01e010170101e01017018888,0x01e010300100102030011006b00102a8a8,0x01e0101e0101e0101e018888,0x01e0101e0100801008010080101e0100801ca0e,0x1008a100870010200101100861002a0010200101aaaa,0x02c0102c01012010050102c0102c010120100501aaaa,0x02f0102f01001020010102f0102f010170100101aaaa,0x1008f1008d00102001011008b100600010200101aaaa,0x100951009201e0100501100901007901e0101101aaaa,0x01e0101e0101e01e000,0x008010080100801e000]⟩
def n134 : Entry := ⟨8, [357,368], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1002b001021001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601001021001,0x0000,0x014011000,0x012011000,0x001011000]⟩
def n135 : Entry := ⟨8, [357,880], 383, [0x0000,0x0000,0x01201012012020,0x00102001024004,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00102012010440,0x0000,0x0000,0x0000,0x0000,0x00102030030440,0x0000,0x0000,0x00102001022020,0x0000,0x0000,0x1002b001020060,0x012010050101201005012222,0x017010010100102001012222,0x001020010100102001012222,0x0200100c011008800c012222,0x00a010010100102001012222,0x008010010100102001012222]⟩
def n136 : Entry := ⟨7, [357,880,388], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10089005011001,0x02601001011001,0x0000,0x0000,0x0000,0x0000]⟩
def n137 : Entry := ⟨6, [357,880,388,913], 1149, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n138 : Entry := ⟨8, [357,880], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x100290010,0x0000,0x0000,0x0000,0x0000,0x100370010,0x0000,0x0000,0x0000,0x0000,0x0000,0x001021002b0110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00a01001021001,0x00801001021001,0x001010100]⟩
def n139 : Entry := ⟨8, [357,371], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001020001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01601001021001,0x0000,0x0000,0x0000,0x1008c001021001,0x0000,0x0000,0x0000,0x0000,0x014011000,0x012011000,0x001011000]⟩
def n140 : Entry := ⟨7, [357,371,896], 766, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n141 : Entry := ⟨8, [357,883], 383, [0x0000,0x0000,0x01201012012020,0x00102001020202,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00102001022020,0x0000,0x0000,0x001020010201201001020642,0x0000,0x00102001022020,0x0000,0x0000,0x00102016010440,0x0000,0x0000,0x001020010100102001012222,0x012010020101201002012222,0x004010010100102001012222,0x01601001020060,0x01601003011008e003012222,0x004010010200101001020010200102001012672,0x008010010100102001012222]⟩
def n142 : Entry := ⟨7, [357,883,388], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n143 : Entry := ⟨8, [357,883], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x001020100,0x0000,0x0000,0x0000,0x0000,0x016010010,0x0000,0x0000,0x0000,0x0000,0x0000,0x00102016010110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00102001020110,0x00801001021001,0x001010100]⟩
def n144 : Entry := ⟨8, [357,372], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0200101e011001,0x0000,0x0000,0x0000,0x10091012011001,0x02601001021001,0x0000,0x0000,0x01e011000,0x01f011000,0x005011000]⟩
def n145 : Entry := ⟨7, [357,372,897], 765, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n146 : Entry := ⟨8, [357,884], 383, [0x0000,0x0000,0x01e0101e012020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e0101e012020,0x0010401e012020,0x0000,0x01e01020010440,0x0000,0x01e0101e012020,0x0000,0x0000,0x01e0101e010440,0x0000,0x020010010110093001012222,0x01e010050101e01005012222,0x01c0100b0101e0100b012222,0x016010010110094001012222,0x0200101e010060,0x00a010050101e01005012222,0x005010110100501011012222]⟩
def n147 : Entry := ⟨7, [357,884,384], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n148 : Entry := ⟨7, [357,884,387], 639, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n149 : Entry := ⟨8, [357,884], 511, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x020010010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01e01020010110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00a01005021001,0x0000,0x005010100]⟩
def nodes : Array Entry := #[n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13,n14,n15,n16,n17,n18,n19,n20,n21,n22,n23,n24,n25,n26,n27,n28,n29,n30,n31,n32,n33,n34,n35,n36,n37,n38,n39,n40,n41,n42,n43,n44,n45,n46,n47,n48,n49,n50,n51,n52,n53,n54,n55,n56,n57,n58,n59,n60,n61,n62,n63,n64,n65,n66,n67,n68,n69,n70,n71,n72,n73,n74,n75,n76,n77,n78,n79,n80,n81,n82,n83,n84,n85,n86,n87,n88,n89,n90,n91,n92,n93,n94,n95,n96,n97,n98,n99,n100,n101,n102,n103,n104,n105,n106,n107,n108,n109,n110,n111,n112,n113,n114,n115,n116,n117,n118,n119,n120,n121,n122,n123,n124,n125,n126,n127,n128,n129,n130,n131,n132,n133,n134,n135,n136,n137,n138,n139,n140,n141,n142,n143,n144,n145,n146,n147,n148,n149]
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.GraphTarget PEqualNP.Outside.L_meta_11763_aux.Boost PEqualNP.Outside.L_meta_11763_aux.GraphSymmetry

theorem verifiedCut {cap cs ch code} (validSlice : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (nd : ch.Nodup) (ok : verifyCut cap cs ch code = true) : Impossible true full cap ch.toFinset := by
  let m := (code-1) / 256
  let witness := selectMask ((code-1) % 256) cs
  unfold verifyCut at ok
  simp only [Bool.and_eq_true,List.contains_iff_mem] at ok
  obtain ⟨hm,h⟩ := ok
  change (match makePool true (cliqueDomain m) cols7 witness with
    | none => false
    | some pool => poolCut true (cliqueDomain m) (cliqueBound m) cap witness.length pool ch) = true at h
  cases hp : makePool true (cliqueDomain m) cols7 witness with
  | none => rw [hp] at h; contradiction
  | some pool =>
    apply poolCut_sound (validSlice m hm) witness hp nd
    rw [hp] at h
    exact h

theorem verifiedIso {db cap ch code} (ok : verifyIso db cap ch code = true)
    (prev : ∀ j, j < db.size →
      (db[j]?.getD default).cap = cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full cap ch.toFinset := by
  let j := (code-65536)/1
  let p : Fin 1 := Fin.ofNat 1 ((code-65536) % 1)
  let dest := db[j]?.getD default
  simp only [verifyIso,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨hj,hcap⟩,eq⟩ := ok
  apply isoTransferOf p ch (stateOf dest) cap eq
  exact hcap ▸ prev j hj hcap

set_option maxRecDepth 8192 in
theorem nodeSound {db e}
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (ok : verify db e = true)
    (prev : ∀ j, j < db.size → (db[j]?.getD default).cap < e.cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full e.cap (stateOf e).toFinset := by
  let ws := stateOf e
  let cs := choicesOf e
  by_cases zeroCap : e.cap = 0
  · have missing : full ∉ ws := by simpa [verify,zeroCap,ws] using ok
    intro k hk run
    have ez : k = 0 := by omega
    subst k
    have singleton : ws.toFinset = {full} := run.1
    exact missing (List.mem_toFinset.mp (singleton.symm ▸ Finset.mem_singleton_self _))
  simp only [verify,zeroCap,ite_false,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
  obtain ⟨⟨⟨pos,nd⟩,notout⟩,all⟩ := ok
  apply enumStepOrdered nd (by simpa using notout)
  intro a ha b hb d hd ka kb lt fresh prop len
  have reverse : ¬b.toNat ≤ a.toNat := Nat.not_le.mpr lt
  have ne : a ≠ b := fun eq => (Nat.lt_irrefl _) (eq ▸ lt)
  have op : d ∈ [0,1,2,3] := by rcases allowed_four hd with h|h|h|h <;> simp_all
  have ka' : ka ∈ [false,true] := by cases ka <;> simp
  have kb' : kb ∈ [false,true] := by cases kb <;> simp
  have chk := all a ha b hb d op ka ka' kb kb'
  have nz := prop.1
  have no := prop.2
  simp only [verifyChild,beq_iff_eq,List.contains_iff_mem,Bool.or_eq_true,decide_eq_true_eq,
    reverse,ne,fresh,nz,no,Nat.not_lt.mpr len,or_self,ite_false] at chk
  split at chk
  next bad => exact indistSound bad _
  next =>
    split at chk
    next => contradiction
    next =>
      split at chk
      next =>
        have dec : e.cap-1 < e.cap := by omega
        exact verifiedIso chk (fun j hj heq => prev j hj (heq.trans_lt dec))
      next =>
        apply verifiedCut slices _ chk
        unfold childTwo kept
        have nodup := nd
        have rn : ((ws.erase a).erase b).Nodup := (nodup.erase a).erase b
        have notA : a ∉ (ws.erase a).erase b := fun h => ((nodup.mem_erase_iff).mp (List.mem_of_mem_erase h)).1 rfl
        have notB : b ∉ (ws.erase a).erase b := fun h => (((nodup.erase a).mem_erase_iff).mp h).1 rfl
        have old : ∀ x ∈ (ws.erase a).erase b, x ∈ ws := fun _ h => List.mem_of_mem_erase (List.mem_of_mem_erase h)
        have ya : bin d a b ≠ a := by intro eq; apply fresh; rw [eq]; exact ha
        have yb : bin d a b ≠ b := by intro eq; apply fresh; rw [eq]; exact hb
        have yr : bin d a b ∉ (ws.erase a).erase b := fun h => fresh (old _ h)
        change (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))).Nodup
        cases ka <;> cases kb <;> simp [kept,ya,yb,yr,notA,notB,rn,ne]


theorem forestSound (db : Array Entry)
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (good : ∀ j, j < db.size → verify db (db[j]?.getD default) = true)
    (j : Nat) (hj : j < db.size) :
    Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset := by
  suffices ∀ k i, i < db.size → (db[i]?.getD default).cap = k →
      Impossible true full (db[i]?.getD default).cap (stateOf (db[i]?.getD default)).toFinset from this _ j hj rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hi hc
    apply nodeSound slices (good i hi)
    intro j hj lt
    exact ih _ (hc ▸ lt) j hj rfl
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok0 : verify nodes n0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok8 : verify nodes n8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok16 : verify nodes n16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok24 : verify nodes n24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok32 : verify nodes n32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok40 : verify nodes n40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok48 : verify nodes n48 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok56 : verify nodes n56 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok64 : verify nodes n64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok72 : verify nodes n72 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok80 : verify nodes n80 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok88 : verify nodes n88 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok96 : verify nodes n96 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok104 : verify nodes n104 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok112 : verify nodes n112 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok120 : verify nodes n120 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok128 : verify nodes n128 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok136 : verify nodes n136 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok144 : verify nodes n144 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok1 : verify nodes n1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok9 : verify nodes n9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok17 : verify nodes n17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok25 : verify nodes n25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok33 : verify nodes n33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok41 : verify nodes n41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok49 : verify nodes n49 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok57 : verify nodes n57 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok65 : verify nodes n65 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok73 : verify nodes n73 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok81 : verify nodes n81 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok89 : verify nodes n89 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok97 : verify nodes n97 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok105 : verify nodes n105 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok113 : verify nodes n113 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok121 : verify nodes n121 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok129 : verify nodes n129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok137 : verify nodes n137 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok145 : verify nodes n145 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok2 : verify nodes n2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok10 : verify nodes n10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok18 : verify nodes n18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok26 : verify nodes n26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok34 : verify nodes n34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok42 : verify nodes n42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok50 : verify nodes n50 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok58 : verify nodes n58 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok66 : verify nodes n66 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok74 : verify nodes n74 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok82 : verify nodes n82 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok90 : verify nodes n90 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok98 : verify nodes n98 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok106 : verify nodes n106 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok114 : verify nodes n114 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok122 : verify nodes n122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok130 : verify nodes n130 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok138 : verify nodes n138 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok146 : verify nodes n146 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok3 : verify nodes n3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok11 : verify nodes n11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok19 : verify nodes n19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok27 : verify nodes n27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok35 : verify nodes n35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok43 : verify nodes n43 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok51 : verify nodes n51 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok59 : verify nodes n59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok67 : verify nodes n67 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok75 : verify nodes n75 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok83 : verify nodes n83 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok91 : verify nodes n91 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok99 : verify nodes n99 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok107 : verify nodes n107 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok115 : verify nodes n115 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok123 : verify nodes n123 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok131 : verify nodes n131 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok139 : verify nodes n139 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok147 : verify nodes n147 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok4 : verify nodes n4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok12 : verify nodes n12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok20 : verify nodes n20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok28 : verify nodes n28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok36 : verify nodes n36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok44 : verify nodes n44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok52 : verify nodes n52 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok60 : verify nodes n60 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok68 : verify nodes n68 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok76 : verify nodes n76 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok84 : verify nodes n84 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok92 : verify nodes n92 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok100 : verify nodes n100 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok108 : verify nodes n108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok116 : verify nodes n116 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok124 : verify nodes n124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok132 : verify nodes n132 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok140 : verify nodes n140 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok148 : verify nodes n148 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok5 : verify nodes n5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok13 : verify nodes n13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok21 : verify nodes n21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok29 : verify nodes n29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok37 : verify nodes n37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok45 : verify nodes n45 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok53 : verify nodes n53 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok61 : verify nodes n61 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok69 : verify nodes n69 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok77 : verify nodes n77 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok85 : verify nodes n85 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok93 : verify nodes n93 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok101 : verify nodes n101 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok109 : verify nodes n109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok117 : verify nodes n117 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok125 : verify nodes n125 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok133 : verify nodes n133 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok141 : verify nodes n141 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok149 : verify nodes n149 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok6 : verify nodes n6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok14 : verify nodes n14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok22 : verify nodes n22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok30 : verify nodes n30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok38 : verify nodes n38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok46 : verify nodes n46 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok54 : verify nodes n54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok62 : verify nodes n62 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok70 : verify nodes n70 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok78 : verify nodes n78 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok86 : verify nodes n86 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok94 : verify nodes n94 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok102 : verify nodes n102 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok110 : verify nodes n110 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok118 : verify nodes n118 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok126 : verify nodes n126 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok134 : verify nodes n134 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok142 : verify nodes n142 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok7 : verify nodes n7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok15 : verify nodes n15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok23 : verify nodes n23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok31 : verify nodes n31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok39 : verify nodes n39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok47 : verify nodes n47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok55 : verify nodes n55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok63 : verify nodes n63 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok71 : verify nodes n71 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok79 : verify nodes n79 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok87 : verify nodes n87 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok95 : verify nodes n95 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok103 : verify nodes n103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok111 : verify nodes n111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok119 : verify nodes n119 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok127 : verify nodes n127 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok135 : verify nodes n135 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok143 : verify nodes n143 = true := by decide +kernel
end PEqualNP.Outside.L_meta_11763_aux.Certificate

namespace PEqualNP.Outside.L_meta_11763_aux.Certificate
open PEqualNP.Outside.L_meta_11763_aux.LiveCircuits PEqualNP.Outside.L_meta_11763_aux.GraphTarget
set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem allChecks : ∀ j : Nat, j < nodes.size → verify nodes (nodes[j]?.getD default) = true
  | 0, _ => ok0
  | 1, _ => ok1
  | 2, _ => ok2
  | 3, _ => ok3
  | 4, _ => ok4
  | 5, _ => ok5
  | 6, _ => ok6
  | 7, _ => ok7
  | 8, _ => ok8
  | 9, _ => ok9
  | 10, _ => ok10
  | 11, _ => ok11
  | 12, _ => ok12
  | 13, _ => ok13
  | 14, _ => ok14
  | 15, _ => ok15
  | 16, _ => ok16
  | 17, _ => ok17
  | 18, _ => ok18
  | 19, _ => ok19
  | 20, _ => ok20
  | 21, _ => ok21
  | 22, _ => ok22
  | 23, _ => ok23
  | 24, _ => ok24
  | 25, _ => ok25
  | 26, _ => ok26
  | 27, _ => ok27
  | 28, _ => ok28
  | 29, _ => ok29
  | 30, _ => ok30
  | 31, _ => ok31
  | 32, _ => ok32
  | 33, _ => ok33
  | 34, _ => ok34
  | 35, _ => ok35
  | 36, _ => ok36
  | 37, _ => ok37
  | 38, _ => ok38
  | 39, _ => ok39
  | 40, _ => ok40
  | 41, _ => ok41
  | 42, _ => ok42
  | 43, _ => ok43
  | 44, _ => ok44
  | 45, _ => ok45
  | 46, _ => ok46
  | 47, _ => ok47
  | 48, _ => ok48
  | 49, _ => ok49
  | 50, _ => ok50
  | 51, _ => ok51
  | 52, _ => ok52
  | 53, _ => ok53
  | 54, _ => ok54
  | 55, _ => ok55
  | 56, _ => ok56
  | 57, _ => ok57
  | 58, _ => ok58
  | 59, _ => ok59
  | 60, _ => ok60
  | 61, _ => ok61
  | 62, _ => ok62
  | 63, _ => ok63
  | 64, _ => ok64
  | 65, _ => ok65
  | 66, _ => ok66
  | 67, _ => ok67
  | 68, _ => ok68
  | 69, _ => ok69
  | 70, _ => ok70
  | 71, _ => ok71
  | 72, _ => ok72
  | 73, _ => ok73
  | 74, _ => ok74
  | 75, _ => ok75
  | 76, _ => ok76
  | 77, _ => ok77
  | 78, _ => ok78
  | 79, _ => ok79
  | 80, _ => ok80
  | 81, _ => ok81
  | 82, _ => ok82
  | 83, _ => ok83
  | 84, _ => ok84
  | 85, _ => ok85
  | 86, _ => ok86
  | 87, _ => ok87
  | 88, _ => ok88
  | 89, _ => ok89
  | 90, _ => ok90
  | 91, _ => ok91
  | 92, _ => ok92
  | 93, _ => ok93
  | 94, _ => ok94
  | 95, _ => ok95
  | 96, _ => ok96
  | 97, _ => ok97
  | 98, _ => ok98
  | 99, _ => ok99
  | 100, _ => ok100
  | 101, _ => ok101
  | 102, _ => ok102
  | 103, _ => ok103
  | 104, _ => ok104
  | 105, _ => ok105
  | 106, _ => ok106
  | 107, _ => ok107
  | 108, _ => ok108
  | 109, _ => ok109
  | 110, _ => ok110
  | 111, _ => ok111
  | 112, _ => ok112
  | 113, _ => ok113
  | 114, _ => ok114
  | 115, _ => ok115
  | 116, _ => ok116
  | 117, _ => ok117
  | 118, _ => ok118
  | 119, _ => ok119
  | 120, _ => ok120
  | 121, _ => ok121
  | 122, _ => ok122
  | 123, _ => ok123
  | 124, _ => ok124
  | 125, _ => ok125
  | 126, _ => ok126
  | 127, _ => ok127
  | 128, _ => ok128
  | 129, _ => ok129
  | 130, _ => ok130
  | 131, _ => ok131
  | 132, _ => ok132
  | 133, _ => ok133
  | 134, _ => ok134
  | 135, _ => ok135
  | 136, _ => ok136
  | 137, _ => ok137
  | 138, _ => ok138
  | 139, _ => ok139
  | 140, _ => ok140
  | 141, _ => ok141
  | 142, _ => ok142
  | 143, _ => ok143
  | 144, _ => ok144
  | 145, _ => ok145
  | 146, _ => ok146
  | 147, _ => ok147
  | 148, _ => ok148
  | 149, _ => ok149
  | j+150,h => by change j+150 < 150 at h; omega

set_option maxRecDepth 16384 in
theorem complete
    (h3 : Lower true (inputs.take 3) PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions.k3 4)
    (h4 : Lower true (inputs.take 4) PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions.k4 7)
    (h5 : Lower true (inputs.take 5) PEqualNP.Outside.L_meta_11763_aux.CliqueRestrictions.k5 9) : Lower true cols7 full 11 := by
  have impossible := forestSound nodes (PEqualNP.Outside.L_meta_11763_aux.Boost.validWithBounds h3 h4 h5) allChecks 0 (by decide +kernel)
  have home : stateOf n0 = cols7 := by decide +kernel
  change Impossible true full 10 (stateOf n0).toFinset at impossible
  rw [home] at impossible
  let xs : List (Sig × Row × Row) := [(cols7.getD 0 zero,8,9),(cols7.getD 1 zero,16,18),(cols7.getD 2 zero,16,20),(cols7.getD 3 zero,1,9),(cols7.getD 4 zero,2,18),(cols7.getD 5 zero,1,33),(cols7.getD 6 zero,1,65)]
  have er := essential_ok (T:=full) (raw:=cols7) (xs:=xs) (by decide +kernel)
  have eq : (xs.map Prod.fst).toFinset = cols7.toFinset := by decide +kernel
  rw [eq] at er
  exact lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun a h => er a (List.mem_toFinset.mpr h)) impossible
end PEqualNP.Outside.L_meta_11763_aux.Certificate

theorem PEqualNP.Outside.L_meta_11763 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_11763_aux.GraphTarget.finish (PEqualNP.Outside.L_meta_11763_aux.Certificate.complete PEqualNP.Outside.L_meta_11763_aux.TriangleBound.standardLower3 PEqualNP.Outside.L_meta_11763_aux.CliqueBounds.standardLower4 PEqualNP.Outside.L_meta_11763_aux.CliqueBounds.standardLower5)
