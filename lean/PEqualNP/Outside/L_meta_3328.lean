import Mathlib
import PEqualNP.Defs

-- A straight-line program over a base is kept as a chain of steps.
-- The proof prepends the first gate, appends the target, then drops repeats and base values.
namespace PEqualNP.Outside.L_meta_3328

def Step (B : List ℕ) (v : ℕ) : Prop := ∃ a ∈ B, ∃ b ∈ B, v = a &&& b ∨ v = a ||| b

def Chain (B L : List ℕ) : Prop := ∀ i : Fin L.length, Step (B ++ L.take i) (L.get i)

def Good (B : List ℕ) : List ℕ → Prop
  | [] => True
  | v :: L => Step B v ∧ Good (v :: B) L

def clean (B : List ℕ) : List ℕ → List ℕ
  | [] => []
  | v :: L => if v ∈ B then clean B L else v :: clean (v :: B) L

theorem step_mono {B B' : List ℕ} {v : ℕ} (h : ∀ a, a ∈ B → a ∈ B') (s : Step B v) : Step B' v := by
  obtain ⟨a, ha, b, hb, e⟩ := s
  exact ⟨a, h a ha, b, h b hb, e⟩

theorem good_mono {B B' : List ℕ} (L : List ℕ) (h : ∀ a, a ∈ B → a ∈ B') (s : Good B L) :
    Good B' L := by
  induction L generalizing B B' with
  | nil => trivial
  | cons v L ih =>
    refine ⟨step_mono h s.1, ih ?_ s.2⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h a ha)

theorem good_of_chain (B L : List ℕ) (c : Chain B L) : Good B L := by
  induction L generalizing B with
  | nil => trivial
  | cons v L ih =>
    refine ⟨?_, ih (v :: B) ?_⟩
    · have h0 := c ⟨0, Nat.succ_pos _⟩
      refine step_mono ?_ h0
      intro a ha
      simpa using ha
    · intro i
      have hi := c ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      refine step_mono ?_ hi
      intro a ha
      simp only [List.take_succ_cons, List.mem_append, List.mem_cons] at ha
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem chain_of_good (B L : List ℕ) (g : Good B L) : Chain B L := by
  induction L generalizing B with
  | nil => intro i; exact absurd i.isLt (Nat.not_lt_zero _)
  | cons v L ih =>
    intro i
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      refine step_mono ?_ g.1
      intro a ha
      simpa using ha
    | succ j =>
      have hj := ih (v :: B) g.2 ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      refine step_mono ?_ hj
      intro a ha
      simp only [List.mem_append, List.mem_cons] at ha
      simp only [List.take_succ_cons, List.mem_append, List.mem_cons]
      tauto

theorem good_snoc (B L : List ℕ) (t : ℕ) (g : Good B L) (s : Step (B ++ L) t) :
    Good B (L ++ [t]) := by
  induction L generalizing B with
  | nil =>
    refine ⟨step_mono ?_ s, trivial⟩
    intro a ha
    simpa using ha
  | cons v L ih =>
    refine ⟨g.1, ih (v :: B) g.2 (step_mono ?_ s)⟩
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    simp only [List.mem_append, List.mem_cons]
    tauto

theorem clean_length (B L : List ℕ) : (clean B L).length ≤ L.length := by
  induction L generalizing B with
  | nil => exact Nat.le_refl _
  | cons v L ih =>
    unfold clean
    split
    · exact Nat.le_succ_of_le (ih B)
    · exact Nat.succ_le_succ (ih (v :: B))

theorem clean_notin (B L : List ℕ) : ∀ w ∈ clean B L, w ∉ B := by
  induction L generalizing B with
  | nil => intro w hw; exact absurd hw List.not_mem_nil
  | cons v L ih =>
    intro w hw
    unfold clean at hw
    split at hw
    · exact ih B w hw
    · rename_i hv
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact fun hb => ih (v :: B) w hw (List.mem_cons_of_mem _ hb)

theorem clean_nodup (B L : List ℕ) : (clean B L).Nodup := by
  induction L generalizing B with
  | nil => exact List.nodup_nil
  | cons v L ih =>
    unfold clean
    split
    · exact ih B
    · refine List.nodup_cons.mpr ⟨?_, ih (v :: B)⟩
      exact fun hv => clean_notin (v :: B) L v hv List.mem_cons_self

theorem clean_mem (B L : List ℕ) (w : ℕ) (hw : w ∈ L) (hb : w ∉ B) : w ∈ clean B L := by
  induction L generalizing B with
  | nil => exact absurd hw List.not_mem_nil
  | cons v L ih =>
    unfold clean
    split
    · rename_i hv
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hv hb
      · exact ih B hw hb
    · by_cases e : w = v
      · subst e
        exact List.mem_cons_self
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd rfl e
        · refine List.mem_cons_of_mem _ (ih (v :: B) hw ?_)
          intro h
          rcases List.mem_cons.mp h with rfl | h
          · exact e rfl
          · exact hb h

theorem clean_good (B L : List ℕ) (g : Good B L) : Good B (clean B L) := by
  induction L generalizing B with
  | nil => trivial
  | cons v L ih =>
    unfold clean
    split
    · rename_i hv
      refine ih B (good_mono L ?_ g.2)
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hv
      · exact ha
    · exact ⟨g.1, ih (v :: B) g.2⟩

theorem main (B : List ℕ) (g t : ℕ) (L : List ℕ) (ht : t ∉ B) (hg : Step B g)
    (hL : Chain (g :: B) L) (hs : Step (g :: B ++ L) t) :
    ∃ L' : List ℕ, L'.length ≤ L.length + 2 ∧ L'.Nodup ∧ (∀ v ∈ L', v ∉ B) ∧ t ∈ L' ∧
      Chain B L' := by
  have good : Good B (g :: (L ++ [t])) :=
    ⟨hg, good_snoc (g :: B) L t (good_of_chain (g :: B) L hL) hs⟩
  refine ⟨clean B (g :: (L ++ [t])), ?_, clean_nodup _ _, clean_notin _ _, ?_, ?_⟩
  · refine Nat.le_trans (clean_length _ _) ?_
    simp
  · refine clean_mem _ _ t ?_ ht
    simp
  · exact chain_of_good _ _ (clean_good _ _ good)

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  exact PEqualNP.Outside.L_meta_3328.main
