import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax

inductive Game where
  | mk : List Game → List Game → Game

open Game

def Game.leftMoves (g : Game) : List Game :=
  match g with
  | mk left _ => left

def Game.rightMoves (g : Game) : List Game :=
  match g with
  | mk _ right => right

def zero : Game := mk [] []
def minus_one : Game := mk [] [zero]
def one : Game := mk [zero] []
def half : Game := mk [zero] [one]
def two : Game := mk [one] []


def Game.birthday (g : Game) : Nat :=
  match g with
  | mk L R =>
    let bL := L.map birthday
    let bR := R.map birthday
    (bL ++ bR).maximum.getD 0 + 1

#eval birthday zero
#eval birthday two -- 3
#eval birthday half -- 3

lemma list_maximum_is_none_then_is_empty
    (a : List ℕ) (h_eq : a.maximum = none) : a = [] := by
  cases a with
  | nil => rfl
  | cons hd tl =>
    have h_ne_none : (hd :: tl).maximum ≠ none := by
      apply List.maximum_ne_bot_of_ne_nil
      simp
    contradiction

lemma elt_leq_max (a : List ℕ) (s : ℕ) (h : s ∈ a) : s ≤ a.maximum.getD 0 := by
    match h_eq : a.maximum with
    | none =>
        have h_a_empty : a = [] := by
          apply list_maximum_is_none_then_is_empty a h_eq
        rw [h_a_empty] at h
        contradiction
    | some m =>
      simp only [h_eq, Option.getD_some]
      exact List.le_of_mem_argmax h h_eq


lemma birthday_lt_left (g : Game) (l : Game) (h : l ∈ g.leftMoves) :
    birthday l < birthday g := by
  cases g with
  | mk L R =>
    simp [leftMoves] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday l < b.maximum.getD 0 + 1
    have h_mem_b : l.birthday ∈ b := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      use l
    have aaa : l.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b l.birthday h_mem_b
    linarith

lemma birthday_lt_right (g : Game) (r : Game) (h : r ∈ g.rightMoves) :
    birthday r < birthday g := by
  cases g with
  | mk L R =>
    simp [rightMoves] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday r < b.maximum.getD 0 + 1
    have h_mem_b : r.birthday ∈ b := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      use r
    have aaa : r.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b r.birthday h_mem_b
    linarith

def Game.le (g h : Game) : Prop :=
    (∀ g_l ∈ g.leftMoves, ¬(le h g_l)) ∧ (∀ h_r ∈ h.rightMoves, ¬(le h_r g))
termination_by (birthday g + birthday h)
decreasing_by
  -- Prove termination for the first recursive call: `le h g_l`
  · have xl : g_l ∈ g.leftMoves := by assumption
    rw [add_comm h.birthday g_l.birthday]
    apply add_lt_add_right
    exact birthday_lt_left g g_l xl
  -- Prove termination for the second recursive call: `le h_r g`
  · have xr : h_r ∈ h.rightMoves := by assumption
    rw [add_comm h_r.birthday g.birthday]
    apply add_lt_add_left
    exact birthday_lt_right h h_r xr

def Game.isSurreal (g : Game) : Prop :=
  ∀ g_l ∈ g.leftMoves, ∀ g_r ∈ g.rightMoves, ¬(le g_r g_l)

def Game.lt (g h : Game) : Prop := le g h ∧ ¬(le h g)

def Game.eq (g h : Game) : Prop :=
  le g h ∧ le h g

theorem zero_leq_zero : le zero zero := by
      unfold le
      constructor <;> (intro g h; cases h)

theorem zero_leq_one : le zero one := by
  unfold le
  constructor
  · intro z_l zero_left
    cases zero_left
  · intro o_r one_right
    cases one_right

theorem one_not_leq_zero : ¬(le one zero) := by
  intro h_le
  unfold le at h_le
  let h_not_le_zero_zero := h_le.1 zero (by simp [one, leftMoves])
  exact h_not_le_zero_zero zero_leq_zero

theorem half_surreal : isSurreal half := by
  intro g_l h_l g_r h_r
  simp only [half, leftMoves, List.mem_singleton] at h_l
  subst h_l
  simp only [half, rightMoves, List.mem_singleton] at h_r
  subst h_r
  exact one_not_leq_zero

theorem neg_one_leq_zero : le minus_one zero := by
  unfold le
  constructor
  · intro m_l neg_one_left
    cases neg_one_left
  · intro z_r zero_right
    cases zero_right


theorem half_leq_one : le half one := by
  unfold le
  constructor
  · intro h_l half_left
    simp only [half, leftMoves, List.mem_singleton] at half_left
    subst half_left
    exact one_not_leq_zero
  · intro o_r one_right
    cases one_right


theorem zero_lthan_one : lt zero one := by
  unfold lt
  constructor
  · exact zero_leq_one
  · intro h_le
    unfold le at h_le
    let h_left := h_le.1
    let h_contra := h_left zero (by simp [one, leftMoves])
    exact h_contra zero_leq_zero

def zero' : Game := mk [minus_one] [one]

theorem zero_zero'_eq : eq zero zero' := by
  unfold eq
  constructor
  · -- Prove `zero ≤ zero'`
    unfold le
    constructor
    · intro z_l zero_left
      cases zero_left
    · intro z_r zero'_right
      simp only [zero', rightMoves, List.mem_singleton] at zero'_right
      subst zero'_right
      exact one_not_leq_zero
  · -- Prove `zero' ≤ zero`
    unfold le
    constructor
    · intro z'_l zero'_left
      simp only [zero', leftMoves, List.mem_singleton] at zero'_left
      subst z'_l
      intro h_le_zero_neg_one
      unfold le at h_le_zero_neg_one
      let h_contra := h_le_zero_neg_one.2 zero (by simp [minus_one, rightMoves])
      exact h_contra zero_leq_zero
    · intro z_r zero_right
      cases zero_right
