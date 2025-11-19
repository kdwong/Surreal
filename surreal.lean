import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax


inductive Game where
  | mk : List Game → List Game → Game

def Game.leftMoves (g : Game) : List Game :=
  match g with
  | Game.mk left _ => left

def Game.rightMoves (g : Game) : List Game :=
  match g with
  | Game.mk _ right => right


def zero : Game := Game.mk [] []
def one : Game := Game.mk [zero] []
def half : Game := Game.mk [zero] [one]
def two : Game := Game.mk [one] []
def three : Game := Game.mk [two] []


def Game.birthday (g : Game) : Nat :=
  match g with
  | Game.mk L R =>
    let bL := L.map birthday
    let bR := R.map birthday
    (bL ++ bR).maximum.getD 0 + 1

#eval Game.birthday two -- 3
#eval Game.birthday half -- 3



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
  have h_max : ∀ x ∈ a, x ≤ a.maximum.getD 0 := by
    intro x hx
    match h_eq : a.maximum with
    | none =>
        have h_a_empty : a = [] := by
          apply list_maximum_is_none_then_is_empty a h_eq
        rw [h_a_empty] at hx
        contradiction
    | some m =>
      simp only [h_eq, Option.getD_some]
      exact List.le_of_mem_argmax hx h_eq
  exact h_max s h


lemma Game.birthday_lt_left (g : Game) (l : Game) (h : l ∈ g.leftMoves) :
    Game.birthday l < Game.birthday g := by
  cases g with
  | mk L R =>
    simp [Game.leftMoves] at h
    simp [Game.birthday]
    let b := List.map birthday L ++ List.map birthday R
    change Game.birthday l < b.maximum.getD 0 + 1
    have h_mem_b : l.birthday ∈ b := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      use l
    have aaa : l.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b l.birthday h_mem_b
    linarith


lemma Game.birthday_lt_right (g : Game) (r : Game) (h : r ∈ g.rightMoves) :
    Game.birthday r < Game.birthday g := by
  cases g with
  | mk L R =>
    simp [Game.rightMoves] at h
    simp [Game.birthday]
    let b := List.map birthday L ++ List.map birthday R
    change Game.birthday r < b.maximum.getD 0 + 1
    have h_mem_b : r.birthday ∈ b := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      use r
    have aaa : r.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b r.birthday h_mem_b
    linarith


def Game.le (g h : Game) : Prop :=
    (∀ g_l ∈ g.leftMoves, ¬(Game.le h g_l)) ∧ (∀ h_r ∈ h.rightMoves, ¬(Game.le h_r g))
termination_by (Game.birthday g + Game.birthday h)
decreasing_by
  -- Prove termination for the first recursive call: `Game.le h g_l`
  · have xl : g_l ∈ g.leftMoves := by assumption
    rw [add_comm h.birthday g_l.birthday]
    apply add_lt_add_right
    exact Game.birthday_lt_left g g_l xl
  -- Prove termination for the second recursive call: `Game.le h_r g`
  · have xr : h_r ∈ h.rightMoves := by assumption
    rw [add_comm h_r.birthday g.birthday]
    apply add_lt_add_left
    exact Game.birthday_lt_right h h_r xr


theorem zero_leq_zero : Game.le zero zero := by
      unfold Game.le
      constructor <;> (intro g h; cases h)


theorem zero_leq_one : Game.le zero one := by
  unfold Game.le
  constructor
  · intro z_l zero_left
    cases zero_left
  · intro o_r one_right
    cases one_right


theorem half_leq_one : Game.le half one := by
  unfold Game.le
  constructor
  · intro h_l half_left
    -- The only left move of `half` is `zero`.
    simp only [half, Game.leftMoves, List.mem_singleton] at half_left
    subst half_left
    intro h_le_one_zero
    unfold Game.le at h_le_one_zero
    let h_not_le_zero_zero := h_le_one_zero.1 zero (by simp [one, Game.leftMoves])
    -- This gives us the contradiction.
    exact h_not_le_zero_zero zero_leq_zero
  · intro o_r one_right
    cases one_right
