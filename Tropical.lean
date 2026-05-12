import Tropical.Basic
import mathlib

universe u


-- 加法についての可換性を仮定せず半環を与えたとき、これが加法について可換になるかを確認
-- したかった
-- class MySemiring (R : Type u) where
--   add : R → R → R
--   zero : R
--   mul : R → R → R
--   one : R
--   add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
--   add_left_zero : ∀ a : R, add a zero = a
--   add_right_zero : ∀ a : R, add zero a = a
--   mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
--   mul_left_one : ∀ a : R, mul a one = a
--   mul_right_one : ∀ a : R, mul one a = a
--   zero_ne_one : zero ≠ one
--   left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
--   right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)
--   zero_mul : ∀ a : R, mul zero a = zero
--   mul_zero : ∀ a : R, mul a zero = zero

-- open MySemiring

#check List.any
#print List
#eval (true || false)
#eval ([1,2,3] : List ℕ).head?
#eval ([1,2,3] : List ℕ).tail

-- def mulBoolList : (List Bool) → (List Bool) → (List Bool)
--   | [] , _ => []
--   | _ , [] => []
--   | [x] , [y] => [x||y]
--   | [x], y₁ :: y => (mulBoolList [x] [y₁]) ++ (mulBoolList [x] y)
--   | x₁ :: x , y => (mulBoolList [x₁] y) ++ (mulBoolList x y)

-- def mulBoolList (l₁ l₂ : List Bool) : List Bool :=
--   l₁.flatMap (fun x => l₂.map (fun y => x || y))

-- #eval mulBoolList [true,false,true] [true,true,false]
-- -- [x₁,x₂,x₃] [y₁,y₂,y₃] = [x₁y₁, x₁y₂, x₁y₃, x₂y₁, x₂y₂, x₂y₃, x₃y₁, x₃y₂, x₃y₃]
-- -- となっていると思うが、AI出力なので確認できていない

-- #eval mulBoolList [false] [true,true,false]
-- #eval mulBoolList [true,false,false] [false]

-- #eval mulBoolList (mulBoolList [false,true] [false, true]) [false,true]
-- #eval mulBoolList [false,true] (mulBoolList  [false, true] [false,true])

-- #eval mulBoolList [false,true] ([true,false,false] ++ [true,false])
-- #eval (mulBoolList [false,true] [true,false,false]) ++ (mulBoolList [false,true] [true,false])
-- -- これは半環にならない.
-- instance instList : MySemiring (List Bool) where
--   add := List.append    -- [a,b] + [a,c] = [a,b,a,c]
--   zero := List.nil      -- [] + [a,b] = [a,b] , [a,b] + [] = [a,b]
--   mul := mulBoolList    -- [a,b] * [c,d] = [a∨c, a∨d, b∨c, b∨d]
--   one := [false]        -- [false] * [a,b] = [a,b] , [a,b] * [false] = [a,b]
--   add_assoc := by
--     intro a b c
--     simp
--   add_left_zero := by
--     intro a
--     simp
--   add_right_zero := by
--     intro a
--     simp
--   mul_assoc := by
--     intro a b c
--     sorry
--   mul_left_one := by
--     intro a
--     sorry
--   mul_right_one := by
--     intro a
--     sorry
--   zero_ne_one := by simp
--   left_distrib := by
--     intro a b c
--     sorry -- 分配法則成り立たないのでダメ
--   right_distrib := sorry
--   zero_mul := sorry
--   mul_zero := sorry

-- example : ∃ (a b : List Bool), add a b ≠ add b a := by
--   use [true], [false]
--   simp [add]



inductive S where
  | o : S
  | e : S
  | a : S
  | b : S
deriving DecidableEq, Repr

#print S

instance : Zero S where
  zero := S.o

def S.add : S → S → S
  | o, x => x
  | x, o => x
  | e, _ => e
  | _, e => e
  | a, _ => a
  | b, _ => b

def S.mul : S → S → S
  | e, x => x
  | x, e => x
  | _, _ => o

/-
example.
∘ | y
--+---
x |x∘y


+ | 0 | a | b | 1
--+---+---+---+----
0 | 0 | a | b | 1
a | a | a | a | 1
b | b | b | b | 1
1 | 1 | 1 | 1 | 1

* | 0 | a | b | 1
--+---+---+---+----
0 | 0 | 0 | 0 | 0
a | 0 | 0 | 0 | a
b | 0 | 0 | 0 | b
1 | 0 | a | b | 1

The above S is an example that is noncommutative under addition.
-/

instance : Add S where
  add := S.add

class PseudoSemiring (R : Type*) extends AddMonoid R, Monoid R, Distrib R, MulZeroClass R where
  zero_ne_one : (0 : R) ≠ (1 : R)

instance : PseudoSemiring S where
  add := S.add
  mul := S.mul
  zero := S.o
  one := S.e
  zero_add := by intro x ; rfl
  add_zero := by
    intro x
    cases x <;> rfl
  one_mul := by intro x ; rfl
  mul_one := by
    intro x
    cases x <;> rfl
  zero_ne_one := by exact not_eq_of_beq_eq_false rfl
  zero_mul := by
    intro x
    cases x <;> rfl
  mul_zero := by
    intro x
    cases x <;> rfl
  add_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  left_distrib := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  right_distrib := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  nsmul := nsmulRec


theorem non_commutative_of_PseudoSemiring : ∃(x y : S), x + y ≠ y + x := by
  use S.a, S.b
  decide





#check CommGroup
#check AddGroup
#check Group.inv_mul_cancel



-- (Commを仮定しない)環だと成り立つ
class MyRing (R : Type u) where
  add : R → R → R
  neg : R → R
  sub : R → R → R
  zero : R
  mul : R → R → R
  inv : R → R
  div : R → R → R
  one : R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_left_zero : ∀ a : R, add a zero = a
  add_right_zero : ∀ a : R, add zero a = a
  add_neg_cancel : ∀ a : R, add a (neg a) = zero
  neg_add_cancel : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_left_one : ∀ a : R, mul a one = a
  mul_right_one : ∀ a : R, mul one a = a
  mul_inv_cancel : ∀ a : R, mul a (inv a) = a
  inv_mul_cancel : ∀ a : R, mul (inv a) a = a
  zero_ne_one : zero ≠ one
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a : R, mul zero a = zero
  mul_zero : ∀ a : R, mul a zero = zero

open MyRing


example [MyRing R] : ∀ (a b : R), add a b = add b a := by
  intro a b
  sorry

-- 証明スケッチ
-- (a + b) * (1 + 1) = (a + b) * (1 + 1)
-- 左辺をleft_distrib,右辺をright_distribより
-- a + b + a + b = a + a + b + b
-- left_add_cancel a,right_add_cancel bより(あるいはleft_add -a,right_add -b)
-- a + b = b + a


example [Ring R] (x y : R) : x + y = y + x := by
  exact AddCommMagma.add_comm x y

-- Mathlib.Ringはadd_commを定義として持っている


-- 𝔹 = {0,1} , 0 + 0 = 0, _ + _ = 1, 1 * 1 = 1, _ * _ = 0
#eval (0 : Bool)
#eval (1 : Bool)
#eval (0 : Bool) || (1 : Bool)
#eval (0 : Bool) && (1 : Bool)

instance : Semiring Bool where
  add := (· || ·)
  zero := false
  mul := (· && ·)
  one := true
  add_assoc := by
    intro a b c
    by_cases atr : (a = true)
    · rw [atr]
      rw [@Bool.eq_iff_iff]
      exact Bool.coe_iff_coe.mpr rfl
    · have ha : a = false := by
        exact eq_false_of_ne_true atr
      rw [ha]
      by_cases btr : (b = true)
      · rw [btr]
        rw [Bool.eq_iff_iff]
        exact Bool.coe_iff_coe.mpr rfl
      · have hb : b = false := by
          exact eq_false_of_ne_true btr
        rw [hb]
        by_cases ctr : (c = true)
        · rw [ctr]
          rw [Bool.eq_iff_iff]
          exact Bool.coe_iff_coe.mpr rfl
        · have hc : c = false := by
            exact eq_false_of_ne_true ctr
          rw [hc]
          rfl
  zero_add := by
    intro a
    rfl
  add_comm := by
    intro a b
    by_cases atr : a = true
    · rw [atr]
      by_cases btr : b = true
      · rw [btr]
      · have hb : b = false := by
          exact eq_false_of_ne_true btr
        rw [hb]
        rfl
    · have ha : a = false := by
        exact eq_false_of_ne_true atr
      rw [ha]
      by_cases btr : b = true
      · rw [btr]
        rfl
      · have hb : b = false := by
          exact eq_false_of_ne_true btr
        rw [hb]
  add_zero := by
    intro a
    by_cases atr : a = 1
    · rw [atr]
      rfl
    · have ha : a = 0 := by
        exact Bool.not_eq_not.mp atr
      rw [ha]
      rfl
  left_distrib := by
    intro a b c
    by_cases atr : a = true
    · rw [atr]
      rfl
    · have ha : a = false := by
        exact eq_false_of_ne_true atr
      rw [ha]
      rfl
  right_distrib := by sorry
  zero_mul := by
    intro a
    rfl
  mul_zero := sorry
  mul_assoc := by
    intro a b c
    by_cases atr : a = true
    · rw [atr]
      rfl
    · have ha : a = false := by
        exact eq_false_of_ne_true atr
      rw [ha]
      rfl
  one_mul := by
    intro a
    rfl
  mul_one := by
    intro a
    by_cases atr : a = true
    · rw [atr]
      rfl
    · have ha : a = false := by
        exact eq_false_of_ne_true atr
      rw [ha]
      rfl
  nsmul := by sorry
  nsmul_zero := by sorry
  nsmul_succ := by sorry
  natCast_succ := by sorry


-- クイックアクセス上で#diagonal_powを入力することで、検索できる

-- Set : A → Prop


-- 𝕋 → 𝔹

-- Con

-- とりあえずサクッとスケッチを描くこと（今日）








--example 2.2
example : Semiring (WithTop Nat) where
  zero := ⊤
  one := 0
  add := Min.min
  mul := Add.add
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  add_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  nsmul := by nsmulRec




--definition 2.4

--RingConを使うことになるでしょう．

--definition2.5

-- ねじれ積を定義します．

--lemma 2.6

--example 2.9


--exam,ple 2.10
