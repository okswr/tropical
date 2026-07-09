import Mathlib

import Tropical.TropicalLemma
--import TropicalLemma

universe u



-- 可換性を仮定しないモノイドの組(S,+,*)に分配法則と吸収則と0≠1を与えたものについて
-- (これを擬半環-PseudoSemiring とする)
-- 加法について非可換な例を挙げる．
inductive S where
  | o : S
  | e : S
  | a : S
  | b : S
deriving DecidableEq, Repr



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

-- 上記の擬半環について，加法は非可換だが，乗法については可換である．
-- 加法，乗法ともに非可換である例は存在するのだろうか？







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


-- battingするっぽい
example : Semiring Bool where
  add := (· || ·)
  zero := false
  mul := (· && ·)
  one := true
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_add := by
    intro a
    rfl
  add_comm := by
    intro a b
    cases a <;> cases b <;> rfl
  add_zero := by
    intro a
    cases a <;> rfl
  left_distrib := by
    intro a b c
    cases a <;> cases b <;> rfl
  right_distrib := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_mul := by
    intro a
    rfl
  mul_zero := by
    intro a
    cases a <;> rfl
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    rfl
  mul_one := by
    intro a
    cases a <;> rfl
  nsmul := fun n b => if n = 0 then 0 else b
  nsmul_succ := by
    intro n x
    cases n <;> cases x <;> rfl
  nsmul_zero := by
    intro x
    simp
  natCast
  | 0 => 0
  | _ + 1 => 1
  natCast_succ := by
    intro n
    cases n <;> simp
    · rfl
    · rfl


inductive 𝔹 where
| zero
| one
deriving Repr, DecidableEq

instance : Zero 𝔹 where
  zero := 𝔹.zero

instance : One 𝔹 where
  one := 𝔹.one

instance : CommSemiring 𝔹 where
  add
  | 0, 0 => 0
  | _, _ => 1

  mul
  | 1, 1 => 1
  | _, _ => 0

  zero_add := by intro a ; cases a <;> rfl
  add_zero := by intro a ; cases a <;> rfl
  add_comm := by intro a b ; cases a <;> cases b <;> rfl
  add_assoc := by intro a b c ; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a ; cases a <;> rfl
  mul_one := by intro a ; cases a <;> rfl
  zero_mul := by intro a ; cases a <;> rfl
  mul_zero := by intro a ; cases a <;> rfl
  mul_assoc := by intro a b c ; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b ; cases a <;> cases b <;> rfl
  left_distrib := by intro a b c ; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c ; cases a <;> cases b <;> cases c <;> rfl
  nsmul
  | 0 , _ => 0
  | _ , b => b
  nsmul_succ := by intro n x ; cases n <;> cases x <;> rfl



-- クイックアクセス上で#diagonal_powを入力することで、検索できる

-- Set : A → Prop


-- 𝕋 → 𝔹

-- Con






--example 2.2
example : Semiring (WithTop Nat) where
  zero := ⊤
  one := 0
  add := Min.min
  mul := Add.add
  zero_add := by
    intro a
    change Min.min ⊤ a = a
    cases a <;> rfl
  add_zero := by
    intro a
    change Min.min a ⊤ = a
    cases a <;> rfl
  add_comm := by
    intro a b
    change Min.min a b = Min.min b a
    cases a <;> cases b <;> simp [min_comm]
  add_assoc := by
    intro a b c
    change Min.min (Min.min a b) c = Min.min a (Min.min b c)
    cases a <;> cases b <;> cases c <;> simp [min_assoc]
  one_mul := by
    intro a
    change 0 + a = a
    simp
  mul_one := by
    intro a
    change a + 0 = a
    simp
  zero_mul := by
    intro a
    change ⊤ + a = ⊤
    simp
  mul_zero := by
    intro a
    change a + ⊤ = ⊤
    simp
  mul_assoc := by
    intro a b c
    change a + b + c = a + (b + c)
    cases a <;> cases b <;> cases c <;> simp[_root_.add_assoc]
  left_distrib := by
    intro a b c
    change a + Min.min b c = Min.min (a + b) (a + c)
    cases a <;> cases b <;> cases c <;> simp [add_min]
  right_distrib := by
    intro a b c
    change Min.min a b + c = Min.min (a + c) (b + c)
    cases a <;> cases b <;> cases c <;> simp [min_add]
  nsmul := nsmulRec
  nsmul_zero := by
    intro x
    simp [nsmulRec]
    sorry
  nsmul_succ := by sorry
  natCast_zero := by sorry
  natCast_succ := by sorry

#check Tropical

#check Tropical (WithTop Real)

-- optimization algebra
example : Semiring (WithTop Real) where
  zero := ⊤
  one := 0
  add := Min.min
  mul := Add.add
  zero_add := by
    intro a
    change Min.min (⊤ : WithTop Real) (a : WithTop Real) = (a : WithTop Real)
    rw [min_top_left]
  add_zero := by
    intro a
    change Min.min (a : WithTop Real) (⊤ : WithTop Real) = (a : WithTop Real)
    rw [min_top_right]
  add_comm := by
    intro a b
    change Min.min a b = Min.min b a
    rw [min_comm]
  add_assoc := by
    intro a b c
    change Min.min (Min.min a b) c = Min.min a (Min.min b c)
    rw [min_assoc]
  one_mul := by
    intro a
    change 0 + a = a
    simp
  mul_one := by
    intro a
    change a + 0 = a
    cases a <;> simp
  zero_mul := by
    intro a
    change ⊤ + a = ⊤
    cases a <;> simp
  mul_zero := by
    intro a
    change a + ⊤ = ⊤
    cases a <;> simp
  mul_assoc := by
    intro a b c
    change a + b + c = a + (b + c)
    simp [add_assoc]
  left_distrib := by
    intro a b c
    change a + Min.min b c = Min.min (a + b) (a + c)
    simp [add_min]
  right_distrib := by
    intro a b c
    change Min.min a b + c = Min.min (a + c) (b + c)
    simp [min_add]
  nsmul := nsmulRec
  nsmul_zero := by
    intro x
    simp [nsmulRec]
    sorry
  nsmul_succ := by sorry
  natCast_zero := by sorry
  natCast_succ := by sorry

abbrev 𝕋 := Tropical (WithTop Real)

noncomputable instance : CommSemiring 𝕋 := by
  exact Tropical.instCommSemiring



variable {R : Type*} [CommSemiring R]
--definition 2.4



--RingConを使うことになるでしょう．

--definition2.5

-- ねじれ積を定義．
-- def twistProd : R × R → R × R → R × R
-- | (a, b) , (c, d) => (a * c + b * d, a * d + b * c)

def twistProd : R × R → R × R → R × R
| (a, b) , (c, d) => (a * c + b * d, a * d + b * c)


--lemma 2.6

--theorem :c,d ∈ R, ∀(a,b),∈ E , twistProd (c,d) (a,b) ∈ E

-- r a b → r (a * c + b * d) (a * d + b * c)
theorem twistprod_con (a b c d : R) (r : RingCon R) (h1 : r a b) :
  r (c * a + d * b) (c * b + d * a) := by
    apply RingCon.add
    · apply RingCon.mul
      · exact (RingCon.eq r).mp rfl
      · exact h1
    · apply RingCon.mul
      · exact (RingCon.eq r).mp rfl
      · apply RingCon.symm
        exact h1

-- twistprodを用いた定義（使いにくそうなので保留）
example (a b c d : R) (r : RingCon R) (h1 : r a b) :
  r (twistProd (c, d) (a, b)).1 (twistProd (c, d) (a, b)).2 := by
    rw [twistProd]
    simp only
    apply RingCon.add
    · apply RingCon.mul
      · exact (RingCon.eq r).mp rfl
      · exact h1
    · apply RingCon.mul
      · exact (RingCon.eq r).mp rfl
      · apply RingCon.symm
        exact h1



--   mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
structure RingCon' (R : Type*) [Semiring R] extends Setoid R, AddCon R where
  twist_mul' : ∀{w x y z}, r y z → r (w * y + x * z) (w * z + x * y)

instance : CoeFun (RingCon' R) (fun _ => R → R → Prop) where
   coe r := r.r

instance : CoeFun (RingCon' R) (fun _ => R → R → Prop) where
   coe r := r.r


-- R × R


-- 同値性について
example (r : RingCon R) : ∀(w x y z : R), r w x → r y z → r (w * y + x * z) (w * z + x * y) := by
  intro w x y z rwx ryz
  apply RingCon.add r
  · apply RingCon.mul r
    · exact (RingCon.eq r).mp rfl
    · exact ryz
  · apply RingCon.mul r
    · exact (RingCon.eq r).mp rfl
    · apply RingCon.symm r
      exact ryz

example (r : RingCon' R) : ∀ (w x y z : R), r w x → r y z → r (w * y) (x * z) := by
  intro w x y z rwx ryz
  have rxyxz : r (x * y) (x * z) := by
    rw [← add_zero (x * y), ← add_zero (x * z)]
    nth_rewrite 1 [← zero_mul z]
    nth_rewrite 2 [← zero_mul y]
    apply RingCon'.twist_mul'
    exact ryz
    --apply twistprod_con y z x 0 r ryz
    -- r (x * y + 0 * z) (x * z + 0 * y)
    -- twistprod_con y z x 0 r ryz
  have rywyx : r (y * w) (y * x) := by
    rw [← add_zero (y * w), ← add_zero (y * x)]
    nth_rewrite 1 [← zero_mul x]
    nth_rewrite 2 [← zero_mul w]
    apply RingCon'.twist_mul'
    exact rwx
    -- r (y * w  + 0 * y) (y * x + 0 * w)
    -- twistprod_con w x y 0 r rwx
  -- この話はSemiring ではなく CommSemiring だったので後で直すこと
  nth_rewrite 1 [mul_comm]
  --rw [Setoid.trans' rywyx]
  nth_rewrite 2 [mul_comm] at rywyx
  --memo
  -- xy = X,xz = Y,yw = Z
  -- rxyxz = rXY
  -- rywyx = rZX
  -- ⊢ rZY
  -- trans rZX rXY = rZY
  apply Setoid.trans'
  · exact rywyx
  · exact rxyxz

  -- CommSemiring より y * x = x * y なので
  -- rywxy : r (y * w) (x * y)
  -- Setoid.trans で r (y * w) (x * z)
  -- CommSemiring より y * w = w * y なので
  -- r (w * y) (x * z)


-- T → B を 0 ↦ 0 , else ↦ 1と送ると半環準同型
noncomputable def booleanization : 𝕋 →+* 𝔹 :=
  {
    toFun := fun x => if x = 0 then 0 else 1
    map_one' := by simp
    map_mul' := by
      intro x y
      simp
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx,hy]
    map_zero' := by simp
    map_add' := by
      intro x y
      simp
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx,hy] ; rfl
  }


-- 上記の写像の核合同 ker booleanization = T×T \ {(t,0),(0,t)|t≠0} = E は極大であること
-- note. ker f = {(a,b) | f(a) = f(b)}

-- MaximalIdeal
-- #check MaximalIdeal


--example 2.9

-- 上記の写像の核合同 ker booleanization = T×T \ {(t,0),(0,t)|t≠0} = E は真の合同の中で極大であること
-- note. ker f = {(a,b) | f(a) = f(b)}


-- booleanization が全射であること
theorem booleanization_surjective : Function.Surjective booleanization := by
  intro b
  cases b
  · use 0
    rfl
  · use 1
    rfl
-- ∀b ∈ 𝔹, if b = 0 then ∃0 ∈ 𝕋, booleanization 0 = 0 else ∃ 1 ∈ 𝕋, booleanization 1 = 1
-- 以上より全射であることを示すことができる

-- @RingCon.mk' : R → R ⧸ r

-- 既存のものであるRingHom.ker_isMaximal_of_surjectiveを@RingCon.ker_isMaximal_of_surjectiveとして実装して
-- 上記の定理を証明する（ことを次回までにがんばる）

-- 𝔹がRingConSimple(合同関係が自明なものしか持たない)であること
#check RingConSimple
#check ker_isMaximal'
--#check ker_isMaximal

instance : DivisionSemiring 𝔹 := {
  (inferInstance : CommSemiring 𝔹) with
  inv := fun x => x
  inv_zero := rfl
  mul_inv_cancel := by
    intro a ha
    cases a
    · exact absurd rfl ha
    · decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  nnqsmul := fun q a => ((q.num : 𝔹) * (q.den : 𝔹)) * a
  nnqsmul_def := fun _ _ => rfl }

instance : RingConSimple 𝔹 where
  ringcon_simple := by
    intro c
    by_cases h : c 0 1;
    · refine' Or.inr ( RingCon.ext fun x y => _ );
      cases x <;> cases y <;> simp_all +decide [ RingCon.refl, RingCon.symm ];
      · exact h;
      · exact c.symm h;
    · left;
      ext x y;
      constructor <;> intro <;> cases x <;> cases y <;> simp_all +decide [ RingCon.refl ];
      · contradiction;
      · exact h ( c.symm ‹_› )

theorem pr : IsCoatom (RingCon.ker booleanization):= by
  exact ker_isMaximal' booleanization booleanization_surjective


-- ker_isMaximal_of_surjective は
-- Ring R, DivisionRing K, F : R → K, F : RingHomClass, f : F
-- Surjective f → (ker f).IsMaximal


-- MaximalIdeal
-- #check MaximalIdeal


-- E_B := 𝕋 × 𝕋 \ {((t : 𝕋), (0 : 𝕋)),((0 : 𝕋), (t : 𝕋)) | t ≠ (0 : 𝕋)}
-- これが真の合同の中で極大であることを示す。
-- if E_B ⊊ E ⇒ ∃t : 𝕋, t ≠ 0, (t, 0) ∈ E.
-- ∀t ≠ 0, untrop t ∈ ℝ より ∀t ≠ 0, ∃(t⁻¹).
-- twistProd (t⁻¹, 0) (t, 0) = (1, 0) ∈ E ⇒ E = 𝕋 × 𝕋
-- このEは真の合同ではないため、E_B ⊊ E は存在しない

-- E を 𝕋 上の任意の非自明な真の合同関係とする。これは唯一であることを示す。
-- ∀r, s ∈ 𝕋, r ≠ s, (r, s) ∈ E
-- E は真の合同より r ≠ 0, s ≠ 0. よって untrop r, untrop s ∈ ℝ
-- r < s と仮定.
-- twistProd (r⁻¹, 0) (r, s) = (1, sr⁻¹) ∈ E
-- ∴ (1, (sr⁻¹)^(n : ℕ)) ∈ E
-- 同様に (1, (rs⁻¹)^(n : ℕ)) ∈ E
-- ∀t ∈ 𝕋 \ {0},∃n ∈ ℕ, |untrop t| < n(untrop s - untrop r) (アルキメデス性)
-- |t| < (sr⁻¹)^n

-- if untrop t ≥ 0 (t ≥ 1),
-- (t, (sr⁻¹)^n) = (1, (sr⁻¹)^n) + (t, t) ∈ E (注: 右辺の加法はTropical.addである)
-- (1, t) ∈ E (∵ (t, (sr⁻¹)^n) ∈ E, (1, (sr⁻¹)^n) ∈ E, Setoid.train)

-- if untrop t ≤ 0  (t ≤ 1),
-- (1, t) = (1, (rs⁻¹)^n) + (t, t) ∈ E
-- ∴ ∀t ∈ 𝕋 \ {0}, (1, t) ∈ E
-- E_B ⊆ E
-- E_B は極大より E_B = E

variable (r : RingCon R)
-- R ⧸ r
#check r.Quotient
#check CommSemiring r.Quotient



-- ∀𝒮 ⊆ R × R
-- congruence generated by 𝒮
-- ⇔ 𝒮 を含む R 上の合同関係のうち最小のもの ≝ ⟨𝒮⟩
-- 半環 R 上の合同関係であることを明示する場合は ⟨𝒮⟩_R と書く
-- 合同関係の共通部分は合同関係となるため
-- ⟨𝒮⟩ は 𝒮 を含む R 上のすべての合同関係の共通部分と言い換えられる


--example 2.10


-- ev₀ : R[X] →+* R ; f(X) ↦ f(0)
-- ⇒ ker ev₀ = ⟨(x,0)⟩ が成り立つ

-- proof. (x,0) ∈ ker ev₀ より
-- ⟨(x,0)⟩ ⊆ ker ev₀
-- ∀ f ∈ R[X] ; (f(x),f(0)) ∈ ⟨(x,0)⟩
-- ∵ ∀ a ∈ R , ∀ d ≥ 1
--    (a x^d, 0) = twistProd (a x^(d-1),0) (x, 0) ∈ ⟨(x, 0)⟩
--    f(x) = Σ a_d x^d と書くと
--    (f(x), f(0)) = (Σ a_d x^d, a_0)
--                 = (a_0, a_0) + Σ (a_d x^d, 0) ∈ ⟨(x, 0)⟩
-- ∀ g ∈ ker ev₀,
-- ⇒ f(0) = g(0)
-- ⇒ (f(x), f(0)), (g(0), g(x)) ∈ ⟨(x,0)⟩
-- ⇒ (f(x), g(x)) ∈ ⟨(x,0)⟩
-- ⇒ ker ev₀ ⊆ ⟨(x, 0)⟩
-- ∴ ker ev₀ = ⟨(x, 0)⟩

variable [CSR : CommSemiring R]

open Polynomial
def ev₀ : R[X] →+* R := @Polynomial.evalRingHom R CSR (0 : R)
-- Polynomial.evalRingHom (0 : R) では，型推論の参照先がズレてしまう
-- らしいので，明示的に記述している．
-- memo. CommSemiring Rなどの型を命名するときの命名規則を確認すること ： CSRについて

example : RingCon.ker ev₀ = RingConGen.Rel {r x 0} := by
  sorry


-- 以下はgoedel-prover-v2の出力結果より引用
theorem ker_ev₀_eq_ideal : ∀ (f : Polynomial R), f.eval 0 = 0 ↔ ∃ (g : Polynomial R), f = X * g := by
  intro f
  have h_main : f.eval 0 = 0 ↔ ∃ (g : Polynomial R), f = X * g := by sorry
  sorry


--lemma 2.11

-- R : CommSemiring, 𝒮 ⊆ R × R が性質(E1),(E2),(I1),(I2)を満たしているとする。
-- このとき、⟨𝒮⟩ は有限個のtransitive chain
-- (f,r₁),(r₁,r₂),...,(rₙ,g) ∈ 𝒮
-- が存在するようなすべての組(f,g)からなる



--corollary 2.12

--lemma 2.13
