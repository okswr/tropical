import Mathlib

import Tropical.TropicalLemma
--import TropicalLemma

universe u

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

--example 2.2
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


--lemma 2.11

-- R : CommSemiring, 𝒮 ⊆ R × R が性質(E1),(E2),(I1),(I2)を満たしているとする。
-- このとき、⟨𝒮⟩ は有限個のtransitive chain
-- (f,r₁),(r₁,r₂),...,(rₙ,g) ∈ 𝒮
-- が存在するようなすべての組(f,g)からなる

--corollary 2.12

--lemma 2.13

