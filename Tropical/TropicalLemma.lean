module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.RingTheory.Ideal.Operations

public import Mathlib.RingTheory.Congruence.Hom



variable {R K} [Semiring R] [DivisionSemiring K] (f : R →+* K) (hf : Function.Surjective f)

-- DivisionSemiring K上の環合同c ∈ RingCon Kは自明な２つの合同だけである．

public class RingConSimple (K : Type*) [DivisionSemiring K] where
  ringcon_simple : ∀ c : RingCon K, c = ⊥ ∨ c = ⊤

-- 1. 半環R,単純な剰余半環K(半環Kの合同がRingCon K = {Δ,K×K};Δ:={a~a}の二つのみである),
-- 全射半環準同型f : R →+* Kに対して， R ⧸ ker f ≅+* K

-- f : M →+* Pが全射ならば，M ⧸ ker f ≃+* P
noncomputable def firstIsomorphismTheorem : (RingCon.ker f).Quotient ≃+* K :=
  RingCon.quotientKerEquivOfSurjective f hf


-- RingCon R', f : R →+* R' ⇒
-- RingCon.comap : RingCon R
-- RingCon.comap は 半環準同型f : R →+* R'と環合同R'を引数に環合同Rを引き戻す操作
-- RingCon.comap : (RingCon M' ,(f : M →+* M')) → RingCon M

-- C : RingCon (R ⧸ ker f) ; R ⧸ ker f上の合同関係(R ⧸ ker f) × (R ⧸ ker f)
-- toFun : C ⇒ RingCon.comap C e.symm
--   RingCon.comap : (RingCon M' ,(f : M →+* M')) → RingCon M
--   RingCon.comap C e.symm : ((C : RingCon R⧸kerf), (e.symm : K →+* R⧸kerf)) → RingCon K
-- invFun : C => RingCon.comap C e
--   RingCon.comap C e : ((C : RingCon K), (e : R⧸kerf → K)) → RingCon R⧸kerf

-- R ⧸ ker f ≃+* K ならば Con(R ⧸ ker f) ≃o Con(K) ; R ⧸ ker f上の半環合同とK上の半環合同は包含関係を保つ
noncomputable def OrderIsomorphismTheorem : RingCon (RingCon.ker f).Quotient ≃o RingCon K := by
  let e := firstIsomorphismTheorem f hf
  refine {
    toFun := fun C => RingCon.comap C e.symm
    invFun := fun C => RingCon.comap C e
    left_inv := by
      intro Rkerf
      ext x y
      simp only [RingCon.comap_rel, RingEquiv.symm_apply_apply]
    right_inv := by
      intro Rkerf
      ext x y
      simp only [RingCon.comap_rel, RingEquiv.apply_symm_apply]
    map_rel_iff' := by
      intro a b
      simp only [Equiv.coe_fn_mk]
      constructor
      · intro hab x y hxy
        have h2 := hab (x := e x) (y := e y)
        -- h2 : (a.comap e.symm) (e x) (e y) → (b.comap e.symm) (e x) (e y)
/-
    R⧸kerf ---(e)---> K
    K -------------(e.symm)------------> R⧸kerf
    RingCon K ---(a.comap e.symm)---> RingCon (R⧸kerf)
-/
        simp only [RingCon.comap_rel, RingEquiv.symm_apply_apply] at h2
        exact h2 hxy
      · intro hab
        apply RingCon.comap_mono
        exact hab
  }


-- 2. 半環R,∀θ ∈ Con R, {ρ ∈ Con R | θ ⊆ ρ} ≃o Con R⧸θ
-- つまり包含関係に関する順序を保つような，合同関係の全単射を与えることができる．
section Semiring
def ringConOrderIsoTheorem (θ : RingCon R) : {ρ : RingCon R // θ ≤ ρ} ≃o
  RingCon (RingCon.Quotient θ) := RingCon.correspondence


def ringConKerOrderIsoTheorem : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃o
    RingCon ((RingCon.ker f).Quotient) := RingCon.correspondence

end Semiring

-- 3. Con K = Con R ⧸ ker f = {Δ,K×K} ≃o {ρ ∈ Con R | ker f ⊆ ρ}
-- 元は2つしか存在せず，順序を保つので，ρ = ker f または ρ = R × R のみ．
-- ここで，ker f ⊆ ρ より，ker f ⊆ ker f または ker f ⊆ R × R.
-- つまり，ker f を含む合同は ker f または R × R のみである．
-- これはker fが真の合同の中で最大であることを意味する．



theorem ker_eq_or_top_of_simple'
  [RingConSimple K] (hf : Function.Surjective f) (ρ : RingCon R) (hρ : RingCon.ker f ≤ ρ) :
  ρ = RingCon.ker f ∨ ρ = ⊤ := by
  let e1 := OrderIsomorphismTheorem f hf
  let e2 := ringConKerOrderIsoTheorem f
  have h1 : ∀ c : RingCon K, c = ⊥ ∨ c = ⊤ := RingConSimple.ringcon_simple
  have h2 : ∀ c1 : RingCon (RingCon.ker f).Quotient, c1 = ⊥ ∨ c1 = ⊤ := by
    intro d
    rcases h1 (e1 d) with h | h
    · left
      apply e1.injective
      simpa using h
    · right
      apply e1.injective
      simpa using h
  have h3 : ∀ c2 : {ρ : RingCon R // RingCon.ker f ≤ ρ},
    c2 = ⟨RingCon.ker f, by simp⟩ ∨ c2 = ⟨⊤, by simp⟩ := by
    intro d
    rcases h2 (e2 d) with h | h
    · left
      apply e2.injective
      simpa using h
    · right
      apply e2.injective
      rw [h]
      have : e2 (⟨⊤, by simp⟩ : {ρ : RingCon R // RingCon.ker f ≤ ρ}) = ⊤ := by
        -- Since the top congruence on R relates every element to every other element,
        -- its image under the quotient map should relate every element of the quotient ring
        -- to every other element.
        -- Therefore, the image of the top congruence under the quotient map is the top congruence
        --in the quotient ring.
        ext x y;
        simp only [RingCon.coe_top, Pi.top_apply, «Prop».top_eq_true, iff_true];
        obtain ⟨ x, rfl ⟩ := Quotient.exists_rep x;
        obtain ⟨ y, rfl ⟩ := Quotient.exists_rep y;
        simp only [e2] ;
        apply_rules [ RingConGen.Rel.of ];
        exact ⟨ x, y, trivial, rfl, rfl ⟩
      rw [this]
  rcases h3 ⟨ρ, hρ⟩ with h | h
  · left
    exact congrArg Subtype.val h
  · right
    exact congrArg Subtype.val h


public theorem ker_isMaximal' [RingConSimple K] (hf : Function.Surjective f) :
  IsCoatom (RingCon.ker f) := by
  -- Suppose for contradiction that RingCon.ker f = ⊤.
  by_contra h_contra
  -- ker f = ⊤ でなければ f は定数写像である。
  have h_all : ∀ x y : R, f x = f y := by
    simp_all only [IsCoatom, ne_eq, not_and, not_forall];
    by_cases h : RingCon.ker f = ⊤ <;> simp_all only [not_false_eq_true, lt_iff_le_and_ne, ne_eq,
      exists_prop, forall_const];
    · intro x y
      simpa using congr_arg (fun g => g x y) h
    · obtain ⟨ ρ, ⟨ hρ₁, hρ₂ ⟩, hρ₃ ⟩ := h_contra;
      have := @ker_eq_or_top_of_simple' R K _ _ f ‹_› hf ρ hρ₁;
      intro x y
      simp_all only [or_false, not_false_eq_true, Std.le_refl, not_true_eq_false];
  -- f は全射かつ半環準同型なので f(0.R) = 0.K, f(1.R) = 1.K より K は 0.K と 1.K を元として持つ。
  -- もしも ker f が 極大の合同関係でなければ f　は定数写像であることを h_all で示した。
  -- f が定数写像ならば f は全射であるため K は一点集合より 0.K = 1.K
  -- しかしこれは K が DivisionSemiring より 0.K ≠ 1.K であることに矛盾。
  -- よって ker f は極大の合同関係である。
  exact absurd ( hf 0 ) ( by obtain ⟨ x, hx ⟩ := hf 1; specialize h_all x 0; aesop )
