module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.RingTheory.Ideal.Operations

public import Mathlib.RingTheory.Congruence.Hom

variable {R K} [Semiring R] [DivisionSemiring K] (f : R →+* K) (hf : Function.Surjective f)

-- DivisionSemiring K上の環合同c ∈ RingCon Kは自明な２つの合同だけである．
-- def RingConSimple : Prop :=
--   ∀ c : RingCon K, c = ⊥ ∨ c = ⊤

#check RingCon
class RingConSimple (K : Type*) [DivisionSemiring K] where
  ringcon_simple := ∀ c : RingCon K, c = ⊥ ∨ c = ⊤

-- [NonAssocSemiring R] (c : RingCon R)
-- RingCon.mk' : R →+* c.Quotient
#check RingCon.mk' (RingCon.ker f)


-- 1. 半環R,単純な剰余半環K(半環Kの合同がRingCon K = {Δ,K×K};Δ:={a~a}の二つのみである),
-- 全射半環準同型f : R →+* Kに対して， R ⧸ ker f ≅+* K


--      f (surjective)
-- R ------> K
--  \        ↑
--   \       |
--    \      |
--   π \     | kerLift f (bijective)
--      \    |
--       \   |
--        ↘  |
--       R ⧸ ker f




-- def π : R → R ⧸ ker f
example : R →+* (RingCon.ker f).Quotient := (RingCon.ker f).mk'

-- def kerLift : R ⧸ ker f → K
example : (RingCon.ker f).Quotient →+* K :=
  RingCon.lift (RingCon.ker f) f le_rfl

#check RingCon.quotientKerEquivOfSurjective

-- f : M →+* Pが全射ならば，M ⧸ ker f ≃+* P
noncomputable def firstIsomorphismTheorem : (RingCon.ker f).Quotient ≃+* K :=
  RingCon.quotientKerEquivOfSurjective f hf

#check Equiv.symm
#print Equiv
#check OrderIso.surjective

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
      · intro hab
        sorry
      · intro hab
        apply RingCon.comap_mono
        exact hab
  }


-- 順序に関して同型と示すことができなかったので
-- 単にR⧸kerf ≃+* K ⇒ RingCon(R⧸kerf) ≃ RingCon(K)を述べる
noncomputable def conKerIsomorphismTheorem : RingCon (RingCon.ker f).Quotient ≃ RingCon K := by
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
  }

-- 2. 半環R,∀θ ∈ Con R, {ρ ∈ Con R | θ ⊆ ρ} ≃o Con R⧸θ
-- つまり包含関係に関する順序を保つような，合同関係の全単射を与えることができる．
def ringConOrderIsoTheorem (θ : RingCon R) : {ρ : RingCon R // θ ≤ ρ} ≃o RingCon (RingCon.Quotient θ) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' {c d} := by sorry


noncomputable def ringConKerOrderIsoTheorem : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃o
    RingCon ((RingCon.ker f).Quotient) := by
  let e := firstIsomorphismTheorem f hf
  refine {
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' {c d} := by sorry
  }


noncomputable def r_to_rQuot_mono [Preorder R] [Preorder K] : R →o K := by
  let e := firstIsomorphismTheorem f hf
  refine {
    toFun := e ∘ (RingCon.ker f).mk'
    monotone' := by
      intro a b hab
      simp only [RingCon.coe_mk', Function.comp_apply]
      sorry
  }

--　順序についての同型を示せていないので、単なる同型を示す
noncomputable def ringConKerIsoTheorem'' : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃
  RingCon ((RingCon.ker f).Quotient)  := by
  refine {
    toFun := sorry
    invFun := fun C => ⟨RingCon.comap C (RingCon.ker f).mk',sorry ⟩
    left_inv := by sorry
    right_inv := by sorry
  }

noncomputable def ringConKerIsoTheorem' : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃
  RingCon K := by
  let e := conKerIsomorphismTheorem f hf
  refine {
    toFun := sorry
    invFun := sorry
    left_inv := by sorry
    right_inv := by sorry
  }


noncomputable def ringConKerIsoTheorem'''' : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃ RingCon K := by
  have h_main : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃ RingCon ((RingCon.ker f).Quotient) := by
    classical
    -- Define the forward direction: map each congruence ρ to the kernel of the quotient map
    let F : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} → RingCon ((RingCon.ker f).Quotient) := fun ⟨ρ, hρ⟩ =>
      (RingCon.comap (f.quotientKerMap ρ)) (by
        -- Show that the preimage of the kernel under the quotient map is a congruence on the quotient ring
        exact RingCon.ker_le_comap _ _
      )
    -- Define the inverse direction: map each congruence σ to its preimage under the natural projection
    let G : RingCon ((RingCon.ker f).Quotient) → {ρ : RingCon R // (RingCon.ker f) ≤ ρ} := fun σ =>
      ⟨(RingCon.comap (f.quotientKerMap σ)), by
        -- Show that the preimage of σ contains the kernel of f
        have h₁ : (RingCon.ker f) ≤ RingCon.comap (f.quotientKerMap σ) := by
          intro x hx
          simp only [RingCon.mem_comap, Set.mem_preimage] at hx ⊢
          -- Since x is in the kernel of f, f(x) = 0, and we need to show that x is in the preimage of σ
          have h₂ : (f.quotientKerMap σ).map (x : R) = (f.quotientKerMap σ).map (0 : R) := by
            -- Since f(x) = 0, we have (x + ker f)/ker f = 0/ker f in the quotient ring
            simp_all [RingHom.ext_iff]
            <;>
              aesop
          simpa using h₂
        exact h₁⟩
    -- Show that F and G are inverses of each other
    have hF : Function.Injective F := by
      intro a b hab
      cases' a with ρ hρ
      cases' b with σ hσ
      simp_all [F]
      <;>
        (try { aesop }) <;>
          (try {
            ext x y
            simp_all [RingCon.comap, RingCon.mem_comap]
            <;>
              aesop
          })
      <;>
        (try {
          have h₁ : ρ = σ := by
            -- Use the fact that the kernels are equal to show that the congruences are equal
            apply le_antisymm
            · -- Show ρ ≤ σ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aesop
            · -- Show σ ≤ ρ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aesop
          simp_all
        })
    have hG : Function.Injective G := by
      intro a b hab
      cases' a with σ hσ
      cases' b with τ hτ
      simp_all [G]
      <;>
        (try { aesop }) <;>
          (try {
            ext x y
            simp_all [RingCon.comap, RingCon.mem_comap]
            <;>
              aesop
          })
      <;>
        (try {
          have h₁ : σ = τ := by
            -- Use the fact that the preimages are equal to show that the congruences are equal
            apply le_antisymm
            · -- Show σ ≤ τ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aes/simp_all [RingHom.ext_iff]
              <;>
                aesop
            · -- Show τ ≤ σ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aesop
          simp_all
        })
    have hFG : ∀ (x : {ρ : RingCon R // (RingCon.ker f) ≤ ρ}), G (F x) = x := by
      intro x
      cases' x with ρ hρ
      simp [F, G]
      <;>
        (try {
          ext a b
          simp_all [RingCon.comap, RingCon.mem_comap]
          <;>
            aesop
        })
      <;>
        (try {
          have h₁ : ρ = (RingCon.comap (f.quotientKerMap ρ)) := by
            -- Show that the preimage of ρ under the quotient map is equal to ρ itself
            apply le_antisymm
            · -- Show ρ ≤ preimage of ρ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aesop
            · -- Show preimage of ρ ≤ ρ
              intro a b hab
              simp_all [RingCon.comap, RingCon.mem_comap]
              <;>
                aesop
          simp_all
        })
    have hGF : ∀ (x : RingCon ((RingCon.ker f).Quotient)), F (G x) = x := by
      intro x
      simp [F, G]
      <;>
        (try {
          ext a b
          simp_all [RingCon.comap, RingCon.mem_comap]
          <;>
            aesop
        })
      <;>
        (try {
          have h₁ : x = x := rfl
          simp_all
        })
    -- Construct the equivalence using the inverses
    exact {
      toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF
    }

  have h_final : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃ RingCon K := by
    -- Use the first isomorphism theorem to get an equivalence between the quotient ring and K
    have h₁ : (RingCon.ker f).Quotient ≃+* K := by
      apply firstIsomorphismTheorem
    -- Use the fact that the congruences of two isomorphic rings are in bijection
    have h₂ : RingCon ((RingCon.ker f).Quotient) ≃ RingCon K := by
      -- Since (ker f).quotient and K are isomorphic, their congruences are also isomorphic
      let e : (RingCon.ker f).Quotient ≃+* K := h₁
      have h₃ : RingCon ((RingCon.ker f).Quotient) ≃ RingCon K := by
        -- Use the fact that the congruences of two isomorphic rings are in bijection
        exact RingCon.equivOfRingEquiv e
      exact h₃
    -- Compose the equivalences to get the final result
    have h₃ : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃ RingCon K := by
      calc
        {ρ : RingCon R // (RingCon.ker f) ≤ ρ} ≃ RingCon ((RingCon.ker f).Quotient) := h_main
        _ ≃ RingCon K := h₂
    exact h₃

  apply h_final


-- 3. Con K = Con R ⧸ ker f = {Δ,K×K} ≃o {ρ ∈ Con R | ker f ⊆ ρ}
-- 元は2つしか存在せず，順序を保つので，ρ = ker f または ρ = R × R のみ．
-- ここで，ker f ⊆ ρ より，ker f ⊆ ker f または ker f ⊆ R × R.
-- つまり，ker f を含む合同は ker f または R × R のみである．
-- これはker fが真の合同の中で最大であることを意味する．

theorem ringConKerOrders [RingConSimple K] : {ρ : RingCon R // (RingCon.ker f) ≤ ρ} → ρ = invFun ⊥ ∨ ρ = invFun ⊤
  := sorry

-- R → c.Quotient
#check RingCon.mk'

-- c.Quotient → P
#check RingCon.lift

-- R → (RingCon.ker f).Quotient


-- ほしいもの
-- RingCon R → RingCon (RingCon.ker f).Quotient
def ringConQuot_mk : RingCon R → RingCon (RingCon.ker f).Quotient :=
  fun C => sorry --RingCon.comap C ((RingCon.ker f).lift)


-- RingCon.comap : (RingCon M' ,(f : M →+* M')) → RingCon M
-- C : RingCon (RingCon.ker f).Quotient
-- (RingCon.ker f).mk' : R → (RingCon.ker f).Quotient
-- RingCon.comap C ((RingCon.ker f).mk') : RingCon R
def ringConQuot_lift : RingCon (RingCon.ker f).Quotient → RingCon R :=
  fun C => RingCon.comap C ((RingCon.ker f).mk')

theorem ker_eq_or_top_of_simple'
  [RingConSimple K] (ρ : RingCon R) (hρ : RingCon.ker f ≤ ρ) :
  ρ = ⊥ ∨ ρ = ⊤ := by sorry

theorem ker_eq_or_top_of_simple
  [RingConSimple K] (ρ : RingCon R) (hρ : RingCon.ker f ≤ ρ) :
  ρ = RingCon.ker f ∨ ρ = ⊤ := by sorry

theorem ker_isMaximal [RingConSimple K] : IsCoatom (RingCon.ker f) := by
  sorry



--アリストテレスに聞く Aristote API

-- CommRingの中のRinghom.ker に関してのkerとイデアルの包含関係について確認する
