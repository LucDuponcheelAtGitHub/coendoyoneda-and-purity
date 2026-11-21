module

public import CoEndoYonedaAndPurity

@[expose] public section

namespace CoEndoYonedaAndPurity

open CategoryTheory
open Opposite
open Functor

universe u

theorem η_eq_T {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [BasicFunctionalCategory C FF] :
    (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) =
      g FF (g FF tt_star) :=
  η_eq_T_lemma FF

theorem fz_to_τz_commute {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z Y X : C}
    (fz : (CYF_G_EF FF EF).obj Z) (y2x : Y ⟶ X) :
    (CYEF FF Z).map y2x ≫ fz_to_τz_hom FF fz X =
      fz_to_τz_hom FF fz Y ≫ (G_EF FF EF).map y2x :=
  fz_to_τz_commute_lemma_main FF fz y2x

theorem to_from_proof_hom {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) :
    fft2cyefz FF Z ≫ fz_to_τz_hom FF fz Z = fz :=
  to_from_proof FF fz

theorem from_to_proof' {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z : C}
    (τz : CYEF FF Z ⟶ G_EF FF EF) (Y : C) :
    fz_to_τz_hom FF (τz_to_fz FF τz) Y = τz.app Y :=
  from_to_proof_app FF τz Y

theorem ηFFT_is_η_at_FFT {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [BasicFunctionalCategory C FF] :
    ηFFT FF = (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) :=
  ηFFT_is_η_at_FFT_lemma FF

theorem set_is_functional_category :
    Nonempty (FunctionalCategory (Type u) (𝟭 (Type u))) :=
  ⟨setFunctionalCategory⟩

theorem idempotent_iff_isPure (M : Type u → Type u) [Monad M] [LawfulMonad M] :
    Idempotent M ↔ IsPure M :=
  idempotent_iff_isPure_lemma M

theorem kleisliBasicFunctionalCategory_iff_idempotent
    (M : Type u → Type u) [Monad M] [LawfulMonad M] :
    Nonempty (KleisliBasicFunctionalCategory M) ↔ Idempotent M :=
  ⟨fun ⟨kfc⟩ => kleisliBasicFunctionalCategory_to_idempotent M kfc,
   fun h_idem => ⟨idempotent_to_kleisliBasicFunctionalCategory M h_idem⟩⟩

theorem isPure_implies_monadicTerminalTypeSubSingleton
    (M : Type u → Type u) [Monad M] [LawfulMonad M]
    (ep : IsPure M) : MonadicTerminalTypeSubSingleton M :=
  isPure_implies_monadicTerminalTypeSubSingleton_lemma M ep

theorem maybe_not_pure : ¬ IsPure (Option : Type u → Type u) := by
  intro h
  have h1 := h.enforcingPurity (none : Option T)
  have h_lhs :
      ((none : Option T) >>= ((pure : Option T → Option (Option T)) ∘ (pure : T → Option T))) =
        none := rfl
  have h_rhs : (pure (none : Option T) : Option (Option T)) = some none := rfl
  rw [h_lhs, h_rhs] at h1
  nomatch h1

theorem list_not_pure : ¬ IsPure (List : Type u → Type u) := by
  intro h
  have h1 := h.enforcingPurity ([tt_star, tt_star] : List T)
  have h_lhs :
      (([tt_star, tt_star] : List T) >>= ((pure : List T → List (List T)) ∘ (pure : T → List T))) =
        [[tt_star], [tt_star]] := rfl
  have h_rhs : (pure ([tt_star, tt_star] : List T) : List (List T)) = [[tt_star, tt_star]] := rfl
  rw [h_lhs, h_rhs] at h1
  have h2 := (List.cons.inj h1).2
  nomatch h2

theorem read_purity_implies (R : Type u) :
    IsPure (Read R) → Subsingleton R := by
  intro h
  refine ⟨fun r1 r2 => ?_⟩
  have h1 := h.enforcingPurity (Z := R) (fun r : R => r)
  exact congrFun (congrFun h1 r1) r2

theorem write_purity_implies (W : Type u) [Monoid W] :
    IsPure (Write W) → Subsingleton W := by
  intro h
  have lemma_w : ∀ w : W, w = 1 := by
    intro w
    have h1 := h.enforcingPurity (Z := W) ((1 : W), w)
    have h_fst := congrArg Prod.fst h1
    have h_snd := congrArg Prod.snd h_fst
    exact h_snd.symm
  refine ⟨fun w1 w2 => ?_⟩
  rw [lemma_w w1, lemma_w w2]

theorem state_purity_implies (S : Type u) :
    IsPure (State S) → Subsingleton S := by
  intro h
  refine ⟨fun s1 s2 => ?_⟩
  have h1 := h.enforcingPurity (Z := S) (fun s : S => (s, s))
  have h_s1 := congrArg Prod.fst (congrFun h1 s1)
  have h_s2 := congrArg Prod.fst (congrFun h_s1 s2)
  exact h_s2

theorem cont_purity_implies (R : Type u) :
    IsPure (Cont R) → Subsingleton R := by
  intro h
  refine ⟨fun r1 r2 => ?_⟩
  have h1 := h.enforcingPurity (Z := R) (fun (_ : R → R) => r1)
  exact congrFun h1 (fun (_ : Cont R R) => r2)

theorem io_not_pure {E S : Type u} (e : E) (s : S) :
    ¬ IsPure (ErrorState E S) := by
  intro h
  let m : ErrorState E S T := fun s' => Sum.inl (e, s')
  have h1 := congrFun (h.enforcingPurity m) s
  have h_lhs :
      (m >>= ((pure : ErrorState E S T → ErrorState E S (ErrorState E S T)) ∘
        (pure : T → ErrorState E S T))) s = Sum.inl (e, s) := rfl
  have h_rhs : (pure m : ErrorState E S (ErrorState E S T)) s = Sum.inr (m, s) := rfl
  rw [h_lhs, h_rhs] at h1
  nomatch h1

end CoEndoYonedaAndPurity
