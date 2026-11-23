module

public import CoEndoYonedaAndPurity.Basic

@[expose] public section

namespace CoEndoYonedaAndPurity

open CategoryTheory
open Opposite
open Functor

universe u

/-!
## 1. Basic Functional Category Lemmas

- `FF_hom_id`, `FF_hom_comp`
- `lemma_g : ∀ (t : T), g FF t = 𝟙 (FF.obj T)`
- `lemma_T : g FF tt_star = 𝟙 (FF.obj T)`
- `η_eq_T : η.app (FF.obj T) = g FF (g FF tt_star)`
-/

section BasicFunctionalCategoryLemmas

variable {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)

@[simp]
theorem FF_hom_eq {Z Y : Type u} (f : Z → Y) :
    FF_hom FF f = FF.map (TypeCat.ofHom f) :=
  rfl

@[simp]
theorem FF_hom_id (Z : Type u) :
    FF_hom FF (fun z : Z => z) = 𝟙 (FF.obj Z) := by
  change FF.map (𝟙 Z) = 𝟙 (FF.obj Z)
  exact FF.map_id Z

@[simp]
theorem FF_hom_comp {Z Y X : Type u} (f : Z → Y) (h : Y → X) :
    FF_hom FF f ≫ FF_hom FF h = FF_hom FF (fun z => h (f z)) := by
  dsimp only [FF_hom]
  rw [← FF.map_comp]
  rfl

@[simp]
theorem CYEF_map_eq {Z Y X : C} (y2x : Y ⟶ X) :
    (CYEF FF Z).map y2x = FF_hom FF (fun (z2y : Z ⟶ Y) => z2y ≫ y2x) :=
  rfl

@[simp]
theorem G_map_eq {Y X : C} (y2x : Y ⟶ X) :
    (G FF).map y2x = FF_hom FF (fun (fft2y : FF.obj T ⟶ Y) => fft2y ≫ y2x) :=
  rfl

@[simp]
theorem lemma_g (t : T) : g FF t = 𝟙 (FF.obj T) := by
  have h_fun : (fun (_ : T) => t) = (fun z : T => z) := by
    funext z
    cases t
    cases z
    rfl
  dsimp only [g]
  rw [h_fun]
  exact FF_hom_id FF T

@[simp]
theorem lemma_T : g FF tt_star = 𝟙 (FF.obj T) :=
  lemma_g FF tt_star

theorem η_eq_T_lemma [BasicFunctionalCategory C FF] :
    (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) =
      g FF (g FF tt_star) := by
  have h1 := BasicFunctionalCategory.η_eq (C := C) (FF := FF) T
  have h_g_T : (g FF (Z := T)) = (fun (_ : T) => g FF tt_star) := by
    funext t
    cases t
    rfl
  rw [h1, h_g_T]
  rfl

end BasicFunctionalCategoryLemmas

/-!
## 2. CoEndoYoneda Isomorphism (`CoEndoYonedaIso`)

We establish the isomorphism
`coEndoYonedaIso : (CYEF FF Z ⟶ G_EF FF EF) ≃ (CYF_G_EF FF EF).obj Z`
between natural transformations `NatTrans (CYEF Z) (G ∘F EF)` and elements of
`(CYF (FF.obj T) ∘F (G ∘F EF)).obj Z`.
-/

section CoEndoYonedaIsoSection

variable {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)

theorem fz_to_τz_commute_lemma {EF : C ⥤ C} {Z Y X : C}
    (fz : (CYF_G_EF FF EF).obj Z) (y2x : Y ⟶ X) (z2y : Z ⟶ Y) :
    fz ≫ (G_EF FF EF).map (z2y ≫ y2x) =
      (fz ≫ (G_EF FF EF).map z2y) ≫ (G_EF FF EF).map y2x := by
  rw [(G_EF FF EF).map_comp, Category.assoc]

theorem to_from_proof_lemma {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) :
    fz ≫ (G_EF FF EF).map (𝟙 Z) = fz ≫ 𝟙 ((G_EF FF EF).obj Z) := by
  rw [(G_EF FF EF).map_id]

variable [FunctionalCategory C FF]

theorem fz_to_τz_commute_lemma_main {EF : C ⥤ C} {Z Y X : C}
    (fz : (CYF_G_EF FF EF).obj Z) (y2x : Y ⟶ X) :
    (CYEF FF Z).map y2x ≫ fz_to_τz_hom FF fz X =
      fz_to_τz_hom FF fz Y ≫ (G_EF FF EF).map y2x := by
  dsimp only [fz_to_τz_hom]
  rw [← Category.assoc]
  rw [CYEF_map_eq FF y2x]
  rw [FF_hom_comp FF (fun z2y : Z ⟶ Y => z2y ≫ y2x) (fz_to_ay_to_z2y_to_fft2gefy FF fz X)]
  have h_comm :
      (fun z2y : Z ⟶ Y => fz_to_ay_to_z2y_to_fft2gefy FF fz X (z2y ≫ y2x)) =
        (fun z2y : Z ⟶ Y => (fz_to_ay_to_z2y_to_fft2gefy FF fz Y z2y) ≫ (G_EF FF EF).map y2x) := by
    funext z2y
    exact fz_to_τz_commute_lemma FF fz y2x z2y
  rw [h_comm]
  rw [← FF_hom_comp FF (fz_to_ay_to_z2y_to_fft2gefy FF fz Y)
        (fun fft2gefy => fft2gefy ≫ (G_EF FF EF).map y2x)]
  rw [Category.assoc]
  have h_mu_nat := (FunctionalCategory.μ (C := C) (FF := FF)).naturality (EF.map y2x)
  erw [h_mu_nat, ← Category.assoc]
  rfl

@[simps]
def fz_to_τz {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) :
    CYEF FF Z ⟶ G_EF FF EF where
  app Y := fz_to_τz_hom FF fz Y
  naturality _ _ y2x := fz_to_τz_commute_lemma_main FF fz y2x

theorem to_from_proof {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) :
    τz_to_fz FF (fz_to_τz FF fz) = fz := by
  dsimp only [τz_to_fz, fz_to_τz, fz_to_τz_hom, fft2cyefz, g]
  rw [← Category.assoc]
  rw [FF_hom_comp FF (fun _ : T => 𝟙 Z) (fz_to_ay_to_z2y_to_fft2gefy FF fz Z)]
  have h1 :
      (fun _ : T => fz_to_ay_to_z2y_to_fft2gefy FF fz Z (𝟙 Z)) =
        (fun t : T => g FF t ≫ fz) := by
    funext t
    dsimp only [fz_to_ay_to_z2y_to_fft2gefy]
    erw [to_from_proof_lemma FF fz, Category.comp_id, lemma_g FF t, Category.id_comp]
  rw [h1]
  rw [← FF_hom_comp FF (g FF (Z := T)) (fun fft2fft : FF.obj T ⟶ FF.obj T => fft2fft ≫ fz)]
  have h_eta_T := BasicFunctionalCategory.η_eq (C := C) (FF := FF) T
  rw [← h_eta_T]
  have h_G_fz :
      FF_hom FF (fun fft2fft : FF.obj T ⟶ FF.obj T => fft2fft ≫ fz) =
        (G FF).map fz := rfl
  rw [h_G_fz]
  have h_nat_eta := (BasicFunctionalCategory.η (C := C) (FF := FF)).naturality fz
  dsimp only [Functor.id_map] at h_nat_eta
  rw [← h_nat_eta]
  rw [Category.assoc]
  rw [FunctionalCategory.id_left (C := C) (FF := FF) (EF.obj Z)]
  exact Category.comp_id fz

theorem from_to_proof_app {EF : C ⥤ C} {Z : C}
    (τz : CYEF FF Z ⟶ G_EF FF EF) (Y : C) :
    fz_to_τz_hom FF (τz_to_fz FF τz) Y = τz.app Y := by
  dsimp only [fz_to_τz_hom, τz_to_fz]
  have h_inner :
      fz_to_ay_to_z2y_to_fft2gefy FF (fft2cyefz FF Z ≫ τz.app Z) Y =
        (fun z2y : Z ⟶ Y => g FF z2y ≫ τz.app Y) := by
    funext z2y
    dsimp only [fz_to_ay_to_z2y_to_fft2gefy]
    rw [Category.assoc]
    rw [← τz.naturality z2y]
    rw [← Category.assoc]
    congr 1
    dsimp only [fft2cyefz, g]
    rw [CYEF_map_eq FF z2y]
    rw [FF_hom_comp FF (fun _ : T => 𝟙 Z) (fun z2z : Z ⟶ Z => z2z ≫ z2y)]
    congr 1
    funext _
    exact Category.id_comp z2y
  rw [h_inner]
  rw [← FF_hom_comp FF (g FF (Z := (Z ⟶ Y)))
        (fun fft2cyefy : FF.obj T ⟶ (CYEF FF Z).obj Y => fft2cyefy ≫ τz.app Y)]
  have h_eta := BasicFunctionalCategory.η_eq (C := C) (FF := FF) (Z ⟶ Y)
  rw [← h_eta]
  have h_G_map :
      FF_hom FF (fun fft2cyefy : FF.obj T ⟶ (CYEF FF Z).obj Y => fft2cyefy ≫ τz.app Y) =
        (G FF).map (τz.app Y) := rfl
  rw [h_G_map]
  have h_nat := (BasicFunctionalCategory.η (C := C) (FF := FF)).naturality (τz.app Y)
  dsimp only [Functor.id_map] at h_nat
  erw [← h_nat, Category.assoc]
  erw [FunctionalCategory.id_left (C := C) (FF := FF) (EF.obj Y)]
  exact Category.comp_id (τz.app Y)

theorem from_to_proof {EF : C ⥤ C} {Z : C} (τz : CYEF FF Z ⟶ G_EF FF EF) :
    fz_to_τz FF (τz_to_fz FF τz) = τz := by
  ext Y
  exact from_to_proof_app FF τz Y

def coEndoYonedaIso (EF : C ⥤ C) (Z : C) :
    (CYEF FF Z ⟶ G_EF FF EF) ≃ (CYF_G_EF FF EF).obj Z where
  toFun := τz_to_fz FF
  invFun := fz_to_τz FF
  left_inv := from_to_proof FF
  right_inv := to_from_proof FF

end CoEndoYonedaIsoSection

/-!
## 3. Connecting the CoEndoYoneda Iso to `η` at `FF.obj T` (`UniversalOriginOfEta`)

Applying the forward map of `coEndoYonedaIso`
(for `EF = 𝟭 C` and `Z = FF.obj T`) to the identity natural transformation on `G FF` produces
`ηFFT : FF.obj T ⟶ (G FF).obj (FF.obj T)`, which coincides with `η.app (FF.obj T)` via `η_eq_T`.
-/

section UniversalOriginOfEta

variable {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)

theorem ηFFT_is_η_at_FFT_lemma [BasicFunctionalCategory C FF] :
    ηFFT FF = (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) := by
  calc
    ηFFT FF = fft2cyefz FF (FF.obj T) ≫ 𝟙 ((G FF).obj (FF.obj T)) := rfl
    _ = g FF (𝟙 (FF.obj T)) := Category.comp_id _
    _ = g FF (g FF tt_star) := congrArg (g FF) (lemma_T FF).symm
    _ = (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) := (η_eq_T_lemma FF).symm

end UniversalOriginOfEta

/-!
## 4. Canonical Concrete Instance: `SET` (`Type u`) as a Functional Category

In `Type u` with `FF = 𝟭 (Type u)`, both `η` and `μ` are defined directly and `η_eq`, `η_eq_T`,
and `id_left` hold definitionally by `rfl`.
-/

section SetFunctionalCategory

instance setBasicFunctionalCategory : BasicFunctionalCategory (Type u) (𝟭 (Type u)) where
  η := {
    app := fun Z => TypeCat.ofHom (fun (z : Z) => TypeCat.ofHom (fun (_ : T) => z))
    naturality := fun _ _ _ => rfl
  }
  η_eq := fun _ => rfl

instance setFunctionalCategory : FunctionalCategory (Type u) (𝟭 (Type u)) where
  toBasicFunctionalCategory := setBasicFunctionalCategory
  μ := {
    app := fun Z => TypeCat.ofHom (fun (h : T ⟶ (T ⟶ Z)) => TypeCat.ofHom (fun (t : T) => h t t))
    naturality := fun _ _ _ => rfl
  }
  id_left := fun _ => rfl

def setCoEndoYonedaIso (EF : Type u ⥤ Type u) (Z : Type u) :
    (CYEF (𝟭 (Type u)) Z ⟶ G_EF (𝟭 (Type u)) EF) ≃ (CYF_G_EF (𝟭 (Type u)) EF).obj Z :=
  coEndoYonedaIso (𝟭 (Type u)) EF Z

end SetFunctionalCategory

/-!
## 5. Purity Theorems (`PurityTheorems`)

1. `idempotent_iff_isPure`: `Idempotent M ↔ IsPure M`
2. `kleisliBasicFunctionalCategory_to_idempotent` and
   `idempotent_to_kleisliBasicFunctionalCategory`, yielding
   `kleisliBasicFunctionalCategory_iff_idempotent`:
   `Nonempty (KleisliBasicFunctionalCategory M) ↔ Idempotent M`
   Note that in the `to` direction, only `η_eq_T` (at the terminal object `T`) is used to derive
   idempotency, whereas in the `from` direction, idempotency yields the full parametric `η_eq`
   by `rfl`!
3. `isPure_implies_monadicTerminalTypeSubSingleton`:
   `IsPure M → MonadicTerminalTypeSubSingleton M` (and `Subsingleton (M T)`).
-/

section PurityTheorems

variable (M : Type u → Type u) [Monad M] [LawfulMonad M]

theorem idempotent_iff_isPure_lemma : Idempotent M ↔ IsPure M := by
  constructor
  · intro h_idem
    refine ⟨fun {Z} mz => ?_⟩
    have h_bind : (mz >>= ((pure : M Z → M (M Z)) ∘ (pure : Z → M Z))) = (pure <$> mz : M (M Z)) := by
      exact bind_pure_comp pure mz
    rw [h_bind]
    exact h_idem.idempotent mz
  · intro h_pure
    refine ⟨fun {Z} mz => ?_⟩
    have h_bind : (mz >>= ((pure : M Z → M (M Z)) ∘ (pure : Z → M Z))) = (pure <$> mz : M (M Z)) := by
      exact bind_pure_comp pure mz
    rw [← h_bind]
    exact h_pure.enforcingPurity mz

/-- Every `KleisliBasicFunctionalCategory M` implies `Idempotent M`, using only `η_eq_T` and the
naturality of `η`. -/
theorem kleisliBasicFunctionalCategory_to_idempotent
    (kfc : KleisliBasicFunctionalCategory M) : Idempotent M := by
  have : BasicFunctionalCategory (KleisliCat M) (KFF M) := kfc
  let ηK : ∀ (W : Type u), W → M (T → M W) :=
    fun W => (BasicFunctionalCategory.η (C := KleisliCat M) (FF := KFF M)).app ((KFF M).obj W)
  refine ⟨fun {Z} mz => ?_⟩
  -- `eval_lemma` (lines 848–873): `∀ {W} (mw : M W), (mw >>= ηK W) = pure (fun _ => mw)`
  have eval_lemma : ∀ {W : Type u} (mw : M W),
      (mw >>= ηK W) = (pure (fun (_ : T) => mw) : M (T → M W)) := by
    intro W mw
    let t_to_mw : (KFF M).obj T ⟶ (KFF M).obj W := fun (_ : T) => mw
    have h_nat :=
      (BasicFunctionalCategory.η (C := KleisliCat M) (FF := KFF M)).naturality t_to_mw
    have h_nat_tt := congrFun h_nat tt_star
    have h_lhs_eval :
        ((𝟭 (KleisliCat M)).map t_to_mw ≫
          (BasicFunctionalCategory.η (C := KleisliCat M) (FF := KFF M)).app ((KFF M).obj W)) tt_star =
          (mw >>= ηK W) := rfl
    have h_eta_T := η_eq_T_lemma (C := KleisliCat M) (FF := KFF M)
    have h_eta_T_tt :
        (ηK T tt_star : M (T → M T)) =
          (pure (fun (_ : T) => (pure tt_star : M T)) : M (T → M T)) :=
      congrFun h_eta_T tt_star
    have left_eq :
        (((BasicFunctionalCategory.η (C := KleisliCat M) (FF := KFF M)).app ((KFF M).obj T) ≫
          (G (KFF M)).map t_to_mw) tt_star) =
          (pure (fun (_ : T) => mw) : M (T → M W)) := by
      have h_comp :
          (((BasicFunctionalCategory.η (C := KleisliCat M) (FF := KFF M)).app ((KFF M).obj T) ≫
            (G (KFF M)).map t_to_mw) tt_star) =
          ((ηK T tt_star : M (T → M T)) >>= fun (h : T → M T) =>
            (pure (fun t : T => h t >>= (fun (_ : T) => mw)) : M (T → M W))) := rfl
      rw [h_comp, h_eta_T_tt, pure_bind]
      congr 1
      funext t
      exact pure_bind tt_star (fun (_ : T) => mw)
    rw [← h_lhs_eval, h_nat_tt, left_eq]
  -- `mgz→mmz` (lines 875–876)
  let mgz_to_mmz : M (T → M Z) → M (M Z) :=
    fun m_t2mz => m_t2mz >>= fun t2mz => pure (t2mz tt_star)
  -- `idempotent_lemma` (lines 878–890)
  have idempotent_lemma : ∀ (z : Z),
      mgz_to_mmz (ηK Z z) = (pure (pure z : M Z) : M (M Z)) := by
    intro z
    calc
      mgz_to_mmz (ηK Z z)
        = mgz_to_mmz ((pure z : M Z) >>= ηK Z) := by
          rw [pure_bind]
      _ = mgz_to_mmz (pure (fun (_ : T) => (pure z : M Z))) := by
          rw [eval_lemma (pure z)]
      _ = (pure (pure z : M Z) : M (M Z)) := by
          dsimp only [mgz_to_mmz]
          rw [pure_bind]
  -- Main chain (lines 893–904)
  calc
    (pure <$> mz : M (M Z))
      = (mz >>= fun z => (pure (pure z : M Z) : M (M Z))) := by
        exact (bind_pure_comp pure mz).symm
    _ = (mz >>= fun z => mgz_to_mmz (ηK Z z)) := by
        congr 1
        funext z
        exact (idempotent_lemma z).symm
    _ = mgz_to_mmz (mz >>= ηK Z) := by
        dsimp only [mgz_to_mmz]
        rw [bind_assoc]
    _ = mgz_to_mmz (pure (fun (_ : T) => mz)) := by
        rw [eval_lemma mz]
    _ = (pure mz : M (M Z)) := by
        dsimp only [mgz_to_mmz]
        rw [pure_bind]

/-- Backward direction `from` of `idempotent-equiv-kleisli-basic-functional-category`
    Every `Idempotent M` induces a `KleisliBasicFunctionalCategory M`, where `η_eq` holds by
    `rfl`. -/
@[instance_reducible]
def idempotent_to_kleisliBasicFunctionalCategory
    (h_idem : Idempotent M) : KleisliBasicFunctionalCategory M := by
  -- `mApply_lemma` (lines 914–938)
  have mApply_lemma : ∀ {Z : Type u} (mz : M Z),
      (mz >>= fun z => (pure (fun (_ : T) => (pure z : M Z)) : M (T → M Z))) =
        (pure (fun (_ : T) => mz) : M (T → M Z)) := by
    intro Z mz
    let mz_to_mgmz : M Z → M (T → M Z) := fun m => pure (fun (_ : T) => m)
    have h_step1 :
        (fun z : Z => (pure (fun (_ : T) => (pure z : M Z)) : M (T → M Z))) =
          (fun z : Z => (pure (pure z : M Z) : M (M Z)) >>= mz_to_mgmz) := by
      funext z
      dsimp only [mz_to_mgmz]
      rw [pure_bind]
    have h_bind_map :
        ((mz >>= fun z => (pure (pure z : M Z) : M (M Z))) >>= mz_to_mgmz) =
          ((pure <$> mz : M (M Z)) >>= mz_to_mgmz) :=
      congrArg (· >>= mz_to_mgmz) (bind_pure_comp pure mz)
    calc
      (mz >>= fun z => (pure (fun (_ : T) => (pure z : M Z)) : M (T → M Z)))
        = (mz >>= fun z => ((pure (pure z : M Z) : M (M Z)) >>= mz_to_mgmz)) := by
          rw [h_step1]
      _ = ((mz >>= fun z => (pure (pure z : M Z) : M (M Z))) >>= mz_to_mgmz) := by
          rw [← bind_assoc]
      _ = ((pure <$> mz : M (M Z)) >>= mz_to_mgmz) := h_bind_map
      _ = ((pure mz : M (M Z)) >>= mz_to_mgmz) := by
          rw [h_idem.idempotent mz]
      _ = (pure (fun (_ : T) => mz) : M (T → M Z)) := by
          dsimp only [mz_to_mgmz]
          rw [pure_bind]
  -- `comm` (lines 939–959)
  have comm : ∀ {Y X : Type u} (y_to_mx : Y → M X) (y : Y),
      (y_to_mx y >>= fun x => (pure (fun (_ : T) => (pure x : M X)) : M (T → M X))) =
        ((pure (fun (_ : T) => (pure y : M Y)) : M (T → M Y)) >>=
          fun gmy => (pure (fun t : T => gmy t >>= y_to_mx) : M (T → M X))) := by
    intro Y X y_to_mx y
    have h_rhs :
        ((pure (fun (_ : T) => (pure y : M Y)) : M (T → M Y)) >>=
          fun gmy => (pure (fun t : T => gmy t >>= y_to_mx) : M (T → M X))) =
          (pure (fun (_ : T) => ((pure y : M Y) >>= y_to_mx)) : M (T → M X)) := by
      exact pure_bind (fun (_ : T) => (pure y : M Y))
        (fun gmy => (pure (fun t : T => gmy t >>= y_to_mx) : M (T → M X)))
    calc
      (y_to_mx y >>= fun x => (pure (fun (_ : T) => (pure x : M X)) : M (T → M X)))
        = (pure (fun (_ : T) => y_to_mx y) : M (T → M X)) := mApply_lemma (y_to_mx y)
      _ = (pure (fun (_ : T) => ((pure y : M Y) >>= y_to_mx)) : M (T → M X)) := by
          congr 1
          funext _
          exact (pure_bind y y_to_mx).symm
      _ = ((pure (fun (_ : T) => (pure y : M Y)) : M (T → M Y)) >>=
            fun gmy => (pure (fun t : T => gmy t >>= y_to_mx) : M (T → M X))) := h_rhs.symm
  exact {
    η := {
      app := fun Y => fun (y : Y) => (pure (fun (_ : T) => (pure y : M Y)) : M (T → M Y))
      naturality := fun Y X y_to_mx => by
        ext y
        exact comm y_to_mx y
    }
    η_eq := fun _ => rfl
  }

/-- `is-pure-implies-monadic-terminal-type-subsingleton`
Direct equational derivation showing that `IsPure M` implies every `mt : M T` equals
`pure tt_star`. -/
theorem isPure_implies_monadicTerminalTypeSubSingleton_lemma
    (ep : IsPure M) : MonadicTerminalTypeSubSingleton M := by
  refine ⟨fun mt => ?_⟩
  let mmt_to_mt : M (M T) → M T := fun mmt => mmt >>= fun _ => pure tt_star
  have h_unit : (pure : T → M T) = (fun (_ : T) => pure tt_star) := by
    funext t
    cases t
    rfl
  have h_step :
      (fun (_ : T) => (pure tt_star : M T)) =
        (fun t : T => mmt_to_mt (((pure : M T → M (M T)) ∘ (pure : T → M T)) t)) := by
    funext t
    dsimp only [mmt_to_mt, Function.comp]
    rw [pure_bind]
  calc
    mt = (mt >>= (pure : T → M T)) := (bind_pure mt).symm
    _ = (mt >>= fun (_ : T) => pure tt_star) := by rw [h_unit]
    _ = (mt >>= fun t : T => mmt_to_mt (((pure : M T → M (M T)) ∘ (pure : T → M T)) t)) := by
        rw [h_step]
    _ = mmt_to_mt (mt >>= ((pure : M T → M (M T)) ∘ (pure : T → M T))) := by
        dsimp only [mmt_to_mt]
        rw [bind_assoc]
    _ = mmt_to_mt (pure mt) := by
        rw [ep.enforcingPurity mt]
    _ = pure tt_star := by
        dsimp only [mmt_to_mt]
        rw [pure_bind]

/-- Corollary: `IsPure M` implies `Subsingleton (M T)`. -/
theorem isPure_implies_subsingleton_M_T (ep : IsPure M) : Subsingleton (M T) := by
  have h := (isPure_implies_monadicTerminalTypeSubSingleton_lemma M ep).monadic_terminal_type_sub_singleton
  refine ⟨fun m1 m2 => ?_⟩
  rw [h m1, h m2]

end PurityTheorems

end CoEndoYonedaAndPurity
