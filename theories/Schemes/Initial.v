Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.Hylomorphisms.

(** * Least fixed points: the default initial algebra *)
Section LFixDef.
  Context `(F : Cont Sh P).

  Unset Elimination Schemes.
  Inductive LFix : Type := LFix_in { LFix_out : App F LFix }.
  Set Elimination Schemes.

  Lemma LFix_rect [Q : LFix -> Type]
    : (forall x : App F LFix,
          (forall e : Pos F (shape x), Q (cont x e)) ->
          Q (LFix_in x))
      -> forall l : LFix, Q l.
  Proof. intros H; fix Ih 1; intros []; apply H; intros e; apply Ih. Defined.
  Lemma LFix_rec [Q : LFix -> Set]
    : (forall x : App F LFix,
          (forall e : Pos F (shape x), Q (cont x e)) ->
          Q (LFix_in x))
      -> forall l : LFix, Q l.
  Proof. intros H. apply LFix_rect, H. Defined.
  Lemma LFix_ind [Q : LFix -> Prop]
    : (forall x : App F LFix,
          (forall e : Pos F (shape x), Q (cont x e)) ->
          Q (LFix_in x))
      -> forall l : LFix, Q l.
  Proof. intros H. apply LFix_rect, H. Defined.

  Register Scheme LFix_rect as rect_dep for LFix.
  Register Scheme LFix_rec as rec_dep for LFix.
  Register Scheme LFix_ind as ind_dep for LFix.

  Fixpoint LFixR (x y : LFix) : Prop :=
    let f_x := LFix_out x in
    let f_y := LFix_out y in
    shape f_x =e shape f_y /\
      (forall e1 e2, val e1 = val e2 -> LFixR (cont f_x e1) (cont f_y e2)).

  Lemma LFixR_refl (x : LFix) : LFixR x x.
  Proof.
    induction x as [x Ih]; split; [reflexivity|].
    intros e1 e2 Heq; rewrite (elem_val_eq Heq); apply Ih.
  Qed.

  Lemma LFixR_sym (x y : LFix) : LFixR x y -> LFixR y x.
  Proof.
    revert y; induction x as [x Ih]; intros [y] [Sxy H]; split; auto with ffix.
  Qed.

  Lemma LFixR_trans (x y z : LFix) : LFixR x y -> LFixR y z -> LFixR x z.
  Proof.
    revert y z; induction x as [sx Ih]; intros [sy] [sz] [Sxy Exy] [Syz Eyz].
    split; [rewrite Sxy; trivial|].
    intros e1 e2 V1; destruct (elem_valid_irr Sxy e1) as [e3 V2].
    apply (Ih _ _ _ (Exy _ _ V2)), Eyz; rewrite <- V2; trivial.
  Qed.

  #[export] Instance LFix_Eq : setoid LFix :=
    {| eqRel := LFixR;
      e_refl := LFixR_refl;
      e_sym := LFixR_sym;
      e_trans := LFixR_trans;
    |}.
  #[export] Instance LFix_no_def_eq : NoDefEq LFix := {}.

  Lemma l_in_eq (x y : App F LFix) : x =e y -> LFix_in x =e LFix_in y.
  Proof. simpl. intros []; auto with ffix. Qed.

  Lemma l_out_eq (x y : LFix) : x =e y -> LFix_out x =e LFix_out y.
  Proof. destruct x, y. intros []. simpl. auto with ffix. Qed.

  Definition lfix_in : App F LFix ~> LFix := MkMorph l_in_eq.
  Definition lfix_out : LFix ~> App F LFix := MkMorph l_out_eq.

  Lemma lfix_in_out : lfix_in \o lfix_out =e id (A:=LFix).
  Proof.
    intros x; split; [reflexivity|].
    intros e1 e2 He; rewrite (elem_val_eq He); apply LFixR_refl.
  Qed.

  Lemma lfix_out_in : lfix_out \o lfix_in =e id (A:=App F LFix).
  Proof.
    intros x; split; [reflexivity|].
    intros e1 e2 He; rewrite (elem_val_eq He); apply LFixR_refl.
  Qed.
End LFixDef.

Arguments lfix_in {Sh Esh P F}.
Arguments lfix_out {Sh Esh P F}.

Lemma fin_out `{F : Cont Sh P} : forall x, RecF (lfix_out (F := F)) x.
Proof. induction x as [s Ih]. constructor. apply Ih. Defined.

Canonical Structure f_out `{F : Cont Sh P} : RCoalg F (LFix F) :=
  Rec (coalg := lfix_out) fin_out.
Arguments f_out & {Sh Esh P F}.
#[export] Hint Unfold f_out : canonical.

(** * Initial algebras
  *
  * An algebra [l_in] whose inverse [l_out] is a recursive coalgebra. It is
  * initial: [cata g := hylo g l_out] is the unique algebra morphism
  * ([cata_univ] is [hylo_uniq]). [LFix F] is the default one, finite trees
  * are another, and any two are isomorphic ([iso]). *)
#[mode = "- - - - - -"]
Class Initial `(F : Cont Sh P) (T : Type) `{eT : setoid T} :=
  { l_in : App F T ~> T;
    l_out : RCoalg F T;
    l_in_out : l_in \o l_out =e id;
    l_out_in : l_out \o l_in =e id
  }.
Arguments Initial {Sh Esh P} F T {eT}.
Arguments l_in & {Sh Esh P F T eT _}.
Arguments l_out & {Sh Esh P F T eT _}.
Arguments l_in_out {Sh Esh P F T eT _}.
Arguments l_out_in {Sh Esh P F T eT _}.

#[export] Instance LFix_initial `(F : Cont Sh P) : Initial F (LFix F) | 1 :=
  {| l_in := lfix_in;
     l_out := f_out;
     l_in_out := lfix_in_out (F := F);
     l_out_in := lfix_out_in (F := F)
  |}.

#[export] Instance FinGFix_initial `(F : Cont Sh P)
  : Initial F {x : GFix F | FinF x} | 10 :=
  {| l_in := lg_in;
     l_out := lg_out_c;
     l_in_out := lg_in_out (F := F);
     l_out_in := lg_out_in (F := F)
  |}.

Section Cata.
  Context `{F : Cont Sh P} `{eT : setoid T} `{!Initial F T}.

  Definition cata `{eA : setoid A} : Alg F A ~> T ~> A := flip hylo l_out.

  Lemma hylo_cata `{eA : setoid A} (g : Alg F A) : cata g =e hylo g l_out.
  Proof. reflexivity. Qed.

  Lemma cata_univ `{eA : setoid A} (g : Alg F A) (f : T ~> A)
    : f =e cata g <-> f =e g \o fmap f \o l_out.
  Proof. apply hylo_uniq. Qed.

  Lemma cata_univ_r `{eA : setoid A} (g : Alg F A) (f : T ~> A)
    : f =e g \o fmap f \o l_out -> f =e cata g.
  Proof. apply cata_univ. Qed.

  Lemma cata_univ_l `{eA : setoid A} (g : Alg F A) (f : T ~> A)
    : f =e cata g -> f =e g \o fmap f \o l_out.
  Proof. apply cata_univ. Qed.

  Corollary cata_unfold `{eA : setoid A} (g : Alg F A)
    : cata g =e g \o fmap (cata g) \o l_out.
  Proof. apply hylo_unr. Qed.

  Lemma cata_in `{eA : setoid A} (g : Alg F A)
    : cata g \o l_in =e g \o fmap (cata g).
  Proof.
    rewrite (cata_unfold g) at 1; intros x; cbn [app comp].
    apply app_eq, app_eq, (l_out_in x).
  Qed.

  Lemma cata_uniq `{eA : setoid A} (g : Alg F A) (f : T ~> A)
    : f \o l_in =e g \o fmap f -> f =e cata g.
  Proof.
    intros Hf; apply cata_univ; intros x; cbn [app comp].
    rewrite <- (l_in_out x) at 1; exact (Hf (l_out x)).
  Qed.

  Lemma cata_in_id : cata l_in =e id (A := T).
  Proof.
    symmetry; apply cata_univ; rewrite fmap_id, idKr, l_in_out; reflexivity.
  Qed.

  (** Anamorphisms into [T] *)
  Definition rana `{eA : setoid A} : RCoalg F A ~> A ~> T := hylo l_in.

  Lemma hylo_ana `{eA : setoid A} (h : RCoalg F A) : rana h =e hylo l_in h.
  Proof. reflexivity. Qed.

  Lemma rana_univ `{eA : setoid A} (h : RCoalg F A) (f : A ~> T)
    : f =e rana h <-> f =e l_in \o fmap f \o h.
  Proof. apply hylo_uniq. Qed.

  Corollary rana_unfold `{eA : setoid A} (h : RCoalg F A)
    : rana h =e l_in \o fmap (rana h) \o h.
  Proof. apply hylo_unr. Qed.

  Corollary cata_ana_hylo `{eA : setoid A} `{eB : setoid B}
    (g : Alg F B) (h : RCoalg F A)
    : cata g \o rana h =e hylo g h.
  Proof. apply hylo_fusion_l, cata_in. Qed.

  Lemma rana_ana `{eA : setoid A} (f : RCoalg F A)
    : ana (T := GFix F) f =e ana l_out \o rana f.
  Proof.
    symmetry; apply ana_univ.
    rewrite fmap_comp.
    ainsert (l_out_in (F := F) (T := T)) before (fmap (F := F) (rana f)).
    arewrite <- (ana_unfold (T := GFix F) (l_out (T := T))).
    arewrite <- (rana_unfold f).
    reflexivity.
  Qed.
End Cata.
Arguments cata & {Sh Esh P F T eT _ A eA}.
Arguments rana & {Sh Esh P F T eT _ A eA}.

(** Any two initial algebras are isomorphic *)
Section InitialIso.
  Context `{F : Cont Sh P} `{eT : setoid T} `{!Initial F T}
    `{eU : setoid U} `{!Initial F U}.

  Definition iso : T ~> U := cata l_in.

  Lemma iso_in : iso \o l_in =e l_in \o fmap iso.
  Proof. apply cata_in. Qed.

  Lemma iso_out : l_out \o iso =e fmap iso \o l_out.
  Proof.
    intros x; cbn [app comp]; unfold iso; rewrite (cata_unfold l_in x).
    exact (l_out_in _).
  Qed.

  (** Catamorphisms and anamorphisms do not depend on the initial algebra *)
  Lemma cata_iso `{eA : setoid A} (g : Alg F A) : cata g \o iso =e cata g.
  Proof.
    apply cata_uniq; intros x; cbn [app comp].
    rewrite (iso_in x); cbn [app comp]; exact (cata_in g _).
  Qed.

  Lemma iso_rana `{eA : setoid A} (h : RCoalg F A) : iso \o rana h =e rana h.
  Proof. apply hylo_fusion_l, iso_in. Qed.

  Lemma ana_out_iso : ana (T := GFix F) l_out \o iso =e ana l_out.
  Proof.
    apply ana_uniq; intros x; cbn [app comp].
    etransitivity; [apply (ana_out (T := GFix F) l_out)|]; cbn [app comp].
    etransitivity; [apply app_eq, (iso_out x)|]; reflexivity.
  Qed.
End InitialIso.
Arguments iso {Sh Esh P F} T {eT _} U {eU _}.
Arguments iso_in {Sh Esh P F} T {eT _} U {eU _} _.
Arguments iso_out {Sh Esh P F} T {eT _} U {eU _} _.
Arguments cata_iso {Sh Esh P F} T {eT _} U {eU _} {A eA} g _.
Arguments iso_rana {Sh Esh P F} T {eT _} U {eU _} {A eA} h _.
Arguments ana_out_iso {Sh Esh P F} T {eT _} U {eU _} _.

Lemma iso_inv `{F : Cont Sh P} `{eT : setoid T} `{!Initial F T}
  `{eU : setoid U} `{!Initial F U}
  : iso U T \o iso T U =e id.
Proof. unfold iso at 1; rewrite (cata_iso T U l_in); apply cata_in_id. Qed.
Arguments iso_inv {Sh Esh P F} T {eT _} U {eU _} _.

(** * Finite trees *)
Section FinTrees.
  Context `{F : Cont Sh P}.

  Lemma fin_val_morph : forall x y : {x : GFix F | FinF x},
    x =e y -> proj1_sig x =e proj1_sig y.
  Proof. intros x y E; exact E. Qed.

  Definition fin_val : {x : GFix F | FinF x} ~> GFix F := MkMorph fin_val_morph.

  Lemma fin_val_ana
    : fin_val =e ana (T := GFix F) (l_out (T := {x : GFix F | FinF x})).
  Proof.
    apply ana_uniq; intros [x Fx]; cbn; split; [reflexivity|].
    intros e1 e2 Hv; rewrite (elem_val_eq Hv); reflexivity.
  Qed.

  Lemma fin_rana `{setoid A} (h : RCoalg F A)
    : liftP (ana h) (rcoalg_fin h) =e rana (T := {x : GFix F | FinF x}) h.
  Proof. apply rana_univ; intros x; apply (ana_unfold h x). Qed.

  Corollary cata_ana_hylo_gf `{setoid A} `{setoid B}
    (g : Alg F B) (h : RCoalg F A)
    : cata g \o liftP (ana h) (rcoalg_fin h) =e hylo g h.
  Proof. arewrite (fin_rana h); apply cata_ana_hylo. Qed.

  Corollary cata_ana_hylo_f `{setoid A} `{setoid B}
    (g : Alg F B) (h : RCoalg F A)
    : cata (T := LFix F) g \o iso _ (LFix F) \o liftP (ana h) (rcoalg_fin h)
      =e hylo g h.
  Proof.
    arewrite (cata_iso {x : GFix F | FinF x} (LFix F) g).
    apply cata_ana_hylo_gf.
  Qed.

  Corollary ana_rana `{setoid A} (f : RCoalg F A)
    : iso _ (LFix F) \o liftP (ana f) (rcoalg_fin f) =e rana f.
  Proof. arewrite (fin_rana f); apply iso_rana. Qed.

  Lemma ccata_ana `{setoid A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : f =e ana l_out \o g <-> iso _ (LFix F) \o liftP f Ff =e g.
  Proof.
    split; intros Hf.
    - assert (E : liftP f Ff =e iso (LFix F) {x : GFix F | FinF x} \o g).
      { intros x.
        change (f x =e fin_val (iso (LFix F) {x : GFix F | FinF x} (g x))).
        rewrite (Hf x), (fin_val_ana _); cbn [app comp].
        symmetry; apply (ana_out_iso (LFix F) {x : GFix F | FinF x}). }
      intros x; cbn [app comp]; rewrite (E x).
      apply (iso_inv (LFix F) {x : GFix F | FinF x}).
    - intros x; change (fin_val (liftP f Ff x) =e ana l_out (g x)).
      rewrite (fin_val_ana _), <- (Hf x).
      symmetry; apply (ana_out_iso {x : GFix F | FinF x} (LFix F)).
  Qed.
End FinTrees.

(** * Changing the shape of every layer *)
Corollary hylo_map_fusion_c `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{eU : setoid U} `{!Initial G U} `{setoid A} `{setoid B}
  (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo g l_out \o hylo (l_in (T := U) \o natural m) h
    =e hylo g (natural m \o h).
Proof. rewrite hylo_map_shift, deforest; [reflexivity | apply l_out_in]. Qed.

Corollary hylo_map_fusion `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{eU : setoid U} `{!Initial G U} `{setoid A} `{setoid B}
  (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo g l_out \o hylo (l_in (T := U) \o natural m) h
    =e hylo (g \o natural m) h.
Proof.
  rewrite hylo_map_shift, deforest, ?hylo_map_shift;
    [reflexivity | apply l_out_in].
Qed.

Definition everywhere `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{eT : setoid T} `{!Initial F T} `{eU : setoid U} `{!Initial G U}
  (f : naturalM F G) : T ~> U :=
  hylo (l_in \o natural f) l_out.

Lemma everywhere_id `{F : Cont Sf P} `{eT : setoid T} `{!Initial F T}
  : everywhere (T := T) (U := T) id =e id.
Proof.
  unfold everywhere; symmetry; apply hylo_uniq.
  rewrite fmap_id, idKr, natural_idI, idKr, l_in_out; reflexivity.
Qed.

Lemma everywhere_comp `{F : Cont Sf P} `{SSg : setoid Sg} {G : Cont Sg P}
  `{SSh : setoid Sh} {H : Cont Sh P}
  `{eT : setoid T} `{!Initial F T} `{eU : setoid U} `{!Initial G U}
  `{eV : setoid V} `{!Initial H V}
  (f : naturalM G H) (g : naturalM F G)
  : everywhere (T := U) (U := V) f \o everywhere (T := T) (U := U) g
    =e everywhere (f \o g).
Proof.
  unfold everywhere; rewrite hylo_map_fusion; refine (app_eq hylo _ l_out).
  arewrite (natural_comp (X := V) f g); reflexivity.
Qed.
