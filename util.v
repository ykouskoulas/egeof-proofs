Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.
Require Import Lia.
Open Scope R_scope.
Import Lra.
Import Lia.


Create HintDb null.

Hint Rewrite sin_0 cos_0 Rmult_1_l Rmult_1_r Ropp_0 Rsqr_0 sqrt_0
     cos_PI2 sin_PI2 Rplus_opp_r Rplus_opp_l Rmult_0_l  Rmult_0_r
     Rplus_0_l Rplus_0_r cos_PI sin_PI Rminus_0_l Rminus_0_r sin2_cos2: null.


Ltac arn := autorewrite with null.


Ltac fieldrewrite a b :=
  let name := fresh "ident" in
  assert (a = b) as name; [try unfold Rsqr, pow; field |
                           rewrite name; clear name].

Ltac Radd n :=
  match goal with
  | [|- ?a < ?b] => apply (Rplus_lt_reg_r n)
  | [|- ?a <= ?b] => apply (Rplus_le_reg_r n)
  | [|- ?a > ?b] => apply Rlt_gt; Radd n
  | [|- ?a >= ?b] => apply Rle_ge; Radd n
  | [|- ?a = ?b] => apply (Rplus_eq_reg_l n)
  end.

Ltac Rmult n :=
  match goal with
  | [|- ?a < ?b] => apply (Rmult_lt_reg_r n)
  | [|- ?a <= ?b] => apply (Rmult_le_reg_r n)
  | [|- ?a > ?b] => apply Rlt_gt; Radd n
  | [|- ?a >= ?b] => apply Rle_ge; Radd n
  | [|- ?a = ?b] => apply (Rmult_eq_reg_l n)
  end.

Ltac setr e :=
  match goal with
  | [|- (?op ?a ?b) ] =>
    assert (b = e) as beq0; 
    [ try unfold Rsqr, pow; field | rewrite beq0; clear beq0]
  end.

Ltac setl e :=
  match goal with
  | [|- (?op ?a ?b) ] =>
    assert (a = e) as beq0; 
    [ try unfold Rsqr, pow; field | rewrite beq0; clear beq0]
  end.

(* What it means to be minimum. *)
Lemma Rmin_def : forall a b c, a < Rmin b c -> a < b /\ a < c.
Proof.
  intros.
  unfold Rmin in H.
  destruct (Rle_dec b c). split.
  assumption. lra.
  split. generalize (Rnot_le_lt b c n).
  intros. lra. assumption.
Qed.

Lemma def_Rmin : forall a b c, a < b /\ a < c -> a < Rmin b c.
Proof.
  intros.
  inversion_clear H.
  unfold Rmin.
  destruct (Rle_dec b c). 
  assumption. generalize (Rnot_le_lt b c n).
  intros. lra.
Qed.

Lemma reasonable_continuity : forall f x, continuous f x <->
                forall (eps:posreal), exists (del:posreal), forall (y:R),
                Rabs (y - x) < del -> Rabs (f y - f x) < eps.
Proof.
  intros.
  simpl in *.
  split.
  intros.
  unfold continuous,filterlim,filter_le,filtermap,locally in H.
  simpl in H.
  generalize (H (fun (y:R) => ball (f x) eps y)). intros.
  apply H0.
  exists eps.
  intros.
  assumption.

  intros.
  unfold continuous,filterlim,filter_le,filtermap,locally.
  simpl.
  intros.
  inversion_clear H0 as [eps H1].
  generalize (H eps). intros.
  inversion H0 as [del H2].
  exists del.
  intros x0 ballx.
  apply (H1 (f x0)).
  apply (H2 x0).
  assumption.
Qed.

Lemma continuous_pt_impl_continuity_pt : forall f x,
    continuous f x -> continuity_pt f x.
Proof.
  intros f x contf.
  simpl in *.
  unfold continuity_pt, continue_in, limit1_in, limit_in, D_x, no_cond.
  intros eps epsgt0.
  generalize (reasonable_continuity f x) as rc.
  intros. inversion rc as [foo oof].
  generalize (foo contf (mkposreal eps epsgt0)) as epsdelt.
  clear foo oof rc. intros.
  inversion_clear epsdelt as [del epsarg].
  exists del.
  destruct del. simpl in *.
  split. lra.
  intros x0. intros [[duh xneqx0] inball].
  unfold R_dist in *.
  eapply epsarg. assumption.
Qed.

Lemma continuity_pt_impl_continuous_pt : forall f t,
    continuity_pt f t -> continuous f t.
Proof.
  unfold continuous. unfold filterlim, filtermap, filter_le, locally.
  intros f t dearg P locally_codom.
  unfold continuity_pt, continue_in, limit1_in, limit_in, D_x,
  no_cond, dist, R_met, R_dist in dearg. simpl in dearg.

  inversion_clear locally_codom as [eps lcdm].
  case_eq eps. intros ep cond_ep epsdef. rewrite epsdef in *.
  clear eps epsdef.

  simpl in *.
  apply Rlt_gt in cond_ep.

  generalize (dearg ep cond_ep) as darg. clear dearg. intros.

  inversion_clear darg as [dl [dlgt0 arg]].
  apply Rgt_lt in dlgt0.
  exists (mkposreal dl dlgt0).
  simpl.

  intros. apply lcdm.

  generalize (arg y) as ar. clear arg. intros.

  case (Req_dec t y). intro teqy. subst.
  apply Rgt_lt in cond_ep.
  apply (ball_center (f y) (mkposreal ep cond_ep)).
  intros.

  assert ((True /\ t <> y) /\ Rabs (y - t) < dl) as deltapart.
  split. split. apply I. assumption. apply H.
  apply (ar deltapart).
Qed.

  

Ltac lrag H :=
  let T := type of H in
  match T with
  | ?L = ?R => try setl L; try setr R; lra
  | ?L < ?R => try setl L; try setr R; lra
  | ?L <= ?R => try setl L; try setr R; lra
  end.



Lemma IZRposge1 : forall p, 1 <= IZR (Z.pos p).
Proof.
  intros.
  apply IZR_le.
  lia.
Qed.

Lemma IZRneglen1 : forall p, IZR (Z.neg p) <= -1.
Proof.
  intros.
  apply IZR_le.
  lia.
Qed.

Lemma sin0r : forall r,
    r * sin (0 / r + 0) = 0.
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Rmult_0_l. reflexivity.
  + fieldrewrite (0 / r + 0) 0. assumption.
    rewrite sin_0, Rmult_0_r. reflexivity.
Qed.

Lemma cos0r : forall r,
    r * cos (0 / r + 0) = r.
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Rmult_0_l. reflexivity.
  + fieldrewrite (0 / r + 0) 0. assumption.
    rewrite cos_0, Rmult_1_r. reflexivity.
Qed.


Lemma rsinrr : forall r a b,
    r * sin (r * a / r + b) = r * sin (a + b).
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Rmult_0_l, Rmult_0_l. reflexivity.
  + fieldrewrite (r * a / r + b) (a + b). assumption.
    reflexivity.
Qed.

Lemma rcosrr : forall r a b,
    r * cos (r * a / r + b) = r * cos (a + b).
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Rmult_0_l, Rmult_0_l. reflexivity.
  + fieldrewrite (r * a / r + b) (a + b). assumption.
    reflexivity.
Qed.

Lemma rsinrrn : forall r a b,
    -r * sin (r * a / r + b) = -r * sin (a + b).
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Ropp_0, Rmult_0_l, Rmult_0_l. reflexivity.
  + fieldrewrite (r * a / r + b) (a + b). assumption.
    reflexivity.
Qed.

Lemma rcosrrn : forall r a b,
    - r * cos (r * a / r + b) = - r * cos (a + b).
Proof.
  intros.
  destruct (Req_dec r 0).
  + rewrite H, Ropp_0, Rmult_0_l, Rmult_0_l. reflexivity.
  + fieldrewrite (r * a / r + b) (a + b). assumption.
    reflexivity.
Qed.

Lemma RmultRinv : forall a b,
    a * / b = a / b.
Proof.
  intros.
  lra.
Qed.

Lemma rtp_zner :
  forall r t, 0 < r * t -> 0 <> r.
Proof.
  intros.
  intro.
  rewrite <- H0 in H.
  lra.
Qed.


Ltac addzner :=
  let rtp2 := fresh "rtp" in
  match goal with
  | rtp : 0 < ?r * ?t < Rabs ?r * 2 * PI |- _ =>
    inversion rtp as [rtpl rtpu];
    specialize (rtp_zner _ _ rtpl) as zner
  end.




Lemma derive_decreasing_interv :
  forall (a b : R) (f : R -> R) (pr : derivable f),
    a < b ->
    (forall t : R, a < t < b -> derive_pt f t (pr t) < 0) ->
    forall x y : R, a <= x <= b -> a <= y <= b -> x < y -> f y < f x.
Proof.
  intros.
  assert (forall t : R,
             a < t < b ->
             0 < derive_pt (-f) t (derivable_pt_opp f t (pr t))).
  intros; erewrite (derive_pt_opp).
  specialize (H0 _ H4). lra.
  assert (((-f)%F x) < ((-f)%F y)).
  eapply (derive_increasing_interv a b (-f)%F); eauto.
  intros. apply (H4 _ H5).
  unfold opp_fct in *; lra.
Qed.

Ltac zltab :=
  match goal with
  | |- 0 <= / ?a => left; try zltab
  | |- 0 < / ?a => apply Rinv_0_lt_compat; try zltab
  | |- 0 < PI => apply PI_RGT_0
  | |- - _ <> 0 => apply Ropp_neq_0_compat; try zltab
  | |- / _ <> 0 => apply Rinv_neq_0_compat; try zltab
  | |- _ <> 0 => try lra
  | |- 0 <= ?a + ?b => apply Rplus_le_le_0_compat;
                       try zltab
  | |- 0 < ?a / ?b => setr (a * / b); try zltab
  | |- 0 <= ?a / ?b => setr (a * / b); try zltab
  | |- 0 < ?a * / ?b => apply Rmult_lt_0_compat;
                        try lra; try zltab
  | |- 0 <= ?a * / ?b => apply Rmult_le_pos;
                        try lra; try zltab
  | |- 0 < ?a * ?b => apply Rmult_lt_0_compat;
                        try lra; try zltab
  | |- 0 <= ?a * ?b => apply Rmult_le_pos;
                       try lra; try zltab
  | |- 0 <= sqrt ?a => apply sqrt_pos
  | |- 0 <= ?a² => apply Rle_0_sqr
  | A : 0 <= ?a |- 0 <= ?a => assumption
  | A : 0 < ?a |- 0 < ?a => assumption
  end.

Lemma pm : forall a b,
    a + - b = a - b.
Proof.
  intros.
  field.
Qed.


Lemma gt0ne0 :forall a, 0 < a -> 0 <> a. intros. lra. Qed.
Lemma lt0ne0 :forall a, a < 0 -> 0 <> a. intros. lra. Qed.

Lemma signeqm1_eqv : forall x, sign x = -1 <-> x < 0.
Proof.
  intros. split.
  intros. unfold sign in H.
  destruct (total_order_T 0 x).
  destruct s; exfalso; lra.
  lra.
  apply sign_eq_m1.
Qed.

Lemma signeq0_eqv : forall x, sign x = 0 <-> x = 0.
Proof.
  intros. split.
  intros. unfold sign in H.
  destruct (total_order_T 0 x).
  destruct s; [exfalso; lra|].
  symmetry. assumption.
  lra.
  intro. rewrite H.
  apply sign_0.
Qed.

Lemma signeq1_eqv : forall x, sign x = 1 <-> 0 < x.
Proof.
  intros. split.
  intros. unfold sign in H.
  destruct (total_order_T 0 x).
  destruct s; [assumption| exfalso; lra].
  exfalso; lra.
  intro.
  apply sign_eq_1; assumption.
Qed.

Lemma sumsqeq0 : forall a b,
    a² + b² = 0 -> a = 0 /\ b = 0.
Proof.
  intros.
  specialize (Rle_0_sqr a) as a2ge0.
  specialize (Rle_0_sqr b) as b2ge0.
  inversion_clear a2ge0 as [a2gt0 |a2eq0].
  exfalso.
  specialize (Rplus_lt_le_compat _ _ _ _  a2gt0 b2ge0) as gt0.
  assert (0 + 0 = 0) as z. field. rewrite z, H in gt0. lra.

  inversion_clear b2ge0 as [b2gt0 |b2eq0].
  exfalso. rewrite <- a2eq0 in H. rewrite <- H in b2gt0. lra.

  split; apply Rsqr_eq_0; symmetry; assumption.
Qed.


Lemma zero_num : forall (a b : R),
    b <> 0 -> a = 0 -> a/b = 0.
Proof.
  intros. rewrite H0. setl 0. assumption. reflexivity.
Qed.

Lemma zero_num2 : forall (a b : R),
    b <> 0 -> a/b = 0 -> a = 0.
Proof.
  intros. apply (Rmult_eq_reg_r (/ b)). setl (a/b). assumption.
  setr 0. assumption. assumption.
  apply Rinv_neq_0_compat. assumption.
Qed.



Lemma sqrt_lem : forall x y : R, 0 <= y -> y * y = x -> sqrt x = y.
Proof.
  intros.
  destruct (Rle_dec 0 x).
  apply sqrt_lem_1; assumption.
  exfalso.
  change (y² = x) in H0.
  rewrite <- H0 in n.
  apply Rnot_le_lt in n.
  specialize (Rle_0_sqr y) as y2ge0. lra.
Qed.


Lemma quad_basic : forall b c x,
    0 <= b² - 4*c -> 
    x² + b*x +c = 0 ->
    x = (- b + sqrt (b²-4*c))/2 \/
    x = (- b - sqrt (b²-4*c))/2.
Proof.
  intros b c x R0leb2m4ac quad.
  assert ((x + b/2)² = (b/2)² -c) as id.
  apply (Rmult_eq_reg_l 4); [| discrR].
  assert (forall p, 4*p² = (2*p)²) as id. intro.
  unfold Rsqr. field.
  rewrite id.
  rewrite Rmult_minus_distr_l.
  rewrite id.
  fieldrewrite (2 * ( b /2)) b.
  fieldrewrite (2*(x+b/2)) (2*x + b).
  unfold Rsqr. setl (4 * x * x + b * b + 4 * b * x).
  apply (Rplus_eq_reg_r (- b*b + 4 * c)).
  setr 0. setl (4 * x * x + 4 * b * x + 4 * c).
  apply (Rmult_eq_reg_r (/ 4)). setr 0. setl (x * x + b * x + c).
  unfold Rsqr in quad. assumption.
  apply Rinv_neq_0_compat. discrR.

  assert (forall p, sqrt p / 2 = sqrt (p/4)) as id2. intro.
  rewrite sqrt_div_alt.

  assert (sqrt 4 = 2). unfold sqrt. destruct (Rcase_abs 4).
  lra. destruct (Rge_le 4 0 r).
  unfold Rsqrt. simpl. destruct (Rsqrt_exists 4 (or_introl r0)).
  inversion_clear a.
  assert (4 = 2²). unfold Rsqr. field. rewrite H1 in H0.
  apply Rsqr_inj. assumption. left. lra. symmetry. assumption.
  clear - e. exfalso. generalize e. change (0 <> 4). discrR.
  rewrite H. reflexivity. lra.

  unfold Rsqr in id at 1.
  destruct (Rle_dec 0 (x+b/2));
    [| apply Rnot_le_lt in n;
       assert (0 < -(x+b/2)) as pos;
       [ lra|
         assert ((x + b / 2) * (x + b / 2) =
                 (-(x + b / 2)) * (-(x + b / 2))) as neg;
         [field |
          rewrite neg in id; clear neg]]].

  apply sqrt_lem_1 in id;
    [| apply (Rmult_le_reg_l 4); 
       [lra |
        setl 0;
        rewrite Rmult_minus_distr_l;
        assert (4 * (b / 2)² = b²) as id3;
        [unfold Rsqr; field |
         rewrite id3; clear id3; assumption]]| assumption].

  left.
  unfold Rsqr.
  fieldrewrite ((- b + sqrt (b * b - 4 * c))/2) (- (b/2) + sqrt (b * b - 4*c)/2).
  rewrite id2.
  rewrite <- Rdiv_minus_distr; [| discrR].
  fieldrewrite (b * b / 4) ((b/2) * (b / 2)).
  apply (Rplus_eq_reg_r (b/2)). setr (sqrt (b / 2 * (b / 2) - c)).
  symmetry. unfold Rsqr in id. assumption.

  apply sqrt_lem_1 in id;
    [| apply (Rmult_le_reg_l 4); 
       [lra |
        setl 0;
        rewrite Rmult_minus_distr_l;
        assert (4 * (b / 2)² = b²) as id3;
        [unfold Rsqr; field |
         rewrite id3; clear id3; assumption]]|
     try left; assumption; try clear neg].

  right.
  unfold Rsqr.
  fieldrewrite ((- b - sqrt (b * b - 4 * c))/2) (- (b/2) - sqrt (b * b - 4*c)/2).
  rewrite id2.
  rewrite <- Rdiv_minus_distr; [| discrR].
  fieldrewrite (b * b / 4) ((b/2) * (b / 2)).
  apply (Rplus_eq_reg_r (b/2)). setr (- sqrt (b / 2 * (b / 2) - c)).
  symmetry. unfold Rsqr in id. rewrite id. field.
Qed.


Lemma quad : forall a b c x,
    a <> 0 ->
    0 <= b² - 4*a*c -> 
    a*x² + b*x +c = 0 ->
    x = (- b + sqrt (b²-4*a*c))/(2*a) \/
    x = (- b - sqrt (b²-4*a*c))/(2*a).
Proof.
  intros a b c x ane0 R0leb2m4ac quad.

  rename R0leb2m4ac into R0leb2m4ac'.
  rename quad into quad'.

  assert (x² + (b/a) * x + (c/a) = 0) as quad.
  apply (Rmult_eq_reg_l a).
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  fieldrewrite (a * (b / a * x)) (b*x). assumption.
  fieldrewrite (a*(c/a)) (c). assumption. setr 0. assumption. assumption.

  assert (0 <= (b/a)² - 4 * (c/a)) as R0leb2m4ac.
  apply (Rmult_le_reg_l a²).
  specialize (Rle_0_sqr a) as anneg. inversion_clear anneg. assumption.
  exfalso. apply ane0.
  apply Rsqr_eq_0. symmetry. assumption. setl 0.
  rewrite Rmult_minus_distr_l.
  assert (a² * (b / a)² = b²) as id. unfold Rsqr. field. assumption.
  rewrite id. clear id.
  assert (a² * (4 * (c / a)) = 4*a*c) as id. unfold Rsqr. field. assumption.
  rewrite id. clear id. assumption.
  
  assert (x = (- (b/a) + sqrt ((b/a)² - 4 * (c/a))) / 2 \/
          x = (- (b/a) - sqrt ((b/a)² - 4 * (c/a))) / 2) as rew.
  apply quad_basic; assumption.

  inversion_clear rew as [pos | neg]. 
  rewrite pos.
  assert (4 * (c / a) = (4*a*c)*(/(a²))) as id.
  unfold Rsqr. field. assumption.
  rewrite id. clear id.

  assert ((b / a)² = b² * (/ (a)²)) as id.
  unfold Rsqr.
  fieldrewrite (b / a * (b / a)) (b * b * / (a * a)).
  assumption.
  field. assumption. rewrite id. clear id.
  rewrite <- Rmult_minus_distr_r.
  rewrite sqrt_mult_alt ; [|assumption].
  rewrite <- Rsqr_inv.
  rewrite sqrt_Rsqr_abs.
  assert ((- b + sqrt (b² - 4 * a * c)) / (2 * a) =
          (- b + sqrt (b² - 4 * a * c)) * / 2 * /a) as id. field. assumption.
  rewrite id. clear id.
  assert ((- b - sqrt (b² - 4 * a * c)) / (2 * a) =
          (- b - sqrt (b² - 4 * a * c)) * / 2 * /a) as id. field. assumption.
  rewrite id. clear id.
  destruct (Rle_dec 0 a). inversion_clear r.
  left.
  rewrite Rabs_right.
  fieldrewrite (-(b/a)) ((-b) * (/a)). assumption. field. assumption.
  unfold Rge. left.
  apply Rlt_gt. apply Rinv_0_lt_compat. assumption.
  exfalso. apply ane0. symmetry. assumption.
  apply Rnot_le_lt in n.
  assert (0 < -a) as R0ltma. lra.

  right.
  rewrite Rabs_left.
  fieldrewrite (-(b/a)) ((-b) * (/a)). assumption. field. assumption.
  apply Ropp_lt_cancel. setl 0.
  fieldrewrite (-/a) (/ -a). assumption. 
  apply Rinv_0_lt_compat. assumption. assumption.


  rewrite neg.
  assert (4 * (c / a) = (4*a*c)*(/(a²))) as id.
  unfold Rsqr. field. assumption.
  rewrite id. clear id.

  assert ((b / a)² = b² * (/ (a)²)) as id.
  unfold Rsqr.
  fieldrewrite (b / a * (b / a)) (b * b * / (a * a)).
  assumption.
  field. assumption. rewrite id. clear id.
  rewrite <- Rmult_minus_distr_r.
  rewrite sqrt_mult_alt ; [|assumption].
  rewrite <- Rsqr_inv; [|assumption].
  rewrite sqrt_Rsqr_abs.
  assert ((- b + sqrt (b² - 4 * a * c)) / (2 * a) =
          (- b + sqrt (b² - 4 * a * c)) * / 2 * /a) as id. field. assumption.
  rewrite id. clear id.
  assert ((- b - sqrt (b² - 4 * a * c)) / (2 * a) =
          (- b - sqrt (b² - 4 * a * c)) * / 2 * /a) as id. field. assumption.
  rewrite id. clear id.
  destruct (Rle_dec 0 a). inversion_clear r.

  right.
  rewrite Rabs_right.
  fieldrewrite (-(b/a)) ((-b) * (/a)). assumption. field. assumption.
  unfold Rge. left.
  apply Rlt_gt. apply Rinv_0_lt_compat. assumption.
  exfalso. apply ane0. symmetry. assumption.
  apply Rnot_le_lt in n.
  assert (0 < -a) as R0ltma. lra.
  specialize (Rinv_lt_0_compat _ n) as Rinvalt0.

  left.
  rewrite Rabs_left; [|assumption].
  fieldrewrite (-(b/a)) ((-b) * (/a)). assumption. field. assumption.
Qed.


Lemma factor_quad : forall A B C X,
    let D := sqrt (B² -  A * C) in
    forall (Ane0 : A <> 0) (R0leD : 0 <= (B² -  A * C)),
  (A*(X)² - 2 * B * X + C) = 
  A * ((X-((B + D) / A))*(X-((B - D) / A))).
Proof.
  intros.
  assert (((X - (B + D) / A) * (X - (B - D) / A))=
          X² - 2* B /A * X + C/A ) as id.
  unfold Rsqr.
  fieldrewrite ((X - (B + D) / A) * (X - (B - D) / A))
               ((X*X + ((B*B - D*D) / (A* A))
                       - X * (2 * B / A))).
  assumption.
  assert (D² = (B² - A * C)) as id.
  unfold D.
  rewrite Rsqr_sqrt. reflexivity.
  unfold D in R0leD.
  assumption. unfold Rsqr in id.
  rewrite id.
  fieldrewrite ((B * B - (B * B - A * C)) / (A * A))
               (C/A). assumption. field. assumption.
  rewrite id. field.
  assumption.
Qed.


Lemma sign_eq_pos_den : forall n d,
    0 < d -> sign (n/d) = sign n.
Proof.
  intros.
  assert (d <> 0) as dne0. intro. lra.
  
  unfold sign.
  destruct (total_order_T 0 n).
  destruct (total_order_T 0 (n/d)).
  case_eq s. intros. case_eq s0. intros.
  reflexivity.

  intros. exfalso.
  clear H1. symmetry in e.
  specialize (zero_num2 _ _ dne0 e) as neq0. lra.

  intros. case_eq s0. intros.
  exfalso. assert (n/d = 0) as ndeq0.
  apply (Rmult_eq_reg_r d). setl n. assumption. setr 0.
  symmetry. assumption. assumption. clear H1. rewrite ndeq0 in r.
  lra.

  intros. reflexivity.
  exfalso.
  destruct s.
  assert (n < 0) as nlt0.
  apply (Rmult_lt_reg_r (/d)).
  apply Rinv_0_lt_compat. assumption.
  setr 0. assumption. setl (n/d). assumption. auto.
  lra.

  assert (n < 0) as nlt0.
  apply (Rmult_lt_reg_r (/d)).
  apply Rinv_0_lt_compat. assumption.
  setr 0. assumption. setl (n/d). assumption. auto.
  lra.

  
  destruct (total_order_T 0 (n/d)).
  case_eq s. intros.
  exfalso.
  assert (n/d < 0) as ndlt0.
  apply (Rmult_lt_reg_r d). assumption. setr 0. setl n. assumption. auto.
  apply Rlt_not_le in ndlt0.
  apply ndlt0. left. assumption.

  intros. exfalso.
  assert (n = 0) as neq0.
  apply (Rmult_eq_reg_r (/d)).
  setr 0. assumption. setl (n/d). assumption.
  symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.
  lra. reflexivity.
Qed.


Lemma Rinv_eqv : forall n,
    n/2 = n * / 2.
Proof.
  intros. field.
Qed.

Lemma Rinv_neqv : forall n,
    -n/2 = - n * / 2.
Proof.
  intros. field.
Qed.

Lemma Rinv_ideqv : forall n,
    n/2*2 = n.
Proof.
  intros. field.
Qed.


Lemma minus_neg : forall a b,
    a - - b = a + b.
Proof.
  intros. field.
Qed.

(* sum of squares is nonzero when both components are not
simultaneously zero *)
Lemma posss : forall x y (nO : ~ (x = 0 /\ y = 0)),
    0 < x² + y².
Proof.
  intros.
  specialize (Rle_0_sqr x) as mx2ge0.
  specialize (Rle_0_sqr y) as my2ge0.
  destruct mx2ge0 as [mx2lt0 | mx2eq0];
    destruct my2ge0 as [my2lt0 | my2eq0].
  apply Rplus_lt_0_compat; assumption.
  rewrite <- my2eq0.
  arn; assumption.
  rewrite <- mx2eq0.
  arn; assumption.
  exfalso; apply nO.
  symmetry in mx2eq0, my2eq0.
  apply Rsqr_eq_0 in mx2eq0.
  apply Rsqr_eq_0 in my2eq0.
  split; assumption.
Qed.
