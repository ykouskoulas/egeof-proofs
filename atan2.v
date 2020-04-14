(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import Lra.
Require Import Lia.
Require Import ProofIrrelevance.
Require Import Eqdep.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import util.
Import EqNotations.
Import Lra.

Open Scope R_scope.

(* end hide *)


(** Define arcsin, along with a type for its domain. *)

Record TI  : Set  := trig_interval { val :> R;
                                     bound : -1 <= val <= 1}.


(*
Coercion val (v : TI) : R :=
  match v with
  | trig_interval tval _ => tval
  end.
*)
(* A uniform space is one that has open balls.  Prove that TI is a
  uniform space.

  A compact space means that for any open cover we can find a finite
  subset that is also a cover

  Hausdorff means that for any two points in our topology, we can find
  open neighborhoods that do not intersect *)

Section TrigInterval_UniformSpace.
  Definition TrigInterval_ball (x : TI) (eps : R) (y : TI) :=
    ball (val x) eps (val y).
  
  Lemma TrigInterval_ball_center : forall (x : TI) (eps : posreal),
      TrigInterval_ball x eps x.
    intros. unfold TrigInterval_ball. apply ball_center.
  Qed.
  
  Lemma TrigInterval_ball_triangle : forall (x y z : TI) (e1 e2 : R),
      TrigInterval_ball x e1 y ->
      TrigInterval_ball y e2 z ->
      TrigInterval_ball x (e1 + e2) z.
    intros. unfold TrigInterval_ball in *.
    apply (ball_triangle (val x)(val y)(val z)); assumption.
  Qed.

  Lemma TrigInterval_ball_sym : forall (x y : TI) (eps : R),
      TrigInterval_ball x eps y -> TrigInterval_ball y eps x.
    intros. unfold TrigInterval_ball in *.
    apply (ball_sym). assumption.
  Qed.
  
  Definition TrigInterval_UniformSpace_mixin :=
    UniformSpace.Mixin _ _ TrigInterval_ball_center
                       TrigInterval_ball_sym
                       TrigInterval_ball_triangle.

  Canonical TrigInterval_Uniformspace :=
    UniformSpace.Pack TI TrigInterval_UniformSpace_mixin TI.

End TrigInterval_UniformSpace.

Theorem TI_map (x : R) : TI.
  refine (
      match total_order_T (-1) x with
      | inright y =>  trig_interval (-1) _
      | inleft y =>
        match total_order_T x 1 with
        | inleft z =>
          (match z with
           |right w => trig_interval 1 _ (* x == 1 case *)
           |left w => trig_interval x _ end) (* x < 1 case *)
        | inright z => trig_interval 1 _ end (* x > 1 case *)
      end);
    split;
    try inversion_clear y; try inversion_clear z; try lra;
      try apply (cond_nonneg D).
Defined.

(* Coercion TI_map : R >-> TI. *)

Ltac eqTI :=
  match goal with
  | [|- {|val := ?v; bound := ?p|} = {|val := ?v; bound := ?q|} ] =>
    let eqpf := fresh "eqpf" in
    specialize (proof_irrelevance _ p q) as eqpf; rewrite eqpf; reflexivity
  end.
    
Lemma TI_Map_equiv_TI : forall (x : TI), x = TI_map x.
Proof.
  intros.
  case_eq x.
  intros.
  unfold TI_map.
  simpl in *.
  destruct (total_order_T (-1) val0).
  destruct s.
  destruct (total_order_T val0 1).
  destruct s.
  eqTI.
  subst.
  eqTI.

  exfalso.
  inversion_clear bound0. clear r H.
  lra.

  
  destruct (total_order_T val0 1).
  destruct s.

  eqTI.

  subst.
  exfalso.
  discrR.
  generalize e0.
  change (-1 <> 1).
  discrR.

  exfalso.
  rewrite <- e in r.
  lra.
  discrR.

  exfalso.
  destruct bound0.
  clear - r0 r.
  lra.
Qed.
  
Lemma TI_Map_equiv_int : forall (x : R), -1 <= x <= 1 -> val (TI_map x) = x.
Proof.
  intros.
  unfold TI_map.
  destruct (total_order_T (-1) x).
  destruct s.
  destruct (total_order_T x 1).
  destruct s.
  simpl. reflexivity.
  simpl. symmetry. assumption.
  destruct H.
  destruct H0.
  lra. lra.
  destruct (total_order_T x 1).
  destruct s.
  simpl. reflexivity.
  simpl. symmetry. assumption.

  exfalso.
  subst. inversion_clear H.
  eapply Rgt_not_le; eassumption.
  
  exfalso.
  subst. inversion_clear H.
  eapply Rgt_not_le; eassumption.
Qed.



Lemma TI_Map_lt0 : forall (x : R), x < -1 -> val (TI_map x) = -1.
Proof.
  intros.
  unfold TI_map.
  destruct (total_order_T (-1) x).
  destruct (total_order_T x 1).
  destruct s.
  destruct s0. 
  lra. lra.
  destruct s0. lra. lra.
  simpl. destruct s.
  exfalso.
  eapply Rlt_asym. apply H. apply r0.

  exfalso.
  subst. eapply Rlt_irrefl. apply H.

  simpl. reflexivity.
Qed.


Lemma TI_Map_gt1 : forall (x : R), 1 < x -> val (TI_map x) = 1.
Proof.
  intros.
  unfold TI_map.
  destruct (total_order_T (-1) x).
  destruct s.
  destruct (total_order_T x 1).
  destruct s. lra. lra.
  simpl. reflexivity.
  destruct (total_order_T x 1). destruct s.
  lra. lra.
  simpl. reflexivity.

  exfalso. lra.
Qed.


Lemma TI_lt0_Map : forall  (x : R), val (TI_map x) = -1 -> x <= -1.
Proof.
  intros x. intro.
  unfold TI_map in H.
  destruct (total_order_T (-1) x).
  destruct s.
  destruct (total_order_T x 1).
  destruct s.
  simpl in *. subst. left. assumption.
  simpl in *. subst. right. assumption.
  simpl in *. exfalso.
  lra.

  destruct (total_order_T x 1).
  destruct s.
  simpl in *. subst. right. reflexivity.
  simpl in *. exfalso. lra. 
  simpl in *. exfalso.  lra.
  simpl in *. left. lra.
Qed.




  
Definition pre_asin (y : TI) : {x : R | -PI/2 <= x <= PI/2 /\ sin x = y}.
Proof.
  destruct y as [y [m1lev  vle1]]. simpl.

  assert (- PI / 2 < PI / 2) as PI2ordering.
  apply (Rmult_lt_reg_l 2). lra.
  setl (- PI). setr PI.
  generalize PI_RGT_0. intro.
  lra.

  generalize (total_order_T (-1) y) as m1vorder. intros.
  inversion m1vorder as [[m1ltv | m1eqv] | m1gtv]. clear m1vorder.
  generalize (total_order_T y 1) as v1order. intros.
  inversion v1order as [[vlt1 | veq1] | vgt1]. clear v1order.
  assert (-1 < y < 1) as H. split; assumption.
  clear m1lev vle1 m1ltv vlt1.

  assert (0 < PI/2) as P1;specialize PI2_1 as TMP. lra. clear TMP.
  specialize (Ropp_lt_gt_0_contravar _ (Rlt_gt _ _ P1)) as P2.
  assert (-(PI/2) < PI/2) as TMP2. lra. clear P1 P2.
  assert (forall x, -(PI/2) <= x <= PI/2 -> continuity_pt (sin - (fun _ => y)) x) as TMP1;[intros|].
  assert (constant (fun _ => y)); unfold constant; auto. 
  apply (continuity_pt_minus sin (fun _ => y) x (continuity_sin x) (continuity_pt_const _ _ H1)).
  assert (((fun z => sin z - y) (-(PI/2))) < 0) as TMP3; [
  rewrite (sin_neg (PI/2)); rewrite sin_PI2; destruct H; lra|].
  assert (0 < ((fun z => sin z - y)(PI/2))) as TMP4;[rewrite sin_PI2; destruct H;lra|].
  destruct (IVT_interv (fun z => sin z - y) _ _ TMP1 TMP2 TMP3 TMP4).
  destruct a.

  exists x; split; simpl; auto.
  destruct H0; split. setl (- (PI/2)).
  assumption. assumption.
  apply (Rplus_eq_reg_r (-y)).
  setl (sin x - y). setr 0. assumption.

  exists (PI/2). subst.
  split. split. left. assumption.
  right. reflexivity. apply sin_PI2.
  exfalso. lra.

  exists (- PI/2). subst.
  split. split. right. reflexivity.
  left. assumption.
  fieldrewrite (- PI / 2) (- (PI/2)).
  rewrite sin_antisym.
  apply (Rmult_eq_reg_l (-1)).
  setl (sin (PI / 2)). setr 1.
  apply sin_PI2. intro. lra.

  exfalso; lra.
Qed.

Definition asin x := let (v, _) := pre_asin x in v.


Lemma sin_asin_id : forall (x: TI), sin (asin x) = x.
Proof.
  intros.
  unfold asin.
  destruct (pre_asin x).
  inversion_clear a. assumption.
Qed.

Lemma asin_sin_id : forall (x : R) (pf : -1 <= sin x <= 1), 
  (- PI/2 <= x <= PI/2) -> asin (trig_interval (sin x) pf) = x.
Proof.
  intros;unfold asin.
  destruct H.
  destruct (pre_asin {| val := sin x; bound := pf |}).
  inversion_clear a. simpl in H2.
  assert (- (PI / 2) <= x). setl (- PI / 2). lra.
  inversion_clear H1.
  assert (- (PI / 2) <= x0). setl (- PI / 2). lra.
  apply Rle_antisym.
  apply (sin_incr_0 x0 x); try assumption. right. assumption.
  apply (sin_incr_0 x x0); try assumption. right. symmetry. assumption.
Qed.


Lemma asin_sin_id_0 : forall (x : R), (- PI/2 <= x <= PI/2) ->
                                      asin (TI_map (sin x)) = x.
Proof.
  intros.
  unfold TI_map.
  destruct (total_order_T (-1) (sin x)).
  destruct (total_order_T (sin x) 1).
  destruct s0. destruct s.
  apply asin_sin_id; assumption.
  apply asin_sin_id; assumption.
  destruct s.
  unfold asin.
  match goal with
  | [|- (let (_,_) := ?a in _) = _ ] =>
    destruct a
  end.
  inversion_clear a. simpl in H1.

  inversion_clear H. inversion_clear H0.
  assert (- (PI / 2) <= x). setl (- PI / 2). lra.
  assert (- (PI / 2) <= x0). setl (- PI / 2). lra.
  apply Rle_antisym.
  apply (sin_incr_0 x0 x); try assumption. right. rewrite H1. rewrite e. reflexivity.
  apply (sin_incr_0 x x0); try assumption. right. rewrite H1. rewrite e. reflexivity.

  exfalso. lra.
  exfalso.
  generalize (SIN_bound x). intros.
  inversion_clear H0. lra.

  generalize (SIN_bound x). intros.
  inversion_clear H0. lra.
Qed.

Lemma RInt_unique : forall (f:R->R) (a b If Ig:R),
    If=Ig -> is_RInt f a b If -> is_RInt f a b Ig.
Proof.
  intros.
  rewrite <- H.
  assumption.
Qed.

(** Helper lemmas that describe properties of standard trig functions. *)

Lemma sin_period1 : forall x k, sin (x + 2* IZR k * PI) = sin x.
Proof.
  intros.
  destruct k.
  fieldrewrite (x + 2 * 0 * PI) (x). reflexivity.

  rewrite <- (positive_nat_Z p).
  rewrite <- INR_IZR_INZ.
  rewrite sin_period. reflexivity.

  rewrite <- (sin_period _ (Pos.to_nat p)).
  rewrite INR_IZR_INZ.
  rewrite positive_nat_Z.
  fieldrewrite (x + 2 * IZR (Z.neg p) * PI + 2 * IZR (Z.pos p) * PI)
               (x + 2 * (IZR (Z.pos p) + IZR (Z.neg p)) * PI).
  rewrite <- plus_IZR_NEG_POS.
  rewrite <- Pos2Z.opp_pos.
  assert (((Z.pos p + - Z.pos p) = 0)%Z). omega.
  rewrite H.
  fieldrewrite (x + 2 * 0 * PI) x. reflexivity.
Qed.

Lemma cos_period1 : forall x k, cos (x + 2* IZR k * PI) = cos x.
Proof.
  intros.
  destruct k.
  fieldrewrite (x + 2 * 0 * PI) (x). reflexivity.

  rewrite <- (positive_nat_Z p).
  rewrite <- INR_IZR_INZ.
  rewrite cos_period. reflexivity.

  rewrite <- (cos_period _ (Pos.to_nat p)).
  rewrite INR_IZR_INZ.
  rewrite positive_nat_Z.
  fieldrewrite (x + 2 * IZR (Z.neg p) * PI + 2 * IZR (Z.pos p) * PI)
               (x + 2 * (IZR (Z.pos p) + IZR (Z.neg p)) * PI).
  rewrite <- plus_IZR_NEG_POS.
  rewrite <- Pos2Z.opp_pos.
  assert (((Z.pos p + - Z.pos p) = 0)%Z). omega.
  rewrite H.
  fieldrewrite (x + 2 * 0 * PI) x. reflexivity.
Qed.

Lemma sinθeq0 : forall θ (θrng : -PI < θ <= PI), sin θ = 0 -> θ = 0 \/ θ = PI.
Proof.
  intros.
  generalize sin_0 as sin0; intro.
  generalize sin_PI as sinPI; intro.
  inversion_clear θrng as [mPIltth thlePI].
  destruct thlePI; [| auto].
  destruct (Rle_dec 0 θ) as [zleth | thltz].
  inversion_clear zleth; [| left; auto].

  exfalso.
  destruct (Rle_dec θ (PI/2)) as [tlePI2 |tgtPI2].
  assert (- (PI / 2) <= 0) as mPI2le0. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (- (PI / 2) <= θ) as mPI2leθ. lra.
  assert (θ <= PI / 2) as θlePI2. lra.
  assert (sin 0 < sin θ) as sincr.
  apply (sin_increasing_1 0 θ); assumption.
  lra.

  apply Rnot_le_lt in tgtPI2.
  assert (θ <= 3 * (PI / 2)) as tle3PI2.
  generalize PI_RGT_0 as PIRGT0; intro.
  apply (Rle_trans _ PI); try lra.
  (* apply (Rmult_le_reg_l 2); try lra. *)
  (* setr (3*PI). lra. *)
  assert (PI / 2 <= θ) as PI2leθ; [lra|].
  assert (PI <= 3 * (PI / 2)) as PIle3PI2.
  apply (Rmult_le_reg_l 2); try lra.
  (* setr (3*PI). lra. *)
  assert (PI / 2 <= PI) as PI2lePI; [lra|].
  assert (sin PI < sin θ) as sindec.
  apply (sin_decreasing_1 θ PI); assumption.
  lra.

  (* negative θ *)
  apply Rnot_le_lt in thltz.
  rename θ into phi.
  set (θ := - phi).
  assert (θ < PI) as phltPI; unfold θ; [lra | ].
  assert (- PI < θ) as PIltph; unfold θ; [lra | ].

  exfalso.
  destruct (Rle_dec θ (PI/2)) as [tlePI2 |tgtPI2].
  assert (- (PI / 2) <= 0) as mPI2le0. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (- (PI / 2) <= θ) as mPI2leθ. unfold θ. lra.
  assert (θ <= PI / 2) as θlePI2. unfold θ in *. lra.
  assert (sin 0 < sin θ) as sincr.
  apply (sin_increasing_1 0 θ); unfold θ in *; lra.
  unfold θ in *.
  rewrite sin_neg in sincr.
  lra.

  apply Rnot_le_lt in tgtPI2.
  assert (θ <= 3 * (PI / 2)) as tle3PI2.
  generalize PI_RGT_0 as PIRGT0; intro.
  apply (Rle_trans _ PI); try lra.
  (* apply (Rmult_le_reg_l 2); try lra. *)
  (* setr (3*PI). lra. *)
  assert (PI / 2 <= θ) as PI2leθ; [lra|].
  assert (PI <= 3 * (PI / 2)) as PIle3PI2.
  apply (Rmult_le_reg_l 2); try lra.
  (* setr (3*PI). lra. *)
  assert (PI / 2 <= PI) as PI2lePI; [lra|].
  assert (sin PI < sin θ) as sindec.
  apply (sin_decreasing_1 θ PI); assumption.
  unfold θ in *.
  rewrite sin_neg in sindec.
  lra.
Qed.

Lemma cosθeq0 : forall θ (θrng : -PI < θ <= PI), cos θ = 0 -> θ = PI/2 \/ θ = -PI/2.
Proof.
  intros.
  generalize cos_PI2 as cosPI2; intro.
  inversion_clear θrng as [mPIltth thlePI].
  destruct (Rle_dec 0 θ) as [zleth | thltz].

  destruct (Rle_dec θ (PI/2)) as [tlePI2 |tgtPI2].
  inversion_clear tlePI2 as [tltPI2 | teqPI2].
  exfalso.
  assert (0 <= θ) as zlet. lra.
  assert (θ <= PI) as tlePI. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (PI / 2 <= PI) as PI2lePI. lra.
  assert (cos (PI / 2) < cos θ) as cosdec.
  apply (cos_decreasing_1 θ (PI/2)); assumption.
  lra.

  left. assumption.
  
  apply Rnot_le_lt in tgtPI2.
  exfalso.
  assert (0 <= θ) as zlet. lra.
  assert (θ <= PI) as tlePI. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (PI / 2 <= PI) as PI2lePI. lra.
  assert (cos θ < cos (PI / 2)) as cosdec.
  apply (cos_decreasing_1 (PI/2) θ); assumption.
  lra.


  (* negative θ *)
  apply Rnot_le_lt in thltz.
  rename θ into phi.
  set (θ := - phi).
  assert (θ < PI) as phltPI; unfold θ; [lra | ].
  assert (0 < θ) as PIltph; unfold θ; [lra | ].

  destruct (Rle_dec θ (PI/2)) as [tlePI2 |tgtPI2].
  inversion_clear tlePI2 as [tltPI2 | teqPI2].
  exfalso.
  assert (0 <= θ) as zlet. unfold θ in *. lra.
  assert (θ <= PI) as tlePI. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (PI / 2 <= PI) as PI2lePI. lra.
  assert (cos (PI / 2) < cos θ) as cosdec.
  apply (cos_decreasing_1 θ (PI/2)); assumption.
  assert (cos θ = 0) as cosnteq0. unfold θ.
  rewrite cos_neg. assumption.
  lra.

  right. unfold θ in teqPI2.
  apply (Rmult_eq_reg_l (-1)).
  setl (-phi). setr (PI/2). assumption.
  intro.
  lra.

  apply Rnot_le_lt in tgtPI2.
  
  exfalso.
  assert (0 <= θ) as zlet. lra.
  assert (θ <= PI) as tlePI. lra.
  assert (0 <= PI / 2) as zlePI2. lra.
  assert (PI / 2 <= PI) as PI2lePI. lra.
  assert (cos θ < cos (PI / 2)) as cosdec.
  apply (cos_decreasing_1 (PI/2) θ); assumption.
  assert (cos θ = 0) as cosnteq0. unfold θ.
  rewrite cos_neg. assumption.
  lra.
Qed.

Lemma coseq0_sinneq0_rng : forall θ (θrng : -PI < θ <= PI), cos θ = 0 -> ~ sin θ = 0.
Proof.
  intros until 1. intros cost sint.
  generalize (sinθeq0 θ θrng sint) as θvalsin; intro.
  generalize (cosθeq0 θ θrng cost) as θvalcos; intro.
  generalize PI_RGT_0 as PIRGT0; intro.

  inversion_clear θvalsin as [θsv | θsv];
    inversion_clear θvalcos as [θcv | θcv];
    rewrite θsv in θcv; try lra.
Qed.

Lemma cos_increasing_0_var : forall x y : R,
    -PI <= y -> y <= 0 -> -PI <= x -> x <= 0 -> cos y < cos x -> y < x.
Proof.
  intros.
  rewrite <- (cos_period x 1) in H3.
  rewrite <- (cos_period y 1) in H3.
  unfold INR in H3.
  assert (2 * 1 * PI = 2 * PI) as twoPI. field. rewrite twoPI in H3.
  apply (Rplus_lt_reg_r (2*PI)).
  assert (PI <= x + 2*PI) as xlb. lra.
  assert (PI <= y + 2*PI) as ylb. lra.
  assert (x + 2*PI <= 2*PI) as xub. lra.
  assert (y + 2*PI <= 2*PI) as yub. lra.
  set (x' := (x + 2 * PI)) in *.
  set (y' := (y + 2 * PI)) in *.
  apply cos_increasing_0; try assumption.
Qed.

Lemma inrange_0T : forall x T (Tgt0 : T > 0), exists k, 0 <= x + IZR k * T < T.
Proof.
  intros.
  destruct (total_order_T 0 x).
  inversion_clear s.
  destruct (total_order_T x T).
  inversion_clear s.
  exists (0%Z).
  fieldrewrite (x + 0*T) x.
  split; lra.
  exists ((-1)%Z). rewrite H0.
  fieldrewrite (T + -1 *T) 0.
  split; lra.

  exists ((1 - up (x/T))%Z).
  rewrite minus_IZR.
  fieldrewrite (x + (1 - IZR (up (x / T))) * T) (x + T - T * IZR (up (x / T))).
  split.
  apply (Rmult_le_reg_r (/ T)).
  apply Rinv_0_lt_compat; assumption.
  setl 0. intro. subst. lra.
  setr ( 1 - (IZR (up (x / T)) - (x/ T))).
  intro. subst. lra.
  generalize (for_base_fp (x/T)) as upineq; intro.
  inversion_clear upineq as [zlt le1].
  set (q := IZR (up (x / T)) - x / T) in *.
  lra.

  apply (Rmult_lt_reg_r (/ T)).
  apply Rinv_0_lt_compat; assumption.
  setr 1. intro. subst. lra.
  setl ( 1 - (IZR (up (x / T)) - (x/ T))).
  intro. subst. lra.
  generalize (for_base_fp (x/T)) as upineq; intro.
  inversion_clear upineq as [zlt le1].
  set (q := IZR (up (x / T)) - x / T) in *.
  lra.

  exists (0%Z).
  fieldrewrite (x + 0*T) x.
  split; lra.

  exists ((1 - up (x/T))%Z).
  rewrite minus_IZR.
  fieldrewrite (x + (1 - IZR (up (x / T))) * T) (x + T - T * IZR (up (x / T))).
  split.
  apply (Rmult_le_reg_r (/ T)).
  apply Rinv_0_lt_compat; assumption.
  setl 0. intro. subst. lra.
  setr ( 1 - (IZR (up (x / T)) - (x/ T))).
  intro. subst. lra.
  generalize (for_base_fp (x/T)) as upineq; intro.
  inversion_clear upineq as [zlt le1].
  set (q := IZR (up (x / T)) - x / T) in *.
  lra.

  apply (Rmult_lt_reg_r (/ T)).
  apply Rinv_0_lt_compat; assumption.
  setr 1. intro. subst. lra.
  setl ( 1 - (IZR (up (x / T)) - (x/ T))).
  intro. subst. lra.
  generalize (for_base_fp (x/T)) as upineq; intro.
  inversion_clear upineq as [zlt le1].
  set (q := IZR (up (x / T)) - x / T) in *.
  lra.
Qed.

Lemma inrange_mT2T2 : forall x T (Tgt0 : T > 0), exists k, - T/2 < x + IZR k * T <= T/2.
Proof.
  intros.
  specialize (inrange_0T x T Tgt0) as zT.
  inversion_clear zT as [k [rnglb rngub]].
  destruct (Rle_dec (x + IZR k * T) (T/2)).
  clear rngub.
  exists k. split.
  apply (Rlt_le_trans _ 0).
  apply (Rmult_lt_reg_l 2). lra. setl (-T). setr 0. lra.
  assumption. assumption.
  apply Rnot_le_lt in n. clear rnglb.
  exists ((k-1)%Z).
  rewrite minus_IZR.
  fieldrewrite (x + (IZR k - 1) * T) (x + (IZR k * T) - T).
  split.
  apply (Rplus_lt_reg_r T).
  setr (x + IZR k * T).
  setl (T/2). assumption.

  apply (Rplus_le_reg_r T).
  setl (x + IZR k * T).
  setr (3* T/2). left.
  apply (Rlt_trans _ T). assumption.
  apply (Rmult_lt_reg_r 2). lra.
  setr (3*T).
  lra.
Qed.

Lemma pos_nat_R : forall q, (IZR (Z.pos q)) - 1 = INR ((Pos.to_nat q) - 1).
Proof.
  intros.
  rewrite INR_IZR_INZ.
  rewrite Nat2Z.inj_sub.
  unfold Z.of_nat at 2.
  unfold Pos.of_succ_nat.
  rewrite minus_IZR.
  rewrite <- positive_nat_Z.
  reflexivity.
  rewrite <- Pos2Nat.inj_1.
  rewrite <- Pos2Nat.inj_le.
  apply Pos.le_1_l.
Qed.


Lemma coseq0_sinneq0 : forall θ, cos θ = 0 -> ~ sin θ = 0.
Proof.
  intros.
  generalize (total_order_T (-PI) θ) as toTmPI.
  generalize (total_order_T θ PI) as toTPI.
  intros.

  assert ((-PI < θ <= PI) \/ θ <= -PI \/ PI < θ ) as thloc.
  inversion_clear toTPI as [tlePI | tgtPI].
  inversion_clear toTmPI as [[tltmPI | teqmPI] | tgtmPI].
  left. inversion_clear tlePI; split; lra.

  right. left. right. auto.
  right. left. left. auto.
  right. right. assumption.
  clear toTPI toTmPI.
  inversion_clear thloc as [thinrng|thnotinrng].
  apply coseq0_sinneq0_rng; assumption.
  
  assert (2*PI > 0) as twoPIGT0.
  generalize PI_RGT_0 as PIGT0; intro.
  lra.
  generalize (inrange_0T θ (2*PI) twoPIGT0) as shftth; intro.
  inversion_clear shftth as [k [tshftrngl tshftrngr]].

  destruct k.
  assert (θ + 0 * (2 * PI) = θ) as th; [field|].
  rewrite th in *; clear th.
  inversion_clear thnotinrng as [tlemPI | PIltt].
  exfalso. lra.

  intro.
  assert (cos (θ - 2*PI) = 0) as cosshft.
  rewrite <- (cos_period _ 1%nat).
  assert (θ - 2 * PI + 2 * INR 1 * PI = θ) as th.
  unfold INR. field. rewrite th. assumption.
  assert (sin (θ - 2*PI) = 0) as sinshft.
  rewrite <- (sin_period _ 1%nat).
  assert (θ - 2 * PI + 2 * INR 1 * PI = θ) as th.
  unfold INR. field. rewrite th. assumption.

  assert (-PI < θ - 2 * PI <= PI) as argrng.
  split; lra.

  generalize sinshft.
  apply coseq0_sinneq0_rng; assumption.

  (**************************)

  destruct (Rle_dec (θ + IZR (Z.pos p) * (2 * PI)) PI).
  set (phi := (θ + IZR (Z.pos p) * (2 * PI))) in *.
  assert (-PI < phi <= PI) as thrng.
  split; lra.
  rewrite <- (sin_period _ (Z.to_nat (Z.pos p))).
  assert (2 * INR (Z.to_nat (Z.pos p)) * PI =
          IZR (Z.pos p) * (2 * PI)).
  unfold IZR.
  unfold Z.to_nat.
  rewrite INR_IPR. field.
  rewrite H0.
  change (sin phi <> 0).

  assert (cos phi = 0). unfold phi.
  rewrite <- H0. rewrite cos_period. assumption.
  clear H0.
  apply coseq0_sinneq0_rng; assumption.

  apply Rnot_le_lt in n.
  
  assert (-PI < θ + 2 * (IZR (Z.pos p) - 1) * PI <= PI) as argrng.
  assert (θ + 2 * (IZR (Z.pos p) - 1) * PI =
          θ + IZR (Z.pos p) *(2 *PI) - 2*PI) as arngarg. field.
  rewrite arngarg.
  split; lra.
  
  assert (cos (θ + 2 * (IZR (Z.pos p) - 1) *  PI) = 0) as cosshft.
  rewrite pos_nat_R.
  rewrite cos_period. assumption.

  intro.
  assert (sin (θ + 2 * (IZR (Z.pos p) - 1) * PI) = 0) as sinshft.
  rewrite pos_nat_R.
  rewrite (sin_period _ (Pos.to_nat p - 1)). assumption.
  generalize sinshft.
  apply coseq0_sinneq0_rng; assumption.

  (**************************)

  destruct (Rle_dec (θ + IZR (Z.neg p) * (2 * PI)) PI).
  set (phi := (θ + IZR (Z.neg p) * (2 * PI))) in *.
  assert (-PI < phi <= PI) as thrng.
  split; lra.
  assert (θ = θ + IZR (Z.neg p) * (2 * PI) +
              2 * INR (Z.to_nat (Z.pos p)) * PI) as thval.
  unfold Z.to_nat.
  unfold IZR.
  rewrite INR_IPR. field.
  rewrite thval.
  rewrite sin_period.
  change (sin phi <> 0).

  rewrite thval in H. rewrite cos_period in H.
  change (cos phi = 0) in H.
  apply coseq0_sinneq0_rng; assumption.

  apply Rnot_le_lt in n.
  
  assert (-PI < θ + 2 * (IZR (Z.neg (p + 1))) * PI <= PI) as argrng.
  assert (θ + 2 * (IZR (Z.neg (p + 1))) * PI =
          θ + IZR (Z.neg p) * (2 *PI) - 2*PI) as arngarg.
  rewrite <- Pos2Z.add_neg_neg.
  rewrite plus_IZR. field.
  rewrite arngarg.
  split; lra.
  
  assert (cos (θ + 2 * IZR (Z.neg (p + 1)) *  PI) = 0) as cosshft.
  rewrite <- (cos_period _ (Pos.to_nat (p + 1))).
  assert (IZR (Z.neg (p + 1)) + INR (Pos.to_nat (p + 1)) = 0) as ZNzero.
  rewrite INR_IZR_INZ.
  rewrite positive_nat_Z.
  rewrite Rplus_comm.
  rewrite <- plus_IZR_NEG_POS.
  assert ((Z.pos (p + 1) + Z.neg (p + 1) = 0)%Z).
  rewrite <- Pos2Z.opp_neg. omega.
  rewrite H0. reflexivity.
  fieldrewrite (θ + 2 * IZR (Z.neg (p + 1)) * PI +
                2 * INR (Pos.to_nat (p + 1)) * PI)
               (θ + 2 * (IZR (Z.neg (p + 1)) +
                         INR (Pos.to_nat (p + 1))) * PI).
  rewrite ZNzero.
  fieldrewrite (θ + 2 * 0 * PI) (θ). assumption.

  intro.
  assert (sin (θ + 2 * (IZR (Z.neg (p + 1))) * PI) = 0) as sinshft.
  rewrite <- (sin_period _ (Pos.to_nat (p + 1))).

  assert (IZR (Z.neg (p + 1)) + INR (Pos.to_nat (p + 1)) = 0) as ZNzero.
  rewrite INR_IZR_INZ.
  rewrite positive_nat_Z.
  rewrite Rplus_comm.
  rewrite <- plus_IZR_NEG_POS.
  assert ((Z.pos (p + 1) + Z.neg (p + 1) = 0)%Z).
  rewrite <- Pos2Z.opp_neg. omega.
  rewrite H1. reflexivity.
  fieldrewrite (θ + 2 * IZR (Z.neg (p + 1)) * PI +
                2 * INR (Pos.to_nat (p + 1)) * PI)
               (θ + 2 * (IZR (Z.neg (p + 1)) +
                         INR (Pos.to_nat (p + 1))) * PI).
  rewrite ZNzero.
  fieldrewrite (θ + 2 * 0 * PI) (θ). assumption.

  generalize sinshft.
  apply coseq0_sinneq0_rng; assumption.
Qed.  

Lemma cosθeq1 : forall θ (θrng : 0 <= θ < 2*PI), cos θ = 1 -> θ = 0.
Proof.
  intros.
  
  generalize cos_0 as cos0; intro.
  generalize cos_PI as cosPI; intro.
  inversion_clear θrng as [zleth thlt2PI].
  inversion_clear zleth as [zltth | theq0].
  exfalso.
  destruct (Rle_dec θ PI) as [thlePI | thgePI].
  inversion thlePI as [thltPI | theqPI].
  assert (0 <= θ) as zleth; [left; assumption | ].
  generalize PI_RGT_0 as PI_RGT_0 ; intro.
  assert (0 <= 0) as zlez; [right; reflexivity | ].
  assert (0 <= PI) as zlePI; [lra | ].
  generalize (cos_decreasing_1 0 θ zlez zlePI zleth thlePI zltth) as costhval; intro.
  rewrite cos_0 in costhval.
  rewrite H in costhval.
  lra.

  rewrite theqPI in H.
  rewrite H in cosPI.
  lra.

  apply Rnot_le_lt in thgePI.
  assert (2*PI <= 2*PI) as tPIletPI; [right; reflexivity|].
  assert (PI <= 2*PI) as PIle2PI; [lra|].
  assert (PI <= θ) as PIleth; [left; assumption|].
  assert (θ <= 2*PI) as thle2PI; [left;assumption|].
  generalize (cos_increasing_1 θ (2*PI) PIleth thle2PI PIle2PI tPIletPI thlt2PI) as cosval; intro.
  rewrite cos_2PI in cosval.
  rewrite H in cosval. lra.

  auto.
Qed.

Lemma sin_injective_range : forall x y,
    - PI/2 <= x <= PI/2 -> - PI/2 <= y <= PI/2 -> sin x = sin y -> x = y.
Proof.
  intros.
  rewrite <- (asin_sin_id_0 x).
  rewrite <- (asin_sin_id_0 y).
  rewrite H1. reflexivity.
  inversion H0. split; assumption.
  inversion H. split; assumption. 
Qed.

Lemma cos_injective_range : forall x y,
    0 <= x <= PI -> 0 <= y <= PI -> cos x = cos y -> x = y.
Proof.
  intros. inversion_clear H as [xlb xub]. inversion_clear H0 as [ylb yub].
  destruct (Rle_dec x y) ;[|exfalso].
  inversion_clear r as [xlty |xeqy]; [|assumption]; exfalso.
  specialize (cos_decreasing_1 _ _ xlb xub ylb yub xlty) as cosyltcosx.
  rewrite H1 in cosyltcosx. lra.
  apply Rnot_le_lt in n.
  specialize (cos_decreasing_1 _ _ ylb yub xlb xub n) as cosxltcosy.
  rewrite H1 in cosxltcosy. lra.
Qed.

Lemma cos_eq_1_2PI_0 : forall x : R,
    0 <= x -> x <= 2 * PI -> cos x = 1 -> x = 0 \/ x = 2*PI.
Proof.
  intros.
  specialize cos_0 as cos0.
  specialize cos_PI as cosPI.
  specialize cos_2PI as cos2PI.
  inversion_clear H as [zltx | zeqx]; [  | left; subst; reflexivity].
  inversion_clear H0 as [xlt2PI | xeq2PI]; [ exfalso | right; subst; reflexivity].
  rewrite <- H1 in cos0. symmetry in cos0.
  destruct (Rle_dec x PI).
  assert (0 <= x) as zlex. lra.
  assert (0 <= 0) as zlez. right. reflexivity.
  assert (0 <= PI) as zlePI. left. lra.
  specialize (cos_decreasing_1 _ _ zlez zlePI zlex r zltx) as cosxltcos0.
  rewrite cos0 in cosxltcos0. lra.

  apply Rnot_le_lt in n.
  assert (PI <= x) as PIlex. lra.
  assert (PI <= 2*PI) as PIlePI. lra.
  assert (x <= 2*PI) as xlePI. lra.
  assert (2*PI <= 2*PI) as PIle2PI. right. reflexivity.
  specialize (cos_increasing_1 _ _ PIlex xlePI PIlePI PIle2PI xlt2PI) as cosPIltcosx.
  rewrite H1, cos2PI in cosPIltcosx. lra.
Qed.
(* begin hide *)
Lemma IZR_to_INR : forall p, exists n, IZR (Z.pos p) = INR n.
  intros.
  exists (Pos.to_nat p).
  unfold IZR.
  rewrite INR_IPR.
  reflexivity.
Qed.
(* end hide *)

(** Additional lemmas about tangent *)

Lemma tan_period_0 : forall (x:R) (k:nat),
    sin (x + INR k * PI) * cos x = cos (x + INR k * PI) * sin x.
Proof.
  intros.
  generalize (Nat.Even_or_Odd k) as evenorodd; intro.
  inversion_clear evenorodd as [e | o].
  inversion_clear e.
  rewrite H.
  rewrite mult_INR.
  unfold INR at 3.
  unfold INR at 1.
  assert ((1 + 1) * INR x0 * PI = 2* INR x0 * PI).
  field.
  rewrite H0.
  rewrite sin_period.
  rewrite cos_period.
  rewrite Rmult_comm.
  reflexivity.

  inversion_clear o.
  rewrite H.
  rewrite plus_INR.
  rewrite mult_INR.
  unfold INR at 6.
  unfold INR at 4.
  unfold INR at 3.
  unfold INR at 1.
  assert (x + ((1 + 1) * INR x0 + 1) * PI = (x + PI) + (2 * INR x0 * PI)).
  field.
  rewrite H0.
  rewrite sin_period.
  rewrite cos_period.
  rewrite neg_sin.
  rewrite neg_cos.
  field.
Qed.

Lemma tan_period_1 : forall (x:R) (k:nat),
    cos x <> 0 -> tan (x + INR k * PI) = tan (x).
Proof.
  intros.
  assert (cos (x + INR k * PI) <> 0) as H0.
  generalize (Nat.Even_or_Odd k) as evenorodd; intro.
  inversion_clear evenorodd as [e | o].
  inversion_clear e.
  rewrite H0.
  rewrite mult_INR.
  assert ((x + INR 2 * INR x0 * PI) = (x + 2 * INR x0 * PI)) as argid.
  unfold INR at 1. field. rewrite argid.
  rewrite cos_period. assumption.
  inversion_clear o.
  rewrite H0.
  rewrite plus_INR.
  rewrite mult_INR.
  assert (x + (INR 2 * INR x0 + INR 1)* PI = (x + PI) + (2 * INR x0 * PI)) as argid.
  unfold INR. field. rewrite argid. clear argid.
  rewrite cos_period. rewrite neg_cos.
  apply Ropp_neq_0_compat. assumption.

  unfold tan.
  apply (Rmult_eq_reg_l (cos x * cos (x + INR k * PI))).
  setl (sin (x + INR k * PI) * cos x). assumption.
  setr (cos (x + INR k * PI) * sin x). assumption.
  apply tan_period_0.
  apply Rmult_integral_contrapositive_currified; assumption.
Qed.

Lemma tan_period_2 : forall (x : R) (k : nat),
    cos (x + INR k * PI) <> 0 -> tan (x + INR k * PI) = tan x.
Proof.
  intros.
  apply (Rmult_eq_reg_l (-1)). setl (- tan (x + INR k * PI) ). setr (- tan x).
  symmetry.
  rewrite <- tan_neg.
  rewrite <- tan_neg.
  rewrite <- cos_neg in H.
  set (y := (- (x + INR k * PI))) in *.
  assert ( - x = y + INR k * PI) as mx. unfold y. field.
  rewrite mx.
  apply tan_period_1; assumption.
  discrR.
Qed.

Lemma tan_period : forall (x : R) (k : Z),
    cos x <> 0 -> tan (x + IZR k * PI) = tan x.
Proof.
  intros *. intro cosxne0.

  destruct k.
  rewrite Rmult_0_l, Rplus_0_r; reflexivity.

  rewrite <- positive_nat_Z, <- INR_IZR_INZ,
  tan_period_1; [reflexivity| assumption].

  rewrite <- (tan_period_1 _ (Pos.to_nat p)).
  rewrite INR_IZR_INZ.
  rewrite positive_nat_Z.
  fieldrewrite (x + IZR (Z.neg p) * PI + IZR (Z.pos p) * PI)
               (x + (IZR (Z.neg p) + IZR (Z.pos p)) * PI).
  rewrite <- plus_IZR.
  assert (Z.neg p + Z.pos p = 0)%Z as sum0. lia.
  rewrite sum0, Rmult_0_l, Rplus_0_r.
  reflexivity.
  intro cosxp. apply cosxne0. clear cosxne0.
  destruct (Zeven_odd_dec (Z.neg p)) as [znpe|znpo].
  apply Zeven_ex in znpe as [q znd].
  rewrite <- cosxp, znd, mult_IZR, cos_period1.
  reflexivity.
  apply Zodd_ex in znpo as [q znd].
  rewrite znd, plus_IZR, mult_IZR in cosxp.
  assert (x + (2 * IZR q + 1) * PI=(x + PI) + 2 * IZR q * PI) as id. field.
  rewrite id in cosxp. clear id znd.
  rewrite cos_period1 in cosxp.
  rewrite neg_cos in cosxp.
  apply Ropp_eq_compat in cosxp.
  rewrite Ropp_involutive, Ropp_0 in cosxp.
  assumption.
Qed.

Lemma tant2 : forall θ,
    cos (θ / 2) <> 0 -> tan (θ / 2) = sin θ / (1 + cos θ).
Proof.
  intros.
  set (φ := θ/2).
  assert (θ = (2*φ)) as th2phi. unfold φ. field.
  rewrite th2phi.
  rewrite sin_2a.
  rewrite cos_2a_cos.
  unfold tan.
  field.
  split.
  fieldrewrite (1 + (2 * cos φ * cos φ - 1)) (2*cos φ*cos φ).
  apply Rmult_integral_contrapositive.
  split.
  apply Rmult_integral_contrapositive.
  split. intro.
  lra.
  assumption.
  assumption.
  assumption.
Qed.

Lemma tant2_2 : forall θ : R,
    sin θ <> 0 -> tan (θ / 2) = (1 - cos θ) / sin θ.
Proof.
  intros θ sintne0.
  specialize PI_RGT_0 as PI_RGT_0.
  assert (2*PI > 0) as twPIgt0. lra.
  specialize (inrange_0T θ (2*PI) twPIgt0) as [n [tlb tub]].
  assert (θ + IZR n * (2 * PI) = θ + 2 * IZR n * PI) as id. field. rewrite id in tlb, tub.
  clear id.
  set (phi := θ + 2 * IZR n * PI) in *.
  assert (cos θ = cos phi) as coseq.
  unfold phi.
  destruct n.
  rewrite <- (cos_period _ (0%nat)). unfold INR. reflexivity.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite <- (cos_period _ (d%nat)). reflexivity.
  set (xi := (θ + 2 * IZR (Z.neg p) * PI)) in *.
  assert (θ = xi + 2 * IZR (Z.pos p) * PI) as tdef.
  unfold xi.
  rewrite <- Pos2Z.opp_pos.
  unfold IZR. simpl.
  fieldrewrite (θ + IPR 2 * - IPR p * PI + IPR 2 * IPR p * PI) θ.
  reflexivity.
  rewrite tdef.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite (cos_period). reflexivity.

  assert (sin θ = sin phi) as sineq.
  unfold phi.
  destruct n.
  rewrite <- (sin_period _ (0%nat)). unfold INR. reflexivity.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite <- (sin_period _ (d%nat)). reflexivity.
  set (xi := (θ + 2 * IZR (Z.neg p) * PI)) in *.
  assert (θ = xi + 2 * IZR (Z.pos p) * PI) as tdef.
  unfold xi.
  rewrite <- Pos2Z.opp_pos.
  unfold IZR. simpl.
  fieldrewrite (θ + IPR 2 * - IPR p * PI + IPR 2 * IPR p * PI) θ.
  reflexivity.
  rewrite tdef.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite (sin_period). reflexivity.
  (*****)
  assert (1 + cos θ <> 0) as opluscostne0.
  intro. apply sintne0.
  rewrite sineq.
  apply sin_eq_O_2PI_1. assumption. left. assumption.
  rewrite coseq in H.
  assert (- cos phi = 1) as ncosteq1.
  apply (Rplus_eq_reg_l (cos phi)). setl 0. symmetry. rewrite Rplus_comm. assumption.
  
  rewrite <- neg_cos in ncosteq1.
  destruct (Rle_dec 0 (phi-PI)).
  assert (phi+PI = (phi - PI) + 2* INR 1 * PI) as id. unfold INR. field.
  rewrite id in ncosteq1. clear id.
  rewrite cos_period in ncosteq1.
  assert (- PI <= phi - PI) as phipPIlb. lra.
  assert (phi - PI < PI) as phipPIub. lra.
  assert (0 <= phi - PI < 2*PI) as phipPIrng. split; lra.
  specialize (cosθeq1 _ phipPIrng ncosteq1) as phipPIeq0.
  right. left. apply (Rplus_eq_reg_r (- PI)). setl (phi- PI). setr 0. assumption.
  apply Rnot_le_lt in n0.

  assert (0 <= phi+PI < 2*PI) as phipPIrng. split; lra.
  specialize (cosθeq1 _ phipPIrng ncosteq1) as phipPIeq0.
  exfalso. lra.

  clear coseq sineq tlb tub n phi.
  assert (cos (θ/2) <> 0).
  (*** try this ***)
  specialize (inrange_0T (θ/2) (2*PI) twPIgt0) as [n [tlb tub]].
  assert ((θ/2) + IZR n * (2 * PI) = (θ/2) + 2 * IZR n * PI) as id. field. rewrite id in tlb, tub.
  clear id.
  set (phi := (θ/2) + 2 * IZR n * PI) in *.
  assert (cos (θ/2) = cos phi) as coseq.
  unfold phi.
  destruct n.
  rewrite <- (cos_period _ (0%nat)). unfold INR.
  reflexivity.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite <- (cos_period _ (d%nat)).
  reflexivity.
  set (xi := (θ / 2 + 2 * IZR (Z.neg p) * PI)) in *.
  assert ((θ/2) = xi + 2 * IZR (Z.pos p) * PI) as tdef.
  unfold xi.
  rewrite <- Pos2Z.opp_pos.
  unfold IZR. simpl. field.
  unfold IPR, IPR_2. intro. lra.
  rewrite tdef.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  rewrite (cos_period). reflexivity.

  assert (sin θ = sin (2*phi)) as sineq.
  unfold phi.
  destruct n.
  rewrite <- (sin_period _ (0%nat)). unfold INR.
  fieldrewrite (2 * (θ / 2 + 2 * 0 * PI)) (θ + 2 * 0 * PI).
  reflexivity.
  specialize (IZR_to_INR p) as [d ncons]. rewrite ncons.
  fieldrewrite (2 * (θ / 2 + 2 * INR d * PI)) (θ + 2 * (2* INR d) * PI).
  assert (2 = INR 2) as id. unfold INR. field. rewrite id at 2.
  rewrite <- mult_INR.
  rewrite <- (sin_period _ ((2*d)%nat)). reflexivity.
  fieldrewrite (2 * (θ / 2 + 2 * IZR (Z.neg p) * PI))
               (θ + 2 * 2 * IZR (Z.neg p) * PI).
  set (xi := (θ + 2 * 2 * IZR (Z.neg p) * PI)) in *.
  assert (θ = xi + 2 * 2 * IZR (Z.pos p) * PI) as tdef.
  unfold xi.
  rewrite <- Pos2Z.opp_pos.
  unfold IZR. simpl. field.
  rewrite tdef.
  specialize (IZR_to_INR p) as [d ncons].
  rewrite ncons.
  assert (2 = INR 2) as id. unfold INR. field.
  rewrite id at 2.
  fieldrewrite (xi + 2 * INR 2 * INR d * PI) (xi + 2 * (INR 2 * INR d) * PI).
  rewrite <- mult_INR.
  rewrite (sin_period). reflexivity.
  (*****)
  intro costene0. apply sintne0.
  rewrite sineq.
  destruct (Rlt_dec phi PI).
  apply sin_eq_O_2PI_1. lra. lra.
  rewrite coseq in costene0.
  assert (phi <= 2 * PI) as phile2PI. left. assumption.
  specialize (cos_eq_0_2PI_0 _ tlb phile2PI costene0) as phival.
  inversion_clear phival as [v | nv].
  right. left. rewrite v. field. exfalso.
  rewrite nv in r.
  assert (3 * PI < 2 * PI) as contra.
  apply (Rmult_lt_reg_r (/ 2)).
  lra. setl (3* (PI/2)). setr PI. assumption.
  lra.

  apply Rnot_lt_le in n0.
  assert (2*phi = (2*phi - 2 * PI) + 2 * INR 1 * PI) as id. unfold INR. field.
  rewrite id. clear id.
  rewrite sin_period.
  assert (0 <= 2*phi - 2 * PI) as tplb. unfold INR. lra.
  assert (2*phi - 2* PI  < 2*PI) as tbub. unfold INR. lra.
  apply sin_eq_O_2PI_1. assumption. left; assumption.

  assert (phi <= 2 * PI) as phiub2. left. assumption.
  rewrite coseq in costene0.
  specialize (cos_eq_0_2PI_0 _ tlb phiub2 costene0) as phival.
  inversion_clear phival as [cont | val]. rewrite cont in n0. lra.
  right. left. rewrite val. field.
  (*** try this ***)
  
  rewrite tant2.
  apply (Rmult_eq_reg_l ((1 + cos θ)* sin θ)).
  apply (Rplus_eq_reg_l (cos θ * cos θ)).
  setl (sin θ * sin θ + cos θ * cos θ). assumption.
  setr 1. assumption.
  change ((sin θ)² + (cos θ)² = 1).
  apply sin2_cos2.
  apply Rmult_integral_contrapositive_currified.
  assumption. assumption. assumption.
Qed.

Lemma tan_increasing_pi2 : forall x y,
    -PI/2 < x < PI/2 -> -PI/2 < y < PI/2 ->
    tan x < tan y -> x < y.
Proof.
  intros.
  apply atan_increasing in H1.
  unfold atan in H1.
  repeat destruct pre_atan.
  destruct a, a0.
  apply tan_is_inj in H3; auto.
  apply tan_is_inj in H5; auto.
  subst; assumption.
Qed.

(** Define atan2, a two-argument atan function whose return angle
acconts for the sign of each argument.  It has a branch cut at PI and
a range in (-PI,PI]. *)

Definition pre_atan2 (dy dx : R) : {θ : R | -PI < θ <= PI /\
                                        dy = sqrt (dy² + dx²) * sin θ /\
                                        dx = sqrt (dy² + dx²) * cos θ}.
Proof.
  generalize (total_order_T 0 dx) as zdxrel. intro.
  inversion_clear zdxrel as [[zltdx | zeqdx] | dxlt0].
  exists (atan (dy/dx)).
  unfold atan.
  destruct (pre_atan (dy/dx)).
  inversion_clear a as [[xgt xlt] tanx].
  split.
  generalize PI_RGT_0 as PIgt0. intro.
  split.
  apply (Rlt_trans _ (-PI/2)).
  apply (Rgt_lt) in PIgt0.
  rewrite Ropp_div. apply Ropp_lt_contravar. lra. lra.
  apply (Rle_trans _ (PI/2)). left. assumption. lra.
  generalize (sin2_cos2 x) as sin2cos2. intro.
  unfold tan in tanx.

  generalize (total_order_T 0 dy) as zdyrel. intro.
  inversion_clear zdyrel as [zledy | dylt0].
  assert (0 <= dy) as zledy1. inversion zledy.
  left; assumption. right; assumption.

  (* first quadrant and +x-axis *)
  split.
  (* dy *)
  rewrite Ropp_div in xgt.
  generalize (cos_gt_0 x xgt xlt) as zltcosx; intro.
  (* dy - 0 <= x *)
  destruct (total_order_T 0 x) as [zlex | xlt0].
  assert (0 <= x) as zlex1. inversion zlex.
  left; assumption. right; assumption.
  assert (x<=PI) as xlePI. apply (Rle_trans _ (PI/2)).
  left; assumption. lra.
  generalize (sin_ge_0 x zlex1 xlePI) as zlesinx; intro.


  inversion_clear zledy1 as [zltdy | zeqdy].

  assert (cos x =  dx / dy * sin x) as cosxdef.
  apply (Rmult_eq_reg_r (dy / dx / cos x)).
  setr (sin x / cos x).
  split. intro; lra. 
  split. intro; lra.
  intro; lra.
  setl (dy/dx).
  split; intro; lra. symmetry.
  assumption.
  assert (0 < dy / dx / cos x).
  repeat apply Rdiv_lt_0_compat; assumption.
  intro. rewrite H0 in H. lra.
  rewrite cosxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((sin x)² = 1 * (sin x)²) as sint1.
  field. rewrite sint1 in sin2cos2 at 1.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < / dy) as zltinvdy.
  apply Rinv_0_lt_compat. assumption.
  assert (0 < / dy²) as zltinvdy2.
  rewrite <- Rsqr_inv.
  apply Rsqr_pos_lt.
  intro. rewrite H in zltinvdy. lra.
  intro. lra.

  assert ((dy² + dx²) * (sin x)² = dy²) as psqrt.
  apply (Rmult_eq_reg_l (/ dy²)).
  setr 1. intro; lra.
  setl (((1 + dx²/ dy²) * (sin x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdy2. lra.
  apply Rsqr_inj. left; assumption.
  apply Rmult_le_pos.
  apply sqrt_pos.  assumption.
  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.

  subst.
  assert (sin x = 0).
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro ;lra.
  setr (0 / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite H. setr 0. reflexivity.

  exfalso.
  assert (0 <= dy/dx) as dydxsign.
  apply Rdiv_le_0_compat; assumption.
  assert (dy/dx < 0) as dydxsign2.
  rewrite <- tanx.
  setl (sin x * / cos x). intro ; lra.
  setr (0 * / cos x). intro; lra.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat; assumption.
  apply sin_lt_0_var.
  apply (Rlt_trans _ (- (PI/2))). lra.
  assumption. assumption.
  generalize dydxsign2.
  apply RIneq.Rle_not_lt; assumption.

  (* dx *)
  rewrite Ropp_div in xgt.
  generalize (cos_gt_0 x xgt xlt) as zltcosx; intro.
  assert (sin x = dy / dx * cos x) as sinxdef.
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro. lra. 
  setr (dy / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite sinxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((cos x)² = 1 * (cos x)²) as cost1.
  field. rewrite cost1 in sin2cos2 at 2.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < / dx) as zltinvdx.
  apply Rinv_0_lt_compat. assumption.
  assert (0 < / dx²) as zltinvdx2.
  rewrite <- Rsqr_inv.
  apply Rsqr_pos_lt.
  intro. rewrite H in zltinvdx. lra.
  intro. lra.

  assert ((dy² + dx²) * (cos x)² = dx²) as psqrt.
  apply (Rmult_eq_reg_l (/ dx²)).
  setr 1. intro; lra.
  setl (((dy²/ dx² + 1) * (cos x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdx2. lra.
  apply Rsqr_inj. left; assumption.
  apply Rmult_le_pos.
  apply sqrt_pos. left; assumption.
  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.

(*************)

  (* fourth quadrant *)
  split.
  (* dy *)
  rewrite Ropp_div in xgt.
  generalize (cos_gt_0 x xgt xlt) as zltcosx; intro.
  (* dy - 0 <= x *)
  destruct (total_order_T 0 x) as [zlex | xlt0].
  assert (0 <= x) as zlex1. inversion zlex.
  left; assumption. right; assumption.
  
  inversion_clear zlex1 as [zltx | zeqx].
  exfalso.
  assert (dy/dx <= 0) as dydxsign.
  setl (dy * /dx). intro; lra.
  setr (dy * 0). 
  apply Rmult_le_compat_neg_l. left; assumption.
  left.
  apply Rinv_0_lt_compat. assumption.

  assert (0 < dy / dx) as dydxsign2.
  rewrite <- tanx.
  assert (x < PI) as xltPI.
  apply (Rlt_trans _ (PI/2)). assumption.
  lra.
  generalize (sin_gt_0 x zltx xltPI) as zltsin; intro.
  setr (sin x * / cos x). intro ; lra.
  setl (0 * / cos x). intro; lra.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat; assumption.
  assumption.  generalize dydxsign2.
  apply RIneq.Rle_not_lt; assumption.

  subst. rewrite sin_0 in *. setr 0.
  apply (Rmult_eq_compat_l dx) in tanx.
  assert (dx * (0 / cos 0) = 0) as zeros. field.
  rewrite cos_0. intro. lra. rewrite zeros in tanx.
  assert (dx * (dy / dx) = dy). field. intro; lra.
  rewrite H in tanx. symmetry. assumption.

  apply Rgt_lt in xlt0.
  apply Rgt_lt in dylt0.
  assert (- PI < x ) as mPIltx.
  apply (Rlt_trans _ (- (PI/2))).
  apply Ropp_lt_contravar.
  lra. assumption.
  generalize (sin_lt_0_var x mPIltx xlt0) as sinlt0;intro.

  assert (cos x =  dx / dy * sin x) as cosxdef.
  apply (Rmult_eq_reg_r (dy / dx / cos x)).
  setr (sin x / cos x).
  split. intro; lra. 
  split. intro; lra.
  intro; lra.
  setl (dy/dx).
  split; intro; lra. symmetry.
  assumption.
  assert (dy / dx / cos x < 0).
  setl (- (- dy * (/ dx) * / cos x)).
  split. intro. lra.
  intro. lra.

  apply Ropp_lt_gt_0_contravar.
  apply Rlt_gt.
  apply Rmult_lt_0_compat.
  apply Rlt_mult_inv_pos.
  apply Ropp_0_gt_lt_contravar.
  assumption. assumption.
  apply Rinv_0_lt_compat; assumption.
  intro. rewrite H0 in H. lra.
  rewrite cosxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((sin x)² = 1 * (sin x)²) as sint1.
  field. rewrite sint1 in sin2cos2 at 1.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < dy²) as zltdy2.
  apply Rsqr_pos_lt. intro; lra.
  assert (0 < / dy²) as zltinvdy2.
  apply Rinv_0_lt_compat; assumption.

  assert ((dy² + dx²) * (sin x)² = dy²) as psqrt.
  apply (Rmult_eq_reg_l (/ dy²)).
  setr 1. intro; lra.
  setl (((1 + dx²/ dy²) * (sin x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdy2. lra.
  apply (Rmult_eq_reg_l (-1)).
  setl (- dy). setr (sqrt (dy² + dx²) * - sin x).
  apply Rsqr_inj. apply Ropp_0_ge_le_contravar.
  left; assumption.
  apply Rmult_le_pos.
  apply sqrt_pos. apply Ropp_0_ge_le_contravar.
  left. assumption.
  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt.
  repeat rewrite <- Rsqr_neg.
  assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.
  intro; lra.
  
  (* dx *)
  rewrite Ropp_div in xgt.
  generalize (cos_gt_0 x xgt xlt) as zltcosx; intro.
  assert (sin x = dy / dx * cos x) as sinxdef.
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro. lra. 
  setr (dy / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite sinxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((cos x)² = 1 * (cos x)²) as cost1.
  field. rewrite cost1 in sin2cos2 at 2.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < / dx) as zltinvdx.
  apply Rinv_0_lt_compat. assumption.
  assert (0 < / dx²) as zltinvdx2.
  rewrite <- Rsqr_inv.
  apply Rsqr_pos_lt.
  intro. rewrite H in zltinvdx. lra.
  intro. lra.

  assert ((dy² + dx²) * (cos x)² = dx²) as psqrt.
  apply (Rmult_eq_reg_l (/ dx²)).
  setr 1. intro; lra.
  setl (((dy²/ dx² + 1) * (cos x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdx2. lra.
  apply Rsqr_inj. left; assumption.
  apply Rmult_le_pos.
  apply sqrt_pos. left; assumption.
  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.

  (* y-axis - 0 = dx *)
  subst. assert (dy² + 0² = dy²) as dy2. unfold Rsqr. field.
  rewrite dy2. clear dy2.
  destruct (total_order_T 0 dy).
  destruct s.
  exists (PI/2). 
  split.
  generalize PI_RGT_0 as PIval; intro.
  split; lra.
  split. rewrite sin_PI2. rewrite sqrt_Rsqr. field.
  left; assumption.
  rewrite cos_PI2. field.

  exists 0. subst.
  generalize PI_RGT_0 as PIval; intro.
  split. split; lra.
  split. rewrite sin_0. field.
  rewrite sqrt_Rsqr. field. right. reflexivity.

  exists (- PI/2).
  generalize PI_RGT_0 as PIval; intro.
  split. split. rewrite Ropp_div.
  apply Ropp_lt_contravar.
  lra.
  apply (Rle_trans _  0).
  rewrite Ropp_div.
  lra. lra.

  split. rewrite Ropp_div.
  rewrite sin_neg. rewrite sin_PI2.
  rewrite sqrt_Rsqr_abs.
  apply (Rmult_eq_reg_l (-1)).
  setl (-dy). setr (Rabs dy).

  apply Rgt_lt in r.
  rewrite Rabs_left; try assumption. reflexivity.
  intro.  lra.

  rewrite Ropp_div.
  rewrite cos_neg. rewrite cos_PI2.
  field.
(*************)

  apply Rgt_lt in dxlt0.
  destruct (total_order_T 0 dy) as [zledy | zgtdy].
  assert (0 <= dy)as zledy1.
  destruct zledy. left. assumption. right. assumption.

  (* third quadrant *)
  exists (atan (dy/dx) + PI). unfold atan.
  destruct (pre_atan (dy/dx)).
  inversion_clear a as [[mPIltxpPI xpPIlePI] tand].
  unfold tan in tand.
  generalize (sin2_cos2 x) as sin2cos2. intro.

  rewrite Ropp_div in mPIltxpPI.
  generalize (cos_gt_0 x mPIltxpPI xpPIlePI) as zltcos; intro.

  destruct (total_order_T 0 x).
  inversion_clear s as [zltx | zeqx].

  exfalso.

  assert (x < PI) as xlePI. 
  apply (Rlt_trans _ (PI/2)). assumption. lra.
  generalize (sin_gt_0 x zltx xlePI) as zlesin; intro.

  assert (dy/dx <= 0) as dydxle0.
  setl (- 1 * (dy / (-dx))).
  intro. lra.
  setr (-1 * 0).
  apply Rmult_le_compat_neg_l. lra.
  setr (dy * / - dx). intro; lra.
  apply Rdiv_le_0_compat. assumption.
  apply Ropp_0_gt_lt_contravar. assumption.

  assert (0 < dy / dx) as zltdydx.
  rewrite <- tand.
  apply Rdiv_lt_0_compat; assumption.
  generalize zltdydx.
  apply RIneq.Rle_not_lt; assumption.
  subst.
  split. split; lra.
  fieldrewrite (0 + PI) (PI).
  split.
  rewrite sin_PI.
  apply (Rmult_eq_reg_r (/ dx)).
  setl (dy / dx). intro; lra.
  setr (0 / 1). intro; lra.
  rewrite <- cos_0. rewrite <- sin_0 at 1.
  symmetry. assumption.
  apply Rinv_neq_0_compat.
  intro; lra.

  rewrite cos_PI.
  assert (dy = 0) as dyeq0.
  apply (Rmult_eq_reg_r (/ dx)).
  setl (dy/dx). intro; lra.
  setr (0 / 1). intro; lra.
  rewrite <- sin_0.
  rewrite <- cos_0.
  symmetry. assumption.
  apply Rinv_neq_0_compat.
  intro; lra.
  rewrite dyeq0.
  assert ((0² + dx²) = dx²) as dx2def.
  unfold Rsqr. field. rewrite dx2def.
  rewrite sqrt_Rsqr_abs.
  rewrite Rabs_left. field. assumption.

  apply Rgt_lt in r.
  split.
  generalize PI_RGT_0 as PIval; intro.
  split.
  apply (Rplus_lt_reg_r (-PI)).
  setl (-(2*PI)). setr x.
  apply (Rlt_trans _ (- (PI / 2))).
  lra. assumption.
  lra.

  inversion_clear zledy1 as [zltdy | zeqdy].
  split.
  rewrite neg_sin. 
  apply Ropp_0_gt_lt_contravar in r.

  assert (cos x =  dx / dy * sin x) as cosxdef.
  apply (Rmult_eq_reg_r (dy / dx / cos x)).
  setr (sin x / cos x).
  split. intro; lra. 
  split. intro; lra.
  intro; lra.
  setl (dy/dx).
  split; intro; lra. symmetry.
  assumption.
  assert (dy / dx / cos x < 0).
  setl (- (dy / - dx / cos x)).
  split; intro; lra.

  apply Ropp_lt_gt_0_contravar.
  apply Rlt_gt.
  apply Rmult_lt_0_compat.
  apply Rlt_mult_inv_pos. assumption.
  apply Ropp_0_gt_lt_contravar. assumption.
  apply Rinv_0_lt_compat; assumption.

  intro. rewrite H0 in H. lra.
  rewrite cosxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((sin x)² = 1 * (sin x)²) as sint1.
  field. rewrite sint1 in sin2cos2 at 1.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < dy²) as zltdy2.
  apply Rsqr_pos_lt. intro; lra.
  assert (0 < / dy²) as zltinvdy2.
  apply Rinv_0_lt_compat; assumption.

  assert ((dy² + dx²) * (sin x)² = dy²) as psqrt.
  apply (Rmult_eq_reg_l (/ dy²)).
  setr 1. intro; lra.
  setl (((1 + dx²/ dy²) * (sin x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdy2. lra.
  apply Rsqr_inj. 
  left; assumption.
  apply Rmult_le_pos.
  apply sqrt_pos.
  rewrite <- sin_neg.
  apply sin_ge_0. left. assumption.

  setr (- (- PI)).
  apply Ropp_le_contravar.
  apply (Rle_trans _ (- (PI / 2))).
  lra. left. assumption.
  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt.
  repeat rewrite <- Rsqr_neg.
  assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.

  rewrite neg_cos.
  assert (sin x = dy / dx * cos x) as sinxdef.
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro. lra. 
  setr (dy / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite sinxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((cos x)² = 1 * (cos x)²) as cost1.
  field. rewrite cost1 in sin2cos2 at 2.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < / - dx) as zltinvdx.
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar. assumption.
  assert (0 < / dx²) as zltinvdx2.
  rewrite Rsqr_neg.
  rewrite <- Rsqr_inv.
  apply Rsqr_pos_lt.
  intro. rewrite H in zltinvdx. lra.
  intro. lra.

  assert ((dy² + dx²) * (cos x)² = dx²) as psqrt.
  apply (Rmult_eq_reg_l (/ dx²)).
  setr 1. intro; lra.
  setl (((dy²/ dx² + 1) * (cos x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdx2. lra.
  apply (Rmult_eq_reg_l (-1)).
  apply Rsqr_inj. left; lra.
  setr (sqrt (dy² + dx²) *  cos x).
  apply Rmult_le_pos.
  apply sqrt_pos. left; assumption.
  setl (dx²).
  assert (-1 * (sqrt (dy² + dx²) * - cos x) =
          sqrt (dy² + dx²) * cos x). field.
  rewrite H. clear H. symmetry.
  rewrite Rsqr_mult.
  rewrite Rsqr_sqrt. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.
  intro; lra.

  subst.
  assert (0² + dx² = dx²) as dxdef. unfold  Rsqr.
  field. rewrite dxdef. clear dxdef.
  rewrite neg_cos.
  rewrite neg_sin.

  assert (sin x  = 0) as sinx.
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro; lra.
  setr (0 / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite sinx in *.
  split. field.
  assert (cos x = 1) as cosx.
  apply Rsqr_inj. left. assumption. lra.
  unfold Rsqr at 2. setr 1.
  rewrite <- sin2cos2. unfold Rsqr. field.
  rewrite cosx.
  rewrite sqrt_Rsqr_abs.
  rewrite Rabs_left.
  field. assumption.

  (* fourth quadrant *)
  apply Rgt_lt in zgtdy.
  exists (atan (dy/dx) - PI).
  unfold atan.
  destruct (pre_atan (dy/dx)).
  inversion_clear a as [[mPI2ltx xltPI2] tand].
  unfold tan in tand.

  generalize (sin2_cos2 x) as sin2cos2. intro.

  rewrite Ropp_div in mPI2ltx.
  generalize (cos_gt_0 x mPI2ltx xltPI2) as zltcos; intro.

  assert (0 < dy / dx) as zltdydx.
  setr ((- dy) * / - dx). intro; lra.
  apply Rlt_mult_inv_pos;
    apply Ropp_0_gt_lt_contravar; assumption.

  destruct (total_order_T 0 x) as [[zltx | zeqx] | zgtx].
  assert (x < PI) as xltPI. apply (Rlt_trans _ (PI/2)).
  assumption. lra.
  generalize (sin_gt_0 x zltx xltPI) as zltsinx; intro.

  split. split; lra.

  fieldrewrite (x - PI) (- (-x + PI)).
  split.

  (* fourth quadrant dy *)
  rewrite sin_neg. rewrite neg_sin. rewrite sin_neg.
  fieldrewrite (- - - sin x) (- sin x).
  assert (cos x =  dx / dy * sin x) as cosxdef.
  apply (Rmult_eq_reg_r (dy / dx / cos x)).
  setr (sin x / cos x).
  split. intro; lra. 
  split. intro; lra.
  intro; lra.
  setl (dy/dx).
  split; intro; lra. symmetry.
  assumption.
  assert (0 < dy / dx / cos x).
  setr (- dy * / - dx * / cos x).
  split; intro; lra.
  repeat apply Rmult_lt_0_compat.
  apply Ropp_gt_lt_0_contravar. assumption.
  apply Rinv_0_lt_compat.
  apply Ropp_gt_lt_0_contravar. assumption.
  apply Rinv_0_lt_compat. assumption.

  intro. rewrite H0 in H. lra.
  rewrite cosxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((sin x)² = 1 * (sin x)²) as sint1.
  field. rewrite sint1 in sin2cos2 at 1.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < dy²) as zltdy2.
  apply Rsqr_pos_lt. intro; lra.
  assert (0 < / dy²) as zltinvdy2.
  apply Rinv_0_lt_compat; assumption.

  assert ((dy² + dx²) * (sin x)² = dy²) as psqrt.
  apply (Rmult_eq_reg_l (/ dy²)).
  setr 1. intro; lra.
  setl (((1 + dx²/ dy²) * (sin x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdy2. lra.
  apply (Rmult_eq_reg_l (-1)). setl (-dy).
  setr (sqrt (dy² + dx²) * sin x).
  apply Rsqr_inj. left.
  apply Ropp_gt_lt_0_contravar. assumption.

  apply Rmult_le_pos.
  apply sqrt_pos. left. assumption.

  rewrite Rsqr_mult. symmetry.
  rewrite Rsqr_sqrt.
  repeat rewrite <- Rsqr_neg.
  assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.
  intro; lra.

  (* fourth quadrant dx *)
  rewrite cos_neg. rewrite neg_cos. rewrite cos_neg.
  assert (sin x = dy / dx * cos x) as sinxdef.
  apply (Rmult_eq_reg_r (/ cos x)).
  setl (sin x / cos x). intro. lra. 
  setr (dy / dx). split; intro; lra.
  assumption.
  apply Rinv_neq_0_compat. intro; lra.
  rewrite sinxdef in sin2cos2.
  rewrite Rsqr_mult in sin2cos2.

  assert ((cos x)² = 1 * (cos x)²) as cost1.
  field. rewrite cost1 in sin2cos2 at 2.
  rewrite <- Rmult_plus_distr_r in sin2cos2.
  rewrite Rsqr_div in sin2cos2.

  assert (0 < / - dx) as zltinvdx.
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar. assumption.
  assert (0 < / dx²) as zltinvdx2.
  rewrite Rsqr_neg.
  rewrite <- Rsqr_inv.
  apply Rsqr_pos_lt.
  intro. rewrite H in zltinvdx. lra.
  intro. lra.

  assert ((dy² + dx²) * (cos x)² = dx²) as psqrt.
  apply (Rmult_eq_reg_l (/ dx²)).
  setr 1. intro; lra.
  setl (((dy²/ dx² + 1) * (cos x)²)).
  intro; lra. assumption.
  intro. rewrite H in zltinvdx2. lra.
  apply (Rmult_eq_reg_l (-1)).
  apply Rsqr_inj. left; lra.
  setr (sqrt (dy² + dx²) *  cos x).
  apply Rmult_le_pos.
  apply sqrt_pos. left; assumption.
  setl dx².
  assert (-1 * (sqrt (dy² + dx²) * - cos x) =
          sqrt (dy² + dx²) * cos x). field.
  rewrite H. clear H. symmetry.
  rewrite Rsqr_mult.
  rewrite Rsqr_sqrt. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  intro; lra.
  intro; lra.


  (* other possibilities for x are not feasible *)
  exfalso.
  subst. assert (dy/dx = 0) as dydxdef. rewrite <- tand.
  rewrite sin_0. rewrite cos_0. field.
  rewrite dydxdef in zltdydx. lra.

  exfalso.
  apply Rgt_lt in zgtx.
  assert (-PI < x) as mPIltx.
  apply (Rlt_trans _ (-(PI/2))).
  lra. assumption.
  generalize (sin_lt_0_var x mPIltx zgtx) as sinxlt0; intro.
  assert (dy/dx < 0).
  rewrite <- tand.
  setl (- ((- sin x) * / cos x)). intro; lra.
  apply Ropp_lt_gt_0_contravar.
  apply Rlt_gt.
  apply Rmult_lt_0_compat. lra.
  apply Rinv_0_lt_compat. assumption.
  generalize H.
  apply Rlt_asym; assumption.
Qed. 

Definition atan2 y x := let (v, _) := pre_atan2 y x in v.


Lemma atan2Q1 : forall x y (xgt0 : 0 < x) (ygt0 : 0 < y), 0 < atan2 y x < PI/2.
Proof.
  intros.
  unfold atan2.
  destruct (pre_atan2 y x) as [t a].
  inversion_clear a as [trng [ydef xdef]].

  assert (0 < sqrt (y² + x²)) as zltnorm.
  apply sqrt_lt_R0.
  apply Rplus_lt_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rsqr_pos_lt. intro. lra.
  assert (0 < sin t) as zltsint.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setl 0. rewrite Rmult_comm, <- ydef. assumption.

  assert (0 < cos t) as zltcost.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setl 0. rewrite Rmult_comm, <- xdef. assumption.

  generalize sin_0 as sin_0; intro. rewrite <- sin_0 in zltsint.
  generalize cos_PI2 as cos_PI2; intro. rewrite <- cos_PI2 in zltcost.

  inversion_clear trng as [mPIltt tltPI].
  generalize PI_RGT_0 as PI_RGT_0; intro.

  split.
  destruct (Rle_dec (-(PI/2)) t).
  destruct (Rle_dec t (PI/2)).
  apply sin_increasing_0 in zltsint; try (left; lra).
  assumption.
  assumption.
  assumption.
  apply Rnot_le_lt in n. lra.
  exfalso.
  apply Rnot_le_lt in n.
  assert (t < 0) as sintlt0.
  apply (Rlt_trans _ (- (PI/2))). assumption. lra.
  rewrite sin_0 in zltsint.
  generalize (sin_lt_0_var _ mPIltt sintlt0) as sinlt0; intro.
  lra.

  destruct (Rle_dec 0 t).
  apply cos_decreasing_0 in zltcost; try (left; lra).
  assumption.
  assumption.
  assumption.

  apply Rnot_le_lt in n. lra.
Qed.

Lemma atan2Q2 : forall x y (xgt0 : x < 0) (ygt0 : 0 < y), PI/2 < atan2 y x < PI.
Proof.
  intros.
  unfold atan2.
  destruct (pre_atan2 y x) as [t a].
  inversion_clear a as [trng [ydef xdef]].

  assert (0 < sqrt (y² + x²)) as zltnorm.
  apply sqrt_lt_R0.
  apply Rplus_lt_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rsqr_pos_lt. intro. lra.

  assert (0 < sin t) as zltsint.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setl 0. rewrite Rmult_comm, <- ydef. assumption.

  assert (cos t < 0) as zltcost.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setr 0. rewrite Rmult_comm, <- xdef. assumption.

  generalize sin_0 as sin_0; intro. rewrite <- sin_0 in zltsint.
  generalize cos_PI2 as cos_PI2; intro. rewrite <- cos_PI2 in zltcost.

  inversion_clear trng as [mPIltt tlePI].
  generalize PI_RGT_0 as PI_RGT_0; intro.

  split.
  destruct (Rle_dec 0 t).
  apply cos_decreasing_0 in zltcost; try (left; lra).
  assumption.
  assumption.
  assumption.

 
  exfalso.
  apply Rnot_le_lt in n.
  apply sin_increasing_0 in zltsint; try (left; lra).
  lra.
  rewrite sin_0 in zltsint.
  generalize (sin_lt_0_var _ mPIltt n) as sinlt0; intro.
  lra.

  inversion_clear tlePI as [tltPI | teqPI].
  assumption.
  exfalso.
  subst.
  rewrite sin_0 in zltsint.
  rewrite sin_PI in zltsint.
  lra.
Qed.
     
Lemma atan2Q3 : forall x y (xgt0 : x < 0) (ygt0 : y < 0), - PI < atan2 y x < - (PI/2).
Proof.
  intros.
  unfold atan2.
  destruct (pre_atan2 y x) as [t a].
  inversion_clear a as [trng [ydef xdef]].

  assert (0 < sqrt (y² + x²)) as zltnorm.
  apply sqrt_lt_R0.
  apply Rplus_lt_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rsqr_pos_lt. intro. lra.

  assert (sin t < 0) as zltsint.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setr 0. rewrite Rmult_comm, <- ydef. assumption.

  assert (cos t < 0) as zltcost.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setr 0. rewrite Rmult_comm, <- xdef. assumption.

  generalize sin_0 as sin_0; intro. rewrite <- sin_0 in zltsint.
  generalize cos_PI2 as mcos_PI2; intro.
  rewrite <- cos_neg in mcos_PI2. rewrite <- mcos_PI2 in zltcost.

  inversion_clear trng as [mPIltt tlePI].
  generalize PI_RGT_0 as PI_RGT_0; intro.

  split.
  assumption.
  apply cos_increasing_0_var in zltcost; try (left; lra).
  assumption.

  destruct (Rle_dec t 0). assumption.
  exfalso.
  apply Rnot_le_lt in n.
  rewrite sin_0 in zltsint.
  inversion tlePI as [tltPI | teqPI].
  generalize (sin_gt_0 _ n tltPI) as sinlt0; intro.
  lra.

  subst.
  rewrite sin_PI in zltsint.
  lra.
Qed.

Lemma atan2Q4 : forall x y (xgt0 : 0 < x) (ygt0 : y < 0), - (PI/2) < atan2 y x < 0.
Proof.
  intros.
  unfold atan2.
  destruct (pre_atan2 y x) as [t a].
  inversion_clear a as [trng [ydef xdef]].

  assert (0 < sqrt (y² + x²)) as zltnorm.
  apply sqrt_lt_R0.
  apply Rplus_lt_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rsqr_pos_lt. intro. lra.

  assert (sin t < 0) as zltsint.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setr 0. rewrite Rmult_comm, <- ydef. assumption.

  assert (0 < cos t) as zltcost.
  apply (Rmult_lt_reg_r ((sqrt (y² + x²)))); [assumption |].
  setl 0. rewrite Rmult_comm, <- xdef. assumption.

  generalize sin_0 as sin_0; intro. rewrite <- sin_0 in zltsint.
  generalize cos_PI2 as mcos_PI2; intro.
  rewrite <- cos_neg in mcos_PI2. rewrite <- mcos_PI2 in zltcost.

  inversion_clear trng as [mPIltt tlePI].
  generalize PI_RGT_0 as PI_RGT_0; intro.

  split.
  apply cos_increasing_0_var in zltcost; try (left; lra).
  assumption. left.

  destruct (Rle_dec (-(PI/2)) t).
  destruct (Rle_dec t (PI/2)).
  apply sin_increasing_0 in zltsint; try (left; lra).
  assumption.
  assumption.
  assumption.

  exfalso.
  apply Rnot_le_lt in n.
  rewrite cos_neg in zltcost.
  apply cos_decreasing_0 in zltcost; try (left; lra).
  lra.
  assumption.  

  apply Rnot_le_lt in n.
  lra.

  (* again *)
    destruct (Rle_dec (-(PI/2)) t).
  destruct (Rle_dec t (PI/2)).
  apply sin_increasing_0 in zltsint; try (left; lra).
  assumption.
  assumption.
  assumption.

  exfalso.
  apply Rnot_le_lt in n.
  rewrite cos_neg in zltcost.
  apply cos_decreasing_0 in zltcost; try (left; lra).
  lra.
  assumption.  

  apply Rnot_le_lt in n.
  lra.
Qed.

Lemma atan2_PI : forall dx (xlt0 : dx < 0), atan2 0 dx = PI.
Proof.
  intros.
  unfold atan2 in *.
  destruct (pre_atan2 0 dx) as [x [xrng [dydef dxdef]]].

  assert (0² + dx² = dx²) as id. unfold Rsqr. field.
  rewrite id in dxdef. clear id.
  rewrite sqrt_Rsqr_abs in dxdef.
  rewrite Rabs_left in dxdef; [| assumption].

  assert (0 < sqrt (0² + dx²)) as nzterm.
  apply sqrt_lt_R0.
  unfold Rsqr.
  setr (dx * dx). change (0 < dx ²).
  apply Rsqr_pos_lt. intro. lra.
  assert (sin (x) = 0) as sineq0.
  symmetry.
  apply (Rmult_eq_reg_l (sqrt (0² + dx²))). setl 0. assumption.
  intro. rewrite H in nzterm. lra.
  specialize (sin_eq_0_0 _ sineq0) as [k xdef]. 

  destruct (Z_dec 1 k).
  exfalso.
  inversion_clear s as [oneltk | onegtk].
  specialize (IZR_lt _ _ oneltk) as oneltIZRk.
  inversion_clear xrng as [xrnglb xrngub].
  rewrite xdef in xrngub.
  specialize PI_RGT_0 as PI_RGT_0.
  assert (IZR k <= 1) as IZRkle1.
  apply (Rmult_le_reg_r PI). assumption.
  setr PI. assumption.
  lra.
  apply Z.gt_lt in onegtk.

  destruct (Z_dec 0 k).
  inversion_clear s as [zltk |zgtk].
  assert ((k <= 0)%Z) as kle0.
  rewrite <- (Z.lt_succ_r k 0). unfold Z.succ.
  assumption.
  omega.

  apply Z.gt_lt in zgtk.

  specialize (IZR_lt _ _ zgtk) as oneltIZRk.
  inversion_clear xrng as [xrnglb xrngub].
  rewrite xdef in xrnglb.
  specialize PI_RGT_0 as PI_RGT_0.
  assert (- 1 < IZR k) as IZRkle1.
  apply (Rmult_lt_reg_r PI). assumption.
  setl (-PI). assumption.

  assert ((k <= -1)%Z) as kle0.
  rewrite <- (Z.lt_succ_r k (-1)). unfold Z.succ.
  omega.

  assert ((-1 < k)%Z).
  apply lt_IZR. assumption.
  omega.

  rewrite <- e in xdef.
  assert (x = 0) as xeq0. rewrite xdef.
  field.
  rewrite xeq0 in dxdef.
  rewrite cos_0 in dxdef.
  assert (dx = 0) as dxeq0.
  apply (Rmult_eq_reg_l 2). setr 0.
  apply (Rplus_eq_reg_r (-dx)). setr (-dx). setl dx.
  apply (Rmult_eq_reg_r 1). setl dx. assumption.
  discrR. discrR.
  lra.
  rewrite <- e in xdef.
  rewrite xdef. field.
Qed.


Lemma atan2_0 : forall dx (xlt0 : 0 < dx), atan2 0 dx = 0.
Proof.
  intros.
  unfold atan2 in *.
  destruct (pre_atan2 0 dx) as [x [xrng [dydef dxdef]]].

  assert (0² + dx² = dx²) as id. unfold Rsqr. field.
  rewrite id in dxdef. clear id.
  rewrite sqrt_Rsqr in dxdef; [| left; assumption].
  assert (cos x = 1) as cosxeq1.
  symmetry.
  apply (Rmult_eq_reg_l dx). setl dx. assumption. intro. lra.
  inversion_clear xrng as [xrnglb xrngub].
  destruct (Rle_dec 0 x).
  assert (0 <= x < 2*PI) as xrng'. split; lra.
  generalize (cosθeq1 _ xrng' cosxeq1) as xeq0. intro.
  assumption.

  exfalso.
  apply Rnot_le_lt in n.
  rewrite <- (cos_period _ 1) in cosxeq1.
  assert (0 <= x + 2 * 1 * PI < 2*PI) as xrng'. split; lra.
  generalize (cosθeq1 _ xrng' cosxeq1) as xeq0. intro.
  assert (x  = - 2*PI) as xdef.
  apply (Rplus_eq_reg_r (2 * 1 * PI)). setr 0. assumption.
  lra.
Qed.

Lemma atan2_PI2 : forall dy (xlt0 : 0 < dy), atan2 dy 0 = PI/2.
Proof.
  intros.
  unfold atan2 in *.
  destruct (pre_atan2 dy 0) as [x [xrng [dydef dxdef]]].
  assert (dy² + 0² = dy²) as id. unfold Rsqr. field.
  rewrite id in dydef. clear id.
  rewrite sqrt_Rsqr in dydef; [ | left; assumption].
  assert (sin x = 1) as sinx. symmetry.
  apply (Rmult_eq_reg_l dy).
  setl dy.
  assumption. intro. lra.
  assert (x = PI/2 + (x - PI/2)) as id. field. rewrite id in sinx.
  rewrite <- cos_sin in sinx.
  clear id.
  inversion_clear xrng as [xrnglb xrngub].
  assert (x - PI/2 <= PI/2) as xub. lra.
  assert (- 3*PI/2 < x -  PI/2) as lub.
  apply (Rplus_lt_reg_r (PI/2)).
  setr x. setl (-PI). lra.

  destruct (Rlt_dec 0 (x - PI / 2)).
  assert (0 <= x - PI / 2 < 2 * PI) as rng.
  split; lra. 
  generalize (cosθeq1 _ rng sinx) as xval.
  intro.
  assert (x = PI/2) as xval'.
  apply (Rplus_eq_reg_r (-PI/2)).
  setr 0. setl (x - PI/2). assumption.
  subst.
  assert (0 < 2*(PI/2)).
  setr PI. lra. 
  reflexivity.

  apply Rnot_lt_ge in n.
  apply Rge_le in n.
  inversion_clear n.

  exfalso.  
  assert (0 <= (x - PI / 2) + 2* INR 1* PI < 2 * PI) as rng. unfold INR.
  split; lra.
  rewrite <- (cos_period _ 1) in sinx.
  generalize (cosθeq1 _ rng sinx) as xval. intro.
  assert (x = - 3 * PI/2) as xval'.
  apply (Rplus_eq_reg_r (3*PI/2)).
  setr 0. setl (x - PI / 2 + 2 * 1 * PI). assumption.
  lra.

  assert (x = PI/2) as xval.
  apply (Rplus_eq_reg_r (-PI/2)).
  setl (x - PI/2). setr 0. assumption.
  assumption.
Qed.

Lemma atan2_mPI2 : forall dy (xlt0 : dy < 0), atan2 dy 0 = - PI/2.
Proof.
  intros.
  unfold atan2 in *.
  destruct (pre_atan2 dy 0) as [x [xrng [dydef dxdef]]].
  assert (dy² + 0² = dy²) as id. unfold Rsqr. field.
  rewrite id in dydef. clear id.
  rewrite sqrt_Rsqr_abs, Rabs_left in dydef.
  assert (sin (- x) = 1) as sinx. symmetry.
  apply (Rmult_eq_reg_l dy).
  setl dy. rewrite sin_neg. setr (- dy * sin x).
  assumption. intro. lra.
  assert (- x = PI/2 + (- x - PI/2)) as id. field. rewrite id in sinx.
  rewrite <- cos_sin in sinx.
  clear id.
  inversion_clear xrng as [xrnglb xrngub].
  assert (- x - PI/2 <= PI/2) as xub. lra.
  assert (- 3*PI/2 <= - x -  PI/2) as lub.
  apply (Rplus_le_reg_r (PI/2)).
  setr (- x). setl (-PI). lra.

  destruct (Rlt_dec 0 (- x - PI / 2)).
  assert (0 <= - x - PI / 2 < 2 * PI) as rng.
  split; lra. 
  generalize (cosθeq1 _ rng sinx) as xval.
  intro.
  assert (x = - PI/2) as xval'.
  apply (Rplus_eq_reg_r (-x )).
  setl 0. setr (- x - PI/2). symmetry. assumption.
  subst.
  assert (0 < 2*(- PI/2)).
  setr (-PI). lra. 
  lra.
  
  apply Rnot_lt_ge in n.
  apply Rge_le in n.
  inversion_clear n.

  exfalso.  
  assert (0 <= (- x - PI / 2) + 2* INR 1* PI < 2 * PI) as rng. unfold INR.
  split; lra.
  rewrite <- (cos_period _ 1) in sinx.
  generalize (cosθeq1 _ rng sinx) as xval. intro.
  assert (2 * x = 3 * PI) as xval'.
  apply (Rmult_eq_reg_r (/2)).
  apply (Rplus_eq_reg_r (- x)).
  setl 0. setr (- x - PI / 2 + 2 * 1 * PI). symmetry. assumption.
  apply Rinv_neq_0_compat.
  discrR.
  lra.

  assert (x = - PI/2) as xval.
  apply (Rplus_eq_reg_r (- x)).
  setl 0. setr (- x - PI/2). symmetry. assumption.
  assumption.
  assumption.
Qed.


Lemma atan2_val : forall dy dx θ, - PI < θ <= PI -> (dy <> 0 \/ dx <> 0) -> 
    dy = sqrt (dy² + dx²) * sin θ -> dx = sqrt (dy² + dx²) * cos θ ->
    atan2 dy dx = θ.
Proof.
  intros dy dx θ H noc. intros.
  specialize PI_RGT_0 as PI_RGT_0.
  assert (0 < sqrt (dy² + dx²)) as sqrtdy2pldy2gt0.
  apply sqrt_lt_R0.
  inversion noc.
  apply Rplus_lt_le_0_compat.
  apply Rlt_0_sqr. assumption.
  apply Rle_0_sqr.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr. 
  apply Rlt_0_sqr. assumption.
  
  unfold atan2.
  destruct (pre_atan2 dy dx) as [x [xrng [dydef dxdef]]].

  destruct (Req_dec (cos θ) 0) as [costeq0 | costne0].
  specialize (coseq0_sinneq0 _ costeq0) as sintne0.
  rewrite costeq0 in H1.
  assert (dx = 0) as dxeq0.
  fieldrewrite (0) (sqrt (dy² + dx²) * 0). assumption. clear H1.
  rewrite dxeq0 in *.
  specialize (cosθeq0 _ H costeq0) as thval.
  assert (dy² = (dy² + 0²)) as dy2def. unfold Rsqr. field.
  rewrite <- dy2def in *. clear dy2def.
  rewrite sqrt_Rsqr_abs in *.
  destruct (Rlt_dec 0 dy).
  inversion_clear thval as [theqpi2 | theqmpi2].
  subst.
  rewrite sin_PI2 in H0.
  rewrite Rabs_right in *; try lra.
  assert (cos x = 0) as cosxeq0. symmetry.
  apply (Rmult_eq_reg_l dy). setl 0. assumption.
  intro. rewrite H1 in r. lra.
  specialize (cosθeq0 _ xrng cosxeq0) as xval.
  inversion_clear xval as [xeqPI2 | xeqmPI2].
  assumption.
  exfalso.
  rewrite xeqmPI2 in dydef.
  assert (- PI / 2 = - (PI / 2)) as id. field. rewrite id in dydef.
  rewrite sin_neg in dydef.
  rewrite sin_PI2 in dydef. lra.
  rewrite theqmpi2 in H0.
  assert (- PI / 2 = - (PI / 2)) as id. field. rewrite id in H0.
  rewrite sin_neg in H0.
  rewrite sin_PI2 in H0. exfalso.
  rewrite Rabs_right in H0; lra.

  apply Rnot_lt_le in n.
  inversion_clear n.
  rewrite (Rabs_left dy) in *; try assumption.

  inversion_clear thval as [theqPI2 | theqmPI2].
  rewrite theqPI2 in H0. rewrite sin_PI2 in H0.
  exfalso.
  assert (dy = -dy) as dydef'. setr (- dy * 1). assumption.
  lra.
  subst. clear H0.
  assert (cos x = 0) as cosxeq0. symmetry.
  apply (Rmult_eq_reg_l (-dy)). setl 0. assumption.
  intro. lra.
  specialize (cosθeq0 _ xrng cosxeq0) as xval.
  inversion_clear xval as [xeqPI2 | xeqmPI2].
  exfalso.
  rewrite xeqPI2 in dydef.
  rewrite sin_PI2 in dydef.
  assert (dy = -dy) as dydef'. setr (-dy * 1). assumption.
  lra.
  assumption.
  inversion noc as [noc' | noc']; exfalso; apply noc';
    [assumption | reflexivity ].

  rewrite H0 in dydef at 1.
  rewrite H1 in dxdef at 1.
  assert (sin θ = sin x) as sineq.
  apply (Rmult_eq_reg_l (sqrt (dy² + dx²))). assumption.
  intro. lra.

  assert (cos θ = cos x) as coseq.
  apply (Rmult_eq_reg_l (sqrt (dy² + dx²))). assumption.
  intro. lra.

  assert (tan θ = tan x) as taneq.
  unfold tan.
  rewrite sineq, coseq. reflexivity.

  destruct (Rlt_dec x (PI/2)).
  destruct (Rlt_dec (-PI/2) x).

  destruct (Rlt_dec θ (PI/2)).
  destruct (Rlt_dec (-PI/2) θ).
  apply tan_is_inj. split; assumption. split; assumption.
  rewrite taneq.
  reflexivity.

  exfalso.
  apply Rnot_lt_le in n.
  assert (0 < cos x) as zltcosx.
  assert (- PI /2 = - (PI/2)) as id. field. rewrite id in r0.
  apply cos_gt_0; lra.
  assert (cos θ <= 0) as costle0.
  inversion_clear H.
  rewrite <- (cos_period _ (1%nat)).
  specialize PI_RGT_0 as PI_RGT_0.
  assert (PI/2 <= (θ + 2 * INR 1 * PI)). unfold INR. lra.
  assert ((θ + 2 * INR 1 * PI) <= 3 * (PI/2)). unfold INR.
  setr (2 * 1 * PI + - PI/2). lra.
  apply cos_le_0; try assumption.
  lra.

  exfalso.
  apply Rnot_lt_le in n.
  assert (0 < cos x) as zltcosx.
  assert (- PI /2 = - (PI/2)) as id. field. rewrite id in r0.
  apply cos_gt_0; lra.
  assert (cos θ <= 0) as costle0.
  inversion_clear H.
  assert (θ  <= 3 * (PI/2)). apply (Rle_trans _ PI). assumption.
  setr (PI + PI/2). lra.
  apply cos_le_0; try assumption.
  lra.

  apply Rnot_lt_le in n.
  destruct (Rlt_dec θ (-PI/2)) as [tlemPI2 | tgemPI2].
  inversion_clear H as [tlb tub].
  inversion_clear xrng as [xlb xub].
  inversion_clear n as [xltmPI2 | xeqmPI2].

  rewrite <- (tan_period_1 _ 1) in taneq at 1.
  rewrite <- (tan_period_1 x 1) in taneq at 1.
  apply (Rplus_eq_reg_r (INR 1 * PI)).
  symmetry.
  assert (-PI/2<x+INR 1 * PI<PI/2) as xrng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (-PI)).
  setl x. setr (-PI/2). assumption.
  assert (-PI/2<θ+INR 1 * PI<PI/2) as trng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (-PI)).
  setl θ. setr (-PI/2). assumption.
  apply (tan_is_inj _ _ trng xrng taneq).
  rewrite <- coseq. assumption. assumption.

  exfalso.
  assert (x = - (PI/2)) as xeqmPI2'. rewrite xeqmPI2. field.
  rewrite xeqmPI2' in *.
  rewrite cos_neg in coseq.
  rewrite cos_PI2 in coseq.
  apply costne0. assumption.

  inversion_clear n as [xltmPI2 | xeqmPI2].
  apply Rnot_lt_le in tgemPI2.
  inversion_clear xrng as [xlb xub]. clear r xub.
  inversion_clear H as [tlb tub]. clear tlb.

  exfalso.
  destruct (Rle_dec θ (PI/2)) as [tlePI2 | tgtPI2].
  assert (- (PI / 2) <= θ) as tgtmPI2'. setl (- PI/2). lra.
  specialize (cos_ge_0 θ tgtmPI2' tlePI2) as zlecost.
  assert (PI / 2 < x + 2 * INR 1 * PI) as xpub. unfold INR. lra.
  assert (x + 2 * INR 1 * PI < 3 * (PI / 2)) as xplb. unfold INR.
  apply (Rplus_lt_reg_r (- 4 * (PI/2))).
  setl x. setr (- PI/2). assumption.
  specialize (cos_lt_0 (x+2*INR 1 * PI) xpub xplb) as cosxlt0.
  rewrite cos_period in cosxlt0.
  rewrite coseq in zlecost. lra.

  apply Rnot_le_lt in tgtPI2.
  assert (PI < x + 2 * INR 1 * PI) as xplb. unfold INR. lra.
  assert (x + 2 * INR 1 * PI < 2 * PI) as xpub. unfold INR.
  apply (Rplus_lt_reg_r (-2*PI)).
  setl x. setr 0. apply (Rlt_trans _ (-PI/2)). assumption.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0. 
  lra.
  specialize (sin_lt_0 (x+ 2 * INR 1 * PI) xplb xpub) as sinlt0.
  rewrite sin_period in sinlt0.

  assert (0 <= θ) as zlet. lra.
  specialize (sin_ge_0 θ zlet tub) as zlesin.
  rewrite sineq in zlesin. lra.

  exfalso. subst.
  assert (- PI / 2 = -(PI/2)) as id. field. rewrite id in coseq. clear id.
  rewrite cos_neg in coseq. rewrite cos_PI2 in coseq.
  apply costne0. assumption.

  (* last section *)
  apply Rnot_lt_le in n.
  inversion_clear xrng as [xlb xub]. clear xlb.
  inversion_clear n as [PI2ltx | PI2eqx];
    [ | exfalso; subst;
        rewrite cos_PI2 in coseq;
        apply costne0; assumption].
  destruct (Rlt_dec (PI/2) θ).
  inversion_clear H as [tlb tub]. clear tlb.

  assert (x = (x - INR 1 * PI) +  INR 1 * PI) as xid. unfold INR. field.
  assert (θ = (θ - INR 1 * PI) +  INR 1 * PI) as tid. unfold INR. field.
  rewrite xid, tid in taneq.
  rewrite (tan_period_2 _ 1) in taneq at 1;
    [| rewrite <- tid; assumption].
  rewrite (tan_period_2 _ 1) in taneq at 1;
    [| rewrite <- xid; rewrite <- coseq; assumption].
  apply (Rplus_eq_reg_r (- INR 1 * PI)).
  setl (x - INR 1 * PI). setr (θ - INR 1 * PI).
  symmetry.
  
  assert (-PI/2<x-INR 1 * PI<PI/2) as xrng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (PI)).
  setl x. setr (3 * PI/2).
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (3 * PI). lra.
  assert (-PI/2<θ-INR 1 * PI<PI/2) as trng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (PI)).
  setl θ. setr (3*PI/2).
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (3 * PI). lra.
  apply (tan_is_inj _ _ trng xrng taneq).

  apply Rnot_lt_le in n.
  inversion_clear H as [tlb tub]. clear tub.

  exfalso.
  destruct (Rle_dec (-PI/2) θ) as [mPI2let | mPI2gtt]. clear tlb.

  
  assert (-( PI / 2) <= θ) as mPI2let'. setl (- PI /2).  assumption.
  specialize (cos_ge_0 _ mPI2let' n) as costge0.
  assert (x < 3*(PI/2)) as xlt3PI2. apply (Rle_lt_trans _ PI); [assumption|].
  assert (PI = 2 * (PI/2)) as id. field. rewrite id at 1.  lra.
  specialize (cos_lt_0 _ PI2ltx xlt3PI2) as cosxlt0. rewrite coseq in costge0.
  lra.

  apply Rnot_le_lt in mPI2gtt. clear n.
  assert (0 <= x) as zlex. lra.
  specialize (sin_ge_0 _ zlex xub) as sinxge0.
  assert (PI < θ + 2 * INR 1 * PI) as PIlet. unfold INR. lra.
  assert (θ + 2 * INR 1 * PI < 2 * PI) as tlt2PI. unfold INR.
  apply (Rplus_lt_reg_r (- 2 * PI)). setr 0. setl θ.
  apply (Rlt_trans _ (-PI/2)). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI). lra.
  specialize (sin_lt_0 _ PIlet tlt2PI) as sintlt0.
  rewrite sin_period in sintlt0.
  rewrite sineq in sintlt0. lra.
Qed.

Lemma atan2_right_inv : forall (dx dy : R),
    dx <> 0 -> tan (atan2 dy dx) = dy/dx.
Proof.
  intros.
  assert (0 < sqrt (dy² + dx²)).
  apply sqrt_lt_R0.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rlt_0_sqr; assumption.
  unfold atan2.
  destruct (pre_atan2 dy dx) as [x [[xlb xub] [dydef dxdef]]].
  assert (sin x = dy / sqrt (dy² + dx²)) as sinx.
  apply (Rmult_eq_reg_l (sqrt (dy² + dx²)));
    [ setr dy;
      [change (sqrt (dy² + dx²) <> 0); intro; lra |
       symmetry; assumption]
    | intro; lra ].
  assert (cos x = dx / sqrt (dy² + dx²)) as cosx.
  apply (Rmult_eq_reg_l (sqrt (dy² + dx²)));
    [ setr dx;
      [change (sqrt (dy² + dx²) <> 0); intro; lra |
       symmetry; assumption]
    | intro; lra ].
  assert (cos x <> 0) as cosxne0.
  intro. apply H.
  apply (Rmult_eq_reg_r (/ sqrt (dy² + dx²))).
  setl (dx / sqrt (dy² + dx²)).
  change (sqrt (dy² + dx²) <> 0). intro. lra.
  setr 0.
  change (sqrt (dy² + dx²) <> 0). intro. lra.
  rewrite <- H1. symmetry. assumption.
  apply Rinv_neq_0_compat. intro. lra.
  unfold tan.
  apply (Rmult_eq_reg_r (cos x * dx)).
  setl (dx * sin x); try assumption. setr (dy * cos x); try assumption.
  rewrite dydef. rewrite dxdef at 1. field.
  apply Rmult_integral_contrapositive_currified; assumption.
Qed.

Lemma atan2_left_inv : forall (t q : R) (trng :-PI < t <= PI),
    0 < q -> atan2 (q * sin t) (q * cos t) = t.
Proof.
  intros.
  unfold atan2.
  destruct (pre_atan2 (q * sin t) (q * cos t)) as [x [xrng [dydef dxdef]]].
  assert (((q * sin t)² + (q * cos t)²) = q²) as id.
  unfold Rsqr.
  fieldrewrite (q * sin t * (q * sin t) + q * cos t * (q * cos t))
               (q * q * ((sin t * sin t) + (cos t * cos t))).
  change (q * q * ((sin t)² + (cos t)²) = q * q). rewrite sin2_cos2. field.  
  rewrite id in dxdef, dydef. clear id.
  rewrite sqrt_Rsqr in dydef, dxdef; try (left; assumption).
  apply Rmult_eq_reg_l in dydef; [|intro; lra].
  apply Rmult_eq_reg_l in dxdef; [|intro; lra].

  (*********************)
  assert (tan t = tan x) as taneq.
  unfold tan.
  rewrite dxdef, dydef. reflexivity.

  destruct (Rlt_dec x (PI/2)).
  destruct (Rlt_dec (-PI/2) x).

  destruct (Rlt_dec t (PI/2)).
  destruct (Rlt_dec (-PI/2) t).
  apply tan_is_inj. split; assumption. split; assumption.
  rewrite taneq.
  reflexivity.

  exfalso.
  apply Rnot_lt_le in n. clear r1.
  assert (0 < cos x) as zltcosx.
  assert (- PI /2 = - (PI/2)) as id. field. rewrite id in r0.
  apply cos_gt_0; lra.
  assert (cos t <= 0) as costle0.
  inversion_clear trng.
  rewrite <- (cos_period _ (1%nat)).
  specialize PI_RGT_0 as PI_RGT_0.
  assert (PI/2 <= (t + 2 * INR 1 * PI)). unfold INR. lra.
  assert ((t + 2 * INR 1 * PI) <= 3 * (PI/2)). unfold INR.
  setr (2 * 1 * PI + - PI/2). lra.
  apply cos_le_0; try assumption.
  lra.

  exfalso.
  apply Rnot_lt_le in n.
  assert (0 < cos x) as zltcosx.
  assert (- PI /2 = - (PI/2)) as id. field. rewrite id in r0.
  apply cos_gt_0; lra.
  assert (cos t <= 0) as costle0.
  inversion_clear trng.
  assert (t  <= 3 * (PI/2)). apply (Rle_trans _ PI). assumption.
  setr (PI + PI/2). lra.
  apply cos_le_0; try assumption.
  lra.

  apply Rnot_lt_le in n.
  destruct (Rlt_dec t (-PI/2)) as [tlemPI2 | tgemPI2].
  inversion trng as [tlb tub].
  inversion xrng as [xlb xub].
  inversion_clear n as [xltmPI2 | xeqmPI2].
  clear r tub.
  
  rewrite <- (tan_period_1 _ 1) in taneq at 1.
  rewrite <- (tan_period_1 x 1) in taneq at 1.
  apply (Rplus_eq_reg_r (INR 1 * PI)).
  symmetry.
  assert (-PI/2<x+INR 1 * PI<PI/2) as xrng2. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (-PI)).
  setl x. setr (-PI/2). assumption.
  assert (-PI/2<t+INR 1 * PI<PI/2) as trng2. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (-PI)).
  setl t. setr (-PI/2). assumption.
  apply (tan_is_inj _ _ trng2 xrng2 taneq).

  intro. rewrite H0 in dxdef.
  specialize (cosθeq0 _ xrng H0) as [xeqPI2 | xeqmPI2].
  specialize PI_RGT_0 as PI_RGT_0. 
  rewrite xeqPI2 in xltmPI2.
  assert (PI < - PI) as ns. apply (Rmult_lt_reg_r (/2)).
  apply Rinv_0_lt_compat. lra. assumption. lra.
  rewrite xeqmPI2 in xltmPI2. lra.

  intro. rewrite H0 in dxdef.
  specialize (cosθeq0 _ trng H0) as [xeqPI2 | xeqmPI2].
  specialize PI_RGT_0 as PI_RGT_0. 
  rewrite xeqPI2 in tlemPI2.
  assert (PI < - PI) as ns. apply (Rmult_lt_reg_r (/2)).
  apply Rinv_0_lt_compat. lra. assumption. lra.
  rewrite xeqmPI2 in tlemPI2. lra.

  exfalso. clear tub xub xlb r.
  assert (x = - (PI/2)) as xeqmPI2'. rewrite xeqmPI2. field.
  rewrite xeqmPI2' in *.
  rewrite cos_neg in dxdef.
  rewrite cos_PI2 in dxdef.

  assert (t + 2 * INR 1 * PI < 3 * (PI/2)) as tub.
  unfold INR. apply (Rplus_lt_reg_r (- 2 * PI)).
  setl t. setr (- PI/2). assumption.
  assert (PI/2 < t + 2 * INR 1 * PI) as tlb'.
  unfold INR. apply (Rplus_lt_reg_r (- 2 * PI)).
  setl (- 3 * PI / 2). setr t.
  apply (Rlt_trans _ (-PI)).
  apply (Rmult_lt_reg_r 2). lra.
  setl (-3*PI). lra. assumption.

  specialize (cos_lt_0 _ tlb' tub) as costlt0.
  rewrite cos_period in costlt0. rewrite dxdef in costlt0. lra.
  
  inversion_clear n as [xltmPI2 | xeqmPI2].
  apply Rnot_lt_le in tgemPI2.
  inversion_clear xrng as [xlb xub]. clear r xub.
  inversion_clear trng as [tlb tub]. clear tlb.

  exfalso.
  destruct (Rle_dec t (PI/2)) as [tlePI2 | tgtPI2].
  assert (- (PI / 2) <= t) as tgtmPI2'. setl (- PI/2). lra.
  specialize (cos_ge_0 t tgtmPI2' tlePI2) as zlecost.
  assert (PI / 2 < x + 2 * INR 1 * PI) as xpub. unfold INR. lra.
  assert (x + 2 * INR 1 * PI < 3 * (PI / 2)) as xplb. unfold INR.
  apply (Rplus_lt_reg_r (- 4 * (PI/2))).
  setl x. setr (- PI/2). assumption.
  specialize (cos_lt_0 (x+2*INR 1 * PI) xpub xplb) as cosxlt0.
  rewrite cos_period in cosxlt0.
  rewrite dxdef in zlecost. lra.

  apply Rnot_le_lt in tgtPI2.
  assert (PI < x + 2 * INR 1 * PI) as xplb. unfold INR. lra.
  assert (x + 2 * INR 1 * PI < 2 * PI) as xpub. unfold INR.
  apply (Rplus_lt_reg_r (-2*PI)).
  setl x. setr 0. apply (Rlt_trans _ (-PI/2)). assumption.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0. 
  lra.
  specialize (sin_lt_0 (x+ 2 * INR 1 * PI) xplb xpub) as sinlt0.
  rewrite sin_period in sinlt0.

  assert (0 <= t) as zlet. lra.
  specialize (sin_ge_0 t zlet tub) as zlesin.
  rewrite dydef in zlesin. lra.

  apply Rnot_lt_le in tgemPI2.
  inversion_clear tgemPI2 as [mPI2ltt | mPI2eqt].
  subst. assert (- PI / 2 = -(PI/2)) as id. field.
  rewrite id in dxdef, dydef.
  rewrite cos_neg, cos_PI2 in dxdef.
  rewrite sin_neg, sin_PI2 in dydef.

  destruct (Rlt_dec t (PI/2)). rewrite id in mPI2ltt.
  specialize (cos_gt_0 _ mPI2ltt r0) as zltcost.
  rewrite dxdef in zltcost. lra.
  apply Rnot_lt_le in n.
  inversion_clear trng as [tlb tub].
  assert (0 <= t) as zlet. apply (Rle_trans _ (PI/2)).
  left. lra. assumption.
  specialize (sin_ge_0 _ zlet tub) as zlesint.
  rewrite dydef in zlesint. lra. rewrite mPI2eqt in xeqmPI2.
  assumption.

  apply Rnot_lt_le in n.
  inversion_clear xrng as [xlb xub]. clear xlb.
  inversion_clear n as [PI2ltx | PI2eqx].
  destruct (Rlt_dec (PI/2) t).
  inversion_clear trng as [tlb tub]. clear tlb.

  assert (x = (x - INR 1 * PI) +  INR 1 * PI) as xid. unfold INR. field.
  assert (t = (t - INR 1 * PI) +  INR 1 * PI) as tid. unfold INR. field.
  rewrite xid, tid in taneq.

  assert (t < 3*(PI/2)) as tlt3PI2.
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra.
  setr (3*PI). lra.
  specialize (cos_lt_0 _ r tlt3PI2) as costlt0.
  rewrite (tan_period_2 _ 1) in taneq at 1;
    [ | unfold INR; fieldrewrite (t - 1 * PI + 1 * PI) t;
        intro costeq0; rewrite costeq0 in costlt0; lra].

  assert (x < 3*(PI/2)) as xlt3PI2.
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra.
  setr (3*PI). lra.
  specialize (cos_lt_0 _ PI2ltx xlt3PI2) as cosxlt0.

  rewrite (tan_period_2 _ 1) in taneq at 1;
    [ | unfold INR; fieldrewrite (x - 1 * PI + 1 * PI) x;
        intro cosxeq0; rewrite cosxeq0 in cosxlt0; lra].

  apply (Rplus_eq_reg_r (- INR 1 * PI)).
  setl (x - INR 1 * PI). setr (t - INR 1 * PI).
  symmetry.
  
  assert (-PI/2<x-INR 1 * PI<PI/2) as xrng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (PI)).
  setl x. setr (3 * PI/2).
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (3 * PI). lra.
  assert (-PI/2<t-INR 1 * PI<PI/2) as trng. unfold INR.
  split. setl (-(PI/2)). lra.
  apply (Rplus_lt_reg_r (PI)).
  setl t. setr (3*PI/2).
  apply (Rle_lt_trans _ PI). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (3 * PI). lra.
  apply (tan_is_inj _ _ trng xrng taneq).

  apply Rnot_lt_le in n.
  inversion_clear trng as [tlb tub]. clear tub.

  exfalso.
  destruct (Rle_dec (-PI/2) t) as [mPI2let | mPI2gtt]. clear tlb.

  
  assert (-( PI / 2) <= t) as mPI2let'. setl (- PI /2).  assumption.
  specialize (cos_ge_0 _ mPI2let' n) as costge0.
  assert (x < 3*(PI/2)) as xlt3PI2. apply (Rle_lt_trans _ PI); [assumption|].
  assert (PI = 2 * (PI/2)) as id. field. rewrite id at 1.  lra.
  specialize (cos_lt_0 _ PI2ltx xlt3PI2) as cosxlt0. rewrite dxdef in costge0.
  lra.

  apply Rnot_le_lt in mPI2gtt. clear n.
  assert (0 <= x) as zlex. lra.
  specialize (sin_ge_0 _ zlex xub) as sinxge0.
  assert (PI < t + 2 * INR 1 * PI) as PIlet. unfold INR. lra.
  assert (t + 2 * INR 1 * PI < 2 * PI) as tlt2PI. unfold INR.
  apply (Rplus_lt_reg_r (- 2 * PI)). setr 0. setl t.
  apply (Rlt_trans _ (-PI/2)). assumption.
  apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI). lra.
  specialize (sin_lt_0 _ PIlet tlt2PI) as sintlt0.
  rewrite sin_period in sintlt0.
  rewrite dydef in sintlt0. lra.

  subst.
  rewrite sin_PI2 in dydef.
  rewrite cos_PI2 in dxdef.

  specialize (cosθeq0 _ trng dxdef) as [xeqPI2 | xeqnPI2].
  subst. reflexivity.

  exfalso. rewrite xeqnPI2 in dydef.
  assert (- PI/2 = -(PI/2)) as id. field. rewrite id in dydef.
  rewrite sin_neg, sin_PI2 in dydef. lra.
Qed.

Corollary atan2_left_inv_neg_npos : forall (t q : R) (trng :-PI < t <= 0),
    q < 0 -> atan2 (q * sin t) (q * cos t) = t + PI.
Proof.
  intros.
  specialize (Ropp_gt_lt_0_contravar _ H) as nq_pos.
  assert (q * sin t = (-q) * (sin (t + PI))) as EQ1.
  { rewrite neg_sin; lra. }
  assert (q * cos t = (-q) * (cos (t + PI))) as EQ2.
  { rewrite neg_cos; lra. }
  rewrite EQ1, EQ2.
  apply atan2_left_inv; lra.
Qed.

Corollary atan2_left_inv_neg_pos : forall (t q : R) (trng : 0 < t <= PI),
    q < 0 -> atan2 (q * sin t) (q * cos t) = t - PI.
Proof.
  intros.
  specialize (Ropp_gt_lt_0_contravar _ H) as nq_pos.
  assert (q * sin t = (-q) * (sin (t + PI))) as EQ1.
  { rewrite neg_sin; lra. }
  assert (q * cos t = (-q) * (cos (t + PI))) as EQ2.
  { rewrite neg_cos; lra. }
  rewrite EQ1, EQ2.
  rewrite <- (sin_period1 _ (-1)).
  rewrite <- (cos_period1 _ (-1)).
  assert (t + PI + 2 * -1 * PI = t - PI) as EQ3; [lra|].
  rewrite EQ3.
  apply atan2_left_inv; lra.
Qed.

Lemma atan2_0_impl : forall (dx dy : R)
    (nc : ~(dx = 0 /\ dy = 0)), atan2 dy dx = 0 -> 0 < dx /\ dy = 0.
Proof.
  intros.
  destruct (Rlt_dec 0 dx).
  destruct (Req_dec dy 0).
  split; assumption.

  exfalso.
  destruct (Rlt_dec dy 0).
  specialize (atan2Q4 _ _ r r0) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ledy | R0eqdy]; auto.
  specialize (atan2Q1 _ _ r R0ledy) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].

  destruct (Rlt_dec dy 0).
  specialize (atan2Q3 _ _ R0ltdx r) as [lb ub]. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2Q2 _ _ R0ltdx R0ltdy) as [lb ub]. lra.

  rewrite <- R0eqdy in H.
  specialize (atan2_PI _ R0ltdx) as atan20.
  rewrite atan20 in H.
  specialize (PI_RGT_0) as PIgt0. lra.

  rewrite R0eqdx in *.
  destruct (Rlt_dec dy 0).
  specialize (atan2_mPI2 _ r) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  assert (0 = -1) as ns.
  apply (Rmult_eq_reg_r (PI/2)). setl 0. setr (- PI /2).
  assumption. intro. lra. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2_PI2 _ R0ltdy) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  assert (0 = 1) as ns.
  apply (Rmult_eq_reg_r (PI/2)). setl 0. setr (PI /2).
  assumption. intro. lra. lra.
  apply nc. auto.
Qed.

Lemma atan2_PI_impl : forall (dx dy : R) (nc : ~(dx = 0 /\ dy = 0)),
    atan2 dy dx = PI -> dx < 0 /\ dy = 0.
Proof.
  intros.
  destruct (Rlt_dec dx 0).
  destruct (Req_dec dy 0).
  split; assumption.

  exfalso.
  destruct (Rlt_dec dy 0).
  specialize (atan2Q3 _ _ r r0) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ledy | R0eqdy]; auto.
  specialize (atan2Q2 _ _ r R0ledy) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].

  destruct (Rlt_dec dy 0).
  specialize (atan2Q4 _ _ R0ltdx r) as [lb ub]. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2Q1 _ _ R0ltdx R0ltdy) as [lb ub]. lra.

  rewrite <- R0eqdy in H.
  specialize (atan2_0 _ R0ltdx) as atan20.
  rewrite atan20 in H.
  specialize (PI_RGT_0) as PIgt0. lra.

  rewrite <- R0eqdx in H.
  destruct (Rlt_dec dy 0).
  specialize (atan2_mPI2 _ r) as atan20.
  rewrite H in atan20. 
  specialize (PI_RGT_0) as PIgt0.
  assert (2 = -1) as ns.
  apply (Rmult_eq_reg_r (PI/2)). setl PI. setr (- PI /2).
  assumption. intro. lra. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2_PI2 _ R0ltdy) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  assert (2 = 1) as ns.
  apply (Rmult_eq_reg_r (PI/2)). setl PI. setr (PI /2).
  assumption. intro. lra. lra.
  apply nc. auto.
Qed.

Lemma atan2_PI2_impl : forall (dx dy : R) (nc : ~(dx = 0 /\ dy = 0)),
    atan2 dy dx = PI / 2 -> dx = 0 /\ 0 < dy.
Proof.
  intros.
  destruct (Rlt_dec 0 dy).
  destruct (Req_dec dx 0).
  split; assumption.

  exfalso.
  destruct (Rlt_dec dx 0).
  specialize (atan2Q2 _ _ r0 r) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ledy | R0eqdy]; auto.
  specialize (atan2Q1 _ _ R0ledy r) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].

  destruct (Rlt_dec dx 0).
  specialize (atan2Q3 _ _ r R0ltdy) as [lb ub]. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].
  specialize (atan2Q4 _ _ R0ltdx R0ltdy) as [lb ub]. lra.

  rewrite <- R0eqdx in H.
  symmetry in R0eqdx.
  specialize (atan2_mPI2 _ R0ltdy) as atan20.
  rewrite atan20 in H.
  specialize (PI_RGT_0) as PIgt0. lra.

  rewrite R0eqdy in *.
  destruct (Rlt_dec dx 0).
  specialize (atan2_PI _ r) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  lra.
  
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].
  specialize (atan2_0 _ R0ltdx) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  lra.
  lra.
Qed.

Lemma atan2_mPI2_impl : forall (dx dy : R) (nc : ~(dx = 0 /\ dy = 0)),
    atan2 dy dx = - PI / 2 -> dx = 0 /\ dy < 0.
Proof.
  intros.
  destruct (Rlt_dec 0 dy).
  destruct (Req_dec dx 0).

  exfalso.
  specialize (atan2_PI2 _ r) as atd.
  rewrite H0, atd in H.
  specialize (PI_RGT_0) as PIgt0. lra.

  exfalso.
  destruct (Rlt_dec dx 0).
  specialize (atan2Q2 _ _ r0 r) as [lb ub]. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ledy | R0eqdy]; auto.
  specialize (atan2Q1 _ _ R0ledy r) as [lb ub]. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].

  destruct (Rlt_dec dx 0).
  specialize (atan2Q3 _ _ r R0ltdy) as [lb ub]. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].
  specialize (atan2Q4 _ _ R0ltdx R0ltdy) as [lb ub]. lra.

  rewrite <- R0eqdx in H.
  symmetry in R0eqdx.
  specialize (atan2_mPI2 _ R0ltdy) as atan20.
  rewrite atan20 in H.
  specialize (PI_RGT_0) as PIgt0. lra.

  rewrite R0eqdy in *.
  destruct (Rlt_dec dx 0).
  specialize (atan2_PI _ r) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  lra.
  
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].
  specialize (atan2_0 _ R0ltdx) as atan20.
  rewrite H in atan20.
  specialize (PI_RGT_0) as PIgt0.
  lra.
  lra.
Qed.

Lemma atan2_bound : forall (dx dy : R) (nc : ~(dx = 0 /\ dy = 0)),  
    -PI < atan2 dy dx <= PI.
Proof.
  intros.
  specialize (PI_RGT_0) as PIgt0. 
  destruct (Rlt_dec dx 0).
  destruct (Req_dec dy 0).
  specialize (atan2_PI _ r) as atan2val.
  rewrite H, atan2val.
  split; lra.

  destruct (Rlt_dec dy 0).
  specialize (atan2Q3 _ _ r r0) as [lb ub]. split; lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ledy | R0eqdy]; auto.
  specialize (atan2Q2 _ _ r R0ledy) as [lb ub]. split; lra.
  exfalso. apply H. rewrite R0eqdy. reflexivity.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdx | R0eqdx].

  destruct (Rlt_dec dy 0).
  specialize (atan2Q4 _ _ R0ltdx r) as [lb ub]. split; lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2Q1 _ _ R0ltdx R0ltdy) as [lb ub]. split; lra.

  rewrite <- R0eqdy.
  specialize (atan2_0 _ R0ltdx) as atan20.
  rewrite atan20.
  split; lra.

  rewrite <- R0eqdx.
  destruct (Rlt_dec dy 0).
  specialize (atan2_mPI2 _ r) as atan20.
  rewrite atan20.
  split.
  apply (Rmult_lt_reg_l (/PI)).
  apply Rinv_0_lt_compat. assumption.
  setl (-1). intro. subst. lra.
  setr (-1/2). intro. subst. lra.
  lra. apply (Rle_trans _ 0).
  apply (Rmult_le_reg_l 2). lra. setl (-PI). setr 0. lra.
  lra.
  
  apply Rnot_lt_le in n.
  inversion_clear n as [R0ltdy | R0eqdy].
  specialize (atan2_PI2 _ R0ltdy) as atan20.
  rewrite atan20.
  split; lra.
  

  exfalso.
  apply nc. auto.
Qed.

Lemma atan2Q2_rev : forall dx dy,
    ~(dx=0/\dy=0) -> PI / 2 < atan2 dy dx < PI -> dx < 0 /\ 0 < dy.
Proof.
  intros *. intros notO at2rng.
  destruct (Rlt_dec dx 0).
  destruct (Rlt_dec 0 dy).
  split; assumption.

  exfalso.
  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  destruct at2rng.
  specialize (atan2Q3 _ _ r dylt0) as [arl aru].
  lra.

  subst.
  destruct at2rng.
  specialize (atan2_PI _ r) as at2PI.
  subst. lra.

  exfalso.
  apply Rnot_lt_le in n.
  destruct n as [zltdx |zeqdx].
  destruct (Rlt_dec 0 dy).
  destruct at2rng.
  specialize (atan2Q1 _ _ zltdx r) as [at2l at2u].
  lra.

  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  destruct at2rng.
  specialize (atan2Q4 _ _ zltdx dylt0) as [at2l at2u].
  lra.

  subst.
  destruct at2rng.
  specialize (atan2_0 _ zltdx) as at2PI.
  rewrite at2PI in H. clear - H zltdx.
  specialize PI_RGT_0 as pigt0.
  lra.

  subst.
  destruct (Rlt_dec 0 dy).
  rewrite atan2_PI2 in at2rng; try assumption.
  destruct at2rng.
  lra.

  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  rewrite atan2_mPI2 in at2rng; try assumption.
  destruct at2rng.
  specialize PI_RGT_0 as pigt0.
  assert (PI < -PI) as abs.
  apply (Rmult_lt_reg_r (/2)).
  apply Rinv_0_lt_compat. lra.
  fieldrewrite (PI * / 2) (PI/2).
  fieldrewrite (-PI*/2) (-PI/2). assumption.
  lra.

  subst.
  apply notO. split; reflexivity.
Qed.

Lemma atan2_cos_id (x y : R) (valid : ~(x = 0 /\ y = 0)) :
  cos (atan2 y x) = x/(sqrt (x^2 + y^2)).
Proof.
  unfold atan2.
  destruct pre_atan2.
  destruct a.
  destruct H0.
  rewrite H1 at 1.
  repeat rewrite Rsqr_pow2.
  rewrite Rplus_comm.
  field.
  intro.
  apply sqrt_eq_0 in H2.
  repeat rewrite <- Rsqr_pow2 in H2.
  apply valid.
  split; [| rewrite Rplus_comm in H2];eapply Rplus_sqr_eq_0_l; eauto.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma atan2_sin_id (x y : R) (valid : ~(x = 0 /\ y = 0)) :
  sin (atan2 y x) = y/(sqrt (x^2 + y^2)).
Proof.
  unfold atan2.
  destruct pre_atan2.
  destruct a.
  destruct H0.
  rewrite H0 at 1.
  repeat rewrite Rsqr_pow2.
  rewrite Rplus_comm.
  field.
  intro.
  apply sqrt_eq_0 in H2.
  repeat rewrite <- Rsqr_pow2 in H2.
  apply valid.
  split; [| rewrite Rplus_comm in H2];eapply Rplus_sqr_eq_0_l; eauto.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

(** Relate atan2 to atan *)

Lemma atan2_atan_Q1 : forall dx dy,
    0 < dx -> 0 < dy -> atan2 dy dx = atan (dy/dx).
Proof.
  intros.
  specialize (atan2Q1 _ _ H H0) as atan2rng.
  unfold atan, atan2 in *.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  destruct (pre_atan (dy/dx)) as [q [qrng tanq]].
  assert (0 < sqrt (dy² + dx²)) as zltsqrtdx2dy2.
  apply sqrt_lt_R0.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rlt_0_sqr. intro. lra.
  rewrite dydef in tanq.
  rewrite dxdef in tanq at 2.
  assert (tan p = tan q) as taneq.
  symmetry.
  apply (Rmult_eq_reg_l ((sqrt (dy² + dx²))/(sqrt (dy² + dx²)))).
  setl (tan q). change (sqrt (dy² + dx²) <> 0). intro. lra.
  unfold tan at 2.
  setr (sqrt (dy² + dx²) * sin p / (sqrt (dy² + dx²) * cos p)).
  split.
  intro. rewrite H1 in dxdef.
  assert (sqrt (dy² + dx²) * 0 = 0). field. rewrite H2 in dxdef.
  lra.
  change (sqrt (dy² + dx²) <> 0). intro. lra. assumption.
  intro.
  assert (sqrt (dy² + dx²) = 0) as sqrt0.
  apply (Rmult_eq_reg_r (/ sqrt (dy² + dx²))).  setr 0.
  intro.
  change (sqrt (dy² + dx²) = 0) in H2. lra.
  assumption.
  apply Rinv_neq_0_compat.
  intro. lra. lra.
  apply tan_is_inj. inversion_clear atan2rng. split.
  specialize PI_RGT_0 as PIgt0. 
  apply (Rlt_trans _ 0).
  apply (Rmult_lt_reg_r 2). lra.
  setl (-PI). setr 0. lra. assumption. assumption.
  assumption. assumption.
Qed.  


Lemma atan2_atan_Q4 : forall dx dy,
    0 < dx -> dy < 0 -> atan2 dy dx = atan (dy/dx).
Proof.
  intros.
  specialize (atan2Q4 _ _ H H0) as atan2rng.
  unfold atan, atan2 in *.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  destruct (pre_atan (dy/dx)) as [q [qrng tanq]].
  assert (0 < sqrt (dy² + dx²)) as zltsqrtdx2dy2.
  apply sqrt_lt_R0.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rlt_0_sqr. intro. lra.
  rewrite dydef in tanq.
  rewrite dxdef in tanq at 2.
  assert (tan p = tan q) as taneq.
  symmetry.
  apply (Rmult_eq_reg_l ((sqrt (dy² + dx²))/(sqrt (dy² + dx²)))).
  setl (tan q). change (sqrt (dy² + dx²) <> 0). intro. lra.
  unfold tan at 2.
  setr (sqrt (dy² + dx²) * sin p / (sqrt (dy² + dx²) * cos p)).
  split.
  intro. rewrite H1 in dxdef.
  assert (sqrt (dy² + dx²) * 0 = 0). field. rewrite H2 in dxdef.
  lra.
  change (sqrt (dy² + dx²) <> 0). intro. lra. assumption.
  intro.
  assert (sqrt (dy² + dx²) = 0) as sqrt0.
  apply (Rmult_eq_reg_r (/ sqrt (dy² + dx²))).  setr 0.
  intro.
  change (sqrt (dy² + dx²) = 0) in H2. lra.
  assumption.
  apply Rinv_neq_0_compat.
  intro. lra. lra.
  apply tan_is_inj. inversion_clear atan2rng. split.
  specialize PI_RGT_0 as PIgt0.
  setl (- (PI/2)). assumption.
  apply (Rlt_trans _ 0). assumption.
  apply (Rmult_lt_reg_r 2). lra.
  setr (PI). setl 0. lra. assumption. assumption.
Qed.  


Lemma atan2_atan_Q2 : forall dx dy,
    dx < 0 -> 0 < dy -> atan2 dy dx = atan (dy/dx) + PI.
Proof.
  intros.
  specialize (atan2Q2 _ _ H H0) as atan2rng.
  unfold atan, atan2 in *.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  destruct (pre_atan (dy/dx)) as [q [qrng tanq]].
  assert (0 < sqrt (dy² + dx²)) as zltsqrtdx2dy2.
  apply sqrt_lt_R0.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rlt_0_sqr. intro. lra.

  assert (dy/dx < 0) as dydxlt0.
  fieldrewrite (dy/dx) (-dy * / - dx). intro. lra.
  fieldrewrite 0 (0 * / - dx). intro. lra.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar.
  assumption. lra.

  destruct (Rlt_dec q 0).
  rewrite dydef in tanq.
  rewrite dxdef in tanq at 2.
  assert (tan p = tan (q)) as taneq.
  symmetry.
  apply (Rmult_eq_reg_l ((sqrt (dy² + dx²))/(sqrt (dy² + dx²)))).
  setl (tan (q)). change (sqrt (dy² + dx²) <> 0). intro. lra.
  unfold tan at 2.
  setr (sqrt (dy² + dx²) * sin p / (sqrt (dy² + dx²) * cos p)).
  split.
  intro. rewrite H1 in dxdef.
  assert (sqrt (dy² + dx²) * 0 = 0). field. rewrite H2 in dxdef.
  lra.
  change (sqrt (dy² + dx²) <> 0). intro. lra. assumption.
  intro.
  assert (sqrt (dy² + dx²) = 0) as sqrt0.
  apply (Rmult_eq_reg_r (/ sqrt (dy² + dx²))).  setr 0.
  intro.
  change (sqrt (dy² + dx²) = 0) in H2. lra.
  assumption.
  apply Rinv_neq_0_compat.
  intro. lra. lra.

  assert (p = p - INR 1 * PI + INR 1 * PI) as pid. field.
  rewrite pid in taneq. clear pid. rewrite (tan_period_1 _ 1) in taneq.
  unfold INR in taneq.
  assert (p - 1 * PI = p - PI) as id. field. rewrite id in taneq. clear id.
  apply (Rplus_eq_reg_r (-PI)). setl (p - PI). setr q.

  apply tan_is_inj. inversion_clear atan2rng. split.
  specialize PI_RGT_0 as PIgt0.
  apply (Rplus_lt_reg_r PI). setr p. setl (PI/2). assumption.
  apply (Rplus_lt_reg_r PI). setl p.
  apply (Rlt_trans _ (PI)). assumption.
  lra. assumption. assumption.

  unfold INR. rewrite <- cos_neg.
  fieldrewrite (- (p - 1 * PI)) ((- p) + PI).
  rewrite neg_cos. rewrite cos_neg.
  fieldrewrite 0 (-1 * 0). fieldrewrite (- cos p) (-1 * cos p).
  intro. apply (Rmult_eq_reg_l (-1)) in H1.
  rewrite H1 in dxdef.
  assert (dx = 0) as dxeq0. setr (sqrt (dy² + dx²) * 0).
  assumption. lra.
  discrR.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [zltq | zeqq].
  inversion_clear qrng as [qlb qub].
  specialize (tan_gt_0 q zltq qub) as tanqgt0.
  rewrite <- tanq in dydxlt0. lra.

  subst. rewrite tan_0 in tanq. rewrite <- tanq in dydxlt0.
  lra.
Qed.


Lemma atan2_atan_Q3 : forall dx dy,
    dx < 0 -> dy < 0 -> atan2 dy dx = atan (dy/dx) - PI.
Proof.
  intros.
  specialize (atan2Q3 _ _ H H0) as atan2rng.
  unfold atan, atan2 in *.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  destruct (pre_atan (dy/dx)) as [q [qrng tanq]].
  assert (0 < sqrt (dy² + dx²)) as zltsqrtdx2dy2.
  apply sqrt_lt_R0.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rlt_0_sqr. intro. lra.

  assert (0 < dy/dx) as dydxgt0.
  fieldrewrite (dy/dx) (- dy * / - dx). intro. lra.
  fieldrewrite 0 (0 * / - dx). intro. lra.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar.
  assumption. lra.

  destruct (Rlt_dec 0 q).
  rewrite dydef in tanq.
  rewrite dxdef in tanq at 2.
  assert (tan p = tan (q)) as taneq.
  symmetry.
  apply (Rmult_eq_reg_l ((sqrt (dy² + dx²))/(sqrt (dy² + dx²)))).
  setl (tan (q)). change (sqrt (dy² + dx²) <> 0). intro. lra.
  unfold tan at 2.
  setr (sqrt (dy² + dx²) * sin p / (sqrt (dy² + dx²) * cos p)).
  split.
  intro. rewrite H1 in dxdef.
  assert (sqrt (dy² + dx²) * 0 = 0). field. rewrite H2 in dxdef.
  lra.
  change (sqrt (dy² + dx²) <> 0). intro. lra. assumption.
  intro.
  assert (sqrt (dy² + dx²) = 0) as sqrt0.
  apply (Rmult_eq_reg_r (/ sqrt (dy² + dx²))).  setr 0.
  intro.
  change (sqrt (dy² + dx²) = 0) in H2. lra.
  assumption.
  apply Rinv_neq_0_compat.
  intro. lra. lra.

  (* assert (p = p - INR 1 * PI + INR 1 * PI) as pid. field. *)
  (* rewrite pid in taneq. clear pid. *)
  rewrite <- (tan_period_1 _ 1) in taneq.
  unfold INR in taneq.
  assert (p + 1 * PI = p + PI) as id. field. rewrite id in taneq. clear id.
  apply (Rplus_eq_reg_r (PI)). setr q.

  apply tan_is_inj. inversion_clear atan2rng. split.
  specialize PI_RGT_0 as PIgt0.
  apply (Rplus_lt_reg_r (-PI)). setr p.
  apply (Rlt_trans _ (-PI)).
  apply (Rplus_lt_reg_r PI). setr 0. setl (-PI/2). 
  apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI).
  lra. assumption. lra.
  assumption. assumption. 

  intro. assert (dx = 0) as dxeq0. setr (sqrt (dy² + dx²) * 0).
  rewrite H1 in dxdef.
  assumption. lra.

  exfalso.
  apply Rnot_lt_le in n.
  inversion_clear n as [qltz | qeqz].
  inversion_clear qrng as [qlb qub].
  assert (- (PI/2)<q) as mPI2ltq. setl (-PI/2). assumption.
  specialize (tan_lt_0 q mPI2ltq qltz) as tanqlt0.
  rewrite <- tanq in dydxgt0. lra.

  subst. rewrite tan_0 in tanq. rewrite <- tanq in dydxgt0.
  lra.
Qed.

Lemma atan2_atan_Q1Q4 : forall dx dy : R,
    0 < dx -> atan2 dy dx = atan (dy / dx).
Proof.
  intros.
  destruct (Rle_dec 0 dy).
  inversion_clear r.
  apply atan2_atan_Q1; assumption.
  subst. fieldrewrite (0/dx) 0. intro. lra.
  rewrite atan_0; try assumption.
  rewrite atan2_0. reflexivity. assumption.
  apply Rnot_le_lt in n.
  apply atan2_atan_Q4; assumption.
Qed.


Lemma atan2_atan_Q1Q2 : forall dy dx (zlty : 0 < dy),
    atan2 dy dx = PI/2 - atan (dx/dy).
Proof.
  intros.
  specialize PI_RGT_0 as PI_RGT_0.
  destruct (Rlt_dec 0 dx).

  specialize (atan2Q1 _ _ r zlty) as [atan2lb atan2ub].
  rewrite (atan2_atan_Q1 _ _ r zlty) in atan2lb, atan2ub.
  rewrite (atan2_atan_Q1 _ _ r zlty).
  unfold atan in *.
  destruct (pre_atan (dy/dx)) as [p [prng prel]].
  destruct (pre_atan (dx/dy)) as [q [qrng qrel]].
  unfold tan in *.

  assert (cos p <> 0) as cospne0. intro cospeq0.
  assert (-PI < p <= PI) as prng2. inversion_clear prng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ prng2 cospeq0). intros.
  inversion_clear H. subst. inversion_clear prng. lra.
  subst. inversion_clear prng. lra.

  assert (cos q <> 0) as cosqne0. intro cosqeq0.
  assert (-PI < q <= PI) as qrng2. inversion_clear qrng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ qrng2 cosqeq0). intros.
  inversion_clear H. subst. inversion_clear qrng. lra.
  subst. inversion_clear qrng. lra.

  assert (sin p * dx = cos p * dy) as r1.
  apply (Rmult_eq_reg_r (/ (dx * cos p)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin p / cos p).
  split; [assumption | intro; lra].
  setr (dy/dx).
  split; [ intro; lra | assumption].
  assumption.

  assert (sin q * dy = cos q * dx) as r2.
  apply (Rmult_eq_reg_r (/ (dy * cos q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin q / cos q).
  split; [assumption | intro; lra].
  setr (dx/dy).
  split; [ intro; lra | assumption].
  assumption.

  assert (dy <> 0) as dyne0. intro. subst.
  assert (dx = 0). apply (Rmult_eq_reg_l (cos q)). setr (sin q * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (dx <> 0) as dxne0. intro. subst.
  assert (dy = 0). apply (Rmult_eq_reg_l (cos p)). setr (sin p * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (sin q <> 0) as sinqne0. intro sinqeq0. rewrite sinqeq0 in qrel.
  apply dxne0. apply (Rmult_eq_reg_r (/ dy)). setl (dx/dy). assumption. setr (0 / cos q).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (sin p <> 0) as sinpne0. intro sinpeq0. rewrite sinpeq0 in prel.
  apply dyne0. apply (Rmult_eq_reg_r (/ dx)). setl (dy/dx). assumption. setr (0 / cos p).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (cos (p + q) = 0) as cosppqeq0.
  rewrite cos_plus.
  apply (Rplus_eq_reg_r (sin p * sin q)). setl (cos p * cos q). setr (sin p * sin q).
  symmetry.
  apply (Rmult_eq_reg_r (/ (cos p * sin q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified; try assumption].

  setl (sin p / cos p). split; assumption.
  setr (/ (sin q / cos q)). split; [assumption | split; try assumption ].
  rewrite prel, qrel. field. split; assumption.

  apply (Rplus_eq_reg_r q). setr (PI/2).
  assert (- PI < p + q <= PI) as ppq. split.
  inversion_clear prng. inversion_clear qrng.
  setl ((-PI/2) + (-PI/2)).
  apply Rplus_lt_compat; try assumption.
  left. inversion_clear prng. inversion_clear qrng. lra.

  specialize (cosθeq0 _ ppq cosppqeq0) as [ppqeqPI2 | ppqeqmPI2].
  assumption.

  exfalso.
  assert (- PI / 2 < p + q).
  apply (Rlt_trans _ (0 + q)).
  setr q. inversion qrng. assumption.
  apply Rplus_lt_compat_r. assumption.
  rewrite ppqeqmPI2 in H. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [r | r];
    [| subst; rewrite atan2_PI2; [
         fieldrewrite (0/dy) 0; [intro; lra | rewrite atan_0;  field] | assumption]].
  
  specialize (atan2Q2 _ _ r zlty) as [atan2lb atan2ub].
  rewrite (atan2_atan_Q2 _ _ r zlty) in atan2lb, atan2ub.
  rewrite (atan2_atan_Q2 _ _ r zlty).
  unfold atan in *.
  destruct (pre_atan (dy/dx)) as [p [prng prel]].
  destruct (pre_atan (dx/dy)) as [q [qrng qrel]].
  unfold tan in *.

  assert (cos p <> 0) as cospne0. intro cospeq0.
  assert (-PI < p <= PI) as prng2. inversion_clear prng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ prng2 cospeq0). intros.
  inversion_clear H. subst. inversion_clear prng. lra.
  subst. inversion_clear prng. lra.

  assert (cos q <> 0) as cosqne0. intro cosqeq0.
  assert (-PI < q <= PI) as qrng2. inversion_clear qrng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ qrng2 cosqeq0). intros.
  inversion_clear H. subst. inversion_clear qrng. lra.
  subst. inversion_clear qrng. lra.

  assert (sin p * dx = cos p * dy) as r1.
  apply (Rmult_eq_reg_r (/ (dx * cos p)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin p / cos p).
  split; [assumption | intro; lra].
  setr (dy/dx).
  split; [ intro; lra | assumption].
  assumption.

  assert (sin q * dy = cos q * dx) as r2.
  apply (Rmult_eq_reg_r (/ (dy * cos q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin q / cos q).
  split; [assumption | intro; lra].
  setr (dx/dy).
  split; [ intro; lra | assumption].
  assumption.

  assert (dy <> 0) as dyne0. intro. subst.
  assert (dx = 0). apply (Rmult_eq_reg_l (cos q)). setr (sin q * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (dx <> 0) as dxne0. intro. subst.
  assert (dy = 0). apply (Rmult_eq_reg_l (cos p)). setr (sin p * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (sin q <> 0) as sinqne0. intro sinqeq0. rewrite sinqeq0 in qrel.
  apply dxne0. apply (Rmult_eq_reg_r (/ dy)). setl (dx/dy). assumption. setr (0 / cos q).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (sin p <> 0) as sinpne0. intro sinpeq0. rewrite sinpeq0 in prel.
  apply dyne0. apply (Rmult_eq_reg_r (/ dx)). setl (dy/dx). assumption. setr (0 / cos p).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (cos (p + q) = 0) as cosppqeq0.
  rewrite cos_plus.
  apply (Rplus_eq_reg_r (sin p * sin q)). setl (cos p * cos q). setr (sin p * sin q).
  symmetry.
  apply (Rmult_eq_reg_r (/ (cos p * sin q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified; try assumption].

  setl (sin p / cos p). split; assumption.
  setr (/ (sin q / cos q)). split; [assumption | split; try assumption ].
  rewrite prel, qrel. field. split; assumption.

  apply (Rplus_eq_reg_r (q - PI)). setr (- PI/2).
  assert (- PI < p + q <= PI) as ppq. split.
  inversion_clear prng. inversion_clear qrng.
  setl ((-PI/2) + (-PI/2)).
  apply Rplus_lt_compat; try assumption.
  left. inversion_clear prng. inversion_clear qrng. lra.
  setl (p + q).

  specialize (cosθeq0 _ ppq cosppqeq0) as [ppqeqPI2 | ppqeqmPI2]; [| assumption].

  exfalso.
  assert (p + q < PI / 2).
  apply (Rlt_trans _ (0 + q)).
  apply Rplus_lt_compat_r. lra.
  setl q. inversion qrng. assumption.
  rewrite ppqeqPI2 in H. lra.
Qed.

Lemma atan2_atan_Q3Q4 : forall dy dx (ylt0 : dy < 0),
    atan2 dy dx = - PI/2 - atan (dx/dy).
Proof.
  intros.
  specialize PI_RGT_0 as PI_RGT_0.
  destruct (Rlt_dec 0 dx).

  specialize (atan2Q4 _ _ r ylt0) as [atan2lb atan2ub].
  rewrite (atan2_atan_Q4 _ _ r ylt0) in atan2lb, atan2ub.
  rewrite (atan2_atan_Q4 _ _ r ylt0).
  unfold atan in *.
  destruct (pre_atan (dy/dx)) as [p [prng prel]].
  destruct (pre_atan (dx/dy)) as [q [qrng qrel]].
  unfold tan in *.

  assert (cos p <> 0) as cospne0. intro cospeq0.
  assert (-PI < p <= PI) as prng2. inversion_clear prng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ prng2 cospeq0). intros.
  inversion_clear H. subst. inversion_clear prng. lra.
  subst. inversion_clear prng. lra.

  assert (cos q <> 0) as cosqne0. intro cosqeq0.
  assert (-PI < q <= PI) as qrng2. inversion_clear qrng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ qrng2 cosqeq0). intros.
  inversion_clear H. subst. inversion_clear qrng. lra.
  subst. inversion_clear qrng. lra.

  assert (sin p * dx = cos p * dy) as r1.
  apply (Rmult_eq_reg_r (/ (dx * cos p)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin p / cos p).
  split; [assumption | intro; lra].
  setr (dy/dx).
  split; [ intro; lra | assumption].
  assumption.

  assert (sin q * dy = cos q * dx) as r2.
  apply (Rmult_eq_reg_r (/ (dy * cos q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin q / cos q).
  split; [assumption | intro; lra].
  setr (dx/dy).
  split; [ intro; lra | assumption].
  assumption.

  assert (dy <> 0) as dyne0. intro. subst.
  assert (dx = 0). apply (Rmult_eq_reg_l (cos q)). setr (sin q * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (dx <> 0) as dxne0. intro. subst.
  assert (dy = 0). apply (Rmult_eq_reg_l (cos p)). setr (sin p * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (sin q <> 0) as sinqne0. intro sinqeq0. rewrite sinqeq0 in qrel.
  apply dxne0. apply (Rmult_eq_reg_r (/ dy)). setl (dx/dy). assumption. setr (0 / cos q).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (sin p <> 0) as sinpne0. intro sinpeq0. rewrite sinpeq0 in prel.
  apply dyne0. apply (Rmult_eq_reg_r (/ dx)). setl (dy/dx). assumption. setr (0 / cos p).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (cos (p + q) = 0) as cosppqeq0.
  rewrite cos_plus.
  apply (Rplus_eq_reg_r (sin p * sin q)). setl (cos p * cos q). setr (sin p * sin q).
  symmetry.
  apply (Rmult_eq_reg_r (/ (cos p * sin q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified; try assumption].

  setl (sin p / cos p). split; assumption.
  setr (/ (sin q / cos q)). split; [assumption | split; try assumption ].
  rewrite prel, qrel. field. split; assumption.

  apply (Rplus_eq_reg_r q). setr (- PI/2).
  assert (- PI < p + q <= PI) as ppq. split.
  inversion_clear prng. inversion_clear qrng.
  setl ((-PI/2) + (-PI/2)).
  apply Rplus_lt_compat; try assumption.
  left. inversion_clear prng. inversion_clear qrng. lra.

  specialize (cosθeq0 _ ppq cosppqeq0) as [ppqeqPI2 | ppqeqmPI2]; [|   assumption].

  exfalso.
  assert (p + q < PI/2).
  apply (Rlt_trans _ (0 + q)). apply (Rplus_lt_reg_r (-q)).
  setl (p). setr 0. 
  assumption. setr (0 + PI/2).
  apply Rplus_lt_compat_l. inversion qrng. assumption.
  rewrite ppqeqPI2 in H. lra.

  apply Rnot_lt_le in n.
  inversion_clear n as [r | r];
    [| subst; rewrite atan2_mPI2; [
         fieldrewrite (0/dy) 0; [intro; lra | rewrite atan_0;  field] | assumption]].
  
  specialize (atan2Q3 _ _ r ylt0) as [atan2lb atan2ub].
  rewrite (atan2_atan_Q3 _ _ r ylt0) in atan2lb, atan2ub.
  rewrite (atan2_atan_Q3 _ _ r ylt0).
  unfold atan in *.
  destruct (pre_atan (dy/dx)) as [p [prng prel]].
  destruct (pre_atan (dx/dy)) as [q [qrng qrel]].
  unfold tan in *.

  assert (cos p <> 0) as cospne0. intro cospeq0.
  assert (-PI < p <= PI) as prng2. inversion_clear prng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ prng2 cospeq0). intros.
  inversion_clear H. subst. inversion_clear prng. lra.
  subst. inversion_clear prng. lra.

  assert (cos q <> 0) as cosqne0. intro cosqeq0.
  assert (-PI < q <= PI) as qrng2. inversion_clear qrng.
  split. apply (Rlt_trans _ (-PI/2)). apply (Rmult_lt_reg_r 2). lra. setr (-PI). setl (- 2 *PI). lra.
  assumption. left.
  apply (Rlt_trans _ (PI/2)). assumption. apply (Rmult_lt_reg_r 2). lra. setl (PI). lra.
  specialize (cosθeq0 _ qrng2 cosqeq0). intros.
  inversion_clear H. subst. inversion_clear qrng. lra.
  subst. inversion_clear qrng. lra.

  assert (sin p * dx = cos p * dy) as r1.
  apply (Rmult_eq_reg_r (/ (dx * cos p)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin p / cos p).
  split; [assumption | intro; lra].
  setr (dy/dx).
  split; [ intro; lra | assumption].
  assumption.

  assert (sin q * dy = cos q * dx) as r2.
  apply (Rmult_eq_reg_r (/ (dy * cos q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified;
       [ intro; lra | assumption]].
  setl (sin q / cos q).
  split; [assumption | intro; lra].
  setr (dx/dy).
  split; [ intro; lra | assumption].
  assumption.

  assert (dy <> 0) as dyne0. intro. subst.
  assert (dx = 0). apply (Rmult_eq_reg_l (cos q)). setr (sin q * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (dx <> 0) as dxne0. intro. subst.
  assert (dy = 0). apply (Rmult_eq_reg_l (cos p)). setr (sin p * 0). symmetry.
  assumption. assumption. subst. lra.

  assert (sin q <> 0) as sinqne0. intro sinqeq0. rewrite sinqeq0 in qrel.
  apply dxne0. apply (Rmult_eq_reg_r (/ dy)). setl (dx/dy). assumption. setr (0 / cos q).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (sin p <> 0) as sinpne0. intro sinpeq0. rewrite sinpeq0 in prel.
  apply dyne0. apply (Rmult_eq_reg_r (/ dx)). setl (dy/dx). assumption. setr (0 / cos p).
  split; assumption. symmetry. assumption.
  apply Rinv_neq_0_compat. assumption.

  assert (cos (p + q) = 0) as cosppqeq0.
  rewrite cos_plus.
  apply (Rplus_eq_reg_r (sin p * sin q)). setl (cos p * cos q). setr (sin p * sin q).
  symmetry.
  apply (Rmult_eq_reg_r (/ (cos p * sin q)));
    [| apply Rinv_neq_0_compat;
       apply Rmult_integral_contrapositive_currified; try assumption].

  setl (sin p / cos p). split; assumption.
  setr (/ (sin q / cos q)). split; [assumption | split; try assumption ].
  rewrite prel, qrel. field. split; assumption.

  apply (Rplus_eq_reg_r (q + PI)). setr (PI/2).
  assert (- PI < p + q <= PI) as ppq. split.
  inversion_clear prng. inversion_clear qrng.
  setl ((-PI/2) + (-PI/2)).
  apply Rplus_lt_compat; try assumption.
  left. inversion_clear prng. inversion_clear qrng. lra.
  setl (p + q).

  specialize (cosθeq0 _ ppq cosppqeq0) as [ppqeqPI2 | ppqeqmPI2]; [ assumption |].

  exfalso.
  assert (- PI/2 < p + q).
  apply (Rlt_trans _ (0 + q)). setl (0 + - PI/2).
  apply Rplus_lt_compat_l. inversion qrng. lra.
  apply (Rplus_lt_reg_l (-q- PI)). setl (-PI).
  setr (p-PI). assumption.
  rewrite ppqeqmPI2 in H. lra.
Qed.

Lemma atan2_neg_posy : forall x y,
    0 < y -> atan2 y x = atan2 (-y) (-x) + PI.
Proof.
  intros.
  destruct (Rlt_dec 0 x) as [zltx |zgex].
  rewrite atan2_atan_Q1; [|assumption|assumption].
  rewrite atan2_atan_Q3; [|lra|lra].
  fieldrewrite (- y / - x) (y / x). intro. lra. field.

  apply Rnot_lt_le in zgex.
  inversion_clear zgex as [xlt0 |xeq0].
  rewrite atan2_atan_Q2; [|assumption|assumption].
  rewrite atan2_atan_Q4; [|lra|lra].
  fieldrewrite (- y / - x) (y / x). intro. lra. field.

  rewrite xeq0.
  rewrite Ropp_0.
  rewrite atan2_PI2; [|assumption].
  rewrite atan2_mPI2; [|lra].
  apply (Rplus_eq_reg_r (PI/2)).
  setl (PI). setr PI. reflexivity.
Qed.

Lemma atan2_neg_negy : forall x y,
    y < 0 -> atan2 y x = atan2 (-y) (-x) - PI.
Proof.
  intros.
  destruct (Rlt_dec 0 x) as [zltx |zgex].
  rewrite atan2_atan_Q4; [|assumption|assumption].
  rewrite atan2_atan_Q2; [|lra|lra].
  fieldrewrite (- y / - x) (y / x). intro. lra. field.

  apply Rnot_lt_le in zgex.
  inversion_clear zgex as [xlt0 |xeq0].
  rewrite atan2_atan_Q3; [|assumption|assumption].
  rewrite atan2_atan_Q1; [|lra|lra].
  fieldrewrite (- y / - x) (y / x). intro. lra. field.

  rewrite xeq0.
  rewrite Ropp_0.
  rewrite atan2_mPI2; [|assumption].
  rewrite atan2_PI2; [|lra].
  apply (Rplus_eq_reg_r (-PI/2)).
  setl (-PI). setr (-PI). reflexivity.
Qed.

Lemma atan2_symmetry : forall x y,
    ~ (x <= 0 /\ y = 0) -> atan2 y x = - atan2 (-y) x.
Proof.
  intros *. intro nog.
  destruct (Rlt_dec 0 y) as [ygt0 |yle0];
  destruct (Rlt_dec 0 x) as [xgt0 |xle0].
  rewrite atan2_atan_Q1; [|assumption|assumption].
  rewrite atan2_atan_Q4; [|assumption|lra].
  fieldrewrite (- y/x) (- (y/x)); [ intro; lra |];
  rewrite atan_opp; rewrite Ropp_involutive;
  reflexivity.
  
  apply Rnot_lt_le in xle0.
  inversion_clear xle0 as [xlt0 |xeq0].
  rewrite atan2_atan_Q2; [|assumption|assumption].
  rewrite atan2_atan_Q3; [|assumption|lra].
  fieldrewrite (- y/x) (- (y/x)); [ intro; lra |];
  rewrite atan_opp. field.

  rewrite xeq0.
  rewrite atan2_PI2; [|assumption].
  rewrite atan2_mPI2; [|lra]. field.

  apply Rnot_lt_le in yle0.
  inversion_clear yle0 as [ylt0| yeq0].
  rewrite atan2_atan_Q4; [|assumption|assumption].
  rewrite atan2_atan_Q1; [|assumption|lra].
  fieldrewrite (- y/x) (- (y/x)); [ intro; lra |];
  rewrite atan_opp; rewrite Ropp_involutive;
  reflexivity.

  rewrite yeq0.
  fieldrewrite (-0) 0.
  rewrite atan2_0; [|assumption]. field.

  apply Rnot_lt_le in yle0.
  apply Rnot_lt_le in xle0.

  inversion_clear yle0 as [ylt0 |yeq0].
  inversion_clear xle0 as [xlt0 |xeq0].
  rewrite atan2_atan_Q3; [|assumption|assumption].
  rewrite atan2_atan_Q2; [|assumption|lra].
  fieldrewrite (- y/x) (- (y/x)); [ intro; lra |];
  rewrite atan_opp. field.

  rewrite xeq0.
  rewrite atan2_mPI2; [|assumption].
  rewrite atan2_PI2; [|lra]. field.

  rewrite yeq0.
  exfalso. apply nog.
  split; assumption.
Qed.

Lemma chord_property : forall r θ (rne0 : 0 < r) (trng : 0 < θ < 2 * PI),
    2 * atan2 (r * (1 - cos θ)) (r * sin θ) = θ.
Proof.
  intros.
  set (y := r * (1 - cos θ)) in *.
  set (x := r * sin θ) in *.
  unfold atan2.
  destruct pre_atan2 as [a [[al au] [yd xd]]].
  set (M := sqrt (y² + x²)) in *.

  specialize (sqrt_pos (y² + x²)) as [mne0 |meq0];
    [change (0 < M) in mne0|
     change (0 = M) in meq0;
     exfalso;
     rewrite <- meq0 in xd, yd;
     autorewrite with null in xd, yd;
     unfold x, y in xd, yd;
     
     assert (sin θ = 0) as sinteq0;
     [apply (Rmult_eq_reg_l r);
      arn;
      lra|];
     
     assert (cos θ = 1) as costeq1;
       [apply (Rmult_eq_reg_l r); [|lra];
      apply (Rplus_eq_reg_l (- r* cos θ));
      symmetry|];
     
     destruct trng as [tl th];
     specialize (sin_eq_O_2PI_0 _ (Rlt_le _ _ tl)
                                (Rlt_le _ _ th) sinteq0)
       as [teq0 | [q | s]]; try lra;
     rewrite q, cos_PI in costeq1;
     lra].
  
  unfold x, y in *.
  assert (r * (1 - cos θ) = M * sin (θ - a)) as yd2. {
    rewrite sin_minus.
    rewrite (Rmult_minus_distr_l M).
    repeat rewrite <- Rmult_assoc.
    apply (Rmult_eq_compat_r (cos θ)) in yd.
    rewrite (Rmult_assoc M), (Rmult_comm (sin a)) in yd.
    rewrite <- (Rmult_assoc M) in yd.
    
    apply (Rmult_eq_compat_r (sin θ)) in xd.
    rewrite (Rmult_assoc M), (Rmult_comm (cos a)) in xd.
    rewrite <- (Rmult_assoc M) in xd.
    rewrite <- yd, <- xd.
    setr (r * ((sin θ)² + (cos θ)²) - r * (cos θ)).
    rewrite sin2_cos2.
    field. }
  
  assert (r * sin θ = M * cos (θ - a)) as xd2. {
    rewrite cos_minus.
    rewrite (Rmult_plus_distr_l M).
    repeat rewrite <- Rmult_assoc.
    apply (Rmult_eq_compat_r (sin θ)) in yd.
    rewrite (Rmult_assoc M), (Rmult_comm (sin a)) in yd.
    rewrite <- (Rmult_assoc M) in yd.
    
    apply (Rmult_eq_compat_r (cos θ)) in xd.
    rewrite (Rmult_assoc M), (Rmult_comm (cos a)) in xd.
    rewrite <- (Rmult_assoc M) in xd.
    rewrite <- yd, <- xd.
    field. }
  
  rewrite xd2 in xd.
  rewrite yd2 in yd.
  
  assert (sin (θ - a) = sin a) as seqv. {
    apply (Rmult_eq_reg_l M).
    assumption.
    lra. }
  
  assert (cos (θ - a) = cos a) as ceqv. {
    apply (Rmult_eq_reg_l M).
    assumption.
    lra. }

  destruct trng as [tl th].
  destruct au as [au | aq].
  apply Rminus_diag_eq in seqv.
  apply Rminus_diag_eq in ceqv.
  rewrite form4 in seqv.
  rewrite form2 in ceqv.
  assert ((θ - a - a) = (θ - 2 * a)) as id;
    [field|rewrite id in *; clear id].
  set (p := (θ - 2 * a)) in *.
  assert (θ - a + a = θ) as id;
    [field|rewrite id in *; clear id].
  destruct (Req_dec p 0) as [peq0 | pne0];
    [unfold p in peq0; lra|].
  + destruct (Req_dec (sin (p / 2)) 0) as [seq0 | sne0].
    ++ assert (p / 2 < 2 * PI) as p2u;
         [unfold p; lra |].
       assert (- PI < p / 2) as p2l;
         [unfold p; lra |].
       destruct (Rle_dec 0 (p/2)).
       +++ apply sin_eq_O_2PI_0 in seq0; try lra.
           destruct seq0 as [p20 | [ p2pi | p22pi]].
           ++++ unfold p in p20.
                lra.
           ++++ assert (0 < a) as zlta. {
                  assert (0 < 1 - cos θ) as dtgt0;
                    [specialize (COS_bound θ) as [cbl cbu];
                    destruct cbu as [lt1 | eq1];
                      [lra|
                       apply cos_eq_1_2PI_0 in eq1; try lra]|].
                  assert (0 < y) as zlty; [ unfold y; zltab | ].
                  rewrite <- yd2 in yd.
                  rewrite <- xd2 in xd.
                  unfold y in zlty.
                  rewrite yd in zlty.
                  rewrite <- (Rmult_0_r M) in zlty.
                  assert (0 < sin a) as zltsa;
                    [apply (Rmult_lt_reg_l M); try assumption|].
                  apply Rnot_ge_lt.
                  intro ale0.
                  apply Rge_le in ale0.
                  generalize zltsa.
                  change (~ (0 < sin a)).
                  apply Rlt_asym.
                  destruct ale0 as [alt0 |aeq0];
                    [apply sin_lt_0_var; try assumption|
                     rewrite aeq0, sin_0 in zltsa; lra]. }
                unfold p in p2pi.
                lra.
           ++++ lra.
       +++ apply Rnot_le_lt in n.
           apply Ropp_eq_compat in seq0.
           rewrite Ropp_0, <- sin_neg in seq0.
           apply sin_eq_O_2PI_0 in seq0; try lra.
    ++ exfalso.
       assert (cos (θ / 2) = 0) as cteq0;
       [apply (Rmult_eq_reg_l (sin(p/2))); try lra|].
       assert (sin (θ / 2) = 0) as steq0;
         [apply (Rmult_eq_reg_l (sin(p/2))); try lra|].
       apply (cos_sin_0 (θ / 2)).
       split; assumption.
  + rewrite aq in *.
    rewrite sin_PI in seqv.
    rewrite cos_PI in ceqv.
    assert (cos θ = 1) as cteq1. {
      apply (Rmult_eq_reg_r (-1)); try lra.
      setl (- cos θ).
      setr (-1).
      rewrite <- cos_neg.
      rewrite <- neg_cos.
      fieldrewrite (- θ + PI) (- (θ - PI)).
      rewrite cos_neg.
      assumption. }

    assert (sin θ = 0) as steq0. {
      rewrite <- (sin_period1 _ 1%Z) in seqv.
      assert (θ - PI + 2 * 1 * PI = θ + PI) as id;
        [lra|rewrite id in *; clear id].
      rewrite neg_sin, <- Ropp_0 in seqv.
      apply (Rmult_eq_reg_l (-1)).
      lrag seqv.
      lra. }
    specialize (sin_eq_O_2PI_0 _ (Rlt_le _ _ tl)
                               (Rlt_le _ _ th) steq0) as tsds.
    specialize (cos_eq_1_2PI_0 _ (Rlt_le _ _ tl)
                               (Rlt_le _ _ th) cteq1) as tcds.

    destruct tsds as [tsds | [tsds | tsds]];
      destruct tcds as [tcds | tcds];
      try lra.
Qed.

Lemma chord_property_neg : forall r θ (rne0 : r < 0) (trng : - 2 * PI < θ < 0),
    2 * atan2 (r * (1 - cos θ)) (r * sin θ) = θ.
Proof.
  intros.
  set (y := r * (1 - cos θ)) in *.
  set (x := r * sin θ) in *.

  set (rn := -r) in *.
  assert (0 < rn) as zltr2;
    [unfold rn in *; lra|].
  set (θn := -θ) in *.
  assert (0 < θn) as zltt2;
    [unfold θn in *; lra|].
  assert (θn < 2 * PI) as t2lt2pi;
    [unfold θn in *; lra|].

  unfold x, y.
  fieldrewrite (r * sin θ) (- r * - sin θ).
  rewrite <- sin_neg.
  rewrite atan2_symmetry;
    [fieldrewrite (- (r * (1 - cos θ))) (- r * (1 - cos θ));
     rewrite <- cos_neg;
     apply (Rmult_eq_reg_l (-1));
     [|lra];
     setl (2 * atan2 (- r * (1 - cos (- θ))) (- r * sin (- θ)));
     setr (- θ);
     apply chord_property; try lra|
     intros [xc yc];
     rewrite sin_neg in xc;
     rewrite Rmult_opp_opp in xc ].

  assert (cos θn = 1) as cteq1. {
    unfold θn.
    rewrite cos_neg.
    apply (Rplus_eq_reg_r (- cos θ)).
    apply (Rmult_eq_reg_r r).
    symmetry.
    lrag yc. lra. }

  assert (sin θn <= 0) as slt0. {
    unfold θn.
    apply (Rmult_le_reg_l (-r)).
    lra.
    rewrite sin_neg.
    setr (0).
    setl (r * sin θ).
    assumption. }

  assert (0 < θn) as tngt0. lra.
  assert (θn < 2 * PI) as tnlt2pi. lra.
  apply cosθeq1 in cteq1; [|split; lra].
  rewrite cteq1 in zltt2.
  lra.
Qed.

Lemma chord_length : forall x y (yne0 : y <> 0),
    let r := (x² + y²)/ (2 * y) in
    let θ := 2 * atan2 y x in
    (r * (1 - cos θ))² + (r * sin θ)² = y² + x².
Proof.
  intros.
  assert ( ~(x = 0 /\ y = 0)) as no; try lra.

  specialize PI_RGT_0 as pigt0.
  assert (0 < r * θ) as zltrtm. {
    unfold θ.

    destruct (total_order_T 0 y); [destruct s|].
    + zltab.
      unfold r.
      apply (Rmult_lt_reg_r (2*y)); try lra.
      setl 0.
      setr (x² + y²); try lra.
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      unfold Rsqr.
      zltab.
      destruct (total_order_T 0 x) ; [destruct s|].
      apply atan2Q1; assumption.
      rewrite <- e, atan2_PI2; lra.
      specialize atan2Q2 as [atl atu]; try eassumption.
      lra.
    + lra.
    + setr (2 * -r * - atan2 y x).
      zltab.
      unfold r.
      apply (Rmult_lt_reg_r (2 * - y)); try lra.
      setl 0.
      setr (x² + y²); try lra.
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      unfold Rsqr.
      setr (- y * -y).
      zltab.
      destruct (total_order_T 0 x) ; [destruct s|].
      specialize atan2Q4 as [atl atu]; try eassumption.
      lra.
      rewrite <- e, atan2_mPI2; lra.
      specialize (atan2Q3 x y) as [atl atu]; try eassumption.
      setl (-0).
      apply Ropp_lt_contravar.
      apply (Rlt_trans _ (-(PI/2))); lra. }

  assert (- 2 * PI < θ < 2 * PI) as [tml tmu]. {
    unfold θ.
    specialize (atan2_bound _ _ no) as [atl atu].
    destruct atu as [atu |ateq].
    split; apply (Rmult_lt_reg_r (/2)); try lra.
    exfalso.
    apply atan2_PI_impl in ateq; lra. }

  assert (r * θ < Rabs r * 2 * PI) as rtmltr2p. {
    destruct (Rge_dec r 0).
    rewrite Rabs_right; try assumption.
    destruct r0 as [rgt0 |req0].
    apply (Rmult_lt_reg_r (/r)); try lra.
    zltab.
    auto.
    lrag tmu.
    exfalso.
    rewrite req0 in zltrtm.
    lra.
    apply Rnot_ge_lt in n.
    rewrite Rabs_left; try assumption.
    setl (-(-r * θ)).
    setr (- (-r * (- 2 * PI))).
    apply Ropp_lt_contravar.
    apply (Rmult_lt_reg_r (/ - r)).
    zltab.
    lra.
    lrag tml. }

  assert (0 <= r * θ) as Dnnpf; try lra.
  assert (0 < r * θ < Rabs r * 2 * PI) as rtp; try lra.

  repeat rewrite Rsqr_mult.
  rewrite Rsqr_minus.
  setl (r² * (1 + ((sin θ)² + (cos θ)²) - 2 * 1 * cos θ)).
  rewrite sin2_cos2.
  fieldrewrite (1 + 1 - 2 * 1 * cos θ) (2*(1 - cos θ)).

  unfold r.
  rewrite <- RmultRinv, Rsqr_mult.
  assert (0 <= x² + y²) as [x2y2gt0 |eq0];
    try (apply Rplus_le_le_0_compat;
         apply Rle_0_sqr).
  2 : { rewrite (Rplus_comm (y²)), <- eq0; try arn; auto. }

  apply (Rmult_eq_reg_r ((2 * y)² * / (x² + y²)² * / 2)).
  2 : { repeat (apply Rmult_integral_contrapositive_currified; try zltab). }
  setl (1 - cos θ).
  split; try assumption.
  unfold Rsqr in x2y2gt0; lra.
  setr ((2 * y)² / (x² + y²) * / 2).
  unfold Rsqr in x2y2gt0; lra.
  assert (θ = 2 * atan2 y x) as tmd. {
    unfold θ.
    auto. }
  rewrite tmd.
  unfold atan2 in *.
  destruct pre_atan2 as [q [[ql qu] [yd xd]]].
  rewrite yd at 1.
  repeat rewrite Rsqr_mult.
  rewrite Rsqr_sqrt; try lra.
  setr (2 * (sin q)²).
  unfold Rsqr in x2y2gt0; lra.
  rewrite cos_2a_sin.
  unfold Rsqr.
  field.
Qed.
(* begin hide *)

Lemma sign_Rabs_eq (x : R) : x = (sign x)*(Rabs x).
Proof.
  unfold sign.
  destruct (total_order_T 0 x).
  * destruct s.
  + rewrite Rabs_pos_eq;[|lra].
    field.
  + rewrite <-e.
    field.
    * rewrite Rabs_left;[|lra].
    field.
Qed.

(* end hide *)

Lemma atan_atan22_id (x : R) : atan(x) = (atan2 (2*x) (1 - x^2))/2.
Proof.
  assert (~ (1 - x ^ 2 = 0 /\ 2 * x = 0)) as P0.
    { intro; destruct H.
      apply Rmult_integral in H0.
      destruct H0;[lra|].
      rewrite H0 in H.
      rewrite pow_ne_zero in H; auto.
      lra.
    }
    destruct (Req_dec x 0) as [P1 | P1].
  - rewrite P1.
    rewrite Rmult_0_r, pow_i, Rminus_0_r, atan2_0, atan_0; [field | lra | auto].
  - apply tan_is_inj.
  * apply atan_bound.
  * destruct (atan2_bound _ _ P0) as [P2 P3]; split. 
  + apply (Rmult_lt_compat_r (/2)) in P2; lra.
  + destruct P3 as [P3 | P3].
  - apply (Rmult_lt_compat_r (/2)) in P3; lra.
  - exfalso.
    destruct (atan2_PI_impl _ _ P0 P3) as [P4 P5].
    apply Rmult_integral in P5.
    destruct P5 as [P5 | P5];[lra|].
    rewrite P5 in P4.
    rewrite pow_ne_zero in P4; auto.
    rewrite atan_right_inv, tant2_2, atan2_cos_id, atan2_sin_id; auto.
    * assert (
          (1 - (1 - x ^ 2) / sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2))
            / (2 * x / sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2)) =
          (sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2) - (1 - x ^ 2))/ (2 * x)
        ).
      {
        field.
        split; auto.
        intro.
        apply sqrt_lem_0 in H.
        rewrite Rmult_0_l in H.
        repeat rewrite <- Rsqr_pow2 in H.
        destruct (Rplus_sqr_eq_0 _ _ (eq_sym H)).
        rewrite Rsqr_pow2 in H0.
        auto.
        specialize (pow2_ge_0 (2 * x)) as P2.
        specialize (pow2_ge_0 (1 - x ^ 2)) as P3.
        lra.
        lra.
      }
    rewrite H.
      assert ( (1 - x ^ 2) ^ 2 + (2 * x) ^ 2 = (1 + x^2)^2) as P2.
      { field. }
      rewrite P2.
      rewrite sqrt_pow2.
      field; auto.
      specialize (pow2_ge_0 x) as P3.
      lra.
      intro.
      rewrite atan2_sin_id in H.
      apply (Rmult_eq_compat_r (sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2))) in H.
      rewrite Rmult_0_l in H.
      assert (2 * x / sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2) *
              sqrt ((1 - x ^ 2) ^ 2 + (2 * x) ^ 2) = 2 * x).
      {
        field.
        intro.
        apply sqrt_lem_0 in H0.
        rewrite Rmult_0_l in H0.
        repeat rewrite <- Rsqr_pow2 in H0.
        destruct (Rplus_sqr_eq_0 _ _ (eq_sym H0)).
        rewrite Rsqr_pow2 in H1.
        auto.
        specialize (pow2_ge_0 (2 * x)) as P2.
        specialize (pow2_ge_0 (1 - x ^ 2)) as P3.
        lra.
        lra.
      }
      rewrite H0 in H.
      apply P1.
      apply Rmult_integral in H.
      destruct H; [lra|auto].
      assumption.
Qed.

Corollary atan_atan2_id (x : R) :
  2 * atan(x) = (atan2 (2*x) (1 - x^2)).
Proof.
  rewrite atan_atan22_id.
  field.
Qed.

Lemma atan2_cancel_id (x y z : R)
      (xne0 : x <> 0) (yne0 : y <> 0) (zne0 : z <> 0) (sm : sign z = sign x):
  atan2 x ((y/z)*x) = atan2 z y.
Proof.
  rename sm into sign_match.
  apply atan2_val; auto.
  - apply atan2_bound.
    intro P0.
    destruct P0; auto.
    rewrite atan2_sin_id;[|intro P0; destruct P0; apply zne0; auto].
    repeat rewrite Rsqr_pow2.
    assert ((x ^ 2 + (y / z * x) ^ 2) = (x/z)^2 * ( z^2 + y^2)).
    { field.
      assumption.
    }
    rewrite H.
    rewrite sqrt_mult_alt;[|apply pow2_ge_0].
    rewrite Rplus_comm.
    assert ((x/z)^2 = (x^2/z^2)) as P0.
    { field; auto. }
    rewrite P0.
    rewrite sqrt_div_alt;[|apply pow2_gt_0; auto].
    rewrite <- (Rsqr_pow2 x), <- (Rsqr_pow2 z) at 1.
    repeat rewrite sqrt_Rsqr_abs.
    assert (Rabs x / Rabs z * sqrt (y ^ 2 + z ^ 2) * (z / sqrt (y ^ 2 + z ^ 2)) = Rabs x * (z/Rabs z)) as P1.
    { field.
      split.
      - apply Rabs_no_R0; auto.
      - intro.
        apply sqrt_eq_0 in H0.
        repeat rewrite <- Rsqr_pow2 in H0.
        apply Rplus_sqr_eq_0 in H0.
        destruct H0.
        auto.
        specialize (pow2_ge_0 y) as P1.
        specialize (pow2_ge_0 z) as P2.
        lra.
    }
    rewrite P1.
    rewrite (sign_Rabs_eq z) at 1.
    assert (Rabs x * (sign z * Rabs z / Rabs z) = Rabs x * sign z) as P2.
    { field.
      apply Rabs_no_R0; auto.
    }
    rewrite P2.
    rewrite sign_match.
    rewrite Rmult_comm.
    apply sign_Rabs_eq.
    rewrite atan2_cos_id.
    repeat rewrite Rsqr_pow2.
    assert ((x ^ 2 + (y / z * x) ^ 2) = (x/z)^2 * ( z^2 + y^2)).
    { field.
      assumption.
    }
    rewrite H.
    rewrite sqrt_mult_alt;[|apply pow2_ge_0].
    rewrite Rplus_comm.
    assert ((x/z)^2 = (x^2/z^2)) as P0.
    { field; auto. }
    rewrite P0.
    rewrite sqrt_div_alt;[|apply pow2_gt_0; auto].
    rewrite <- (Rsqr_pow2 x), <- (Rsqr_pow2 z) at 1.
    repeat rewrite sqrt_Rsqr_abs.
    assert (Rabs x / Rabs z * sqrt (y ^ 2 + z ^ 2) * (y / sqrt (y ^ 2 + z ^ 2)) = Rabs x * (y / Rabs z)) as P1.
    { field.
      split.
      - apply Rabs_no_R0; auto.
      - intro.
        apply sqrt_eq_0 in H0.
        repeat rewrite <- Rsqr_pow2 in H0.
        apply Rplus_sqr_eq_0 in H0.
        destruct H0.
        auto.
        specialize (pow2_ge_0 y) as P1.
        specialize (pow2_ge_0 z) as P2.
        lra.
    }
    rewrite P1.
    rewrite (sign_Rabs_eq z) at 1.
    rewrite (sign_Rabs_eq x) at 1.
    rewrite sign_match.
    field.
    split;[ apply Rabs_no_R0 | apply sign_neq_0]; auto.
    intro.
    destruct H.
    auto.
Qed.



Lemma atan2_rotation : forall (x y θ z : R) (notO : ~ (x = 0 /\ y = 0)),
    atan2 y x = z ->
    exists n, atan2 (x * sin θ + y * cos θ)
                    (x * cos θ - y * sin θ) = (z + θ) + 2 * IZR n * PI.
Proof.
  intros.
  unfold atan2 in H.
  destruct (pre_atan2 y x) as [q [qrng [ydef xdef]]].
  subst.

  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0. lra.
  specialize (inrange_mT2T2 ((z + θ)) _ tpigt0) as [k [alb aub]].
  exists k.
  assert (IZR k * (2 * PI) = 2 * IZR k * PI) as id.
  field. rewrite id in aub, alb. clear id.
  rewrite xdef.
  rewrite ydef at 2 4.
  fieldrewrite (sqrt (y² + x²) * cos z * sin θ + sqrt (y² + x²) * sin z * cos θ)
               (sqrt (y² + x²) * (sin z * cos θ + cos z * sin θ)).
  fieldrewrite (sqrt (y² + x²) * cos z * cos θ - sqrt (y² + x²) * sin z * sin θ)
               (sqrt (y² + x²) * (cos z * cos θ - sin z * sin θ)).
  rewrite <- cos_plus.
  rewrite <- sin_plus.
  rewrite <- (cos_period1 _ k).
  rewrite <- (sin_period1 _ k).

  rewrite atan2_left_inv.
  
  field. split; lra.
  specialize (sqrt_pos (y² + x²)) as zlesqrt.
  destruct zlesqrt as [zltsqrt | zeqsqrt].
  assumption.
  exfalso.
  rewrite <- zeqsqrt in xdef, ydef.
  apply notO.
  rewrite xdef, ydef.
  split; lra.
Qed.



Lemma atan2_rotation1 : forall (x y θ z : R) (notO : ~ (x = 0 /\ y = 0)),
    (exists m, atan2 (x * sin θ + y * cos θ)
                     (x * cos θ - y * sin θ) = (z + θ) + 2 * IZR m * PI) ->
    exists n, atan2 y x = z + 2 * IZR n * PI.
Proof.
  intros.
  destruct H as [m at2rd].

  assert (~ ((x * cos θ - y * sin θ) = 0 /\
             (x * sin θ + y * cos θ) = 0)) as notOr. {
    clear - notO.
    intros [xr yr]. apply notO. clear notO.
    apply Rminus_diag_uniq_sym in xr.
    apply Rplus_opp_r_uniq in yr.

    assert (x² = y²) as x2def.
    rewrite <- Rmult_1_r, <- (sin2_cos2 θ).
    rewrite Rmult_plus_distr_l.
    rewrite <- (Rmult_1_r x²).
    rewrite <- (sin2_cos2 θ).
    rewrite Rmult_plus_distr_l.
    repeat rewrite <- Rsqr_mult.
    rewrite yr, <- xr.
    unfold Rsqr.
    field.

    destruct (Req_dec x 0) as [xeq0 |xne0].
    rewrite xeq0, Rsqr_0 in x2def.
    symmetry in x2def.
    assert (y = 0) as yeq0. {
      apply Rmult_integral in x2def.
      destruct x2def; assumption. }
    split; assumption.

    exfalso.
    apply Rsqr_eq in x2def.
    destruct x2def as [xeqy | xeqny].
    + subst.
      assert (cos θ = - sin θ) as cteqnst.
      apply (Rmult_eq_reg_l y). rewrite yr. field. assumption.
      assert (sin θ = cos θ) as steqst.
      apply (Rmult_eq_reg_l y). rewrite xr. reflexivity. assumption.
      rewrite steqst in cteqnst.
      clear - cteqnst steqst.
      destruct (Req_dec (cos θ) 0) as [cteq0 |ctne0].
      rewrite cteq0 in steqst.
      apply (coseq0_sinneq0) in cteq0. apply cteq0. assumption.
      lra.

    + subst.
      assert (cos θ = - sin θ) as cteqnst.
      apply (Rmult_eq_reg_l (-y)). rewrite <- xr. field. assumption.
      assert (sin θ = cos θ) as steqst.
      apply (Rmult_eq_reg_l y). rewrite yr. field.
      apply Ropp_neq_0_compat in xne0.
      rewrite Ropp_involutive in xne0. assumption.
      rewrite steqst in cteqnst.
      clear - cteqnst steqst.
      destruct (Req_dec (cos θ) 0) as [cteq0 |ctne0].
      rewrite cteq0 in steqst.
      apply (coseq0_sinneq0) in cteq0. apply cteq0. assumption.
      lra.
  }

  specialize (atan2_rotation _ _ (-θ) _ notOr at2rd) as [n rs].
  rewrite sin_neg, cos_neg in rs.
  repeat rewrite Rmult_plus_distr_r in rs.
  repeat rewrite Rmult_minus_distr_r in rs.
  assert ((x * cos θ * - sin θ - y * sin θ * - sin θ +
           (x * sin θ * cos θ + y * cos θ * cos θ)) =
          (y * ((sin θ)² + (cos θ)²))) as id.
  unfold Rsqr. field. rewrite id in rs. clear id.
  assert ((x * cos θ * cos θ - y * sin θ * cos θ -
           (x * sin θ * - sin θ + y * cos θ * - sin θ)) =
          (x * ((sin θ)² + (cos θ)²))) as id.
  unfold Rsqr. field. rewrite id in rs. clear id.
  rewrite sin2_cos2 in rs.
  repeat rewrite Rmult_1_r in rs.
  assert (z + θ + 2 * IZR m * PI + - θ + 2 * IZR n * PI =
          z + 2 * IZR (m+n) * PI) as id.
  rewrite plus_IZR. field. rewrite id in rs. clear id.
  exists (m+n)%Z.
  assumption.
Qed.

Lemma sinatan : forall x, sin (atan x) = x / sqrt (1 + x²).
Proof.
  intros.
  assert (~ (1 = 0 /\ x = 0)) as nO. lra.
  specialize (atan2_sin_id _ _ nO) as sinatan2.
  assert (0 < 1) as zlt1. lra.
  rewrite (atan2_atan_Q1Q4 _ _ zlt1) in sinatan2.
  assert (x = x/1). lra. rewrite H at 1. clear H.
  rewrite Rsqr_pow2.
  assert (1 = 1 ^ 2). lra. rewrite H at 2. clear H.
  assumption.
Qed.

Lemma cosatan : forall x, cos (atan x) = 1 / sqrt (1 + x²).
Proof.
  intros.
  assert (~ (1 = 0 /\ x = 0)) as nO. lra.
  specialize (atan2_cos_id _ _ nO) as sinatan2.
  assert (0 < 1) as zlt1. lra.
  rewrite (atan2_atan_Q1Q4 _ _ zlt1) in sinatan2.
  assert (x = x/1). lra. rewrite H at 1. clear H.
  rewrite Rsqr_pow2.
  assert (1 = 1 ^ 2). lra. rewrite H at 3. clear H.
  assumption.
Qed.

(** Define atan3 as a two-argument arctangent function so the branch
cut is along the +x-axis; its domain is  (0,2*PI]. *)

Definition atan3 dy dx := atan2 (-dy) (-dx) + PI.


Lemma atan3_atan2_Q1Q2_eqv : forall dy dx,
    0 < dy -> atan2 dy dx = atan3 dy dx.
Proof.
  intros.
  unfold atan3, atan2.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].
  inversion_clear pueb as [pub | peq] ;
    [|subst; rewrite sin_PI in dydef;
      assert (dy = 0) as dyeq0;
      [ setr (sqrt (dy² + dx²) * 0); assumption| subst; lra]].
  
  assert (0 < sqrt (dy² + dx²)) as sqrtgt0.
  apply sqrt_lt_R0.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.

  
  assert (0 < p) as zltp.
  assert (0 < sin p) as zltsinp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setl 0.
  rewrite <- dydef. assumption.
  rewrite <- sin_0 in zltsinp.

  destruct (Rle_dec p (PI/2)).
  destruct (Rle_dec (-(PI/2)) p).
  
  assert (- (PI / 2) <= 0) as zlb. lra.
  assert (0 <= (PI / 2)) as zub. lra.
  apply sin_increasing_0; try assumption.

  exfalso.
  apply Rnot_le_lt in n. clear r.
  set (q := p + 2*IZR 1 *PI).
  assert (q <= 3 * (PI/2)) as qle3PI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setl p. setr (- (PI/2)). assumption.
  assert ((PI/2)<=q) as qgePI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setr p. setl (- PI - PI/2).
  apply (Rlt_trans _ (-PI)). lra. assumption.
  specialize PI_RGT_0 as PIgt0.
  assert (PI <= 3*(PI/2)) as PIle2PI2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  rewrite sin_0 in zltsinp.
  rewrite <- sin_PI in zltsinp.
  rewrite <- (sin_period1 p 1%Z) in zltsinp.
  specialize (sin_decreasing_0 _ _ PIle2PI2 PI2lePI qle3PI2 qgePI2 zltsinp) as qltPI.
  unfold q in qltPI. lra.

  apply Rnot_le_lt in n. lra.
  clear plb.
  
  destruct (pre_atan2 (-dy) (-dx)) as [r [[rlb rub] [dydef2 dxdef2]]].
  
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dy)² + (-dx)²)) as sqrteq.
  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  rewrite <- dyeqv, <- dxeqv. reflexivity.
  rewrite <- sqrteq in dydef2, dxdef2. clear sqrteq.
  set (M := sqrt (dy² + dx²)) in *.

  assert (r < 0) as rlt0.
  assert (sin r < 0) as zltsinr.
  apply (Rmult_lt_reg_l M). assumption. setr 0.
  rewrite <- dydef2. lra.
  rewrite <- sin_0 in zltsinr.

  destruct (Rle_dec r (PI/2)).
  destruct (Rle_dec (-(PI/2)) r).
  
  assert (- (PI / 2) <= 0) as zlb. lra.
  assert (0 <= (PI / 2)) as zub. lra.
  apply sin_increasing_0; try assumption.

  apply Rnot_le_lt in n. clear r0 rub. lra.

  exfalso.
  apply Rnot_le_lt in n. 
  assert (r <= 3 * (PI/2)) as qle3PI2. 
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert ((PI/2)<=r) as qgePI2. left. assumption.
  specialize PI_RGT_0 as PIgt0.
  assert (PI <= 3*(PI/2)) as PIle2PI2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  rewrite sin_0 in zltsinr.
  rewrite <- sin_PI in zltsinr.
  specialize (sin_decreasing_0 _ _  qle3PI2 qgePI2 PIle2PI2 PI2lePI zltsinr) as qltPI.
  lra.
  clear rub.
  rewrite dydef in dydef2.
  rewrite dxdef in dxdef2.

  assert (sin p = sin (r + PI)) as sargs. 
  rewrite (neg_sin). 
  apply (Rmult_eq_reg_l (-M)). setl (-(M*sin p)). setr (M * sin r). assumption.
  intro. lra.

  assert (cos p = cos (r + PI)) as cargs.
  rewrite neg_cos.
  apply (Rmult_eq_reg_l (-M)). setl (-(M*cos p)). setr (M * cos r). assumption.
  intro. lra.

  assert (0 <= p<= PI) as zlep. split; lra.
  assert (0 <= r + PI <= PI) as zlerPI. split; lra.
  apply (cos_injective_range _ _ zlep zlerPI cargs).
Qed.

Lemma atan3_atan2_Q3Q4_eqv : forall dy dx,
    dy < 0 -> atan2 dy dx + 2*PI = atan3 dy dx.
Proof.
  intros.
  unfold atan3, atan2.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].
  inversion_clear pueb as [pub | peq] ;
    [|subst; rewrite sin_PI in dydef;
      assert (dy = 0) as dyeq0;
      [ setr (sqrt (dy² + dx²) * 0); assumption| subst; lra]].
  
  assert (0 < sqrt (dy² + dx²)) as sqrtgt0.
  apply sqrt_lt_R0.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.

  
  assert (p < 0) as zltp.
  assert (sin p < 0) as zltsinp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setr 0.
  rewrite <- dydef. assumption.
  rewrite <- sin_0 in zltsinp.

  destruct (Rle_dec p (PI/2)).
  destruct (Rle_dec (-(PI/2)) p).
  assert (- (PI / 2) <= 0) as zlb. lra.
  assert (0 <= (PI / 2)) as zub. lra.
  apply sin_increasing_0; try assumption.

  apply Rnot_le_lt in n. clear r pub. lra.

  exfalso.
  apply Rnot_le_lt in n. 
  assert (p <= 3 * (PI/2)) as qle3PI2. 
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert ((PI/2)<=p) as qgePI2. left. assumption.
  specialize PI_RGT_0 as PIgt0.
  assert (PI <= 3*(PI/2)) as PIle2PI2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  rewrite sin_0 in zltsinp.
  rewrite <- sin_PI in zltsinp.
  specialize (sin_decreasing_0 _ _  qle3PI2 qgePI2 PIle2PI2 PI2lePI zltsinp) as qltPI.
  lra.
  clear pub.

  destruct (pre_atan2 (-dy) (-dx)) as [r [[rlb rub] [dydef2 dxdef2]]].

  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dy)² + (-dx)²)) as sqrteq.
  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  rewrite <- dyeqv, <- dxeqv. reflexivity.
  rewrite <- sqrteq in dydef2, dxdef2. clear sqrteq.
  set (M := sqrt (dy² + dx²)) in *.

  assert (0 < r) as rlt0.
  assert (0 < sin r) as zltsinr.
  apply (Rmult_lt_reg_l M). assumption. setl 0.
  rewrite <- dydef2. lra.
  rewrite <- sin_0 in zltsinr.

  destruct (Rle_dec r (PI/2)).
  destruct (Rle_dec (-(PI/2)) r).
  

  assert (- (PI / 2) <= 0) as zlb. lra.
  assert (0 <= (PI / 2)) as zub. lra.
  apply sin_increasing_0; try assumption.

  exfalso.
  apply Rnot_le_lt in n. clear r0. 
  set (q := r + 2*IZR 1 *PI).
  assert (q <= 3 * (PI/2)) as qle3PI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setl r. setr (- (PI/2)). assumption.
  assert ((PI/2)<=q) as qgePI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setr r. setl (- PI - PI/2).
  apply (Rlt_trans _ (-PI)). lra. assumption.
  specialize PI_RGT_0 as PIgt0.
  assert (PI <= 3*(PI/2)) as PIle2PI2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  rewrite sin_0 in zltsinr.
  rewrite <- sin_PI in zltsinr.
  rewrite <- (sin_period1 r 1%Z) in zltsinr.
  specialize (sin_decreasing_0 _ _ PIle2PI2 PI2lePI qle3PI2 qgePI2 zltsinr) as qltPI.
  unfold q in qltPI. lra.

  apply Rnot_le_lt in n. lra.
  clear rlb.
  
  rewrite dydef in dydef2.
  rewrite dxdef in dxdef2.

  assert (sin p = sin (r + PI)) as sargs. 
  rewrite (neg_sin). 
  apply (Rmult_eq_reg_l (-M)). setl (-(M*sin p)). setr (M * sin r). assumption.
  intro. lra.

  assert (cos p = cos (r + PI)) as cargs.
  rewrite neg_cos.
  apply (Rmult_eq_reg_l (-M)). setl (-(M*cos p)). setr (M * cos r). assumption.
  intro. lra.

  rewrite <- (sin_period1 (r+PI) (-1%Z)) in sargs.
  rewrite <- (cos_period1 (r+PI) (-1%Z)) in cargs.
  assert (r + PI + 2 * IZR (- (1)) * PI = r - PI) as id. rewrite opp_IZR. field.
  rewrite id in sargs, cargs. clear id.

  apply (Rplus_eq_reg_r (-2*PI)). setl p. setr (r - PI).
  apply (Rmult_eq_reg_l (-1)). setl (-p). setr (- (r-PI)).
  rewrite <- cos_neg in cargs.
  rewrite <- (cos_neg (r-PI)) in cargs.

  assert (0 <= - p<= PI) as zlep. split; lra.
  assert (0 <= - (r-PI) <= PI) as zlerPI. split; lra.
  apply (cos_injective_range _ _ zlep zlerPI cargs).
  intro. lra.
Qed.

Lemma atan3_atan2_nX_eqv : forall dx,
    dx < 0 -> atan3 0 dx = PI.
Proof.
  intros.
  unfold atan3.
  set (z := -dx) in *.
  assert (0 < z). unfold z. lra.
  fieldrewrite (-0) 0.
  rewrite atan2_0 ;try assumption.
  field.
Qed.

Lemma atan3_atan2_pX_eqv : forall dx,
    0 < dx -> atan3 0 dx = 2*PI.
Proof.
  intros.
  unfold atan3.
  set (z := -dx) in *.
  assert (z < 0). unfold z. lra.
  fieldrewrite (-0) 0.
  rewrite atan2_PI ;try assumption.
  field.
Qed.


Lemma atan3_atan2_eqv : forall x y,
    ~(x = 0 /\ y = 0) -> exists k, atan2 y x = atan3 y x + 2 * IZR k * PI.
Proof.
  intros.
  destruct (Rlt_dec 0 y).
  rewrite <- atan3_atan2_Q1Q2_eqv; [|assumption].
  exists 0%Z.
  fieldrewrite (atan2 y x + 2 * 0 * PI) (atan2 y x). reflexivity.
  apply Rnot_lt_le in n.
  inversion_clear n as [ylt0 |yeq0].
  rewrite <- atan3_atan2_Q3Q4_eqv; [|assumption].
  exists ((-1)%Z).
  fieldrewrite (atan2 y x + 2 * PI + 2 * -1 * PI) (atan2 y x). reflexivity.

  destruct (Rlt_dec 0 x).
  subst.
  rewrite atan3_atan2_pX_eqv; [|assumption].
  rewrite atan2_0; [|assumption].
  exists (-1)%Z. field.

  apply Rnot_lt_le in n.
  inversion_clear n as [xlt0 | xeq0].
  subst.
  rewrite atan3_atan2_nX_eqv; [|assumption].
  rewrite atan2_PI; [|assumption].
  exists (0)%Z. field.
  exfalso.
  subst. apply H.
  split; reflexivity.
Qed.

Lemma atan3Q2_rev : forall dx dy,
    ~(dx=0/\dy=0) -> PI / 2 < atan3 dy dx < PI -> dx < 0 /\ 0 < dy.
Proof.
  intros *. intros notO at2rng.
  destruct (Rlt_dec dx 0).
  destruct (Rlt_dec 0 dy).
  split; assumption.

  exfalso.
  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  rewrite <- atan3_atan2_Q3Q4_eqv in at2rng; try assumption.
  destruct at2rng.
  specialize (atan2Q3 _ _ r dylt0) as [arl aru].
  lra.

  subst.
  rewrite (atan3_atan2_nX_eqv dx) in at2rng; try assumption.
  destruct at2rng.
  lra.

  exfalso.
  apply Rnot_lt_le in n.
  destruct n as [zltdx |zeqdx].
  destruct (Rlt_dec 0 dy).
  rewrite <- atan3_atan2_Q1Q2_eqv in at2rng; try assumption.

  destruct at2rng.
  specialize (atan2Q1 _ _ zltdx r) as [at2l at2u].
  lra.

  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  rewrite <- atan3_atan2_Q3Q4_eqv in at2rng; try assumption.
  destruct at2rng.
  specialize (atan2Q4 _ _ zltdx dylt0) as [at2l at2u].
  lra.

  subst.
  rewrite atan3_atan2_pX_eqv in at2rng; try assumption.
  destruct at2rng.
  specialize PI_RGT_0 as pigt0.
  lra.

  subst.
  destruct (Rlt_dec 0 dy).
  rewrite <- atan3_atan2_Q1Q2_eqv in at2rng; try assumption.
  rewrite atan2_PI2 in at2rng; try assumption.
  destruct at2rng.
  lra.

  apply Rnot_lt_le in n.
  destruct n as [dylt0 |dyeq0].
  rewrite <- atan3_atan2_Q3Q4_eqv in at2rng; try assumption.
  rewrite atan2_mPI2 in at2rng; try assumption.
  destruct at2rng.
  specialize PI_RGT_0 as pigt0.
  assert (3*PI < 2*PI) as abs. {
  apply (Rmult_lt_reg_r (/2)).
  apply Rinv_0_lt_compat. lra.
  fieldrewrite (3 * PI * / 2) (- PI/2 + 2*PI).
  fieldrewrite (2 * PI*/2) (PI). assumption.
  } lra.

  subst.
  apply notO. split; reflexivity.
Qed.

(** Define atan4 as a two-argument arctangent function with a branch
cut on the -y axis; its domain is (-PI/2, 3*PI/2]. *)

Definition atan4 dy dx := atan2 (-dx) (dy) + (PI/2).

Lemma atan4_atan2_Q1Q2_eqv : forall dy dx,
    0 < dy -> atan2 dy dx = atan4 dy dx.
Proof.
  intros.
  unfold atan4, atan2.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].
  inversion_clear pueb as [pub | peq] ;
    [|subst; rewrite sin_PI in dydef;
      assert (dy = 0) as dyeq0;
      [ setr (sqrt (dy² + dx²) * 0); assumption| subst; lra]].
  
  assert (0 < sqrt (dy² + dx²)) as sqrtgt0.
  apply sqrt_lt_R0.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.

  
  assert (0 < p) as zltp.
  assert (0 < sin p) as zltsinp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setl 0.
  rewrite <- dydef. assumption.
  rewrite <- sin_0 in zltsinp.

  destruct (Rle_dec p (PI/2)).
  destruct (Rle_dec (-(PI/2)) p).
  
  assert (- (PI / 2) <= 0) as zlb. lra.
  assert (0 <= (PI / 2)) as zub. lra.
  apply sin_increasing_0; try assumption.

  exfalso.
  apply Rnot_le_lt in n. clear r.
  set (q := p + 2*IZR 1 *PI).
  assert (q <= 3 * (PI/2)) as qle3PI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setl p. setr (- (PI/2)). assumption.
  assert ((PI/2)<=q) as qgePI2. unfold q. unfold INR.
  left. apply (Rplus_lt_reg_r (-2*PI)). setr p. setl (- PI - PI/2).
  apply (Rlt_trans _ (-PI)). lra. assumption.
  specialize PI_RGT_0 as PIgt0.
  assert (PI <= 3*(PI/2)) as PIle2PI2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  rewrite sin_0 in zltsinp.
  rewrite <- sin_PI in zltsinp.
  rewrite <- (sin_period1 p 1%Z) in zltsinp.
  specialize (sin_decreasing_0 _ _ PIle2PI2 PI2lePI qle3PI2 qgePI2 zltsinp) as qltPI.
  unfold q in qltPI. lra.

  apply Rnot_le_lt in n. lra.
  clear plb.
  
  destruct (pre_atan2 (-dx) (dy)) as [r [[rlb rub] [dydef2 dxdef2]]].
  
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dx)² + (dy)²)) as sqrteq.
  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  rewrite <- dxeqv. rewrite Rplus_comm. reflexivity.
  rewrite <- sqrteq in dydef2, dxdef2. clear sqrteq.
  set (M := sqrt (dy² + dx²)) in *.

  assert (0 < cos r) as zltcosr.
  apply (Rmult_lt_reg_l M). assumption. setl 0. rewrite <- dxdef2. assumption.
  
  destruct (Rlt_dec r (PI/2)).
  destruct (Rlt_dec (-(PI/2)) r).

  rewrite dydef in dxdef2.
  rewrite dxdef in dydef2.
  rewrite sin_cos in dydef2.
  rewrite cos_sin in dxdef2.

  assert (sin p = sin (r + PI/2)) as sargs. 
  apply (Rmult_eq_reg_l (M)). rewrite Rplus_comm.
  assumption.
  intro. lra.

  assert (cos p = cos (r + PI/2)) as cargs.
  rewrite Rplus_comm.
  apply (Rmult_eq_reg_l (-M)). setl (-(M*cos p)). setr (M * (- cos (PI/2+r))).
  assumption.
  intro. lra.

  assert (0 <= p<= PI) as zlep. split; lra.
  assert (0 <= r + PI/2 <= PI) as zlerPI. split; lra.
  apply (cos_injective_range _ _ zlep zlerPI cargs).

  exfalso.
  apply Rnot_lt_le in n. clear r0 rub.
  rewrite <- cos_PI2 in zltcosr.
  rewrite <- cos_neg in zltcosr.
  rewrite <- (cos_period1 _ 1%Z) in zltcosr.
  rewrite <- (cos_period1 r 1%Z) in zltcosr.
  assert (PI <= - (PI / 2) + 2 * 1 * PI) as xlb. lra.
  assert (- (PI / 2) + 2 * 1 * PI <= 2*PI) as xub. lra.
  assert (PI <= r + 2 * 1 * PI) as ylb. lra.
  assert (r + 2 * 1 * PI <= 2*PI) as yub. lra.
  specialize (cos_increasing_0 _ _ xlb xub ylb yub zltcosr) as order.
  lra.

  exfalso.
  apply Rnot_lt_le in n. clear rlb.
  rewrite <- cos_PI2 in zltcosr.

  assert (0 <= PI/2) as xlb. lra.
  assert (PI/2 <= PI) as xub. lra.
  assert (0 <= r) as ylb. lra.
  assert (r <= PI) as yub. lra.
  specialize (cos_decreasing_0 _ _ xlb xub ylb yub zltcosr) as order.
  lra.
Qed.
  

Lemma atan4_atan2_Q3_eqv : forall dy dx,
    dx < 0 -> dy < 0 -> atan2 dy dx + 2*PI = atan4 dy dx.
Proof.
  intros.
  unfold atan4, atan2.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].
  inversion_clear pueb as [pub | peq] ;
    [|subst; rewrite sin_PI in dydef;
      assert (dy = 0) as dyeq0;
      [ setr (sqrt (dy² + dx²) * 0); assumption| subst]].
  (*******)

  assert (0 < sqrt (dy² + dx²)) as sqrtgt0.
  apply sqrt_lt_R0.
  rewrite Rplus_comm.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.
  
  assert (cos p < 0) as zltcosp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setr 0.
  rewrite <- dxdef. assumption.

  assert (sin p < 0) as zltsinp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setr 0.
  rewrite <- dydef. assumption.

  destruct (Rle_dec 0 p).
  assert (p <= PI) as plePI. lra.
  specialize (sin_ge_0 _ r plePI) as zlesinp.
  lra. apply Rnot_le_lt in n.
  
  rewrite <- cos_PI2 in zltcosp.
  rewrite <- (cos_neg (PI/2)) in zltcosp.
  rewrite <- (cos_period1 _ 1%Z) in zltcosp.
  rewrite <- (cos_period1 (-(PI/2)) 1%Z) in zltcosp.
  set (q := p + 2*1*PI) in *.
  assert (-(PI/2)+2*1*PI = 3*(PI/2)) as id. field.
  rewrite id in zltcosp.
  assert (PI <= q) as plb2. unfold q. lra.
  assert (q <= 2*PI) as pub2. unfold q. lra.
  assert (PI <= 3*(PI/2)) as PI2lb2. lra.
  assert (3*(PI/2) <= 2*PI) as PI2ub2. lra.
  specialize (cos_increasing_0 _ _ plb2 pub2 PI2lb2 PI2ub2 zltcosp) as qlt.
  unfold q in qlt.
  assert (p < -(PI/2)) as pltmPI2. lra.
  clear qlt PI2ub2 PI2lb2 plb2 pub2 id n zltcosp zltsinp q pub.

  destruct (pre_atan2 (-dx) (dy)) as [r [[rlb rub] [dydef2 dxdef2]]].
  
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dx)² + (dy)²)) as sqrteq.
  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  rewrite <- dxeqv. rewrite Rplus_comm. reflexivity.
  rewrite <- sqrteq in dydef2, dxdef2. clear sqrteq.
  set (M := sqrt (dy² + dx²)) in *.

  assert (0 < sin r) as zltsinr.
  apply (Rmult_lt_reg_l (M)). assumption. setl 0. rewrite <- dydef2. lra.

  assert (cos r < 0) as cosrlt0.
  apply (Rmult_lt_reg_l (M)). assumption. setr 0. rewrite <- dxdef2. lra.

  destruct (Rle_dec r 0).
  exfalso. clear rub.
  set (q := r + 2*1*PI) in *.
  assert (q <= 2*PI) as qub. unfold q. lra.
  assert (PI <= q) as qlb. unfold q. lra.
  specialize (sin_le_0 _ qlb qub) as sinpos. unfold q in sinpos.
  rewrite (sin_period1) in sinpos. lra.
  apply Rnot_le_lt in n. clear rlb.

  rewrite <- cos_PI2 in cosrlt0.
  assert (0 <= r) as zler. left. assumption.
  assert (0 <= PI/2) as zlePI2.  lra.
  assert (PI/2 <= PI) as PI2lePI. lra.
  specialize (cos_decreasing_0 _ _ zler rub zlePI2 PI2lePI cosrlt0) as PI2ltr.
  clear PI2lePI zlePI2 zler n cosrlt0 zltsinr.

  rewrite dydef in dxdef2.
  rewrite dxdef in dydef2.
  rewrite sin_cos in dydef2.
  rewrite cos_sin in dxdef2.

  assert (sin p = sin (r + PI/2)) as sargs. 
  apply (Rmult_eq_reg_l (M)). rewrite Rplus_comm.
  assumption.
  intro. lra.

  assert (cos p = cos (r + PI/2)) as cargs.
  rewrite Rplus_comm.
  apply (Rmult_eq_reg_l (-M)). setl (-(M*cos p)). setr (M * (- cos (PI/2+r))).
  assumption.
  intro. lra.

  rewrite <- (cos_period1 (r+PI/2) (-1%Z)) in cargs.
  simpl in cargs.
  rewrite <- cos_neg in cargs.
  rewrite <- (cos_neg (r + PI / 2 + 2 * -1 * PI)) in cargs.
  assert (- (r + PI / 2 + 2 * -1 * PI) = - r - PI/2 + 2*PI) as id. field.
  rewrite id in cargs. clear id.
  assert (0 <= - p <= PI) as zlep.
  split; lra.
  assert (0 <= - r - PI/2 + 2*PI <= PI) as rlePI.
  split; lra.
  specialize (cos_injective_range _ _ zlep rlePI cargs) as cosarg.
  apply (Rmult_eq_reg_l (-1)). setl (- p - 2*PI).
  rewrite cosarg. field. discrR.
  (*******)
  rewrite cos_PI in dxdef.
  assert (sqrt (0² + dx²) * -1 = - Rabs dx) as arg.
  apply (Rmult_eq_reg_r (-1)).
  setl (sqrt (0² + dx²)). setr (Rabs dx).
  assert (0² + dx² = dx²) as arg; [
    unfold Rsqr; field; rewrite H0; clear H0;
    rewrite sqrt_Rsqr_abs; reflexivity; discrR |].
  rewrite arg.
  rewrite sqrt_Rsqr_abs. reflexivity.
  discrR.

  exfalso.
  rewrite arg in dxdef.
  rewrite dxdef in H.
  specialize (Rabs_pos dx) as pos.
  lra.
Qed.  

Lemma atan4_atan2_Q1Q4_eqv : forall dy dx,
    0 < dx -> atan2 dy dx = atan4 dy dx.
Proof.
  intros.
  unfold atan4, atan2.
  destruct (pre_atan2 dy dx) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].
  inversion_clear pueb as [pub | peq] ;
    [|subst; rewrite sin_PI in dydef;
      assert (dy = 0) as dyeq0;
      [ setr (sqrt (dy² + dx²) * 0); assumption| subst]].
  (*******)

  assert (0 < sqrt (dy² + dx²)) as sqrtgt0.
  apply sqrt_lt_R0.
  rewrite Rplus_comm.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.
  
  assert (0 < cos p) as zltcosp.
  apply (Rmult_lt_reg_l (sqrt (dy² + dx²))). assumption. setl 0.
  rewrite <- dxdef. assumption.

  destruct (Rge_dec p (PI/2)).
  rewrite <- cos_PI2 in zltcosp.
  assert (0 <= p) as plb2. lra.
  assert (p <= PI) as pub2. lra.
  assert (0 <= PI/2) as PI2lb2. lra.
  assert (PI/2 <= PI) as PI2ub2. lra.
  specialize (cos_decreasing_0 _ _ PI2lb2 PI2ub2 plb2 pub2 zltcosp) as plt.
  lra.
  apply Rnot_ge_lt in n.

  destruct (Rle_dec p (-(PI/2))).
  exfalso.
  rewrite <- cos_PI2 in zltcosp.
  rewrite <- cos_neg in zltcosp.
  rewrite <- (cos_period1 _ 1%Z) in zltcosp.
  rewrite <- (cos_period1 p 1%Z) in zltcosp.
  set (q := p + 2*1*PI) in *.
  assert (PI <= q) as qlb2. unfold q. lra.
  assert (q <= 2*PI) as qub2. unfold q. lra.
  assert (PI <= 3*(PI/2)) as PI2lb2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (3*(PI/2) <= 2*PI) as PI2ub2. 
  apply (Rmult_le_reg_r 2). lra. setl (3*PI). setr (4*PI). lra.
  assert (- (PI / 2) + 2 * 1 * PI = 3*(PI/2)) as id.
  apply (Rmult_eq_reg_r 2). setl (3*PI). setr (3*PI). reflexivity. discrR.
  rewrite id in zltcosp. clear id.
  specialize (cos_increasing_0 _ _ PI2lb2 PI2ub2 qlb2 qub2 zltcosp) as qlt.
  unfold q in qlt. assert (- (PI/2) < p) as plt.
  apply (Rplus_lt_reg_r (2*1*PI)). setl (3*(PI/2)). assumption.
  lra.

  apply Rnot_le_lt in n0.
  
  destruct (pre_atan2 (-dx) (dy)) as [r [[rlb rub] [dydef2 dxdef2]]].
  
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dx)² + (dy)²)) as sqrteq.
  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  rewrite <- dxeqv. rewrite Rplus_comm. reflexivity.
  rewrite <- sqrteq in dydef2, dxdef2. clear sqrteq.
  set (M := sqrt (dy² + dx²)) in *.

  assert (sin r < 0) as sinrlt0.
  apply (Rmult_lt_reg_l (M)). assumption. setr 0. rewrite <- dydef2. lra.

  destruct (Rle_dec 0 r).
  exfalso. specialize (sin_ge_0 r r0 rub) as sinpos. lra.

  apply Rnot_le_lt in n1. clear rub.

  rewrite dydef in dxdef2.
  rewrite dxdef in dydef2.
  rewrite sin_cos in dydef2.
  rewrite cos_sin in dxdef2.

  assert (sin p = sin (r + PI/2)) as sargs. 
  apply (Rmult_eq_reg_l (M)). rewrite Rplus_comm.
  assumption.
  intro. lra.

  assert (cos p = cos (r + PI/2)) as cargs.
  rewrite Rplus_comm.
  apply (Rmult_eq_reg_l (-M)). setl (-(M*cos p)). setr (M * (- cos (PI/2+r))).
  assumption.
  intro. lra.

  assert (-PI/2 <= p<= PI/2) as zlep.
  split; left; try setl (-(PI/2)); assumption.
  assert (-PI/2 <= r + PI/2 <= PI/2) as zlerPI.
  split; left; try setl (-(PI/2)); lra.
  apply (sin_injective_range _ _ zlep zlerPI sargs).
  (*******)
  rewrite cos_PI in dxdef.
  assert (sqrt (0² + dx²) * -1 = - Rabs dx) as arg.
  apply (Rmult_eq_reg_r (-1)).
  setl (sqrt (0² + dx²)). setr (Rabs dx).
  assert (0² + dx² = dx²) as arg; [
    unfold Rsqr; field; rewrite H0; clear H0;
    rewrite sqrt_Rsqr_abs; reflexivity; discrR |].
  rewrite arg.
  rewrite sqrt_Rsqr_abs. reflexivity.
  discrR.

  exfalso.
  rewrite arg in dxdef.
  rewrite dxdef in H.
  specialize (Rabs_pos dx) as pos.
  lra.
Qed.  

Lemma atan4_atan3_Q2Q3_eqv : forall dy dx,
    dx < 0 -> atan3 dy dx = atan4 dy dx.
Proof.
  intros.
  unfold atan4, atan3, atan2.
  destruct (pre_atan2 (-dy) (-dx)) as [p [prng [dydef dxdef]]].
  inversion_clear prng as [plb pueb].

  assert (0 < sqrt ((-dy)² + (-dx)²)) as sqrtgt0.
  apply sqrt_lt_R0.
  rewrite Rplus_comm.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt. intro. lra.
  apply Rle_0_sqr.
  
  assert (0 < cos p) as zltcosp.
  apply (Rmult_lt_reg_l (sqrt ((-dy)² + (-dx)²))). assumption. setl 0.
  rewrite <- dxdef. lra.

  destruct (Rge_dec p (PI/2)).
  exfalso.
  rewrite <- cos_PI2 in zltcosp.
  assert (0 <= p) as plb2. lra.
  assert (p <= PI) as pub2. lra.
  assert (0 <= PI/2) as PI2lb2. lra.
  assert (PI/2 <= PI) as PI2ub2. lra.
  specialize (cos_decreasing_0 _ _ PI2lb2 PI2ub2 plb2 pub2 zltcosp) as plt.
  lra. apply Rnot_ge_lt in n.

  destruct (Rle_dec p (-(PI/2))).
  exfalso.
  rewrite <- cos_PI2 in zltcosp.
  rewrite <- cos_neg in zltcosp.
  rewrite <- (cos_period1 _ 1%Z) in zltcosp.
  rewrite <- (cos_period1 p 1%Z) in zltcosp.
  set (q := p + 2*1*PI) in *.
  assert (PI <= q) as qlb2. unfold q. lra.
  assert (q <= 2*PI) as qub2. unfold q. lra.
  assert (PI <= 3*(PI/2)) as PI2lb2.
  apply (Rmult_le_reg_r 2). lra. setr (3*PI). lra.
  assert (3*(PI/2) <= 2*PI) as PI2ub2. 
  apply (Rmult_le_reg_r 2). lra. setl (3*PI). setr (4*PI). lra.
  assert (- (PI / 2) + 2 * 1 * PI = 3*(PI/2)) as id.
  apply (Rmult_eq_reg_r 2). setl (3*PI). setr (3*PI). reflexivity. discrR.
  rewrite id in zltcosp. clear id.
  specialize (cos_increasing_0 _ _ PI2lb2 PI2ub2 qlb2 qub2 zltcosp) as qlt.
  unfold q in qlt. assert (- (PI/2) < p) as plt.
  apply (Rplus_lt_reg_r (2*1*PI)). setl (3*(PI/2)). assumption.
  lra. apply Rnot_le_lt in n0.
  clear plb pueb.
  
  destruct (pre_atan2 (-dx) (dy)) as [r [[rlb rueb] [dydef2 dxdef2]]].
  inversion_clear rueb as [rub | req];
    [|exfalso; subst; rewrite sin_PI in dydef2; lra].

  assert (dy² = (-dy)²) as dyeqv. unfold Rsqr. field.
  assert (dx² = (-dx)²) as dxeqv. unfold Rsqr. field.
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dy)² + (-dx)²)) as sqrteq.
  rewrite <- dxeqv, <- dyeqv. reflexivity.
  rewrite <- sqrteq in dydef, dxdef, sqrtgt0. clear sqrteq.
  
  assert (sqrt ((dy)² + (dx)²) = sqrt ((-dx)² + (dy)²)) as sqrteq2.
  rewrite <- dxeqv. rewrite Rplus_comm. reflexivity.
  rewrite <- sqrteq2 in dydef2, dxdef2. clear sqrteq2.
  set (M := sqrt (dy² + dx²)) in *.
  clear dyeqv dxeqv.
  
  assert (0 < sin r) as sinrlt0.
  apply (Rmult_lt_reg_l (M)). assumption. setl 0. rewrite <- dydef2. lra.

  destruct (Rge_dec 0 r).
  exfalso.
  assert (PI <= r + 2*1*PI) as rplb. lra.
  assert (r + 2*1*PI <= 2*PI) as rpub. lra.
  specialize (sin_le_0 _ rplb rpub) as sinpos.
  rewrite sin_period1 in sinpos. lra.
  apply Rnot_ge_lt in n1. clear rlb zltcosp sinrlt0.

  rewrite dxdef in dydef2.
  assert (dy = - M * sin p) as id.
  apply (Rmult_eq_reg_l (-1)). setl (-dy). rewrite dydef. field. discrR.
  rewrite id in dxdef2. clear id.
  rewrite sin_cos in dydef2.
  rewrite cos_sin in dxdef2.

  assert (- cos p = cos (r + PI/2)) as ccid.
  apply (Rmult_eq_reg_l (-M)). setl (M*cos p). setr (M * - cos (r + PI/2)).
  rewrite Rplus_comm. assumption. intro. lra.
  rewrite <- (neg_cos p) in ccid. clear dydef2 dydef.

  assert (- sin p = sin (r + PI/2)) as ssid.
  apply (Rmult_eq_reg_l (M)). setl (- M*sin p).
  rewrite Rplus_comm. assumption. intro. lra.
  rewrite <- (neg_sin p) in ssid. clear dxdef2 dxdef.

  assert (0 <= p+PI) as zlepPI. lra.
  assert (0 <= r+PI/2) as zlerPI2. lra.
  
  destruct (Rle_dec (p+PI) PI).
  assert (p <= 0) as ple0. lra. clear n.
  destruct (Rle_dec (r+PI/2) PI).
  apply cos_injective_range.
  split; lra.
  split; lra.
  assumption.

  exfalso.
  apply Rnot_le_lt in n. clear zlerPI2.
  assert (PI/2 < r) as PI2ltr. lra.
  assert (r + PI/2 < 2*PI) as rPI2lt2PI. lra.
  specialize (sin_lt_0 _ n rPI2lt2PI) as sinlt0.
  rewrite <- ssid in sinlt0.
  specialize (sin_ge_0 _ zlepPI r0) as singe0. lra.

  apply Rnot_le_lt in n2.
  destruct (Rle_dec (r+PI/2) PI).
  exfalso.
  clear zlepPI.
  specialize (sin_ge_0 _ zlerPI2 r0) as singe0.
  assert (p+PI < 2*PI) as pPIle2PI. lra.
  specialize (sin_lt_0 _ n2 pPIle2PI) as sinlt0.
  rewrite ssid in sinlt0. lra.

  apply Rnot_le_lt in n3. clear zlepPI zlerPI2.
  apply (Rplus_eq_reg_r (2*(-1)*PI)).
  apply (Rmult_eq_reg_l (-1)).
  setl (- ( p + PI + 2 * -1 * PI)). setr (- (r + PI/2 + 2*-1*PI)).
  apply cos_injective_range.
  split; lra. split; lra.
  rewrite cos_neg. rewrite cos_neg.
  rewrite cos_period1. rewrite cos_period1.
  assumption. discrR.
Qed.

