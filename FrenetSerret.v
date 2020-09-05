(* begin hide *)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import FunctionalExtensionality.
Require Import Lra.
Require Import util.
Require Import atan2.

Lemma nzm : forall a b, (a² + b²) <> 0 -> ~ (a = 0 /\ b = 0).
Proof.
  intros * a2b2ne0.
  intros [aeq0 beq0].
  apply a2b2ne0.
  rewrite aeq0, beq0.
  unfold Rsqr.
  field.
Qed.

(* end hide *)

Definition dot_prod (a b : R * R) := fst a * fst b + snd a * snd b.

Lemma dot_prod_comm : forall A B,
    dot_prod A B = dot_prod B A.
Proof.
  intros.
  unfold dot_prod.
  field.
Qed.

Lemma dot_prod_scal_l : forall K Ax Ay B,
    dot_prod (K * Ax, K * Ay) B = K * dot_prod (Ax, Ay) B.
Proof.
  intros.
  unfold dot_prod.
  simpl.
  field.
Qed.

Lemma dot_prod_colinear : forall ux uy vx vy wx wy,
    ~ (ux = 0 /\ uy = 0) -> 
    ~ (vx = 0 /\ vy = 0) -> 
    ~ (wx = 0 /\ wy = 0) -> 
    dot_prod (ux,uy) (wx,wy) = 0 ->
    dot_prod (vx,vy) (wx,wy) = 0 ->
    exists c, (vx,vy) = (c * ux, c * uy).
Proof.
  intros * une0 vne0 wne0 perpU perpV.
  unfold dot_prod in *.
  simpl in *.
  apply Rplus_opp_r_uniq in perpU.
  apply Rplus_opp_r_uniq in perpV.
  destruct (Req_dec wx 0) as [wxeq0 | wxne0].
  + rewrite wxeq0 in *.
    autorewrite with null in *.
    assert (wy <> 0) as wyne0; try lra.
    assert (uy = 0) as uyeq0. {
      apply (Rmult_eq_reg_r wy); try assumption.
      arn; assumption. }
    assert (vy = 0) as vyeq0. {
      apply (Rmult_eq_reg_r wy); try assumption.
      arn; assumption. }
    rewrite uyeq0, vyeq0.
    assert (ux <> 0) as uxne0; try lra.
    assert (vx <> 0) as vxne0; try lra.
    exists (vx / ux).
    arn.
    fieldrewrite (vx / ux * ux) vx; try assumption.
    reflexivity.
  + assert (ux = - uy * wy * / wx) as uxd. {
      apply (Rmult_eq_reg_r (-wx)); try lra.
      setl (- (ux * wx)).
      rewrite <- perpU.
      field; assumption. }
      assert (vx = - vy * wy * / wx) as vxd. {
      apply (Rmult_eq_reg_r (-wx)); try lra.
      setl (- (vx * wx)).
      rewrite <- perpV.
      field; assumption. }
    rewrite uxd, vxd.
    destruct (Req_dec uy 0) as [uyeq0 | uyne0].
    rewrite uyeq0 in *.
    arn.
    assert (vy = 0) as vyeq0; lra.
    exists (vy / uy).
    fieldrewrite (vy / uy * (- uy * wy * / wx)) (- vy * wy * / wx).
    lra.
    fieldrewrite (vy / uy * uy) vy.
    lra.
    reflexivity.
Qed.

Lemma is_deriv_dot_prod : forall (fx fy gx gy:R->R) (s:R) (dfx dfy dgx dgy:R),
    is_derive fx s dfx ->
    is_derive fy s dfy ->
    is_derive gx s dgx ->
    is_derive gy s dgy ->
    is_derive (fun s:R => dot_prod (fx s, fy s) (gx s, gy s)) s
              (dot_prod (dfx, dfy) (gx s, gy s) +
               dot_prod (fx s, fy s) (dgx, dgy)).
Proof.
  intros.
  unfold dot_prod, fst, snd.
  assert ((fun s : R => fx s * gx s + fy s * gy s)=
          fun s0 : R => plus (mult (fx s0) (gx s0))
                             (mult (fy s0) (gy s0))) as id. {
    unfold mult, plus. simpl. reflexivity. }
  rewrite id. clear id.
  assert ((dfx * gx s + dfy * gy s + (fx s * dgx + fy s * dgy)) =
          plus (plus (mult dfx (gx s)) (mult dfy (gy s)))
               (plus (mult (fx s) dgx) (mult (fy s) dgy))) as id2. {
    unfold mult, plus. simpl. reflexivity. }
  rewrite id2. clear id2.
  assert ((plus (plus (mult dfx (gx s)) (mult dfy (gy s)))
                (plus (mult (fx s) dgx) (mult (fy s) dgy))) =
          (plus (plus (mult dfx (gx s)) (mult (fx s) dgx))
                (plus (mult dfy (gy s)) (mult (fy s) dgy)))) as id3. {
    unfold plus, mult. simpl. field. }
  rewrite id3; clear id3.
  apply (is_derive_plus
           (fun s1 : R => mult (fx s1) (gx s1))
           (fun s1 : R => mult (fy s1) (gy s1))).
  apply (is_derive_mult fx gx s dfx dgx); try assumption.
  simpl; apply Rmult_comm.
  apply (is_derive_mult fy gy s dfy dgy); try assumption.
  simpl; apply Rmult_comm.
Qed.

  
  
Module Type Path2D.
  (* position x and y components *)
  Parameter s : R.
  Parameter (Fx Fy : R -> R). 
  Parameter ex_derive_Fx : locally s (fun s => ex_derive Fx s).
  Parameter ex_derive_Fy : locally s (fun s => ex_derive Fy s).

  (* velocity components *)
  Definition Tx := Derive Fx. 
  Definition Ty := Derive Fy.
  Parameter ex_derive_Tx : locally s (fun s => ex_derive Tx s).
  Parameter ex_derive_Ty : locally s (fun s => ex_derive Ty s).
  (* The path (Fx s, Fy s) is parameterized by distance; velocity is 1 *)
  Parameter unitvelocity : locally s (fun s => (Tx s)² + (Ty s)² = 1).
  (* curvature is always defined -- no straight motion *)
  Parameter accel_nonzero : locally s (fun s => (Derive Tx s)² + (Derive Ty s)² <> 0).

  (* accel direction components *)
  Definition κ s := sqrt ((Derive Tx s)² + (Derive Ty s)²).
  Definition Nx s := / κ s * Derive Tx s. 
  Definition Ny s := / κ s * Derive Ty s.
  Parameter ex_derive_Nx : locally s (fun s => ex_derive Nx s).
  Parameter ex_derive_Ny : locally s (fun s => ex_derive Ny s).
End Path2D.


Ltac ebff :=
  let eps := fresh "eps" in
  let rest := fresh "rest" in
  let yebs := fresh "yebs" in
  let y := fresh "y" in
  match goal with
  | P : locally ?s ?Q |- locally ?s ?R =>
    unfold locally in *;
    destruct P as [eps rest];
    exists eps;
    intros y yebs;
    specialize (rest y yebs)
  end.



Module FrenetSerret2D (Import p : Path2D).
  (* N is a unit vector showing accel direction *)
  Lemma unitN : locally s (fun s => (Nx s)² + (Ny s)² = 1).
  Proof.
    intros.
    unfold Nx, Ny, κ.
    repeat rewrite Rsqr_mult.
    assert (locally s (fun s => 0 < (Derive Tx s)² + (Derive Ty s)²)) as gt0. {
      specialize accel_nonzero as [eps anz].
      unfold locally in *; simpl in *.
      exists eps.
      intros y yebs.
      specialize (anz y yebs).
      assert (0 <= (Derive Tx y)² + (Derive Ty y)²) as ge0. {
        apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    lra. }

    ebff.

    repeat rewrite Rsqr_mult.
    rewrite Rsqr_inv.
    2 : {
      intro DTx2DTy2eq0.
      apply sqrt_eq_0 in DTx2DTy2eq0; try assumption;
      lra. }
    rewrite Rsqr_sqrt; try assumption.
    rename y into s.
    setl (((Derive Tx s)² + (Derive Ty s)²)/((Derive Tx s)² + (Derive Ty s)²)).
    change ((Derive Tx s)² + (Derive Ty s)² <> 0).
    lra.
    field.
    lra.
    lra.
  Qed.
  
  Lemma kgt0 : locally s (fun s => 0 < κ s).
  Proof.
    intros.
    unfold κ.
    specialize (accel_nonzero) as ne0.
    ebff.
    rename y into s.
    specialize (Rle_0_sqr (Derive Ty s)) as DTyge0.
    specialize (Rle_0_sqr (Derive Tx s)) as DTxge0.
    specialize (Rplus_le_le_0_compat _ _ DTxge0 DTyge0) as zle.
    destruct zle as [zlt |zeq]; try lra.
    apply sqrt_lt_R0.
    assumption.
  Qed.

  Lemma Tx_def : locally s (fun s => Tx s = (fun v => cos (atan2 (Ty v) (Tx v))) s).
  Proof.
    set (g := (fun u : R => atan2 (Ty u) (Tx u))) in *.
    specialize (unitvelocity) as uv.
    ebff.
    rename y into s.
    rename rest into uv.
    simpl in *.
    assert ((Tx s)² + (Ty s)² <> 0) as n0. {
      intros.
      intro e0.
      rewrite e0 in uv.
      lra. }
    apply nzm in n0.
    specialize (atan2_bound _ _ n0) as pr.
    change (-PI < g s <= PI) in pr.
    assert (0 < 1). lra.
    specialize (atan2_left_inv _ 1 pr ltac:(lra)) as a2a2.
    unfold g in a2a2 at 3.
    unfold atan2 in a2a2.
    destruct pre_atan2 as [a [abnd [ayd axd]]].
    destruct pre_atan2 as [b [bbnd [byd bxd]]].
    rewrite Rplus_comm in uv.
    rewrite uv in *.
    autorewrite with null in *.
    rewrite sqrt_1 in *.
    autorewrite with null in *.
    subst.
    rewrite <- bxd in axd.
    rewrite <- byd in ayd.
    clear abnd bbnd byd bxd b H.
    symmetry.
    assumption.
  Qed.

  Lemma Ty_def : locally s (fun s => Ty s = (fun v => sin (atan2 (Ty v) (Tx v))) s).
  Proof.
    set (g := (fun u : R => atan2 (Ty u) (Tx u))) in *.
    specialize (unitvelocity) as uv.
    ebff.
    rename y into s.
    rename rest into uv.
    simpl in *.
    assert ((Tx s)² + (Ty s)² <> 0) as n0. {
      intros.
      intro e0.
      rewrite e0 in uv.
      lra. }
    apply nzm in n0.
    specialize (atan2_bound _ _ n0) as pr.
    change (-PI < g s <= PI) in pr.
    assert (0 < 1). lra.
    specialize (atan2_left_inv _ 1 pr ltac:(lra)) as a2a2.
    unfold g in a2a2 at 3.
    unfold atan2 in a2a2.
    destruct pre_atan2 as [a [abnd [ayd axd]]].
    destruct pre_atan2 as [b [bbnd [byd bxd]]].
    rewrite Rplus_comm in uv.
    rewrite uv in *.
    autorewrite with null in *.
    rewrite sqrt_1 in *.
    autorewrite with null in *.
    subst.
    rewrite <- bxd in axd.
    rewrite <- byd in ayd.
    clear abnd bbnd byd bxd b H.
    symmetry.
    assumption.
  Qed.

  (* begin hide *)  
  (* velocity magnitude = 1 *)

  Lemma normTeq1 : locally s (fun s => dot_prod (Tx s, Ty s) (Tx s, Ty s) = 1).
  Proof.
    unfold dot_prod, fst, snd.
    intros.
    apply unitvelocity.
  Qed.

  (* N is a unit vector showing accel direction *)
  Lemma normNeq1 : locally s (fun s => dot_prod (Nx s, Ny s) (Nx s, Ny s) = 1).
  Proof.
    unfold dot_prod, fst, snd.
    intros.
    apply unitN.
  Qed.

  (* end hide *)
  Lemma dTx_eq_kNx: locally s (fun s => Derive Tx s = κ s * Nx s).
  Proof.
    intros.
    unfold Nx.
    specialize (kgt0) as kgt0.
    ebff.
    field.
    lra.
  Qed.
    
  Lemma dTy_eq_kNy: locally s (fun s => Derive Ty s = κ s * Ny s).
  Proof.
    intros.
    unfold Ny.
    specialize (kgt0) as kgt0.
    ebff.
    field.
    lra.
  Qed.

  (* this section gobbles up two locally's in the context *)    
  (* A : locally s f, B : locally s g  *)
  (* find locally common ball in context*)
  Ltac fllcb P Q :=
    let epsp := fresh "epsp" in
    let restp := fresh "restp" in
    let epsq := fresh "epsq" in
    let restq := fresh "restq" in
    let a := fresh "a" in
    let b := fresh "b" in
    let y := fresh "y" in
    let seby := fresh "seby" in
    let lii := fresh "lii" in
    let rii := fresh "rii" in
    match type of P with
    | locally ?s ?f =>
      match type of Q with
      | locally s ?g =>
        unfold locally in P, Q;
        destruct P as [epsp restp];
        destruct Q as [epsq restq];
        assert (0 < Rmin epsp epsq) as zltrmpr; 
        [unfold Rmin;
         destruct Rle_dec;
         [destruct epsp;
          simpl in *; lra|
          destruct epsq;
          simpl in *; lra] |];
        assert (forall y:R, ball s (Rmin epsp epsq) y -> ball s epsp y) as a;
        [simpl; intros y seby; unfold ball in *; simpl in *; unfold AbsRing_ball in *;
         apply Rmin_def in seby; destruct seby as [lii rii]; assumption |];
        assert (forall y:R, ball s (Rmin epsp epsq) y -> ball s epsq y) as b;
        [simpl; intros y seby; unfold ball in *; simpl in *; unfold AbsRing_ball in *;
         apply Rmin_def in seby; destruct seby as [lii rii]; assumption |]
      | _ => fail
      end
    | _ => fail
    end.  

  (* this section needs the context to look like this: 
     A : 0 < eps
     D : locally s f
   *)
  Ltac flcb A L :=
    let epsr := fresh "epsr" in
    let restr := fresh "restr" in
    let zltne := fresh "zltne" in
    let a := fresh "a" in
    let b := fresh "b" in
    match type of A with
    | 0 < ?e =>
      match type of L with
      | locally ?s ?f =>
        match goal with
        | B : forall y, ball s e y -> ?P y |- _ =>
          unfold locally in L;
          destruct L as [epsr restr];
          assert (0 < Rmin epsr e) as zltne;
          [apply def_Rmin;
           split; [destruct epsr; simpl; lra|
                   assumption] |];
          assert (forall y:R, ball s (Rmin epsr e) y -> ball s e y) as a;
          [ simpl; intros y seby; unfold ball in *; simpl in *; unfold AbsRing_ball in *;
            apply Rmin_def in seby; destruct seby as [lii rii]; assumption|];
          assert (forall y:R, ball s (Rmin epsr e) y -> ball s epsr y) as b;
          [ simpl; intros y seby; unfold ball in *; simpl in *; unfold AbsRing_ball in *;
            apply Rmin_def in seby; destruct seby as [lii rii]; assumption|]
        | _ => fail
        end
      | _ => fail
      end
    | _ => fail
    end.

  (* conclude with the smallest ball *)
  Ltac csb egt0 :=
    let y := fresh "y" in
    let sb := fresh "sb" in
    match type of egt0 with
    | 0 < ?e => 
      unfold locally;
      exists (mkposreal _ egt0);
      simpl; intros y sb
    end.

    
  (* specialize with increasing balls *)
  Ltac sib y b :=
    match type of b with
    | ball ?s ?e y =>
      repeat match goal with 
             | A : forall y, ball s e y -> ?P |- _ =>
               specialize (A y b);
               match type of A with
               | ball ?s1 ?e1 ?y1 => sib y1 A
               | _ => idtac
               end
             end
    end.

  Ltac reseat_locally rests :=
    let egt0 := fresh "egt0" in
    let b2 := fresh "b2" in
    let b3 := fresh "b3" in
    let y0 := fresh "y0" in
    let byey0 := fresh "byey0" in
    let r := fresh "r" in
    let r0 := fresh "r0" in
    match type of rests with
    | forall y, ball ?s ?epss y -> ?P y =>
      match goal with
      | b1 : ball s epss ?y |- locally ?y P =>
        unfold locally;
        assert (0 < Rmin (s + epss - y) (y - (s - epss))) as egt0;
        [ unfold ball in b1;
          simpl in *;
          unfold AbsRing_ball, abs, minus, plus, opp in *;
          simpl in *;
          apply Rabs_def2 in b1;
          destruct b1 as [b2 b3];
          unfold Rmin;
          destruct Rle_dec; lra|];
        exists (mkposreal _ egt0);
        simpl;
        intros y0 byey0;
        apply rests;
        unfold ball in *;
        simpl in *;
        unfold AbsRing_ball in *;
        simpl in *;
        unfold abs, minus, opp, plus in *;
        simpl in *;
        clear rests;
        fieldrewrite (y0 + - s) ((y0 + - y) + (y + - s));
        eapply Rle_lt_trans; [apply Rabs_triang | unfold Rabs in b1];
        destruct Rcase_abs as [r | r];
        unfold Rabs at 2;
        destruct Rcase_abs as [r0 | r0];
        try lra;
        clear r0;
        unfold Rmin in *;
        destruct Rle_dec; try lra
      end
    end.
  
  (* begin hide *)  
  Lemma dTperpT : locally s (fun s => dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) = 0).
  Proof.
    intros.
    assert (locally s
                    (fun s =>
                       dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) =
                       / 2 * (dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) +
                              dot_prod (Tx s, Ty s) (Derive Tx s, Derive Ty s)))) as id. {
      unfold dot_prod, fst, snd.
      unfold locally.
      exists (mkposreal 1 ltac:(lra)).
      intros y yebs.
      simpl in yebs.
      field. }
    specialize (ex_derive_Tx) as DTxd. 
    specialize (ex_derive_Ty) as DTyd.

    assert (locally p.s (fun s : R => (fun t => plus (Tx t * Tx t)
                                                     (Ty t * Ty t)) s =
                                      (fun _ => 1) s)) as T2. {
      specialize normTeq1 as nteq1.
      ebff.
      unfold dot_prod, fst, snd in rest.
      unfold plus; simpl.
      assumption. }
    
    fllcb DTxd DTyd.
    flcb zltrmpr id.
    flcb zltne T2.
    csb zltne0.

    change (forall y : R_UniformSpace, ball s epsr0 y ->
             (fun y => plus (Tx y * Tx y) (Ty y * Ty y) = 1) y) in restr0.

    assert (locally y (fun s : R => (fun t => plus (Tx t * Tx t)
                                                     (Ty t * Ty t)) s =
                                    (fun _ => 1) s)) as T3. {
      specialize (b1 y sb).
      rename epsr0 into epss.
      rename restr0 into rests.
      clear - rests y b1.
      reseat_locally rests. }

    sib y sb.
    
    rename restr into id.
    rename y into s.
    rename restq into DTyd.
    rename restp into DTxd.
    rename restr0 into T2.

    rewrite id; clear id.
    unfold dot_prod, fst, snd.
    setl (/ 2 * ((Derive Tx s * Tx s + Tx s * Derive Tx s) +
                 (Derive Ty s * Ty s + Ty s * Derive Ty s))).
    assert (plus (mult (Derive Tx s) (Tx s)) (mult (Tx s) (Derive Tx s)) =
            Derive Tx s * Tx s + Tx s * Derive Tx s) as idx; try reflexivity.
    assert (plus (mult (Derive Ty s) (Ty s)) (mult (Ty s) (Derive Ty s)) =
            Derive Ty s * Ty s + Ty s * Derive Ty s) as idy; try reflexivity.
    rewrite <- idx, <- idy. clear idx idy.

    
    assert (forall (p q:R), mult p q = mult q p) as Rmult_comm_mult. {
      unfold mult.
      simpl.
      apply Rmult_comm. }
    apply Derive_correct in DTxd.
    apply Derive_correct in DTyd.
    specialize (is_derive_mult _ _ _ _ _ DTxd DTxd Rmult_comm_mult) as dTx2.
    specialize (is_derive_mult _ _ _ _ _ DTyd DTyd Rmult_comm_mult) as dTy2.
    generalize dTx2; intro DTx2.
    generalize dTy2; intro DTy2.
    apply is_derive_unique in DTx2. simpl in DTx2.
    apply is_derive_unique in DTy2. simpl in DTy2.
    unfold mult, plus in *.
    simpl in *.
    rewrite <- DTy2, <- DTx2.
    specialize (is_derive_plus _ _ _ _ _ dTx2 dTy2) as dsum.
    rewrite <- DTy2, <- DTx2 in dsum.
    apply is_derive_unique in dsum.
    unfold plus in dsum at 2.
    simpl in dsum.
    rewrite <- dsum.

    unfold plus in *.
    simpl in *.
    rewrite (Derive_ext_loc _ _ _ T3).
    specialize (is_derive_const 1 s) as idc.
    simpl in idc.
    apply is_derive_unique in idc.
    rewrite idc.
    unfold zero.
    simpl.
    field.
  Qed.


  Lemma dNperpN : locally s (fun s => dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) = 0).
  Proof.
    intros.
    assert (locally s
                    (fun s =>
                       dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) =
                       / 2 * (dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) +
                              dot_prod (Nx s, Ny s) (Derive Nx s, Derive Ny s)))) as id. {
      unfold dot_prod, fst, snd.
      unfold locally.
      exists (mkposreal 1 ltac:(lra)).
      intros y yebs.
      simpl in yebs.
      field. }

    specialize (ex_derive_Nx) as DNxd.
    specialize (ex_derive_Ny) as DNyd.

    assert (locally p.s (fun s : R => (fun t => plus (Nx t * Nx t)
                                                     (Ny t * Ny t)) s =
                                      (fun _ => 1) s)) as T2. {
      specialize normNeq1 as nTe1.
      ebff.
      unfold dot_prod, fst, snd, plus in *.
      simpl in *.
      assumption. }

    fllcb DNxd DNyd.
    flcb zltrmpr id.
    flcb zltne T2.
    csb zltne0.

    change (forall y, ball s epsr0 y ->
                      (fun y => plus (Nx y * Nx y) (Ny y * Ny y) = 1) y) in restr0.

    assert (locally y (fun s : R => (fun t => plus (Nx t * Nx t)
                                                   (Ny t * Ny t)) s =
                                    (fun _ => 1) s)) as T3. {
      specialize (b1 y sb).
      rename epsr0 into epss.
      rename restr0 into rests.
      clear - rests y b1.
      reseat_locally rests. }

    sib y sb.

    rename restr into id.
    rename y into s.
    rename restq into DNyd.
    rename restp into DNxd.
    rename restr0 into T2.

    rewrite id; clear id.
    unfold dot_prod, fst, snd.
    setl (/ 2 * ((Derive Nx s * Nx s + Nx s * Derive Nx s) +
                 (Derive Ny s * Ny s + Ny s * Derive Ny s))).
    assert (plus (mult (Derive Nx s) (Nx s)) (mult (Nx s) (Derive Nx s)) =
            Derive Nx s * Nx s + Nx s * Derive Nx s) as idx; try reflexivity.
    assert (plus (mult (Derive Ny s) (Ny s)) (mult (Ny s) (Derive Ny s)) =
            Derive Ny s * Ny s + Ny s * Derive Ny s) as idy; try reflexivity.
    rewrite <- idx, <- idy. clear idx idy.

    assert (forall (p q:R), mult p q = mult q p) as Rmult_comm_mult. {
      unfold mult.
      simpl.
      apply Rmult_comm. }
    apply Derive_correct in DNxd.
    apply Derive_correct in DNyd.
    specialize (is_derive_mult _ _ _ _ _ DNxd DNxd Rmult_comm_mult) as dNx2.
    specialize (is_derive_mult _ _ _ _ _ DNyd DNyd Rmult_comm_mult) as dNy2.
    generalize dNx2; intro DNx2.
    generalize dNy2; intro DNy2.
    apply is_derive_unique in DNx2. simpl in DNx2.
    apply is_derive_unique in DNy2. simpl in DNy2.
    unfold mult, plus in *.
    simpl in *.
    rewrite <- DNy2, <- DNx2.
    specialize (is_derive_plus _ _ _ _ _ dNx2 dNy2) as dsum.
    rewrite <- DNy2, <- DNx2 in dsum.
    apply is_derive_unique in dsum.
    unfold plus in dsum at 2.
    simpl in dsum.
    rewrite <- dsum.

    unfold plus in *.
    simpl in *.
    rewrite (Derive_ext_loc _ _ _ T3).
    specialize (is_derive_const 1 s) as idc.
    simpl in idc.
    apply is_derive_unique in idc.
    rewrite idc.
    unfold zero.
    simpl.
    field.
  Qed.

  Lemma TperpN : locally s (fun s => dot_prod (Tx s, Ty s) (Nx s, Ny s) = 0).
  Proof.
    intros.
    specialize dTperpT as dTT.
    ebff.
    rewrite dot_prod_comm.
    unfold Nx, Ny.
    rewrite dot_prod_scal_l.
    rewrite rest.
    lra.
  Qed.

  Set Bullet Behavior "Strict Subproofs".
  Lemma vad : 
    exists c, ((c=1 \/ c=-1) /\ locally s (fun s => (Nx s, Ny s) = (-c*Ty s, c*Tx s))).
  Proof.
    intros.
    assert (forall s, dot_prod (Nx s, Ny s) (-Ny s, Nx s) = 0) as NdotperpN. {
      intros.
      unfold dot_prod, fst, snd.
      field. }
    specialize TperpN as TperpN.
    setoid_rewrite dot_prod_comm in NdotperpN.
    assert (locally s (fun s => (Nx s)² + (Ny s)² <> 0)) as Nne0. {
      intros.
      specialize unitN as lun.
      clear - lun.
      ebff.
      rewrite rest.
      discrR. }
    
    assert (locally s (fun s => (- Ny s)² + (Nx s)² <> 0)) as perpNne0. {
      clear - Nne0.
      ebff.
      intros.
      rewrite Rplus_comm.
      rewrite  <- Rsqr_neg.
      apply rest. }

    assert (locally s (fun s => (Tx s)² + (Ty s)² <> 0)) as Tne0. {
      intros.
      specialize unitvelocity as uv.
      clear - uv.
      ebff.
      rewrite rest.
      discrR. }

    assert (locally s (fun s =>
                          exists c : R, (Tx s, Ty s) =
                                        (c * (- Ny s), c * Nx s))) as col. {
      specialize TperpN as tn.
      clear - tn NdotperpN perpNne0 Tne0 Nne0.
      fllcb perpNne0 tn.
      flcb zltrmpr Tne0.
      flcb zltne Nne0.
      csb zltne0.
      sib y sb.

      clear zltrmpr a b zltne a0 b0 a1 b1 sb zltne0 zltne epsp epsq epsr epsr0.
      eapply dot_prod_colinear.
      apply nzm; eauto.
      apply nzm; eauto.
      apply nzm; apply restr0.
      auto.
      auto. }

    assert (locally s (fun s => exists c : R,
                           (c = 1 \/ c = -1) /\
                           (Nx s, Ny s) = (- c * Ty s, c * Tx s))) as col2. {
      clear - col.
      specialize unitvelocity as uv.
      specialize unitN as un.
      fllcb uv un.
      flcb zltrmpr col.
      csb zltne.
      sib y sb.

      destruct restr as [c col].
      clear a b a0 b0 sb zltne zltrmpr epsp epsq.
      rename y into s.
      rename restp into uv.
      rename restq into unitN.
      assert (c = 1 \/ c = -1) as cdef. {
        inversion col as [[txd tyd]].
        rewrite tyd, txd in uv.
        repeat rewrite Rsqr_mult in uv.
        rewrite <- Rsqr_neg, <- Rmult_plus_distr_l, Rplus_comm in uv.
        rewrite unitN in uv.
        autorewrite with null in uv.
        rewrite <- Rsqr_1 in uv.
        apply Rsqr_eq in uv.
        auto. }
      destruct cdef as [cd1 | cdn1].
      + exists (-1).
        split; try lra.
        inversion col as [[txd tyd]].
        rewrite txd, tyd, cd1.
        fieldrewrite (- -1 * (1 * Nx s)) (Nx s).
        fieldrewrite (-1 * (1 * - Ny s)) (Ny s).
        reflexivity.
      + exists 1.
        split; try lra.
        inversion col as [[txd tyd]].
        rewrite txd, tyd, cdn1.
        fieldrewrite (- (1) * (-1 * Nx s)) (Nx s).
        fieldrewrite (1 * (-1 * - Ny s)) (Ny s).
        reflexivity.
    }

    (* put ex_derives here *)
    assert (locally s (fun s:R => continuous Tx s)) as lcTx. {
      specialize ex_derive_Tx as ed;
        clear - ed;
        ebff;
        apply ex_derive_continuous in rest; assumption. }

    assert (locally s (fun s:R => continuous Ty s)) as lcTy. {
      specialize ex_derive_Ty as ed;
        clear - ed;
        ebff;
        apply ex_derive_continuous in rest; assumption. }

    assert (locally s (fun s:R => continuous Nx s)) as lcNx. {
      specialize ex_derive_Nx as ed;
        clear - ed;
        ebff;
        apply ex_derive_continuous in rest; assumption. }

    assert (locally s (fun s:R => continuous Ny s)) as lcNy. {
      specialize ex_derive_Ny as ed;
        clear - ed;
        ebff;
        apply ex_derive_continuous in rest; assumption. }

    assert (locally s (fun s:R => continuous (fun r:R => - Nx r * Ty r + Ny r * Tx r) s)) as flc. {
      fllcb lcTx lcTy.
      flcb zltrmpr lcNx.
      flcb zltne lcNy.
      csb zltne0.
      sib y sb.
      clear - restp restq restr restr0.
      
      specialize (continuous_opp Nx y restr) as oNx.
      specialize (continuous_mult _ _ _ oNx restq) as term1.
      specialize (continuous_mult _ _ _ restr0 restp) as term2.
      specialize (continuous_plus _ _ _ term1 term2) as final.
      simpl in final.
      assumption. }

    assert (locally s (fun s => exists c, (c = 1 \/ c = -1) /\
                                          - Nx s * Ty s + Ny s * Tx s = c)) as les. {
      clear - col2.
      specialize unitvelocity as uv.
      fllcb col2 uv.
      csb zltrmpr.
      sib y sb.
      destruct restp as [c [cd Nd]].
      exists c.
      split; try assumption.
      inversion Nd as [[Ndx Ndy]].
      rewrite Ndx, Ndy.
      setl (c * ((Tx y)² + (Ty y)²)).
      rewrite restq.
      lra. }

    assert (exists c, (c = 1 \/ c = -1) /\
                      locally s (fun s => - Nx s * Ty s + Ny s * Tx s = c)) as els. {
      clear - les flc.
      fllcb flc les.
      destruct (restq s (ball_center _ _)) as [c [cd NTeqc]].
      exists c.
      split; try assumption.
      csb zltrmpr.
      generalize restp restq.
      sib y sb.
      destruct restq as [cy [cyd NTy]].
      clear restp.
      intros cs les.

      set (f := (fun y => - Nx y * Ty y + Ny y * Tx y)) in *.
      assert (is_lim f s (f s)) as ilfs. {
        apply is_lim_continuity.
        apply continuous_pt_impl_continuity_pt.
        apply cs.
        apply ball_center. }
      assert (is_lim f y (f y)) as ilfy. {
        apply is_lim_continuity.
        apply continuous_pt_impl_continuity_pt.
        apply cs.
        assumption. }

      destruct cd; destruct cyd; subst; auto;
        exfalso.
      + change (f s = 1) in NTeqc.
        change (f y = -1) in NTy.
        change (forall y : R_UniformSpace,
                   ball s epsq y -> exists c : R, (c = 1 \/ c = -1) /\ f y = c) in les.
        simpl in *.
        
        destruct (Rlt_dec s y).
        ++ assert (forall x : R, Rbar_lt s x -> Rbar_lt x y -> continuity_pt f x) as cp. {
             intros x sltx xlty.
             apply continuous_pt_impl_continuity_pt.
             apply cs.
             simpl in *.
             clear - xlty sltx a.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_right in *; try lra. }

           assert (Rbar_lt (f y) 0 /\ Rbar_lt 0 (f s)) as zr. {
             rewrite NTeqc, NTy.
             simpl.
             lra. }

           specialize (IVT_Rbar_decr f s y (f s) (f y) 0 ilfs ilfy cp r zr)
             as [z [sltz [zlty fz0]]].
           simpl in *.
           assert (ball s epsq z) as bsz. {
             clear - sltz zlty b.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_right in *; try lra. }

           specialize (les z bsz) as [c [cd fzc]].
           rewrite fz0 in fzc.
           lra.

        ++ apply Rnot_lt_le in n.
           destruct n as [lt |eq].
           2 : { subst; lra. }
           assert (forall x : R, Rbar_lt y x -> Rbar_lt x s -> continuity_pt f x) as cp. {
             intros x sltx xlty.
             apply continuous_pt_impl_continuity_pt.
             apply cs.
             simpl in *.
             clear - xlty sltx a.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_left in *; try lra. }

           assert (Rbar_lt (f y) 0 /\ Rbar_lt 0 (f s)) as zr. {
             rewrite NTeqc, NTy.
             simpl.
             lra. }

           specialize (IVT_Rbar_incr f y s (f y) (f s) 0 ilfy ilfs cp lt zr)
             as [z [sltz [zlty fz0]]].
           simpl in *.
           assert (ball s epsq z) as bsz. {
             clear - sltz zlty b.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_left in *; try lra. }

           specialize (les z bsz) as [c [cd fzc]].
           rewrite fz0 in fzc.
           lra.   

      + change (f s = -1) in NTeqc.
        change (f y = 1) in NTy.
        change (forall y : R_UniformSpace,
                   ball s epsq y -> exists c : R, (c = 1 \/ c = -1) /\ f y = c) in les.
        simpl in *.
        
        destruct (Rlt_dec s y).
        ++   assert (forall x : R, Rbar_lt s x -> Rbar_lt x y -> continuity_pt f x) as cp. {
             intros x sltx xlty.
             apply continuous_pt_impl_continuity_pt.
             apply cs.
             simpl in *.
             clear - xlty sltx a.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_right in *; try lra. }

           assert (Rbar_lt (f s) 0 /\ Rbar_lt 0 (f y)) as zr. {
             rewrite NTeqc, NTy.
             simpl.
             lra. }

           specialize (IVT_Rbar_incr f s y (f s) (f y) 0 ilfs ilfy cp r zr)
             as [z [sltz [zlty fz0]]].
           simpl in *.
           assert (ball s epsq z) as bsz. {
             clear - sltz zlty b.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_right in *; try lra. }

           specialize (les z bsz) as [c [cd fzc]].
           rewrite fz0 in fzc.
           lra.

        ++ apply Rnot_lt_le in n.
           destruct n as [lt |eq].
           2 : { subst; lra. }

           assert (forall x : R, Rbar_lt y x -> Rbar_lt x s -> continuity_pt f x) as cp. {
             intros x sltx xlty.
             apply continuous_pt_impl_continuity_pt.
             apply cs.
             simpl in *.
             clear - xlty sltx a.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_left in *; try lra. }

           assert (Rbar_lt (f s) 0 /\ Rbar_lt 0 (f y)) as zr. {
             rewrite NTeqc, NTy.
             simpl.
             lra. }

           specialize (IVT_Rbar_decr f y s (f y) (f s) 0 ilfy ilfs cp lt zr)
             as [z [sltz [zlty fz0]]].
           simpl in *.
           assert (ball s epsq z) as bsz. {
             clear - sltz zlty b.
             unfold ball in *.
             simpl in *.
             unfold AbsRing_ball, abs, minus, plus, opp in *.
             simpl in *.
             rewrite Rabs_left in *; try lra. }

           specialize (les z bsz) as [c [cd fzc]].
           rewrite fz0 in fzc.
           lra. }

    clear - els col2.
    specialize unitvelocity as uv.
    destruct els as [c [cdef ls]].
    exists c.
    split; try assumption.

    fllcb ls uv.
    flcb zltrmpr col2.
    rename restq into t21.
    rename restp into cs.
    rename restr into Nd.
    csb zltne.
    sib y sb.
    destruct Nd as [alpha [cd2 Nd]].
    destruct cdef; destruct cd2; subst; auto;
      exfalso.
    + inversion Nd as [[Nxd Nyd]].
      rewrite Nxd, Nyd in *.
      assert (- ((Tx y)² + (Ty y)²) = 1) as t12. {
        unfold Rsqr.
        lrag t21. }
      rewrite t21 in t12.
      lra.
    + inversion Nd as [[Nxd Nyd]].
      rewrite Nxd, Nyd in *.
      assert (- ((Tx y)² + (Ty y)²) = 1) as t12. {
        unfold Rsqr.
        lrag t21. }
      rewrite t21 in t12.
      lra.
  Qed.
  
  Lemma dN_T_colinear :
    locally s (fun s => exists M, (Derive Nx s, Derive Ny s) =
                                  (M * Tx s, M * Ty s)).
  Proof.
    specialize (unitvelocity) as uv.
    specialize (kgt0) as kgt0.
    specialize vad as [c [cd vadl]].
    specialize accel_nonzero as anz.
    specialize TperpN as TpN.
    specialize dNperpN as dNpN.

    assert (locally s (fun s => Nx s = (fun s => - c * Ty s) s)) as nxd0. {
      clear - vadl.
      ebff.
      inversion rest as [[nxd nyd]].
      reflexivity. }
    assert (locally s (fun s => Ny s = (fun s => c * Tx s) s)) as nyd0. {
      clear - vadl.
      ebff.
      inversion rest as [[nxd nyd]].
      reflexivity. }

    fllcb uv kgt0.
    flcb zltrmpr vadl.
    flcb zltne anz.
    flcb zltne0 TpN.
    flcb zltne1 dNpN.
    flcb zltne2 nxd0.
    flcb zltne3 nyd0.
    csb zltne4.

  change (forall y : R_UniformSpace, ball s epsr4 y -> (fun y => Ny y = c * Tx y) y) in restr4.
  assert (locally y (fun s => Ny s = (fun s => c * Tx s) s)) as nxd. {
    specialize (b5 y sb).
    clear - b5 restr4.
    simpl.
    reseat_locally restr4. }
    
  change (forall y : R_UniformSpace, ball s epsr3 y -> (fun y => Nx y = - c * Ty y) y) in restr3.
  assert (locally y (fun s => Nx s = (fun s => - c * Ty s) s)) as nyd. {
    specialize (a5 y sb).
    specialize (b4 y a5).
    clear - b4 restr3.
    simpl.
    reseat_locally restr3. }

    sib y sb.
  clear a b a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5
        zltne zltne0 zltne1 zltne2 zltne3 zltne4
        restr3 restr4 zltrmpr sb epsp epsq epsr
        epsr0 epsr1 epsr2 epsr3 epsr4.

  simpl in *.
  rename restp into uv.
  rename restq into kgt0.
  rename restr into vad.
  rename restr0 into accel_nonzero.
  rename restr1 into TNeq0.
  rename restr2 into dNNeq0.
  rename y into s.
  assert ((Tx s)² + (Ty s)² <> 0) as Tne0. {
    intros.
    intro ne0.
    rewrite ne0 in uv.
    lra. }
  assert (~ (Tx s = 0 /\ Ty s = 0)) as Tne02. {
    intros.
    specialize (Tne0).
    apply nzm in Tne0.
    assumption. }
  assert (~ (Nx s = 0 /\ Ny s = 0)) as Nne0. {
    intros.
    specialize (Tne0).
    apply nzm.
    unfold Nx, Ny.
    intro N2eq0.
    assert ((Derive Tx s)² + (Derive Ty s)² = 0) as N2eq02. {
      apply (Rmult_eq_reg_l (/ κ s)²).
      rewrite Rmult_plus_distr_l.
      repeat rewrite <- Rsqr_mult.
      arn.
      assumption.
      apply Rmult_integral_contrapositive_currified;
        apply Rinv_neq_0_compat;
        intro kieq0;
        lra. }
    generalize N2eq02.
    apply accel_nonzero. }

  assert (~ (Derive Nx s = 0 /\ Derive Ny s = 0)) as dNne0. {
    apply nzm.
    
    rewrite (Derive_ext_loc _ _ _ nxd).
    rewrite (Derive_ext_loc _ _ _ nyd).

    assert (forall s, Derive (fun s0 : R => - c * Ty s0) s = - c * Derive Ty s) as styd. {
      intros.
      rewrite Derive_scal.
      reflexivity. }

    assert (forall s, Derive (fun s0 : R => c * Tx s0) s = c * Derive Tx s) as stxd. {
      intros.
      rewrite Derive_scal.
      reflexivity. }
    
    rewrite styd, stxd.
    repeat rewrite Rsqr_mult.
    rewrite <- Rsqr_neg.
    fieldrewrite (c² * (Derive Ty s)² + c² * (Derive Tx s)²)
                 (c² * ((Derive Ty s)² + (Derive Tx s)²)).
    
    assert (c² = 1) as c21. {
      destruct cd; subst; unfold Rsqr; field. }
    rewrite c21.
    arn.
    rewrite Rplus_comm.
    apply accel_nonzero. }

  apply (dot_prod_colinear
           _ _ _ _ _ _ Tne02 dNne0 Nne0 TNeq0 dNNeq0).
  Qed.

  Lemma dT_dot_N_eq_k :
      locally s (fun s => dot_prod (Derive Tx s, Derive Ty s)  (Nx s, Ny s) = κ s).
  Proof.
    intros.
    specialize (normNeq1) as n21.
    specialize (kgt0) as nkgt0.
    specialize (kgt0) as ikgt0.

    fllcb nkgt0 ikgt0.
    flcb zltrmpr n21.
    csb zltne.
    sib y sb.

    rename y into s.
    rename restr into n21.
    rename restp into ikgt0.
    rename restq into nkgt0.
    apply Rinv_0_lt_compat in ikgt0.
    apply (Rmult_eq_reg_l (/ κ s)); try lra.
    setr 1; try lra.
    rewrite <- dot_prod_scal_l.
    assumption.
  Qed.


  Lemma dN_eq_nkT :
      locally s (fun s => (Derive Nx s, Derive Ny s) = (- κ s * Tx s, - κ s * Ty s)).
  Proof.
    specialize ex_derive_Tx as edTx.
    specialize ex_derive_Ty as edTy.
    specialize ex_derive_Nx as edNx.
    specialize ex_derive_Ny as edNy.
    
    assert (locally s (fun s =>
                         is_derive (fun s => dot_prod (Tx s, Ty s) (Nx s, Ny s)) s zero)) as d0. {
      specialize TperpN as tn0.
      unfold locally in tn0.
      destruct tn0 as [eps tn0].
      destruct eps as [e zlte].
      simpl in *.
      csb zlte.
      apply (is_derive_ext_loc (fun s => 0)).
      symmetry in tn0.
      change (forall y : R, ball s e y ->
                            (fun y => 0 = dot_prod (Tx y, Ty y) (Nx y, Ny y)) y) in tn0.
      simpl.
      reseat_locally tn0.
      apply is_derive_const. }
    specialize (unitvelocity) as t1.
    specialize dN_T_colinear as dNTc.
    specialize dT_dot_N_eq_k as dTNk.

    fllcb edTx edTy.
    flcb zltrmpr edNx.
    flcb zltne edNy.
    flcb zltne0 d0.
    flcb zltne1 t1.
    flcb zltne2 dNTc.
    flcb zltne3 dTNk.
    csb zltne4.

    rename restp into exdTx.
    rename restq into exdTy.
    rename restr into exdNx.
    rename restr0 into exdNy.
    rename restr1 into TN0.
    rename restr2 into T21.
    rename restr3 into dNeqMT.
    rename restr4 into dTNk.

    assert (exists M : R, (Derive Nx y, Derive Ny y) = (M * Tx y, M * Ty y)) as [alpha dntc]. {
      sib y sb; assumption. }

    (* T'.N=k *
       N'.T=M need
       T.N=0 *
       (T.N)' = T'.N + T.N' = k + M *)
    rename y into s.
    assert (dot_prod (Derive Nx s, Derive Ny s) (Tx s, Ty s) = alpha) as idTN. {
      rewrite dntc.
      unfold dot_prod.
      simpl.
      setl (alpha * ((Tx s)² + (Ty s)²)).
      rewrite T21; try field.
      sib s sb.
      assumption. }

    rewrite dot_prod_comm in idTN.

    assert (locally s (fun s => ex_derive Tx s)) as exdTxs. {
      revert exdTx.
      sib s sb.
      intro exdTx2.
      simpl in *.
      
      change (forall y:R, ball p.s epsp y ->
                          (fun s0 : R => ex_derive Tx s0) y) in exdTx2.
      clear - exdTx2 a.
      reseat_locally exdTx2. }
    
    assert (locally s (fun s => ex_derive Ty s)) as exdTys. {
      revert exdTy.
      sib s sb.
      intro exdTy2.
      simpl in *.
      
      change (forall y:R, ball p.s epsq y ->
                          (fun s0 : R => ex_derive Ty s0) y) in exdTy2.
      clear - exdTy2 b.
      reseat_locally exdTy2. }
    
    assert (locally s (fun s => ex_derive Nx s)) as exdNxs. {
      revert exdNx.
      sib s sb.
      intro exdNx2.
      simpl in *.
      
      change (forall y:R, ball p.s epsr y ->
                          (fun s0 : R => ex_derive Nx s0) y) in exdNx2.
      clear - exdNx2 b0.
      reseat_locally exdNx2. }
    
    assert (locally s (fun s => ex_derive Ny s)) as exdNys. {
      revert exdNy.
      sib s sb.
      intro exdNy2.
      simpl in *.

      change (forall y:R, ball p.s epsr0 y ->
                          (fun s0 : R => ex_derive Ny s0) y) in exdNy2.
      clear - exdNy2 b1.
      reseat_locally exdNy2. }
    
    assert (is_derive (fun s => dot_prod (Tx s, Ty s) (Nx s, Ny s)) s (κ s + alpha)) as dak. {
      rewrite <- dTNk, <- idTN.
      2 : { sib s sb. assumption. }
      apply is_deriv_dot_prod.
      apply locally_singleton in exdTxs.
      apply Derive_correct; assumption.
      apply locally_singleton in exdTys.
      apply Derive_correct; assumption.
      apply locally_singleton in exdNxs.
      apply Derive_correct; assumption.
      apply locally_singleton in exdNys.
      apply Derive_correct; assumption.  }
    apply is_derive_unique in dak.
    sib s sb.
    apply is_derive_unique in TN0.
    rewrite TN0 in dak.
    unfold zero in dak.
    simpl in dak.
    symmetry in dak.
    apply Rplus_opp_r_uniq in dak.

    rewrite dak in dntc.
    assumption.
  Qed.

  (* end hide *)

  Lemma dNx_eq_nkTx : locally  s (fun s => Derive Nx s = - κ s * Tx s).
  Proof.
    intros.
    specialize (dN_eq_nkT) as tpl.
    ebff.
    inversion rest; try reflexivity.
  Qed.

  Lemma dNy_eq_nkTy : locally s (fun s => Derive Ny s = - κ s * Ty s).
  Proof.
    specialize (dN_eq_nkT) as tpl.
    ebff.
    inversion rest; try reflexivity.
  Qed.

End FrenetSerret2D.
