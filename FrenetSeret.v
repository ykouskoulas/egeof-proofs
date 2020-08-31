(* begin hide *)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import FunctionalExtensionality.
Require Import Lra.
Require Import util.

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

Module Type Pt.
  Parameter s : R.
End Pt.

Module Type Path2D (*Import pt :Pt*).
  (* position x and y components *)
  Parameter (Fx Fy : R -> R). 
  Parameter ex_derive_Fx : forall s, ex_derive Fx s.
  Parameter ex_derive_Fy : forall s, ex_derive Fy s.

  (* velocity components *)
  Definition Tx := Derive Fx. 
  Definition Ty := Derive Fy.
  Parameter ex_derive_Tx : forall s, ex_derive Tx s.
  Parameter ex_derive_Ty : forall s, ex_derive Ty s.
  (* The path (Fx s, Fy s) is parameterized by distance; velocity is 1 *)
  Parameter unitvelocity : forall s, (Tx s)² + (Ty s)² = 1.
  (* curvature is always defined -- no straight motion *)
  Parameter accel_nonzero : forall s, ((Derive Tx s)² + (Derive Ty s)²) <> 0.

  (* accel direction components *)
  Definition κ s := sqrt ((Derive Tx s)² + (Derive Ty s)²).
  Definition Nx s := / κ s * Derive Tx s. 
  Definition Ny s := / κ s * Derive Ty s.
  Parameter ex_derive_Nx : forall s, ex_derive Nx s.
  Parameter ex_derive_Ny : forall s, ex_derive Ny s.
End Path2D.

Module FrenetSeret2D (*Import pt : Pt*) (Import p : Path2D (*pt*)).
  (* N is a unit vector showing accel direction *)
  Lemma unitN : forall s, (Nx s)² + (Ny s)² = 1.
  Proof.
    intros.
    unfold Nx, Ny, κ.
    repeat rewrite Rsqr_mult.
    assert (0 <= (Derive Tx s)² + (Derive Ty s)²) as ge0. {
      apply Rplus_le_le_0_compat; apply Rle_0_sqr. }

    repeat rewrite Rsqr_inv.
    2 : {
      intro DTx2DTy2eq0.
      apply sqrt_eq_0 in DTx2DTy2eq0; try assumption.
      eapply accel_nonzero; eassumption. }
    rewrite Rsqr_sqrt; try assumption.
    setl (((Derive Tx s)² + (Derive Ty s)²)/((Derive Tx s)² + (Derive Ty s)²)).
    change ((Derive Tx s)² + (Derive Ty s)² <> 0).
    apply accel_nonzero.
    field.
    apply accel_nonzero.
  Qed.
  
  Lemma kgt0 : forall s, 0 < κ s.
  Proof.
    intros.
    unfold κ.
    specialize (accel_nonzero s) as ne0.
    specialize (Rle_0_sqr (Derive Ty s)) as DTyge0.
    specialize (Rle_0_sqr (Derive Tx s)) as DTxge0.
    specialize (Rplus_le_le_0_compat _ _ DTxge0 DTyge0) as zle.
    destruct zle as [zlt |zeq]; try lra.
    apply sqrt_lt_R0.
    assumption.
  Qed.

  (* Lemma Tx_def : Tx = (fun v => cos (atan2 (Ty v) (Tx v))). *)
  (* Proof. *)
  (*   apply functional_extensionality. *)
  (*   intros. *)
  (*   rename x into s. *)
  (*   change (Tx s = (fun v => cos ((fun u => atan2 (Ty u) (Tx u)) v)) s). *)
  (* *)
  (*   set (g := (fun u : R => atan2 (Ty u) (Tx u))) in *. *)
  (*   specialize (unitvelocity s) as uv. *)
  (*   assert ((Tx s)² + (Ty s)² <> 0) as n0. { *)
  (*     intros. *)
  (*     intro e0. *)
  (*     rewrite e0 in uv. *)
  (*     lra. } *)
  (*   apply nzm in n0. *)
  (*   specialize (atan2_bound _ _ n0) as pr. *)
  (*   change (-PI < g s <= PI) in pr. *)
  (*   assert (0 < 1). lra. *)
  (*   specialize (atan2_left_inv _ 1 pr ltac:(lra)) as a2a2. *)
  (*   unfold g in a2a2 at 3. *)
  (*   unfold atan2 in a2a2. *)
  (*   destruct pre_atan2 as [a [abnd [ayd axd]]]. *)
  (*   destruct pre_atan2 as [b [bbnd [byd bxd]]]. *)
  (*   rewrite Rplus_comm in uv. *)
  (*   rewrite uv in *. *)
  (*   autorewrite with null in *. *)
  (*   rewrite sqrt_1 in *. *)
  (*   autorewrite with null in *. *)
  (*   subst. *)
  (*   rewrite <- bxd in axd. *)
  (*   rewrite <- byd in ayd. *)
  (*   clear abnd bbnd byd bxd b H. *)
  (*   symmetry. *)
  (*   assumption. *)
  (* Qed. *)
  (* *)
  (* Lemma Ty_def : Ty = (fun v => sin (atan2 (Ty v) (Tx v))). *)
  (* Proof. *)
  (*   apply functional_extensionality. *)
  (*   intros. *)
  (*   rename x into s. *)
  (*   change (Ty s = (fun v => sin ((fun u => atan2 (Ty u) (Tx u)) v)) s). *)
  (* *)
  (*   set (g := (fun u : R => atan2 (Ty u) (Tx u))) in *. *)
  (*   specialize (unitvelocity s) as uv. *)
  (*   assert ((Tx s)² + (Ty s)² <> 0) as n0. { *)
  (*     intros. *)
  (*     intro e0. *)
  (*     rewrite e0 in uv. *)
  (*     lra. } *)
  (*   apply nzm in n0. *)
  (*   specialize (atan2_bound _ _ n0) as pr. *)
  (*   change (-PI < g s <= PI) in pr. *)
  (*   assert (0 < 1). lra. *)
  (*   specialize (atan2_left_inv _ 1 pr ltac:(lra)) as a2a2. *)
  (*   unfold g in a2a2 at 3. *)
  (*   unfold atan2 in a2a2. *)
  (*   destruct pre_atan2 as [a [abnd [ayd axd]]]. *)
  (*   destruct pre_atan2 as [b [bbnd [byd bxd]]]. *)
  (*   rewrite Rplus_comm in uv. *)
  (*   rewrite uv in *. *)
  (*   autorewrite with null in *. *)
  (*   rewrite sqrt_1 in *. *)
  (*   autorewrite with null in *. *)
  (*   subst. *)
  (*   rewrite <- bxd in axd. *)
  (*   rewrite <- byd in ayd. *)
  (*   clear abnd bbnd byd bxd b H. *)
  (*   symmetry. *)
  (*   assumption. *)
  (* Qed. *)
(* begin hide *)  
  (* velocity magnitude = 1 *)
  Lemma normTeq1 : forall s, dot_prod (Tx s, Ty s) (Tx s, Ty s) = 1.
  Proof.
    unfold dot_prod, fst, snd.
    intros.
    apply unitvelocity.
  Qed.

  (* N is a unit vector showing accel direction *)
  Lemma normNeq1 : forall s, dot_prod (Nx s, Ny s) (Nx s, Ny s) = 1.
  Proof.
    unfold dot_prod, fst, snd.
    intros.
    apply unitN.
  Qed.

  (* end hide *)
  Lemma dTx_eq_kNx: forall s, Derive Tx s = κ s * Nx s.
  Proof.
    intros.
    unfold Nx.
    field.
    specialize (kgt0 s) as kgt0.
    lra.
  Qed.
    
  Lemma dTy_eq_kNy: forall s, Derive Ty s = κ s * Ny s.
  Proof.
    intros.
    unfold Ny.
    field.
    specialize (kgt0 s) as kgt0.
    lra.
  Qed.

(* begin hide *)  
  Lemma dTperpT : forall s, dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) = 0.
  Proof.
    intros.
    assert (dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) =
            / 2 * (dot_prod (Derive Tx s, Derive Ty s) (Tx s, Ty s) +
                   dot_prod (Tx s, Ty s) (Derive Tx s, Derive Ty s))) as id. {
      unfold dot_prod, fst, snd.
      field. }
    rewrite id; clear id.
    unfold dot_prod, fst, snd.
    setl (/ 2 * ((Derive Tx s * Tx s + Tx s * Derive Tx s) +
                 (Derive Ty s * Ty s + Ty s * Derive Ty s))).
    assert (plus (mult (Derive Tx s) (Tx s)) (mult (Tx s) (Derive Tx s)) =
            Derive Tx s * Tx s + Tx s * Derive Tx s) as idx; try reflexivity.
    assert (plus (mult (Derive Ty s) (Ty s)) (mult (Ty s) (Derive Ty s)) =
            Derive Ty s * Ty s + Ty s * Derive Ty s) as idy; try reflexivity.
    rewrite <- idx, <- idy. clear idx idy.

    specialize (ex_derive_Tx s) as DTxd; apply Derive_correct in DTxd.
    specialize (ex_derive_Ty s) as DTyd; apply Derive_correct in DTyd.
    assert (forall (p q:R), mult p q = mult q p) as Rmult_comm_mult. {
      unfold mult.
      simpl.
      apply Rmult_comm. }
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
    assert ((fun s : R => plus (Tx s * Tx s) (Ty s * Ty s)) =
            (fun s => 1)) as T2. {
      apply functional_extensionality.
      intros.
      specialize (normTeq1 x) as nTe1.
      unfold dot_prod, fst, snd, plus in *.
      simpl in *.
      assumption. }
    unfold plus in *.
    simpl in *.
    rewrite T2.
    specialize (is_derive_const 1 s) as idc.
    simpl in idc.
    apply is_derive_unique in idc.
    rewrite idc.
    unfold zero.
    simpl.
    field.
  Qed.


  Lemma dNperpN : forall s,
      dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) = 0.
  Proof.
    intros.
    assert (dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) =
            / 2 * (dot_prod (Derive Nx s, Derive Ny s) (Nx s, Ny s) +
                   dot_prod (Nx s, Ny s) (Derive Nx s, Derive Ny s))) as id. {
      unfold dot_prod, fst, snd.
      field. }
    rewrite id; clear id.
    unfold dot_prod, fst, snd.
    setl (/ 2 * ((Derive Nx s * Nx s + Nx s * Derive Nx s) +
                 (Derive Ny s * Ny s + Ny s * Derive Ny s))).
    assert (plus (mult (Derive Nx s) (Nx s)) (mult (Nx s) (Derive Nx s)) =
            Derive Nx s * Nx s + Nx s * Derive Nx s) as idx; try reflexivity.
    assert (plus (mult (Derive Ny s) (Ny s)) (mult (Ny s) (Derive Ny s)) =
            Derive Ny s * Ny s + Ny s * Derive Ny s) as idy; try reflexivity.
    rewrite <- idx, <- idy. clear idx idy.

    specialize (ex_derive_Nx s) as DNxd; apply Derive_correct in DNxd.
    specialize (ex_derive_Ny s) as DNyd; apply Derive_correct in DNyd.
    assert (forall (p q:R), mult p q = mult q p) as Rmult_comm_mult. {
      unfold mult.
      simpl.
      apply Rmult_comm. }
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
    assert ((fun s : R => plus (Nx s * Nx s) (Ny s * Ny s)) =
            (fun s => 1)) as T2. {
      apply functional_extensionality.
      intros.
      specialize (normNeq1 x) as nTe1.
      unfold dot_prod, fst, snd, plus in *.
      simpl in *.
      assumption. }
    unfold plus in *.
    simpl in *.
    rewrite T2.
    specialize (is_derive_const 1 s) as idc.
    simpl in idc.
    apply is_derive_unique in idc.
    rewrite idc.
    unfold zero.
    simpl.
    field.
  Qed.

  Lemma TperpN : forall s,
      dot_prod (Tx s, Ty s) (Nx s, Ny s) = 0.
  Proof.
    intros.
    rewrite dot_prod_comm.
    unfold Nx, Ny.
    rewrite dot_prod_scal_l.
    rewrite dTperpT.
    lra.
  Qed.
  
  Lemma vad : 
    exists c, ((c=1\/c=-1) /\ forall s, (Nx s, Ny s) = (-c*Ty s, c*Tx s)).
  Proof.
    intros.
    assert (forall s, dot_prod (Nx s, Ny s) (-Ny s, Nx s) = 0) as NdotperpN. {
      intros.
      unfold dot_prod, fst, snd.
      field. }
    specialize TperpN as TperpN.
    setoid_rewrite dot_prod_comm in NdotperpN.
    assert (forall s, (Nx s)² + (Ny s)² <> 0) as Nne0. {
      intros.
      rewrite unitN.
      discrR. }
    assert (forall s : R, (- Ny s)² + (Nx s)² <> 0) as perpNne0. {
      intros.
      rewrite Rplus_comm.
      rewrite  <- Rsqr_neg.
      apply Nne0. }
    assert (forall s, (Tx s)² + (Ty s)² <> 0) as Tne0. {
      intros.
      rewrite unitvelocity.
      discrR. }
    assert (forall s, exists c : R, (Tx s, Ty s) = (c * (- Ny s), c * Nx s)) as col. {
      intros.
      eapply dot_prod_colinear.
      apply nzm; eauto.
      apply nzm; eauto.
      apply nzm, (Nne0 s).
      apply NdotperpN.
      apply TperpN. }
    assert (forall s : R, exists c : R, (c = 1 \/ c = -1) /\
                                        (Nx s, Ny s) = (- c * Ty s, c * Tx s)) as col2. {
      intros.
      specialize (col s) as [c col].
      assert (c = 1 \/ c = -1) as cdef. {
        specialize (unitvelocity s) as uv.
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
  Admitted.

  
  Lemma dN_T_colinear : forall s:R, 
        exists c : R, (Derive Nx s, Derive Ny s) = (c * Tx s, c * Ty s).
  Proof.
    intros.
    specialize (unitvelocity) as uv.
    assert ((Tx s)² + (Ty s)² <> 0) as Tne0. {
      intros.
      specialize (uv s).
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
          specialize (kgt0 s) as kgt0;
          lra. }
      generalize N2eq02.
      apply accel_nonzero. }
    assert (~ (Derive Nx s = 0 /\ Derive Ny s = 0)) as dNne0. {
      apply nzm.
      specialize vad as [c [cd vad]].
      assert (Nx = (fun s => - c * Ty s)) as nxd. {
        apply functional_extensionality.
        intros.
        specialize (vad x).
        inversion vad as [[nxd nyd]].
        reflexivity. }
      assert (Ny = (fun s => c * Tx s)) as nyd. {
        apply functional_extensionality.
        intros.
        specialize (vad x).
        inversion vad as [[nxd2 nyd]].
        reflexivity. }
      rewrite nxd, nyd.
      assert (forall s, Derive (fun s0 : R => - c * Ty s0) s = - c * Derive Ty s) as styd. {
        intros.
        assert (is_derive (fun s1 : R => - c * Ty s1) s0 (-c * Derive Ty s0)) as styd2. {
          auto_derive.
          apply ex_derive_Ty.
          change (- c * (1 * Derive Ty s0) = - c * Derive Ty s0).
          field. }
        apply is_derive_unique.
        assumption. }

      assert (forall s, Derive (fun s0 : R => c * Tx s0) s = c * Derive Tx s) as stxd. {
        intros.
        assert (is_derive (fun s1 : R => c * Tx s1) s0 (c * Derive Tx s0)) as stxd2. {
          auto_derive.
          apply ex_derive_Tx.
          change (c * (1 * Derive Tx s0) = c * Derive Tx s0).
          field. }
        apply is_derive_unique.
        assumption. }
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

    apply (dot_prod_colinear _ _ _ _ _ _ Tne02 dNne0 Nne0
                             (TperpN s) (dNperpN s)).
  Qed.

  
  Lemma dN_dot_T_eq_c : forall s:R, 
        exists c : R, dot_prod (Derive Nx s, Derive Ny s)  (Tx s, Ty s) = c.
  Proof.
    intros.
    specialize (dN_T_colinear s) as [c dntc].
    exists c.
    rewrite dntc.
    unfold dot_prod.
    simpl.
    specialize (unitvelocity s) as t1.
    setl (c * ((Tx s)² + (Ty s)²)).
    rewrite t1.
    lra.
  Qed.

  Lemma dT_dot_N_eq_k : forall s:R, 
      dot_prod (Derive Tx s, Derive Ty s)  (Nx s, Ny s) = κ s.
  Proof.
    intros.
    specialize (normNeq1 s) as n21.
    specialize (kgt0 s) as nkgt0.
    specialize (kgt0 s) as ikgt0.
    apply Rinv_0_lt_compat in ikgt0.
    apply (Rmult_eq_reg_l (/ κ s)); try lra.
    setr 1; try lra.
    rewrite <- dot_prod_scal_l.
    assumption.
  Qed.

  
  Lemma dN_eq_nkT : forall s:R, 
      (Derive Nx s, Derive Ny s) = (- κ s * Tx s, - κ s * Ty s).
  Proof.
    intros.
    assert (is_derive (fun s => dot_prod (Tx s, Ty s) (Nx s, Ny s)) s zero) as d0. {
      apply (is_derive_ext (fun s => 0)).
      simpl.
      intros.
      symmetry.
      apply TperpN.
      apply is_derive_const. }

    specialize (dN_T_colinear s) as [alpha dntc].

    assert (dot_prod (Derive Nx s, Derive Ny s) (Tx s, Ty s) = alpha) as idTN. {
      rewrite dntc.
      unfold dot_prod.
      simpl.
      specialize (unitvelocity s) as t1.
      setl (alpha * ((Tx s)² + (Ty s)²)).
      rewrite t1.
      lra. }

    rewrite dot_prod_comm in idTN.
    specialize (dT_dot_N_eq_k s) as dTN.

    assert (is_derive (fun s => dot_prod (Tx s, Ty s) (Nx s, Ny s)) s (κ s + alpha)) as dak. {
      rewrite <- dTN, <- idTN.
      apply is_deriv_dot_prod.
      apply Derive_correct, ex_derive_Tx.
      apply Derive_correct, ex_derive_Ty.
      apply Derive_correct.
      apply ex_derive_Nx.
      apply Derive_correct.
      apply ex_derive_Ny. }
    apply is_derive_unique in dak.
    apply is_derive_unique in d0.
    rewrite d0 in dak.
    unfold zero in dak.
    simpl in dak.
    symmetry in dak.
    apply Rplus_opp_r_uniq in dak.

    rewrite dak in dntc.
    assumption.
  Qed.

  (* end hide *)

  Lemma dNx_eq_nkTx : forall s:R, Derive Nx s = - κ s * Tx s.
  Proof.
    intros.
    specialize (dN_eq_nkT s) as tpl.
    inversion tpl; try reflexivity.
  Qed.

  Lemma dNy_eq_nkTy : forall s:R, Derive Ny s = - κ s * Ty s.
  Proof.
    intros.
    specialize (dN_eq_nkT s) as tpl.
    inversion tpl; try reflexivity.
  Qed.

End FrenetSeret2D.
