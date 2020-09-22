
(* begin hide *)

Require Import Reals.
Require Import Ranalysis5.
Require Import Coquelicot.Coquelicot.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Lia.
Require Import Lra.
Require Import util.
Require Import atan2.

Require Import Sorting.
Require Import Coq.Structures.Orders.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import FrenetSerret.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Local Coercion is_true : bool >-> Sortclass.

Module ROrd <: TotalTransitiveLeBool.
  Definition t := R.
  Definition leb x y :=
    match total_order_T x y with
    | inleft _ => true
    | _ => false
    end.
  
  Theorem leb_total : forall (a1 a2 :R), leb a1 a2\/ leb a2 a1.
  Proof.
    intros.
    unfold leb.
    destruct (total_order_T); [destruct s|]; auto.
    destruct (total_order_T); [destruct s|]; auto.
    exfalso.
    lra.
  Qed.

  
  Theorem leb_trans : Transitive leb.
    unfold Transitive.
    intros.
    unfold leb in *.
    repeat (destruct total_order_T; [destruct s|]; auto); try lra.
  Qed.

End ROrd.

Module Import RSort := Sort ROrd.

(* end hide *)

(** "Good fences make good neighbors: designing a formally verified,
predictive geofence"

Y. Kouskoulas, R. Wu, J. Brule, D. Genin, A. Schmidt, TJ Machado

Maintaining control of AI-controlled mobile platforms during
operations and testing is an important safety requirement. This is a
problem for fast moving aerial vehicles, such as fixed wing aircraft
that cannot be brought to a stop in an emergency. To enable geographic
confinement of such AI-controlled vehicles, we present a formally
verified algorithm for predicting geofence violations and selecting a
safe maneuver that will keep the vehicle within the designated
operations area. The algorithm is based on a higher-order dynamics
model that generalizes Dubins paths and allows handling of uncertainty
in model parameters. The proposed algorithm was implemented and tested
on an autonomous aircraft.

We define a function euler_spiral_tangent_pt and prove properties
about the values that it computes, namely that they are related to the
closest geometrical distance to a geofence for a future turning
trajectory. *)


(* Define Fresnel integrals *)
Definition C z := RInt (fun u => cos (1/2*PI*u²)) 0 z.
Definition S z := RInt (fun u => sin (1/2*PI*u²)) 0 z.


(* Fresnel C integral argument is continuous *)
Lemma fresnelC_arg_cont : forall z,
    continuous (fun u : R => cos (1 / 2 * PI * u²)) z.
Proof.
  intros.
  apply (ex_derive_continuous (fun u => cos (1/2*PI*u²))).
  auto_derive.
  constructor.
Qed.


(* Fresnel C integral exists *)
Lemma fresnelC_ex : forall z,
    ex_RInt (fun u => cos (1/2*PI*u²)) 0 z.
Proof.
  intros.
  apply (ex_RInt_continuous (fun u => cos (1/2*PI*u²))).
  intros.
  apply fresnelC_arg_cont.
Qed.

(* Fresnel C derivative exists, and has given value *)
Lemma fresnelC_derive : forall z,
    is_derive C z (cos (1/2*PI*z²)).
Proof.
  intros.
  unfold C.
  auto_derive.
  split.
  apply fresnelC_ex.
  split.
  unfold locally.
  assert (0 < 1) as ogto. lra.
  exists (mkposreal 1 ogto).
  intros y ballz.
  specialize (fresnelC_arg_cont y) as fcc.
  apply continuous_pt_impl_continuity_pt; try assumption.
  constructor.
  rewrite Rmult_1_l.
  reflexivity.
Qed.


Lemma fresnelC_derive2 : forall z,
    is_derive_n C 2 z (- z * PI * sin (1/2*PI*z²)).
Proof.
  intros.
  assert (Derive C = (fun z => (cos (1 / 2 * PI * z²)))) as dc. {
    apply functional_extensionality.
    intros.
    specialize (fresnelC_derive x) as fdc1.
    apply is_derive_unique in fdc1.
    assumption. }
  
  unfold is_derive_n, Derive_n.
  change (is_derive (Derive C) z (- z * PI * sin (1 / 2 * PI * z²))).
  rewrite dc.
  auto_derive.
  constructor.
  field.
Qed.


(* Fresnel S integral argument is continuous *)
Lemma fresnelS_arg_cont : forall z,
    continuous (fun u : R => sin (1 / 2 * PI * u²)) z.
Proof.
  intros.
  apply (ex_derive_continuous (fun u => sin (1/2*PI*u²))).
  auto_derive.
  constructor.
Qed.

(* Fresnel S integral exists *)
Lemma fresnelS_ex : forall z,
    ex_RInt (fun u => sin (1/2*PI*u²)) 0 z.
Proof.
  intros.
  apply (ex_RInt_continuous (fun u => sin (1/2*PI*u²))).
  intros.
  apply fresnelS_arg_cont.
Qed.

(* Fresnel S derivative exists, and has given value *)
Lemma fresnelS_derive : forall z,
    is_derive S z (sin (1/2*PI*z²)).
Proof.
  intros.
  unfold S.
  auto_derive.
  split.
  apply fresnelS_ex.
  split.
  unfold locally.
  assert (0 < 1) as ogto. lra.
  exists (mkposreal 1 ogto).
  intros y ballz.
  specialize (fresnelS_arg_cont y) as fcc.
  apply continuous_pt_impl_continuity_pt; try assumption.
  constructor.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma fresnelS_derive2 : forall z,
    is_derive_n S 2 z (z * PI * cos (1/2*PI*z²)).
Proof.
  intros.
  assert (Derive S = (fun z => (sin (1 / 2 * PI * z²)))) as ds. {
    apply functional_extensionality.
    intros.
    specialize (fresnelS_derive x) as fds1.
    apply is_derive_unique in fds1.
    assumption. }
  
  unfold is_derive_n, Derive_n.
  change (is_derive (Derive S) z (z * PI * cos (1 / 2 * PI * z²))).
  rewrite ds.
  auto_derive.
  constructor.
  field.
Qed.


(** Define Euler spiral as (Fx a s, Fy a s) *)

Definition l a := sqrt (PI/a).
Definition Fx a s := let la := l a in la * C (s/la).
Definition Fy a s := let la := l a in la * S (s/la).

(* begin hide *)
(* l parameter is not zero *)
Lemma agt0_lagt0 : forall a
    (zlta : 0 < a),
  0 < l a.
Proof.
  intros.
  unfold l.
  fieldrewrite (PI/a) (PI * /a). lra.
  specialize PI_RGT_0 as pigt0.
  assert (0 < /a ) as aigt0. {
    apply Rinv_0_lt_compat. assumption. }
  rewrite sqrt_mult; try left; try assumption.
  apply Rmult_lt_0_compat; apply sqrt_lt_R0; assumption.
Qed.


Lemma ane0_lane0 : forall a
    (zlta : 0 < a),
  l a <> 0.
Proof.
  intros.
  intro.
  specialize (agt0_lagt0 _ zlta) as lagt0.
  lra.
Qed.
(* end hide *)
(* Euler spiral x component derivative exists and 
   has given value *)
Lemma Fx_deriv : forall a (zlta : 0 < a) s,
    is_derive (Fx a) s (cos (1/2*PI*(s/(l a))²)).
Proof.
  intros.
  assert (l a <> 0) as lane0.
  apply ane0_lane0; try assumption.
  specialize (fresnelC_derive (s */(l a))) as cd.
  unfold Fx.
  auto_derive.
  change (ex_derive C (s * / l a)).
  unfold ex_derive.
  exists (cos (1 / 2 * PI * (s * / (l a))²)).
  assumption.
  setl (Derive (fun x : R => C x) (s * / (l a))); try assumption.
  unfold C.
  change (Derive C (s * / (l a)) =
          cos (1 / 2 * PI * (s / (l a))²)).
  apply is_derive_unique.
  assumption.
Qed.
  
(* Euler spiral y component derivative exists and 
   has given value *)

Lemma Fy_deriv : forall a (zlta : 0 < a) s,
    is_derive (Fy a) s (sin (1/2*PI*(s/(l a))²)).
Proof.
  intros.
  assert (l a <> 0) as lane0. 
  apply ane0_lane0; try assumption.
  specialize (fresnelS_derive (s */(l a))) as cd.
  unfold Fy.
  auto_derive.
  change (ex_derive S (s * / l a)).
  unfold ex_derive.
  exists (sin (1 / 2 * PI * (s * / l a)²)).
  assumption.
  setl (Derive (fun x : R => S x) (s * / l a)); try assumption.
  change (Derive S (s * / l a) =
          sin (1 / 2 * PI * (s / l a)²)).
  apply is_derive_unique.
  assumption.
Qed.


Lemma Fx_deriv2 : forall a (zlta : 0 < a) s,
    is_derive_n (Fx a) 2 s (- PI * s / (l a)² * sin (1/2*PI*(s/(l a))²)).
Proof.
  intros.
  assert (l a <> 0) as lane0.
  apply ane0_lane0; try assumption.

  assert (Derive (Fx a) = (fun s => cos (1/2*PI*(s/(l a))²))) as dfx. {
    apply functional_extensionality.
    intros r.
    specialize (Fx_deriv _ zlta r) as fxd.
    apply is_derive_unique in fxd.
    assumption.
  }

  assert (is_derive (fun s0 : R => cos (1 / 2 * PI * (s0 / l a)²)) s
                    (- PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²))) as aux. {
  auto_derive.
  constructor.
  repeat rewrite <- RmultRinv.
  unfold Rsqr.
  field.
  assumption. }
  
  unfold is_derive_n.
  auto_derive.
  change (ex_derive (Derive (Fx a)) s).
  rewrite dfx.
  exists (- PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²)).
  assumption.

  arn.
  change (Derive (Derive (Fx a)) s =
          - PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²)).
  rewrite dfx.
  apply is_derive_unique.
  assumption.
Qed.


Lemma Fy_deriv2 : forall a (zlta : 0 < a) s,
    is_derive_n (Fy a) 2 s (PI * s / (l a)² * cos (1/2*PI*(s/(l a))²)).
Proof.
  intros.
  assert (l a <> 0) as lane0.
  apply ane0_lane0; try assumption.

  assert (Derive (Fy a) = (fun s => sin (1/2*PI*(s/(l a))²))) as dfy. {
    apply functional_extensionality.
    intros r.
    specialize (Fy_deriv _ zlta r) as fxd.
    apply is_derive_unique in fxd.
    assumption.
  }

  assert (is_derive (fun s0 : R => sin (1 / 2 * PI * (s0 / l a)²)) s
                    (PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²))) as aux. {
  auto_derive.
  constructor.
  repeat rewrite <- RmultRinv.
  unfold Rsqr.
  field.
  assumption. }
  
  unfold is_derive_n.
  auto_derive.
  change (ex_derive (Derive (Fy a)) s).
  rewrite dfy.
  exists (PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²)).
  assumption.

  arn.
  change (Derive (Derive (Fy a)) s =
          PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²)).
  rewrite dfy.
  apply is_derive_unique.
  assumption.
Qed.



Record pt := mkpt { ptx : R ; pty : R}.

Definition magnitude (p q : R->R) :=
  (comp sqrt (plus_fct (comp Rsqr p)
                       (comp Rsqr q))).

(* Define path segment: paths are continuous and parameterized by
their distance. *)
Record path_segment (D : nonnegreal) (pathx pathy : R->R) (a b:pt) :=
  path_intro {
      contx : (forall (d:R), continuous pathx d);
      conty : (forall (d:R), continuous pathy d);
      abnd : (mkpt (pathx 0) (pathy 0)) = a;
      bbnd : (mkpt (pathx D) (pathy D)) = b;
      pzbydist : forall d, 0 <= d ->
          is_RInt (magnitude (Derive pathx) (Derive pathy))
                  0 d d;
    }.

(* begin hide *)
Definition evalpath {D:nonnegreal} {Hx Hy : R-> R} {a b} 
           (p : path_segment D Hx Hy a b) (z:R) :=
  (mkpt (Hx z) (Hy z)).

Lemma euler_path_segment_0 : forall D a
    (zlta : 0 < a),
    (path_segment D (Fx a) (Fy a)
                  (mkpt (Fx a 0) (Fy a 0))
                  (mkpt (Fx a D) (Fy a D))).
Proof.
  intros.
  constructor.
  + intro. 
    apply (ex_derive_continuous (Fx a)).
    exists (cos (1 / 2 * PI * (d / l a)²)).
    apply Fx_deriv; try assumption.
  + intro. 
    apply (ex_derive_continuous (Fy a)).
    exists (sin (1 / 2 * PI * (d / l a)²)).
    apply Fy_deriv; try assumption.
  + reflexivity.
  + reflexivity.
  + intros.
    specialize (Fx_deriv _ zlta) as fxd.
    assert (Derive (Fx a) =
            (fun s => (cos (1 / 2 * PI * (s / l a)²)))) as fxD. {
      apply functional_extensionality.
      intro s.
      specialize (fxd s).
      apply is_derive_unique.
      assumption. }

    specialize (Fy_deriv _ zlta) as fyd.
    assert (Derive (Fy a) =
            (fun s => (sin (1 / 2 * PI * (s / l a)²)))) as fyD. {
      apply functional_extensionality.
      intro s.
      specialize (fyd s).
      apply is_derive_unique.
      assumption. }

    rewrite fxD, fyD.
    unfold magnitude.

    assert ((comp Rsqr (fun s : R => cos (1 / 2 * PI * (s / l a)²))) +
            (comp Rsqr (fun s : R => sin (1 / 2 * PI * (s / l a)²))) =
            fct_cte 1)%F as id. {
      apply functional_extensionality.
      intros.
      unfold comp, Rsqr, plus_fct, fct_cte.
      set (A := (1 / 2 * PI * (x / l a * (x / l a)))).
      rewrite <- (sin2_cos2 A).
      unfold Rsqr.
      field.
    }
    rewrite id.

    unfold comp, fct_cte.
    rewrite sqrt_1.
    specialize (is_RInt_const 0 d 1) as ir.
    unfold scal in ir. simpl in ir.
    unfold mult in ir. simpl in ir.
    assert (d = ((d - 0) * 1)) as id2. lra.
    rewrite id2 at 2.
    assumption.
Qed.

(* end hide *)
(* An euler spiral starting at si and ending at sm (si<sm) is a path
segment *)
Lemma euler_path_segment : forall a si sm (zlta : 0 < a) (pdp : 0 <= sm - si),
    (path_segment (mknonnegreal (sm-si) pdp)
                     (fun s => Fx a (s + si))
                     (fun s => Fy a (s + si))
                     (mkpt (Fx a si) (Fy a si))
                     (mkpt (Fx a sm) (Fy a sm))).
Proof.
  intros.
  assert (forall d,
             is_derive (fun s => Fx a (s + si)) d
                       (cos (1 / 2 * PI * ((d + si) / l a)²))) as idx. {
    intros.
    assert ((fun x : R => Fx a x) = Fx a) as id. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    auto_derive.
    rewrite id.
    exists (cos (1 / 2 * PI * ((d+si) / l a)²)).
    apply Fx_deriv; try assumption.
    specialize (Fx_deriv _ zlta (d+si)) as idfx.
    apply is_derive_unique in idfx.
    rewrite id, idfx, Rmult_1_l.
    reflexivity. }

    assert (forall d,
             is_derive (fun s => Fy a (s + si)) d
                       (sin (1 / 2 * PI * ((d + si) / l a)²))) as idy. {
    intros.
    assert ((fun y : R => Fy a y) = Fy a) as id. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    auto_derive.
    rewrite id.
    exists (sin (1 / 2 * PI * ((d+si) / l a)²)).
    apply Fy_deriv; try assumption.
    specialize (Fy_deriv _ zlta (d+si)) as idfx.
    apply is_derive_unique in idfx.
    rewrite id, idfx, Rmult_1_l.
    reflexivity. }
  constructor.
  + intro. 
    apply (ex_derive_continuous (fun s => Fx a (s + si))).
    exists (cos (1 / 2 * PI * ((d+si) / l a)²)).
    apply idx.
  + intro. 
    apply (ex_derive_continuous (fun s => Fy a (s + si))).
    exists (sin (1 / 2 * PI * ((d+si) / l a)²)).
    apply idy.
  + fieldrewrite (0 + si) si. reflexivity.
  + simpl.
    fieldrewrite (sm - si + si) sm. reflexivity.
  + intros.
    specialize (Fx_deriv _ zlta) as fxd.
    assert (Derive (fun s => Fx a (s+si)) =
            (fun s => (cos (1 / 2 * PI * ((s+si) / l a)²)))) as fxD. {
      apply functional_extensionality.
      intro s.
      specialize (fxd s).
      apply is_derive_unique.
      apply idx. }

    specialize (Fy_deriv _ zlta) as fyd.
    assert (Derive (fun s => Fy a (s+si)) =
            (fun s => sin (1 / 2 * PI * ((s+si) / l a)²))) as fyD. {
      apply functional_extensionality.
      intro s.
      specialize (fyd s).
      apply is_derive_unique.
      apply idy. }

    rewrite fxD, fyD.
    unfold magnitude.

    assert ((comp Rsqr (fun s : R => cos (1 / 2 * PI * ((s+si) / l a)²))) +
            (comp Rsqr (fun s : R => sin (1 / 2 * PI * ((s+si) / l a)²))) =
            fct_cte 1)%F as id. {
      apply functional_extensionality.
      intros.
      unfold comp, Rsqr, plus_fct, fct_cte.
      set (A := (1 / 2 * PI * ((x+si) / l a * ((x+si) / l a)))).
      rewrite <- (sin2_cos2 A).
      unfold Rsqr.
      field.
    }
    rewrite id.

    unfold comp, fct_cte.
    rewrite sqrt_1.
    specialize (is_RInt_const 0 d 1) as ir.
    unfold scal in ir. simpl in ir.
    unfold mult in ir. simpl in ir.
    assert (d = ((d - 0) * 1)) as id2. lra.
    rewrite id2 at 2.
    assumption.
Qed.

(* Define straight-line distance between two points. *)

Definition dist (x0 y0 x1 y1 : R) := sqrt ((x1-x0)² + (y1-y0)²).
Definition dist2 (x0 y0 x1 y1 : R) := ((x1-x0)² + (y1-y0)²).
(* begin hide *)
(* Derivative of distance squared exists and is as given *)
Lemma dist2_derive_xparam :
  forall (x0 y0 m b x:R),
    is_derive (fun p:R => dist2 x0 y0 p (m*p+b)) x
              (2 * ((x + - x0) + m * (m * x + b + - y0))).
Proof.
  intros.
  unfold dist2.
  auto_derive; [constructor| field].
Qed.


(* Second derivative of distance squared exists and is as given *)
Lemma dist2_2derive_xparam :
  forall (x0 y0 m b x:R),
    is_derive (fun p:R => (2 * ((p + - x0) + m * (m * p + b + - y0)))) x
              (2 * (1 + m²)).
Proof.
  intros.
  auto_derive; [constructor| unfold Rsqr; field].
Qed.


Lemma sf_tx_std : forall px py cx cy mx my,
    mx * (py - cy) - my * (px - cx) =
    mx * (py - cy - 0) - my * (px - cx - 0).
Proof.
  intros.
  lra.
Qed.

Lemma sf_rot_std : forall px py mx my,
    let t := atan2 my mx in
    mx * (py - 0) - my * (px - 0) =
    sqrt (my² + mx²) * (- px * sin t + py * cos t - 0) -
    0 * (px * cos t + py * sin t - 0).
Proof.
  intros.
  arn.
  unfold atan2 in *.
  destruct pre_atan2 as [u [urng [myd mxd]]].
  set (M := sqrt (my² + mx²)) in *.
  unfold t.
  rewrite mxd, myd.
  field.
Qed.

Lemma sf_std : forall px py cx cy mx my,
    let t := atan2 my mx in
    mx * (py - cy) - my * (px - cx) =
    sqrt (my² + mx²) * (- (px - cx) * sin t + (py - cy) * cos t - 0) -
    0 * ((px - cx) * cos t + (py - cy) * sin t - 0).
Proof.
Proof.
  intros.
  rewrite sf_tx_std.
  rewrite sf_rot_std.
  reflexivity.
Qed.


Lemma circ_tx  : forall x y r cx cy nx ny,
    (x - cx)² + (y - cy)² <= r² -> 
    ((x - cx - nx) + nx)² + ((y - cy - ny) + ny)² <= r².
Proof.
  intros.
  fieldrewrite (x - cx - nx + nx) (x - cx).
  fieldrewrite (y - cy - ny + ny) (y - cy).
  assumption.
Qed.


Lemma circ_rot  : forall x y cx cy r φ,
    (x - cx)² + (y - cy)² <= r² -> 
    let rcx := cx * cos φ - cy * sin φ in
    let rcy := cx * sin φ + cy * cos φ in
    let rx := x * cos φ - y * sin φ in
    let ry := x * sin φ + y * cos φ in
    (rx - rcx)² + (ry - rcy)² <= r².
Proof.
  intros.
  repeat rewrite Rsqr_minus.
  unfold rx, ry, rcx, rcy.
  repeat rewrite Rsqr_minus.
  repeat rewrite Rsqr_plus.
  repeat rewrite Rsqr_mult.
  setl ((x² * ((sin φ)² + (cos φ)²)
         + cx² * ((sin φ)²+ (cos φ)²)
           - 2 * x * cx * ((sin φ)² + (cos φ)²))
        + (y² * ((sin φ)² + (cos φ)²)
           + cy² * ((sin φ)² + (cos φ)²)
             - 2 * y * cy * ((sin φ)² + (cos φ)²))).
  rewrite sin2_cos2.
  arn.
  repeat rewrite <- Rsqr_minus.
  assumption.
Qed.

Lemma circ_rot_lt  : forall x y cx cy r φ,
    (x - cx)² + (y - cy)² < r² -> 
    let rcx := cx * cos φ - cy * sin φ in
    let rcy := cx * sin φ + cy * cos φ in
    let rx := x * cos φ - y * sin φ in
    let ry := x * sin φ + y * cos φ in
    (rx - rcx)² + (ry - rcy)² < r².
Proof.
  intros.
  repeat rewrite Rsqr_minus.
  unfold rx, ry, rcx, rcy.
  repeat rewrite Rsqr_minus.
  repeat rewrite Rsqr_plus.
  repeat rewrite Rsqr_mult.
  setl ((x² * ((sin φ)² + (cos φ)²)
         + cx² * ((sin φ)²+ (cos φ)²)
           - 2 * x * cx * ((sin φ)² + (cos φ)²))
        + (y² * ((sin φ)² + (cos φ)²)
           + cy² * ((sin φ)² + (cos φ)²)
             - 2 * y * cy * ((sin φ)² + (cos φ)²))).
  rewrite sin2_cos2.
  arn.
  repeat rewrite <- Rsqr_minus.
  assumption.
Qed.

Lemma circ_safe_std : forall x x0 y r,
    0 < r ->
    (x + x0)² + (y - r)² <= r² -> 
    0 <= y.
Proof.
  intros *.
  intros zltr ic.
  rewrite Rsqr_minus in ic.
  specialize (Rle_0_sqr (x+x0)) as zlex2.
  specialize (Rle_0_sqr y) as zley2.
  assert (0 <= (x+x0)² + y²) as zlex2y2; 
    try (apply Rplus_le_le_0_compat; assumption).
  assert ((x+x0)² + y² <= 2 * y * r) as ict;
    try lra.
  apply (Rmult_le_reg_l 2); try lra.
  apply (Rmult_le_reg_r r); try lra.
Qed.

Lemma circ_safe_std_lt : forall x x0 y r,
    0 < r ->
    (x + x0)² + (y - r)² < r² -> 
    0 < y.
Proof.
  intros *.
  intros zltr ic.
  rewrite Rsqr_minus in ic.
  specialize (Rle_0_sqr (x+x0)) as zlex2.
  specialize (Rle_0_sqr y) as zley2.
  assert (0 <= (x+x0)² + y²) as zlex2y2; 
    try (apply Rplus_le_le_0_compat; assumption).
  assert ((x+x0)² + y² <= 2 * y * r) as ict;
    try lra.
  apply (Rmult_lt_reg_l 2); try lra.
  apply (Rmult_lt_reg_r r); try lra.
Qed.


Lemma linear_dominates_circle : forall x y mx my px py r,
    r > 0 ->
    ~(mx = 0 /\ my = 0) ->
    let M := sqrt (my² + mx²) in
    (x - (px + (- my / M * r)))² + (y - (py + (mx / M * r)))² <= r² ->
    0 <= mx * (y - py) - my * (x - px).
Proof.
  intros *.
  intros rgt0 no M ci.

  assert (0 < M) as mgt0. {
    unfold M.
    clear ci rgt0 x y px py r M.
    apply sqrt_lt_R0.
    specialize (Rle_0_sqr my) as my2.
    specialize (Rle_0_sqr mx) as mx2.
    destruct my2 as [ylt |yeq].
    + apply Rplus_lt_le_0_compat; try assumption.
    + destruct mx2 as [xlt |xeq].
      ++ rewrite <- yeq.
         lra.
      ++ exfalso.
         apply no.
         split.
         +++ unfold Rsqr in xeq.
             symmetry in xeq.
             apply Rmult_integral in xeq.
             destruct xeq; assumption.
         +++ unfold Rsqr in yeq.
             symmetry in yeq.
             apply Rmult_integral in yeq.
             destruct yeq; assumption. }

(*  change (0 <= safe_pt px py mx my x y). *)
  rewrite sf_std.

  unfold atan2 in *.
  destruct pre_atan2 as [γ [grng [yd xd]]].
  change (my = M * sin γ) in yd.
  change (mx = M * cos γ) in xd.

  set (Y := - (x - px) * sin γ + (y - py) * cos γ) in *.
  set (X := (x - px) * cos γ + (y - py) * sin γ) in *.

(*  change (0 <= safe_pt 0 0 M 0 X Y). *)
  
  assert (x - (px + - my / M * r) = (x - px) - (- my / M * r)) as id;
    [field; lra | rewrite id in ci; clear id].
  assert (y - (py + mx / M * r) = (y - py) - mx / M * r) as id;
    [field; lra | rewrite id in ci; clear id].
  
  rewrite xd, yd in *.
  apply (circ_rot (x - px) (y - py) _ _ r (-γ)) in ci.
  rewrite cos_neg, sin_neg in *.

  assert (- (M * sin γ) / M * r * cos γ - M * cos γ / M * r * - sin γ=
          0) as id; try (field; lra).
  rewrite id in ci.
  clear id.

  assert (- (M * sin γ) / M * r * - sin γ + M * cos γ / M * r * cos γ =
          r * ((sin γ)² + (cos γ)²)) as id; try (unfold Rsqr; field; lra).
  rewrite id, sin2_cos2, Rmult_1_r in ci.
  clear id.
  
  assert ((x - px) * cos γ - (y - py) * - sin γ = X) as id;
    try (unfold X; field).
  rewrite id in ci; clear id.
  assert ((x - px) * - sin γ + (y - py) * cos γ = Y) as id;
    try (unfold Y; field).
  rewrite id in ci; clear id.
  fieldrewrite ((M * sin γ)² + (M * cos γ)²)
               (M² * ((sin γ)² + (cos γ)²)).
  rewrite sin2_cos2.
  arn.
  rewrite sqrt_Rsqr; try lra.
  apply (Rmult_le_reg_r (/ M)); try zltab.
  setl 0; try lra.
  setr Y; try lra.
  eapply circ_safe_std.
  eapply rgt0.
  eapply ci.
Qed.

Lemma linear_dominates_circle_lt : forall x y mx my px py r,
    r > 0 ->
    ~(mx = 0 /\ my = 0) ->
    let M := sqrt (my² + mx²) in
    (x - (px + (- my / M * r)))² + (y - (py + (mx / M * r)))² < r² ->
    0 < mx * (y - py) - my * (x - px).
Proof.
  intros *.
  intros rgt0 no M ci.

  assert (0 < M) as mgt0. {
    unfold M.
    clear ci rgt0 x y px py r M.
    apply sqrt_lt_R0.
    specialize (Rle_0_sqr my) as my2.
    specialize (Rle_0_sqr mx) as mx2.
    destruct my2 as [ylt |yeq].
    + apply Rplus_lt_le_0_compat; try assumption.
    + destruct mx2 as [xlt |xeq].
      ++ rewrite <- yeq.
         lra.
      ++ exfalso.
         apply no.
         split.
         +++ unfold Rsqr in xeq.
             symmetry in xeq.
             apply Rmult_integral in xeq.
             destruct xeq; assumption.
         +++ unfold Rsqr in yeq.
             symmetry in yeq.
             apply Rmult_integral in yeq.
             destruct yeq; assumption. }

(*  change (0 <= safe_pt px py mx my x y). *)
  rewrite sf_std.

  unfold atan2 in *.
  destruct pre_atan2 as [γ [grng [yd xd]]].
  change (my = M * sin γ) in yd.
  change (mx = M * cos γ) in xd.

  set (Y := - (x - px) * sin γ + (y - py) * cos γ) in *.
  set (X := (x - px) * cos γ + (y - py) * sin γ) in *.

(*  change (0 <= safe_pt 0 0 M 0 X Y). *)
  
  assert (x - (px + - my / M * r) = (x - px) - (- my / M * r)) as id;
    [field; lra | rewrite id in ci; clear id].
  assert (y - (py + mx / M * r) = (y - py) - mx / M * r) as id;
    [field; lra | rewrite id in ci; clear id].
  
  rewrite xd, yd in *.
  apply (circ_rot_lt (x - px) (y - py) _ _ r (-γ)) in ci.
  rewrite cos_neg, sin_neg in *.

  assert (- (M * sin γ) / M * r * cos γ - M * cos γ / M * r * - sin γ=
          0) as id; try (field; lra).
  rewrite id in ci.
  clear id.

  assert (- (M * sin γ) / M * r * - sin γ + M * cos γ / M * r * cos γ =
          r * ((sin γ)² + (cos γ)²)) as id; try (unfold Rsqr; field; lra).
  rewrite id, sin2_cos2, Rmult_1_r in ci.
  clear id.
  
  assert ((x - px) * cos γ - (y - py) * - sin γ = X) as id;
    try (unfold X; field).
  rewrite id in ci; clear id.
  assert ((x - px) * - sin γ + (y - py) * cos γ = Y) as id;
    try (unfold Y; field).
  rewrite id in ci; clear id.
  fieldrewrite ((M * sin γ)² + (M * cos γ)²)
               (M² * ((sin γ)² + (cos γ)²)).
  rewrite sin2_cos2.
  arn.
  rewrite sqrt_Rsqr; try lra.
  apply (Rmult_lt_reg_r (/ M)); try zltab.
  setl 0; try lra.
  setr Y; try lra.
  eapply circ_safe_std_lt.
  eapply rgt0.
  eapply ci.
Qed.


Lemma lin_pt_ineq : forall mx my px py qx qy x y,
    0 <= mx * (y - py) - my * (x - px) <->
    mx * (py - qy) - my * (px - qx) <= mx * (y - qy) - my * (x - qx).
Proof.
  intros.
  lra.
Qed.

Lemma lin_pt_ineq_lt : forall mx my px py qx qy x y,
    0 < mx * (y - py) - my * (x - px) <->
    mx * (py - qy) - my * (px - qx) < mx * (y - qy) - my * (x - qx).
Proof.
  intros.
  lra.
Qed.


(* end hide *)

Section egeof.
  Variables (px py mx my a :R).
  Context (zlta : 0 < a).
  Context (ds : ~ (mx = 0 /\ my = 0)).

(* begin hide *)
(* sum of squares is nonzero when both components are not
simultaneously zero *)
Lemma nzss : (* determined slope *)
    mx² + my² <> 0.
Proof.
  intros.
  specialize (Rle_0_sqr mx) as mx2ge0.
  specialize (Rle_0_sqr my) as my2ge0.
  intro deq0.
  destruct mx2ge0 as [mx2lt0 | mx2eq0];
    destruct my2ge0 as [my2lt0 | my2eq0];
    try (assert (0 < mx² + my²) as dgt0; lra).
  symmetry in mx2eq0, my2eq0.
  apply Rsqr_eq_0 in mx2eq0.
  apply Rsqr_eq_0 in my2eq0.
  apply ds.
  split; assumption.
Qed.

(* end hide *)

(** Given a point (x0,y0), and a linear boundary described by a ray
with base (px,py) and slope my/mx, define functions that compute a
point (nx,ny) that is nearest to (x0,y0) (measured by straight-line
distance) and on the linear boundary. The slope of the boundary is
defined by its direction theta, i.e. my = K * sin(theta), mx = K *
cos(theta)) *)

Definition nxf x0 y0 :=
  (my² * px - mx * my * py + mx² * x0 + mx * my * y0)
    / (mx² + my²).
Definition nyf x0 y0 :=
  (- mx * my * px + mx² * py + mx * my * x0 + my² * y0)
    / (mx² + my²).

(* begin hide *)
Lemma npt_on_boundary :
  forall x0 y0 (ds : ~ (mx = 0 /\ my = 0)), (* determined slope *)
    let nx := nxf x0 y0 in
    let ny := nyf x0 y0 in
    my*(nx - px) = mx*(ny - py).
Proof.
  intros.
  unfold nxf in nx.
  unfold nyf in ny.
  specialize (nzss ) as dne0.
  apply (Rmult_eq_reg_r (mx² + my²)); try assumption.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rmult_minus_distr_r.
  unfold nx, ny, Rsqr.
  field. auto.
Qed.

Lemma nx_gives_ny :
  forall (x0 y0 :R) (mxne0 : mx <> 0)
         (iol : ~(my*(x0 - px) = mx*(y0 - py))), (* x0,y0 off line *)
    let nx := nxf x0 y0 in
    let ny := nyf x0 y0 in
    let m := my/mx in
    let b := py - px * my / mx in
    ny = m * nx + b.
Proof.
  intros.
  assert (~ (mx = 0 /\ my = 0)) as mdet. {
    intro.
    destruct H.
    apply mxne0.
    assumption. }
  specialize (nzss) as dne0.
  unfold ny, m, nx, b.
  apply (Rmult_eq_reg_r ((mx² + my²)*mx)); [|auto].
  apply (Rplus_eq_reg_r (px * my * mx² - mx²*mx*py - mx*my²*y0 - mx²*my*x0)).
  unfold nyf, nxf.
  setl 0; auto.
  setr 0; auto.
Qed.

(* Derivative of distance squared is zero at nx, ny *)
Lemma dist2_derive_eq0 :
  forall (x0 y0 x:R) (mxne0 : mx <> 0)
         (iol : ~(my*(x0 - px) = mx*(y0 - py))), (* x0,y0 off line *)
    let nx := nxf x0 y0 in
    let m := my/mx in
    let b := py - px * my / mx in
    is_derive (fun p:R => dist2 x0 y0 p (m*p+b)) nx 0.
Proof.
  intros.
  specialize (dist2_derive_xparam x0 y0 m b nx) as dv.
  assert (2 * (nx + - x0 + m * (m * nx + b + - y0)) = 0) as id. {
    clear dv.
    assert (~ (mx = 0 /\ my = 0)) as mdet. {
      intro.
      destruct H.
      apply mxne0.
      assumption. }
    specialize (nzss) as dne0.
    unfold nx.
    apply (Rmult_eq_reg_r (mx² + my²)); try assumption.
    setr 0.
    unfold m, b, nxf.
    setl 0.
    split; assumption.
    reflexivity. }
  rewrite id in dv.
  assumption.
Qed.

(* end hide *)
(* nx,ny is the nearest point to x0,y0 that is also on the line 
   mx*(y - py) = my*(x - px) *)  
Lemma npt_nearest :
  forall x0 y0 lx ly
         (ll : my*(lx - px) = mx*(ly - py)) (* lx,ly on the line *)
         (nl : ~ (my*(x0 - px) = mx*(y0 - py))), (* x0,y0 not on the line *)
    let nx := nxf x0 y0 in
    let ny := nyf x0 y0 in
    forall (nc : ~ (nx = lx /\ ny = ly)), (* not coincident *)
      dist x0 y0 nx ny < dist x0 y0 lx ly /\ my*(nx - px) = mx*(ny - py).
Proof.
  intros.
  specialize (nzss) as dne0.
  split;
    [| apply npt_on_boundary; try assumption].
  unfold dist.
  apply sqrt_lt_1;
    try (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  change (dist2 x0 y0 nx ny < dist2 x0 y0 lx ly).
  destruct (Req_dec mx 0) as [mxeq0 | mxne0].
  + rewrite mxeq0 in *.
    rewrite Rmult_0_l in ll.
    rewrite Rsqr_0, Rplus_0_l in dne0.
    assert (my <> 0) as myne0. {
      intro. apply ds.
      split; [reflexivity| assumption]. }
    assert (lx=px) as lxeqpx. {
      apply (Rplus_eq_reg_r (-px)).
      apply (Rmult_eq_reg_l (my)).
      lrag ll.
      assumption. }
    clear ll ds.
    generalize nc. clear nc.
    unfold nx, ny, dist2, nxf, nyf.
    rewrite lxeqpx, mxeq0.
    fieldrewrite ((my² * px - 0 * my * py + 0² * x0 + 0 * my * y0) / (0² + my²))
                 ((my² * px) / my²); try assumption.
    fieldrewrite ((- 0 * my * px + 0² * py + 0 * my * x0 + my² * y0) / (0² + my²))
                 ((my² * y0) / my²); try assumption.
    fieldrewrite (my² * px / my²) px; try assumption.
    fieldrewrite (my² * y0 / my²) y0; try assumption.
    intro nc.
    apply (Rplus_lt_reg_r (- ((px - x0)²))).
    setl 0.
    setr ((ly - y0)²).
    specialize (Rle_0_sqr (ly - y0)) as zlet.
    destruct zlet as [zltt | zeqt].
    ++ assumption.
    ++ exfalso.
       symmetry in zeqt.
       apply Rsqr_eq_0 in zeqt.
       apply Rminus_diag_uniq in zeqt.
       rewrite zeqt in nc.
       apply nc.
       split; reflexivity.
  + assert (ly = my/mx * lx + (py - px * my / mx)) as lydef. {
      apply (Rplus_eq_reg_r (-py)).
      apply (Rmult_eq_reg_l mx).
      symmetry.
      lrag ll.
      assumption. }
    set (m := my/mx) in *.
    set (b := (py - px * my / mx)) in *.
    rewrite lydef.
    specialize (dist2_derive_xparam x0 y0 m b) as d'.
    specialize (dist2_2derive_xparam x0 y0 m b) as d''.
    specialize (dist2_derive_eq0 x0 y0 (m * lx + b) mxne0 nl) as d2d0.
    simpl in d2d0.
    change (is_derive (fun p : R => dist2 x0 y0 p (m * p + b)) nx 0)
      in d2d0.
    set (f := (fun p : R => dist2 x0 y0 p (m * p + b))) in *.
    set (f' := (fun p : R => 2 * (p + - x0 + m * (m * p + b + - y0)))) in *.
    set (f'' := (fun p : R => (2 * (1 + m²)))) in *.
    change (forall x : R, is_derive f x (f' x)) in d'.
    change (forall x : R, is_derive f' x (f'' x)) in d''.
    assert (forall x, 0 < f'' x) as f''pos. {
      intros.
      unfold f''.
      apply Rmult_lt_0_compat;
        [lra|
         apply Rplus_lt_le_0_compat;
         [lra| apply Rle_0_sqr]].
    }

    assert (strict_increasing f') as f'incr. {
      unfold strict_increasing.
      intros.
      assert (forall x, Rbar_le m_infty x -> Rbar_le x p_infty ->
                        is_derive f' x (f'' x)) as id1. {
        intros.
        apply d''. }
      assert (forall x, Rbar_le m_infty x -> Rbar_le x p_infty ->
                        f'' x > 0) as id2. {
        intros. apply f''pos. }
      apply (incr_function_le _ _ _ _ id1 id2 x y).
      simpl; constructor.
      assumption.
      simpl; constructor. }

    assert (forall x, nx < x -> 0 < f' x) as f'pos. {
      intros.
      apply (is_derive_unique _ nx) in d'.
      apply (is_derive_unique) in d2d0.
      rewrite <- d2d0, d'.
      apply f'incr. assumption.
    }

    assert (forall x, x < nx -> f' x < 0) as f'neg. {
      intros.
      apply (is_derive_unique _ nx) in d'.
      apply (is_derive_unique) in d2d0.
      rewrite <- d2d0, d'.
      apply f'incr. assumption.
    }

    assert (forall x, nx < x -> f nx < f x) as fincr. {
      intros.
      assert (derivable f) as id1. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (f' x1).
      apply d'. }
      
      assert (forall b x : R, nx < x < b -> 0 < derive_pt f x (id1 x)) as id2. {
        intros.
        apply (is_derive_unique _ x1) in d'.
        rewrite Derive_Reals, d'.
        apply f'pos.
        destruct H0.
        assumption. }
      
      apply (derive_increasing_interv _ _ _ id1 H (id2 x)).
      split; [right; reflexivity|left; assumption].
      split; [left; assumption|right; reflexivity].
      assumption. }

    assert (forall x, x < nx -> f nx < f x) as fdecr. {
      intros.
      assert (derivable f) as id1. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (f' x1).
      apply d'. }
      
      assert (forall b x : R, b < x < nx -> derive_pt f x (id1 x) < 0) as id2. {
        intros.
        apply (is_derive_unique _ x1) in d'.
        rewrite Derive_Reals, d'.
        apply f'neg.
        destruct H0.
        assumption. }
      
      apply (derive_decreasing_interv _ _ _ id1 H (id2 x)).
      split; [right; reflexivity|left; assumption].
      split; [left; assumption|right; reflexivity].
      assumption. }

    destruct (total_order_T nx lx); [destruct s|].
    ++ specialize (fincr lx r).
       unfold f in fincr.
       specialize (nx_gives_ny _ _ mxne0 nl) as id.
       change (ny = m * nx + b) in id.
       rewrite id.
       assumption.
    ++ exfalso.
       specialize (nx_gives_ny _ _ mxne0 nl) as id.
       change (ny = m * nx + b) in id.
       rewrite e in id.
       rewrite <- lydef in id.
       apply nc.
       split; assumption.

    ++ specialize (fdecr lx r).
       unfold f in fdecr.
       specialize (nx_gives_ny _ _ mxne0 nl) as id.
       change (ny = m * nx + b) in id.
       rewrite id.
       assumption.
Qed.

(**
safe_pt is a metric relating a point q = (qx, qy) to a linear boundary
defined by point p = (px, px) and slope my/mx; the minimum distance
from the point q to the boundary is proportional the absolute value of
this function, and the sign indicates on which side of the boundary
q is located.

By definition the metric is positive for points in the half-plane to
the left of the ray, negative in the half-plane to the right. Our
convention for boundaries is that we are safe if we are on the left;
if touching the boundary or on the right we are past the safe edge of
the boundary.

These correspond to Theorems 1 and 2 in the paper.
 *)

  Definition safe_pt (qx qy : R) := mx*(qy - py) - my*(qx - px).
  Definition rotate_ccw (x y : R) := (-y, x).
  Definition sub_prod (a b : R * R) := (fst a - fst b, snd a - snd b).
  
  Theorem safety_metric_sign_indicates_safety : forall qx qy,
      0 < dot_prod (rotate_ccw mx my) (sub_prod (qx,qy) (px,py)) ->
      0 < safe_pt qx qy.
  Proof.
    intros *.
    intro dd.
    unfold dot_prod, sub_prod, rotate_ccw in dd.
    simpl in dd.
    rewrite (Rplus_comm (- my * (qx - px))) in dd.
    unfold safe_pt.
    rewrite <- pm.
    fieldrewrite (- (my * (qx - px))) (- my * (qx - px)).
    assumption.
  Qed.

  Definition sf := (fun q:R => safe_pt (Fx a q) (Fy a q)).

  (* begin hide *)
  Lemma sf_deriv : forall s,
      is_derive sf s (mx * sin (1 / 2 * PI * (s / l a)²) +
                      - my * cos (1 / 2 * PI * (s / l a)²)).
  Proof.
    intros.
    unfold sf.
    (*  specialize (ane0_lane0 _ zlta) as lane0. *)
    specialize PI_RGT_0 as pigt0.
    
    assert (Fx a = (fun x => Fx a x)) as idx. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    assert (Fy a = (fun y => Fy a y)) as idy. {
    apply functional_extensionality.
    intros.
    reflexivity. }
  specialize (Fx_deriv _ zlta s) as fxd.
  specialize (Fy_deriv _ zlta s) as fyd.

  unfold safe_pt.
  auto_derive.
  + rewrite <- idx, <- idy.
    unfold ex_derive.
    repeat split; auto.
    exists (sin (1 / 2 * PI * (s / l a)²)); assumption.
    exists (cos (1 / 2 * PI * (s / l a)²)); assumption.
  + apply is_derive_unique in fxd.
    apply is_derive_unique in fyd.
    rewrite <- idx, <- idy, fxd, fyd.
    field.
  Qed.

  Lemma sf_2deriv : forall s,
      is_derive_n sf 2 s (PI * s / (l a)² *
                          (mx * cos (1 / 2 * PI * (s * / l a)²) +
                           my * sin (1 / 2 * PI * (s * / l a)²))).
  Proof.
    intros.
    unfold sf.
    specialize (sf_deriv ) as sp'.
    unfold is_derive_n, Derive_n.
    assert ((fun x : R =>
               Derive (fun x0 : R =>
                         safe_pt (Fx a x0) (Fy a x0))
                      x) =
            (Derive (fun x0 : R =>
                       safe_pt (Fx a x0) (Fy a x0))))
      as feq. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    rewrite feq. clear feq.
    
    assert(Derive (fun q : R => safe_pt (Fx a q) (Fy a q)) =
           (fun s => (mx * sin (1 / 2 * PI * (s / l a)²) +
                      - my * cos (1 / 2 * PI * (s / l a)²)))) as df. {
      apply functional_extensionality.
      intros.
      specialize (sp' x).
      apply is_derive_unique in sp'.
      assumption. }
    
    rewrite df.
    auto_derive.
    constructor.
    unfold Rsqr.
    field.
    apply ane0_lane0; assumption.
  Qed.


  Lemma sf_3deriv : forall s,
      is_derive_n sf 3 s
                  (PI * / (l a)² *
                   ((my - PI * s² * / (l a)² * mx) *
                    sin (1 / 2 * PI * (s * / l a)²) +
                    (mx + PI * s² * / (l a)² * my) *
                    cos (1 / 2 * PI * (s * / l a)²))).
  Proof.
    unfold is_derive_n.
    intros.
    assert (Derive_n sf 2 = (fun s => PI * s / (l a)² *
                             (mx * cos (1 / 2 * PI * (s * / l a)²) +
                              my * sin (1 / 2 * PI * (s * / l a)²))))
      as sf2d. {
      apply functional_extensionality.
      intros.
      specialize (sf_2deriv x) as sf2d.
      apply is_derive_n_unique in sf2d.
      assumption. }
    rewrite sf2d.
    auto_derive.
    constructor.
    unfold Rsqr.
    field.
    specialize (ane0_lane0 _ zlta) as lane0.
    assumption.
  Qed.


  (* end hide *)

  Theorem safety_metric_magnitude_orders_safe_points : forall s,
      let nx := nxf (Fx a s) (Fy a s) in
      let ny := nyf (Fx a s) (Fy a s) in
      Rabs (sf s) / sqrt (mx² + my²) = dist (Fx a s) (Fy a s) nx ny.
  Proof.
    intros.
    unfold sf.
    unfold Rabs.
    destruct Rcase_abs.
    + unfold safe_pt, dist, nx, ny, nxf, nyf in *.
      specialize (nzss) as ssne0.
      assert (sqrt (mx² + my²) <> 0) as sssne0. {
        intro ssseq0.
        apply ssne0.
        apply sqrt_eq_0; try assumption.
        zltab. }
      apply (Rmult_eq_reg_r (sqrt (mx² + my²))); try assumption.
      setl (- mx * (Fy a s - py) + my * (Fx a s - px)).
      assumption.
      rewrite (Rmult_comm _ (sqrt (mx² + my²))).
      rewrite <- sqrt_mult.
      fieldrewrite ((mx² + my²) *
                    (((my² * px - mx * my * py + mx² * Fx a s + mx * my * Fy a s)
                        / (mx² + my²) - Fx a s)² +
                     ((- mx * my * px + mx² * py + mx * my * Fx a s + my² * Fy a s)
                        / (mx² + my²) - Fy a s)²))
                   ((- mx * (Fy a s - py) + my * (Fx a s - px))²).
      assumption.
      rewrite sqrt_Rsqr.
      field.
      lra.
      zltab.
      zltab.
    + unfold safe_pt, dist, nx, ny, nxf, nyf in *.
      specialize (nzss) as ssne0.
      assert (sqrt (mx² + my²) <> 0) as sssne0. {
        intro ssseq0.
        apply ssne0.
        apply sqrt_eq_0; try assumption.
        zltab. }
      apply (Rmult_eq_reg_r (sqrt (mx² + my²))); try assumption.
      setl (mx * (Fy a s - py) - my * (Fx a s - px)).
      assumption.
      rewrite (Rmult_comm _ (sqrt (mx² + my²))).
      rewrite <- sqrt_mult.
      fieldrewrite ((mx² + my²) *
                    (((my² * px - mx * my * py + mx² * Fx a s + mx * my * Fy a s)
                        / (mx² + my²) - Fx a s)² +
                     ((- mx * my * px + mx² * py + mx * my * Fx a s + my² * Fy a s)
                        / (mx² + my²) - Fy a s)²))
                   ((mx * (Fy a s - py) - my * (Fx a s - px))²).
      assumption.
      rewrite sqrt_Rsqr.
      field.
      lra.
      zltab.
      zltab.
  Qed.
  
  (** Definitions for the osculating circle, and proofs showing that a
      piecewise path made by combining it with the euler spiral
      results in: a continuous overall path with continuous first and
      second derivatives.

      These lemmas collectively correspond to Theorem 3 in the
      paper. The axiom below is the only one we added; it expresses
      that the osculating circle at every point contains the rest of
      the spiral, a result due to Euler in 1786. *)

  Definition fx := Fx a.
  Definition fy := Fy a.
  Definition tx := Derive fx.
  Definition ty := Derive fy.
  Definition κ s := sqrt ((Derive tx s)² + (Derive ty s)²).
  Definition nx s := / κ s * Derive tx s.
  Definition ny s := / κ s * Derive ty s.

  Lemma edtx : forall s,
      locally s (ex_derive tx).
  Proof.
    unfold locally.
    exists (mkposreal _ Rlt_0_1).
    simpl.
    intros.
    specialize (Fx_deriv2 _ zlta y) as d2fx.
    unfold is_derive_n, Derive_n in d2fx.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive tx y Q) in d2fx;
       exists Q; assumption
     end).
  Qed.
  
  Lemma edty : forall s,
      locally s (ex_derive ty).
  Proof.
    unfold locally.
    exists (mkposreal _ Rlt_0_1).
    simpl.
    intros.
    specialize (Fy_deriv2 _ zlta y) as d2fy.
    unfold is_derive_n, Derive_n in d2fy.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive ty y Q) in d2fy;
       exists Q; assumption
     end).
  Qed.

  Lemma uv : forall s,
      locally s (fun s : R => (tx s)² + (ty s)² = 1).
  Proof.
    unfold locally.
    exists (mkposreal _ Rlt_0_1).
    simpl.
    intros.
    specialize (Fx_deriv _ zlta y) as dfx.
    apply is_derive_unique in dfx.
    match goal with
    | A : Derive ?P ?v = ?T |- _ => change (tx y = T) in A
    end.
    specialize (Fy_deriv _ zlta y) as dfy.
    apply is_derive_unique in dfy.
    match goal with
    | A : Derive ?P ?v = ?T |- _ => change (ty y = T) in A
    end.
    rewrite dfx, dfy, Rplus_comm, sin2_cos2.
    auto.
  Qed.
  
  Lemma anz : forall s,
      s <> 0 -> locally s (fun s : R => (Derive tx s)² + (Derive ty s)² <> 0).
  Proof.
    intros.
    assert (0 < Rabs s) as zltas. {
      unfold Rabs.
      destruct Rcase_abs; lra. }
    exists (mkposreal _ zltas).
    simpl.
    intros y baly.
    assert (y <> 0) as yne0. {
      intro yeq0.
      rewrite yeq0 in *.
      unfold ball in baly.
      simpl in baly.
      unfold AbsRing_ball, abs, minus, plus, opp in baly.
      simpl in baly.
      autorewrite with null in baly.
      rewrite Rabs_Ropp in baly.
      lra. }
    
    specialize (Fx_deriv2 _ zlta y) as d2fx.
    unfold is_derive_n, Derive_n in d2fx.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive tx y Q) in d2fx
     end).
    apply is_derive_unique in d2fx.
    
    specialize (Fy_deriv2 _ zlta y) as d2fy.
    unfold is_derive_n, Derive_n in d2fy.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive ty y Q) in d2fy
     end).
    apply is_derive_unique in d2fy.
    rewrite d2fx, d2fy.
    
    fieldrewrite
      ((- PI * y / (l a)² * sin (1 / 2 * PI * (y / l a)²))² +
       (PI * y / (l a)² * cos (1 / 2 * PI * (y / l a)²))²)
      ((y * PI * / (l a)²)² * ((sin (1 / 2 * PI * (y / l a)²))² +
                               (cos (1 / 2 * PI * (y / l a)²))²)).
    
    apply ane0_lane0; assumption.
    rewrite sin2_cos2.
    arn.
    specialize PI_RGT_0 as pigt0.
    apply Rmult_integral_contrapositive_currified;
      (apply Rmult_integral_contrapositive_currified;
       [apply Rmult_integral_contrapositive_currified; [assumption| lra] |
        apply Rinv_neq_0_compat;
        apply Rmult_integral_contrapositive_currified;
        apply ane0_lane0; assumption]).
  Qed.

  Lemma dtx :
    Derive tx = (fun y => - PI * y / (l a)² * sin (1 / 2 * PI * (y / l a)²)).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    specialize (Fx_deriv2 _ zlta x) as d2fx.
    unfold is_derive_n, Derive_n in d2fx.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive tx y Q) in d2fx
     end).
    apply is_derive_unique in d2fx.
    assumption.
  Qed.
  
  Lemma dty : 
    Derive ty = (fun y => PI * y / (l a)² * cos (1 / 2 * PI * (y / l a)²)).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    specialize (Fy_deriv2 _ zlta x) as d2y.
    unfold is_derive_n, Derive_n in d2y.
    (match goal with
     | A : is_derive ?P ?y ?Q |- _ => 
       change (is_derive ty y Q) in d2y
     end).
    apply is_derive_unique in d2y.
    assumption.
  Qed.

  Lemma dfx :
    Derive fx = (fun y => cos (1 / 2 * PI * (y / l a)²)).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    specialize (Fx_deriv _ zlta x) as d2fx.
    apply is_derive_unique in d2fx.
    assumption.
  Qed.
  
  Lemma dfy : 
    Derive fy = (fun y => sin (1 / 2 * PI * (y / l a)²)).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    specialize (Fy_deriv _ zlta x) as d2y.
    apply is_derive_unique in d2y.
    assumption.
  Qed.
  
  Lemma dts2id : forall s,
      (Derive tx s)² + (Derive ty s)² = (PI * s / (l a)²)².
  Proof.
    intro s0.
    rewrite dtx, dty.
    setl ((PI * s0 / (l a)²)² * ((sin (1 / 2 * PI * (s0 / l a)²))² +
                                 (cos (1 / 2 * PI * (s0 / l a)²))²)).
    apply ane0_lane0; assumption.
    rewrite sin2_cos2.
    field.
  Qed.

  Lemma ed2txk : forall s,
      s <> 0 ->
      locally s (fun s : R =>
                   ex_derive (fun s0 : R => / κ s0 * Derive tx s0) s).
  Proof.
    intros * sne0.
    unfold κ.
    assert (locally s (fun q =>
                         (fun s0 : R => / Rabs (s0) *
                                        - s0 * sin (1 / 2 * PI * (s0 / l a)²)) q
                         =
                         (fun s0 : R => / sqrt ((Derive tx s0)² + (Derive ty s0)²) *
                                        Derive tx s0) q
           )) as id2. {
      
      assert (0 < Rabs s) as zltas. {
        unfold Rabs.
        destruct Rcase_abs; lra. }
      exists (mkposreal _ zltas).
      simpl.
      intros y baly.
      assert (y <> 0) as yne0. {
        intro yeq0.
        rewrite yeq0 in *.
        unfold ball in baly.
        simpl in baly.
        unfold AbsRing_ball, abs, minus, plus, opp in baly.
        simpl in baly.
        autorewrite with null in baly.
        rewrite Rabs_Ropp in baly.
        lra. }
      
      rewrite dts2id.
      rewrite dtx, sqrt_Rsqr_abs.
      specialize PI_RGT_0 as pigt0.
      assert ((l a)² <> 0) as la2ne0. {
        apply Rmult_integral_contrapositive_currified;
          apply ane0_lane0; assumption. }
      assert (Rabs (PI * y / (l a)²) = PI * / (l a)² * Rabs y) as id3. {
          unfold Rabs.
          destruct Rcase_abs;
            destruct Rcase_abs.
          + lra.
          + exfalso.
            generalize r.
            change (~ (PI * y / (l a)² < 0)).
            apply Rle_not_lt.
            apply Rmult_le_pos.
            apply Rmult_le_pos; lra.
            left;
              apply Rinv_0_lt_compat;
              apply Rsqr_pos_lt;
              intro la0;
              apply la2ne0;
              rewrite la0;
              unfold Rsqr;
              lra.
          + exfalso.
            apply Rge_not_lt in r.
            apply r.
            setl (- (PI * - y / (l a)²)).
            intro lane0; apply la2ne0; rewrite lane0; unfold Rsqr; field.
            setr (- 0).
            apply Ropp_lt_contravar.
            apply Rmult_lt_0_compat.
            apply Rmult_lt_0_compat; try lra.
            apply Rinv_0_lt_compat;
              apply Rsqr_pos_lt;
              intro la0;
              apply la2ne0;
              rewrite la0;
              unfold Rsqr;
              lra.
          + lra. }
      rewrite id3.
      field.
      split.
      assumption.
      split.
      apply Rabs_no_R0.
      lra.
      lra. }

    clear - id2 zlta sne0.
    specialize (anz _ sne0) as anz.
    specialize dtx as dtx.
    specialize dty as dty.
    fllcb anz id2.
    csb zltrmpr.
    assert (locally y
                    (fun q : R =>
                       / Rabs q * - q * sin (1 / 2 * PI * (q / l a)²) =
                       / sqrt ((Derive tx q)² + (Derive ty q)²) * Derive tx q
           )) as id3. {
      specialize (b y sb).
      simpl in *.
      change (forall y, ball s epsq y ->
                        (fun q : R =>
                           / Rabs q * - q * sin (1 / 2 * PI * (q / l a)²) = 
                           / sqrt ((Derive tx q)² + (Derive ty q)²) * Derive tx q)
                          y) in restq.
      clear - restq b.
      reseat_locally restq. }
    
    apply (ex_derive_ext_loc _ _ _ id3).
    auto_derive.
    assert (y <> 0) as yne0. {
      specialize (restp y (a0 y sb)).
      clear - restp dtx dty zlta.
      intro yeq0.
      apply restp.
      rewrite dtx, dty.
      setl ((-( PI * y / (l a)²))² * ((sin (1 / 2 * PI * (y / l a)²))² +
                                      (cos (1 / 2 * PI * (y / l a)²))²)).
      apply (ane0_lane0 _ zlta).
      rewrite sin2_cos2.
      rewrite <- Rsqr_neg.
      arn.
      assert (PI * y / (l a)² = 0) as slr. {
        rewrite yeq0.
        setl (PI * 0 * / (l a)²).
        apply (ane0_lane0 _ zlta).
        arn.
        reflexivity. }
      rewrite slr.
      arn.
      field. }
    split; try assumption.
    split.
    intro ayeq0.
    apply yne0.
    apply Rabs_eq_0.
    assumption.
    constructor.
  Qed.

  Lemma ed2tyk : forall s,
      s <> 0 ->
      locally s
              (fun s : R =>
                 ex_derive (fun s0 : R => / κ s0 * Derive ty s0) s).
  Proof.
    intros * sne0.
    unfold κ.
    assert (locally s (fun q =>
                         (fun s0 : R => / Rabs (s0) *
                                        s0 * cos (1 / 2 * PI * (s0 / l a)²)) q
                         =
                         (fun s0 : R => / sqrt ((Derive tx s0)² + (Derive ty s0)²) *
                                        Derive ty s0) q
           )) as id2. {
      
      assert (0 < Rabs s) as zltas. {
        unfold Rabs.
        destruct Rcase_abs; lra. }
      exists (mkposreal _ zltas).
      simpl.
      intros y baly.
      assert (y <> 0) as yne0. {
        intro yeq0.
        rewrite yeq0 in *.
        unfold ball in baly.
        simpl in baly.
        unfold AbsRing_ball, abs, minus, plus, opp in baly.
        simpl in baly.
        autorewrite with null in baly.
        rewrite Rabs_Ropp in baly.
        lra. }

      rewrite dts2id.
      rewrite dty, sqrt_Rsqr_abs.
      specialize PI_RGT_0 as pigt0.
      assert ((l a)² <> 0) as la2ne0. {
        apply Rmult_integral_contrapositive_currified;
          apply ane0_lane0; assumption. }
      assert (Rabs (PI * y / (l a)²) = PI * / (l a)² * Rabs y) as id3. {
          unfold Rabs.
          destruct Rcase_abs;
            destruct Rcase_abs.
          + lra.
          + exfalso.
            generalize r.
            change (~ (PI * y / (l a)² < 0)).
            apply Rle_not_lt.
            apply Rmult_le_pos.
            apply Rmult_le_pos; lra.
            left;
              apply Rinv_0_lt_compat;
              apply Rsqr_pos_lt;
              intro la0;
              apply la2ne0;
              rewrite la0;
              unfold Rsqr;
              lra.
          + exfalso.
            apply Rge_not_lt in r.
            apply r.
            setl (- (PI * - y / (l a)²)).
            intro lane0; apply la2ne0; rewrite lane0; unfold Rsqr; field.
            setr (- 0).
            apply Ropp_lt_contravar.
            apply Rmult_lt_0_compat.
            apply Rmult_lt_0_compat; try lra.
            apply Rinv_0_lt_compat;
              apply Rsqr_pos_lt;
              intro la0;
              apply la2ne0;
              rewrite la0;
              unfold Rsqr;
              lra.
          + lra. }
      rewrite id3.
      field.
      split.
      assumption.
      split.
      apply Rabs_no_R0.
      lra.
      lra. }
    
    clear - id2 zlta sne0.
    specialize (anz _ sne0) as anz.
    specialize dtx as dtx.
    specialize dty as dty.
    fllcb anz id2.
    csb zltrmpr.
    assert (locally y
                    (fun q : R =>
                       / Rabs q * q * cos (1 / 2 * PI * (q / l a)²) =
                         / sqrt ((Derive tx q)² + (Derive ty q)²) * Derive ty q
           )) as id3. {
      specialize (b y sb).
      simpl in *.
      change (forall y, ball s epsq y ->
                        (fun q : R =>
                           / Rabs q * q * cos (1 / 2 * PI * (q / l a)²) = 
                           / sqrt ((Derive tx q)² + (Derive ty q)²) * Derive ty q)
                          y) in restq.
      clear - restq b.
      reseat_locally restq. }
    
    apply (ex_derive_ext_loc _ _ _ id3).
    auto_derive.
    assert (y <> 0) as yne0. {
      specialize (restp y (a0 y sb)).
      clear - restp dtx dty zlta.
      intro yeq0.
      apply restp.
      rewrite dtx, dty.
      setl ((-( PI * y / (l a)²))² * ((sin (1 / 2 * PI * (y / l a)²))² +
                                      (cos (1 / 2 * PI * (y / l a)²))²)).
      apply (ane0_lane0 _ zlta).
        rewrite sin2_cos2.
        rewrite <- Rsqr_neg.
        arn.
        assert (PI * y / (l a)² = 0) as slr. {
          rewrite yeq0.
        setl (PI * 0 * / (l a)²).
        apply (ane0_lane0 _ zlta).
        arn.
        reflexivity. }
      rewrite slr.
      arn.
      field. }
    split; try assumption.
    split.
    intro ayeq0.
    apply yne0.
    apply Rabs_eq_0.
    assumption.
    constructor.
  Qed.
  
  Definition oscr a s0 := / (a * s0).
  Definition occx a s0 :=
    let dx := Derive (Fx a) s0 in
    let dy := Derive (Fy a) s0 in
    Fx a s0 + - dy/sqrt (dy² + dx²) * oscr a s0.
  Definition occy a s0 :=
    let dx := Derive (Fx a) s0 in
    let dy := Derive (Fy a) s0 in
    Fy a s0 + dx/sqrt (dy² + dx²) * oscr a s0.

  Definition θt a s0 := atan2 (Derive (Fy a) s0) (Derive (Fx a) s0).
  Definition oscx a s0 := Fx a s0 - (oscr a s0) * sin (θt a s0).
  Definition oscy a s0 := Fy a s0 - (oscr a s0) * (1 - cos (θt a s0)).
  (* s0 is the transition point, p is the parameter *)
  Definition cxf a s0 p := (oscr a s0) * sin (/ (oscr a s0) * (p - s0) + θt a s0) + (oscx a s0).
  Definition cyf a s0 p := (oscr a s0) * (1 - cos (/ (oscr a s0) * (p - s0) + θt a s0)) + (oscy a s0).
  (* begin  hide *)
  Lemma posr : forall s,
      s <> 0 -> 
      Rabs (a * s) <> 0.
  Proof.
    intros *.
    intros sne0 rap0.
    apply sne0.
    clear sne0 ds mx my px py.
    destruct (total_order_T 0 s) as [[zlts|seq0]|zgts]; auto.
    + rewrite Rabs_right in rap0.
      ++ apply Rmult_integral in rap0.
         destruct rap0 as [aeq0 |seq0]; lra.
      ++ apply Rle_ge.
         zltab.
    + rewrite Rabs_left in rap0.
      ++ assert (a * -s = 0) as rap. lra.
         clear rap0.
         apply Rmult_integral in rap.
         destruct rap as [aeq0 |seq0]; lra.
      ++ apply Ropp_lt_cancel.
         setr (a * -s).
         arn.
         zltab.
  Qed.
  (* end hide *)

  Lemma circle_pos_arg_x : forall s (sne0 : s <> 0),
      (Fx a) s = (cxf a s) s.
  Proof.
    intros.
    unfold cxf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (x0 := Fx a s - oscr a s * sin (θ)).
    change (Fx a s = oscr a s * sin (/ oscr a s * (s - s) + θ) + x0).
    fieldrewrite (/ oscr a s * (s - s) + θ) θ.
    unfold oscr.
    unfold x0.
    zltab.
    match goal with
    | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
    | |- Rabs _ <> 0 => apply posr; try assumption
    end.
    apply (Rplus_eq_reg_r (- (oscr a s * sin θ))).
    rewrite pm.
    setr x0.
    unfold x0.
    reflexivity.
  Qed.

  Lemma circle_pos_arg_y : forall s (sne0 : s <> 0),
      (Fy a) s = (cyf a s) s.
  Proof.
    intros.
    unfold cyf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (y0 := Fy a s - oscr a s * (1 - cos (θ))).
    change (Fy a s = oscr a s * (1 - cos (/ oscr a s * (s - s) + θ)) + y0).
    fieldrewrite (/ oscr a s * (s - s) + θ) θ.
    unfold oscr.
    zltab.
    match goal with
    | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
    | |- Rabs _ <> 0 => apply posr; try assumption
    end.
    apply (Rplus_eq_reg_r (- (oscr a s * (1 - cos θ)))).
    rewrite pm.
    setr y0.
    unfold y0.
    reflexivity.
  Qed.


  Lemma circle_veloc_arg_x : forall s (sne0 : s <> 0),
      Derive (Fx a) s = Derive (cxf a s) s.
  Proof.
    intros.
    unfold cxf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (x0 := Fx a s - oscr a s * sin (θ)).
    set (y0 := Fy a s - oscr a s * (1 - cos (θ))).
    set (cx := (fun p => oscr a s * sin (/ oscr a s * (p - s) + θ) + x0)).
    set (cy := (fun p => oscr a s * (1 - cos (/ oscr a s * (p - s) + θ)) + y0)).

    assert (forall q, is_derive cx q (cos (/ oscr a s * (q - s) + θ))) as cxd;
      [intros; unfold cx; auto_derive;
       [constructor |
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end; assumption]|].
    assert (forall q, is_derive cy q (sin (/ oscr a s * (q - s) + θ))) as cyd;
      [intros; unfold cy; auto_derive;
       [constructor |
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end]|].
    specialize (cxd s).
    specialize (cyd s).
    apply is_derive_unique in cxd.
    apply is_derive_unique in cyd.
    match goal with
    | |- Derive ?a ?b = Derive ?c ?b =>
      change (Derive a b = Derive cx b)
    end.
    rewrite cxd.
    fieldrewrite (/ oscr a s * (s - s) + θ) (θ).
    unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end.
    specialize (Fx_deriv _ zlta s) as fxd.
    apply is_derive_unique in fxd.
    rewrite fxd.
    specialize (Fy_deriv _ zlta s) as fyd.
    apply is_derive_unique in fyd.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; try lra.
    specialize (inrange_mT2T2 (1 / 2 * PI * (s / l a)²) _ tpigt0) as [k [lb ub]].
    assert (- PI < 1 / 2 * PI * (s / l a)² + 2 * IZR k * PI) as lb0; try lra.
    clear lb.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI <= PI) as ub0; try lra.
    clear ub.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI =
            atan2 (Derive (Fy a) s) (Derive (Fx a) s)) as arg. {
      rewrite fxd, fyd.
      rewrite <- (Rmult_1_l (sin (1 / 2 * PI * (s / l a)²))).
      rewrite <- (Rmult_1_l (cos (1 / 2 * PI * (s / l a)²))).
      rewrite <- (sin_period1 _ k).
      rewrite <- (cos_period1 _ k).
      rewrite atan2_left_inv;
        [reflexivity|
         split; lra|
         lra]. }
    unfold θ.
    rewrite <- (cos_period1 _ k).
    rewrite arg.
    reflexivity.
  Qed.

  Lemma circle_veloc_arg_y : forall s (sne0 : s <> 0),
      Derive (Fy a) s = Derive (cyf a s) s.
  Proof.
    intros.

    unfold cyf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (x0 := Fx a s - oscr a s * sin (θ)).
    set (y0 := Fy a s - oscr a s * (1 - cos (θ))).
    set (cx := (fun p => oscr a s * sin (/ oscr a s * (p - s) + θ) + x0)).
    set (cy := (fun p => oscr a s * (1 - cos (/ oscr a s * (p - s) + θ)) + y0)).

    assert (forall q, is_derive cx q (cos (/ oscr a s * (q - s) + θ))) as cxd;
      [intros; unfold cx; auto_derive;
       [constructor|
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end] |].
    assert (forall q, is_derive cy q (sin (/ oscr a s * (q - s) + θ))) as cyd;
      [intros; unfold cy; auto_derive;
       [constructor|
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end]|].
    specialize (cxd s).
    specialize (cyd s).
    apply is_derive_unique in cxd.
    apply is_derive_unique in cyd.
    match goal with
    | |- Derive ?a ?b = Derive ?c ?b =>
      change (Derive a b = Derive cy b)
    end.
    rewrite cyd.
    fieldrewrite (/ oscr a s * (s - s) + θ) (θ).
    unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try assumption
        end.
    specialize (Fx_deriv _ zlta s) as fxd.
    apply is_derive_unique in fxd.
    specialize (Fy_deriv _ zlta s) as fyd.
    apply is_derive_unique in fyd.
    rewrite fyd.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; try lra.
    specialize (inrange_mT2T2 (1 / 2 * PI * (s / l a)²) _ tpigt0) as [k [lb ub]].
    assert (- PI < 1 / 2 * PI * (s / l a)² + 2 * IZR k * PI) as lb0; try lra.
    clear lb.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI <= PI) as ub0; try lra.
    clear ub.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI =
            atan2 (Derive (Fy a) s) (Derive (Fx a) s)) as arg. {
      rewrite fxd, fyd.
      rewrite <- (Rmult_1_l (sin (1 / 2 * PI * (s / l a)²))).
      rewrite <- (Rmult_1_l (cos (1 / 2 * PI * (s / l a)²))).
      rewrite <- (sin_period1 _ k).
      rewrite <- (cos_period1 _ k).
      rewrite atan2_left_inv;
        [reflexivity|
         split; lra|
         lra]. }
    unfold θ.
    rewrite <- (sin_period1 _ k).
    rewrite arg.
    reflexivity.
  Qed.

  Lemma circle_accel_arg_x : forall s (sne0 : 0 < s),
      Derive_n (Fx a) 2 s = Derive_n (cxf a s) 2 s.
  Proof.
    intros.

    unfold cxf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (x0 := Fx a s - oscr a s * sin (θ)).
    set (y0 := Fy a s - oscr a s * (1 - cos (θ))).
    set (cx := (fun p => oscr a s * sin (/ oscr a s * (p - s) + θ) + x0)).
    set (cy := (fun p => oscr a s * (1 - cos (/ oscr a s * (p - s) + θ)) + y0)).
    
    specialize (Fx_deriv _ zlta) as fxd.
    assert (Derive (Fx a) = (fun s => cos (1 / 2 * PI * (s / l a)²))) as fxde. {
      apply functional_extensionality.
      intro p.
      specialize (fxd p).
      apply is_derive_unique in fxd.
      assumption.  }
    clear fxd.

    specialize (Fx_deriv2 _ zlta) as fxd2.
    assert (Derive_n (Fx a) 2 = (fun s => - PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²))) as fxd2e. {
      apply functional_extensionality.
      intro p.
      specialize (fxd2 p).
      apply is_derive_unique in fxd2.
      assumption. }
    clear fxd2.

    specialize (Fy_deriv _ zlta) as fyd.
    assert (Derive (Fy a) = (fun s => sin (1 / 2 * PI * (s / l a)²))) as fyde. {
      apply functional_extensionality.
      intro p.
      specialize (fyd p).
      apply is_derive_unique in fyd.
      assumption.  }
    clear fyd.

    specialize (Fy_deriv2 _ zlta) as fyd2.
    assert (Derive_n (Fy a) 2 = (fun s => PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²))) as fyd2e. {
      apply functional_extensionality.
      intro p.
      specialize (fyd2 p).
      apply is_derive_unique in fyd2.
      assumption. }
    clear fyd2.

    assert (forall q, is_derive cx q (cos (/ oscr a s * (q - s) + θ))) as cxd;
      [intros; unfold cx; auto_derive;
       [constructor|
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end ] |].
    assert (Derive cx = fun q => (cos (/ oscr a s * (q - s) + θ))) as cxde. {
      apply functional_extensionality.
      intro p.
      specialize (cxd p).
      apply is_derive_unique.
      assumption. }
    clear cxd.

    assert (forall q, is_derive cy q (sin (/ oscr a s * (q - s) + θ))) as cyd;
      [intros; unfold cy; auto_derive;
       [constructor|
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end]|].
    assert (Derive cy = fun q => sin (/ oscr a s * (q - s) + θ)) as cyde. {
      apply functional_extensionality.
      intro p.
      specialize (cyd p).
      apply is_derive_unique.
      assumption. }
    clear cyd.

    assert (forall q, is_derive_n cx 2 q (- / oscr a s * sin (/ oscr a s * (q - s) + θ))) as cxd2. {
      intros.
      unfold is_derive_n, Derive_n.
      match goal with
      | |- is_derive ?a ?b ?c =>
        change (is_derive (Derive cx) b c)
      end.
      rewrite cxde.
      auto_derive.
      constructor.
      rewrite pm.
      field.
      unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end. }

    assert (Derive_n cx 2 = fun q => (- / oscr a s * sin (/ oscr a s * (q - s) + θ))) as cxd2e. {
      apply functional_extensionality.
      intro p.
      specialize (cxd2 p).
      apply is_derive_n_unique in cxd2.
      assumption. }
    clear cxd2.

    assert (forall q, is_derive_n cy 2 q (/ oscr a s * cos (/ oscr a s * (q - s) + θ))) as cyd2. {
      intros.
      unfold is_derive_n, Derive_n.
      match goal with
      | |- is_derive ?a ?b ?c =>
        change (is_derive (Derive cy) b c)
      end.
      rewrite cyde.
      auto_derive.
      constructor.
      rewrite pm.
      field.
      unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end. }

    assert (Derive_n cy 2 = fun q => (/ oscr a s * cos (/ oscr a s * (q - s) + θ))) as cyd2e. {
      apply functional_extensionality.
      intro p.
      specialize (cyd2 p).
      apply is_derive_n_unique in cyd2.
      assumption. }
    clear cyd2.

    match goal with
    | |- Derive_n ?a 2 ?b = Derive_n ?c 2 ?b =>
      change (Derive_n a 2 b = Derive_n cx 2 b)
    end.
    rewrite cxd2e, fxd2e.
    fieldrewrite (/ oscr a s * (s - s) + θ) (θ).
    unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end.
    
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; try lra.
    specialize (inrange_mT2T2 (1 / 2 * PI * (s / l a)²) _ tpigt0) as [k [lb ub]].
    assert (- PI < 1 / 2 * PI * (s / l a)² + 2 * IZR k * PI) as lb0; try lra.
    clear lb.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI <= PI) as ub0; try lra.
    clear ub.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI =
            atan2 (Derive (Fy a) s) (Derive (Fx a) s)) as arg. {
      rewrite fxde, fyde.
      rewrite <- (Rmult_1_l (sin (1 / 2 * PI * (s / l a)²))).
      rewrite <- (Rmult_1_l (cos (1 / 2 * PI * (s / l a)²))).
      rewrite <- (sin_period1 _ k).
      rewrite <- (cos_period1 _ k).
      rewrite atan2_left_inv;
        [reflexivity|
         split; lra|
         lra]. }
    unfold θ.
    rewrite <- (sin_period1 _ k).
    rewrite arg.
    unfold l.
    rewrite Rsqr_sqrt.
    unfold oscr.
    try rewrite Rabs_right.
    field.
    lra.
    try apply Rle_ge.
    repeat zltab.
  Qed.

  Lemma circle_accel_arg_y : forall s (sne0 : 0 < s),
      Derive_n (Fy a) 2 s = Derive_n (cyf a s) 2 s.
  Proof.
    intros.

    unfold cyf.
    set (θ := atan2 (Derive (Fy a) s) (Derive (Fx a) s)).
    set (x0 := Fx a s - oscr a s * sin (θ)).
    set (y0 := Fy a s - oscr a s * (1 - cos (θ))).
    set (cx := (fun p => oscr a s * sin (/ oscr a s * (p - s) + θ) + x0)).
    set (cy := (fun p => oscr a s * (1 - cos (/ oscr a s * (p - s) + θ)) + y0)).

    specialize (Fx_deriv _ zlta) as fxd.
    assert (Derive (Fx a) =
            (fun s => cos (1 / 2 * PI * (s / l a)²)))
      as fxde. {
      apply functional_extensionality.
      intro p.
      specialize (fxd p).
      apply is_derive_unique in fxd.
      assumption.  }
    clear fxd.
    
    specialize (Fx_deriv2 _ zlta) as fxd2.
    assert (Derive_n (Fx a) 2 =
            (fun s => - PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²)))
      as fxd2e. {
      apply functional_extensionality.
      intro p.
      specialize (fxd2 p).
      apply is_derive_unique in fxd2.
      assumption. }
    clear fxd2.

    specialize (Fy_deriv _ zlta) as fyd.
    assert (Derive (Fy a) =
            (fun s => sin (1 / 2 * PI * (s / l a)²)))
      as fyde. {
      apply functional_extensionality.
      intro p.
      specialize (fyd p).
      apply is_derive_unique in fyd.
      assumption.  }
    clear fyd.

    specialize (Fy_deriv2 _ zlta) as fyd2.
    assert (Derive_n (Fy a) 2 =
            (fun s => PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²)))
      as fyd2e. {
      apply functional_extensionality.
      intro p.
      specialize (fyd2 p).
      apply is_derive_unique in fyd2.
      assumption. }
    clear fyd2.

    assert (forall q, is_derive cx q (cos (/ oscr a s * (q - s) + θ)))
      as cxd; [intros; unfold cx; auto_derive;
               [constructor|
                rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end] |].
    assert (Derive cx = fun q => (cos (/ oscr a s * (q - s) + θ))) as cxde. {
      apply functional_extensionality.
      intro p.
      specialize (cxd p).
      apply is_derive_unique.
      assumption. }
    clear cxd.

    assert (forall q, is_derive cy q (sin (/ oscr a s * (q - s) + θ))) as cyd;
      [intros; unfold cy; auto_derive;
       [constructor|
        rewrite pm; field; unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end]|].
    assert (Derive cy = fun q => sin (/ oscr a s * (q - s) + θ)) as cyde. {
      apply functional_extensionality.
      intro p.
      specialize (cyd p).
      apply is_derive_unique.
      assumption. }
    clear cyd.

    assert (forall q, is_derive_n cx 2 q (- / oscr a s * sin (/ oscr a s * (q - s) + θ))) as cxd2. {
      intros.
      unfold is_derive_n, Derive_n.
      match goal with
      | |- is_derive ?a ?b ?c =>
        change (is_derive (Derive cx) b c)
      end.
      rewrite cxde.
      auto_derive.
      constructor.
      rewrite pm.
      field.
      unfold oscr; zltab;
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end. }

    assert (Derive_n cx 2 = fun q => (- / oscr a s * sin (/ oscr a s * (q - s) + θ))) as cxd2e. {
      apply functional_extensionality.
      intro p.
      specialize (cxd2 p).
      apply is_derive_n_unique in cxd2.
      assumption. }
    clear cxd2.

    assert (forall q, is_derive_n cy 2 q (/ oscr a s * cos (/ oscr a s * (q - s) + θ))) as cyd2. {
      intros.
      unfold is_derive_n, Derive_n.
      match goal with
      | |- is_derive ?a ?b ?c =>
        change (is_derive (Derive cy) b c)
      end.
      rewrite cyde.
      auto_derive.
      constructor.
      rewrite pm.
      field.
      unfold oscr; zltab; 
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end. }

    assert (Derive_n cy 2 = fun q => (/ oscr a s * cos (/ oscr a s * (q - s) + θ))) as cyd2e. {
      apply functional_extensionality.
      intro p.
      specialize (cyd2 p).
      apply is_derive_n_unique in cyd2.
      assumption. }
    clear cyd2.

    match goal with
    | |- Derive_n ?a 2 ?b = Derive_n ?c 2 ?b =>
      change (Derive_n a 2 b = Derive_n cy 2 b)
    end.
    rewrite cyd2e, fyd2e.
    fieldrewrite (/ oscr a s * (s - s) + θ) (θ).
    unfold oscr; zltab; 
        match goal with
        | |- _ * _ <> 0 => apply Rmult_integral_contrapositive_currified; lra
        | |- Rabs _ <> 0 => apply posr; try lra
        end.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; try lra.
    specialize (inrange_mT2T2 (1 / 2 * PI * (s / l a)²) _ tpigt0) as [k [lb ub]].
    assert (- PI < 1 / 2 * PI * (s / l a)² + 2 * IZR k * PI) as lb0; try lra.
    clear lb.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI <= PI) as ub0; try lra.
    clear ub.
    assert (1 / 2 * PI * (s / l a)² + 2 * IZR k * PI =
            atan2 (Derive (Fy a) s) (Derive (Fx a) s)) as arg. {
      rewrite fxde, fyde.
      rewrite <- (Rmult_1_l (sin (1 / 2 * PI * (s / l a)²))).
      rewrite <- (Rmult_1_l (cos (1 / 2 * PI * (s / l a)²))).
      rewrite <- (sin_period1 _ k).
      rewrite <- (cos_period1 _ k).
      rewrite atan2_left_inv;
        [reflexivity|
         split; lra|
         lra]. }
    unfold θ.
    rewrite <- (cos_period1 _ k).
    rewrite arg.
    unfold l.
    rewrite Rsqr_sqrt.
    unfold oscr.
    try rewrite Rabs_right.
    field.
    lra.
    try apply Rle_ge.
    repeat zltab.
  Qed.

(* begin hide *)
  Lemma x2eq0implxeq0 : forall x,
      x² = 0 -> x = 0.
  Proof.
    intros.
    unfold Rsqr in H.
    apply Rmult_integral in H.
    destruct H; assumption.
  Qed.
  
(* end hide *)
  Lemma osc_circ_equiv : forall s s0,
      (cxf a s0 s - occx a s0)² +
      (cyf a s0 s - occy a s0)² = (oscr a s0)².
  Proof.
    intros.
    unfold cxf, cyf, occx, occy, oscx, oscy, θt.
    set (fx := Fx a) in *.
    set (fy := Fy a) in *.
    set (dfx := Derive fx s0) in *.
    set (dfy := Derive fy s0) in *.
    unfold atan2.
    destruct pre_atan2 as [q [qrng [dy dx]]].

    set (M := sqrt (dfy² + dfx²)) in *.
    assert (0 < M) as zltm. {
      unfold M, dfy, dfx, fx, fy.
      clear - zlta.
      apply sqrt_lt_R0.
      specialize (Fx_deriv _ zlta s0) as Fxd.
      specialize (Fy_deriv _ zlta s0) as Fyd.
      apply is_derive_unique in Fxd.
      apply is_derive_unique in Fyd.
      rewrite Fxd, Fyd.

      specialize (Rle_0_sqr (sin (1 / 2 * PI * (s0 / l a)²))) as c2g0.
      specialize (Rle_0_sqr (cos (1 / 2 * PI * (s0 / l a)²))) as s2g0.
      destruct c2g0 as [cge0 |ceq0].
      apply Rplus_lt_le_0_compat; try assumption.
      destruct s2g0 as [sge0 |seq0].
      apply Rplus_le_lt_0_compat; try lra.
      exfalso.
      symmetry in ceq0, seq0.
      apply x2eq0implxeq0 in ceq0.
      apply x2eq0implxeq0 in seq0.
      specialize (cos_sin_0 (1 / 2 * PI * (s0 / l a)²)) as ncs0.
      apply ncs0.
      split; assumption. }

    rewrite dx, dy.
    fieldrewrite (oscr a s0 * sin (/ oscr a s0 * (s - s0) + q) +
                  (fx s0 - oscr a s0 * sin q) -
                  (fx s0 + - (M * sin q) / M * oscr a s0))
                 (oscr a s0 * sin (/ oscr a s0 * (s - s0) + q));
      try lra.
    fieldrewrite (oscr a s0 * (1 - cos (/ oscr a s0 * (s - s0) + q)) +
                  (fy s0 - oscr a s0 * (1 - cos q)) -
                  (fy s0 + M * cos q / M * oscr a s0))
                 (oscr a s0 * (- cos (/ oscr a s0 * (s - s0) + q)));
      try lra.
    repeat rewrite Rsqr_mult.
    rewrite <- Rsqr_neg, <- Rmult_plus_distr_l, sin2_cos2.
    field.
  Qed.

  Lemma egeof_dNy_eq_nkTy : forall (s:R) (sne0:s<>0),
      Derive ny s = - κ s * ty s.
  Proof.
    intros.
    specialize  (dNy_eq_nkTy s fx fy (edtx s) (edty s) (uv s)
                             (anz s sne0) (ed2txk s sne0) (ed2tyk s sne0))
      as id2.
    destruct id2 as [e id2].
    specialize (id2 s ltac:(apply ball_center)).
    assumption.
  Qed.

  Lemma egeof_dNx_eq_nkTx : forall (s:R) (sne0:s<>0),
      Derive nx s = - κ s * tx s.
  Proof.
    intros.
    specialize (dNx_eq_nkTx s fx fy (edtx s) (edty s) (uv s)
                            (anz s sne0) (ed2txk s sne0) (ed2tyk s sne0))
      as id2.
    destruct id2 as [e id2].
    specialize (id2 s ltac:(apply ball_center)).
    assumption.
  Qed.
(* begin hide *)
  Lemma circle_geometry_trans : forall x0 y0 r0 x1 y1 x y,
      (x - x0)² + (y - y0)² < r0² <-> 
      ((x - x1) - (x0 - x1))² + ((y - y1) - (y0 - y1))² < r0².
  Proof.
    intros *.
    split.
    + intro sc.
      fieldrewrite (x - x1 - (x0 - x1)) (x - x0).
      fieldrewrite (y - y1 - (y0 - y1)) (y - y0).
      assumption.
    + intro sc.
      fieldrewrite (x - x0) (x - x1 - (x0 - x1)).
      fieldrewrite (y - y0) (y - y1 - (y0 - y1)).
      assumption.
  Qed.

  Lemma circle_geometry_rot : forall x0 y0 r0 x y θ,
      let rx := fun x y => x * cos θ + y * sin θ in
      let ry := fun x y => - x * sin θ + y * cos θ in
      (x - x0)² + (y - y0)² < r0² <-> 
      (rx x y - rx x0 y0)² + (ry x y - ry x0 y0)² < r0².
  Proof.
    intros *.
    split.
    + intro ic.
      unfold rx, ry.
      repeat rewrite Rsqr_minus.
      repeat rewrite Rsqr_plus.
      set (C := cos θ).
      set (S := sin θ).
      setl (x² * (S² + C²) + y² * (S² + C²) + x0² * (S² + C²) + y0² * (S² + C²)
            - 2 * (x * x0 * (S² + C²) + y * y0 * (S² + C²))).
      unfold S, C.
      rewrite sin2_cos2.
      arn.
      lrag ic.
    + intro ic.
      unfold rx, ry in ic.
      repeat rewrite Rsqr_minus in ic.
      repeat rewrite Rsqr_plus in ic.
      set (C := cos θ) in *.
      set (S := sin θ) in *.
      assert (x² * (S² + C²) + y² * (S² + C²) + x0² * (S² + C²) + y0² * (S² + C²)
            - 2 * (x * x0 * (S² + C²) + y * y0 * (S² + C²)) < r0²) as id. {
        lrag ic. }
      unfold S, C in id.
      rewrite sin2_cos2 in id.
      lrag id.
  Qed.

  Lemma circle_geometry_rot_le : forall x0 y0 r0 x y θ,
      let rx := fun x y => x * cos θ + y * sin θ in
      let ry := fun x y => - x * sin θ + y * cos θ in
      (x - x0)² + (y - y0)² <= r0² <-> 
      (rx x y - rx x0 y0)² + (ry x y - ry x0 y0)² <= r0².
  Proof.
    intros *.
    split.
    + intro ic.
      unfold rx, ry.
      repeat rewrite Rsqr_minus.
      repeat rewrite Rsqr_plus.
      set (C := cos θ).
      set (S := sin θ).
      setl (x² * (S² + C²) + y² * (S² + C²) + x0² * (S² + C²) + y0² * (S² + C²)
            - 2 * (x * x0 * (S² + C²) + y * y0 * (S² + C²))).
      unfold S, C.
      rewrite sin2_cos2.
      arn.
      lrag ic.
    + intro ic.
      unfold rx, ry in ic.
      repeat rewrite Rsqr_minus in ic.
      repeat rewrite Rsqr_plus in ic.
      set (C := cos θ) in *.
      set (S := sin θ) in *.
      assert (x² * (S² + C²) + y² * (S² + C²) + x0² * (S² + C²) + y0² * (S² + C²)
            - 2 * (x * x0 * (S² + C²) + y * y0 * (S² + C²)) <= r0²) as id. {
        lrag ic. }
      unfold S, C in id.
      rewrite sin2_cos2 in id.
      lrag id.
  Qed.

  
  Lemma align_x_rot : forall x0 y0,
      let θ := atan2 y0 x0 in
      let ry := fun x y => - x * sin θ + y * cos θ in
      ~ (x0 = 0 /\ y0 = 0) -> ry x0 y0 = 0.
  Proof.
    intros.
    unfold ry, θ.
    rewrite atan2_sin_id, atan2_cos_id; try assumption.
    lra.
  Qed.
  
  Lemma circle_geometry_std_pos : forall x0 r0 r1 x y,
      0 < r1 < r0 ->
      0 <= x0 ->
      x² + y² <= r1² ->
      x0² < (r0 - r1)² ->
      (x - x0)² + y² < r0².
  Proof.
    intros *.
    intros [zltr1 r1ltr0] zltx0 isc ssc.
    repeat rewrite Rsqr_minus.
    setl ((x² + y²) + x0² - 2 * x * x0).
    apply (Rle_lt_trans _ (r1² + x0² - 2 * x * x0)).
    apply (Rplus_le_reg_r (- x0² + 2 * x * x0)).
    lrag isc.
    apply (Rlt_trans _ (r1² + (r0 - r1)² - 2 * x * x0)).
    apply (Rplus_lt_reg_r (- r1² + 2 * x * x0)).
    lrag ssc.
    rewrite Rsqr_minus.
    apply (Rplus_lt_reg_r (- r0²)).
    setr (2 * 0).
    setl (2 * (r1² - r0 * r1 - x * x0)).
    apply Rmult_lt_compat_l; try lra.
    apply (Rplus_lt_reg_r (x * x0)).
    setl (- (r1 * (r0 - r1))).
    arn.
    destruct (Rle_dec 0 x).
    + apply (Rlt_le_trans _ (-0)).
      apply Ropp_lt_contravar.
      apply Rmult_lt_0_compat; lra.
      setl 0.
      apply Rmult_le_pos;
        assumption.
    + apply Rnot_le_lt in n.
      destruct zltx0 as [zltx0 |zeqx0].
      ++ setr (- ((-x)*x0)).
         apply Ropp_lt_contravar.
         apply Rsqr_incrst_0 in ssc; try lra.
         apply (Rle_lt_trans _ (r1 * x0));
           [| apply Rmult_lt_compat_l;
              assumption].
         apply Rmult_le_compat_r.
         lra.
         rewrite <- Rabs_left; try assumption.
         rewrite <- (Rabs_right r1); try lra.
         apply Rsqr_le_abs_0.
         apply (Rle_trans _ (x² + y²)); try assumption.
         apply (Rplus_le_reg_r (-x²)).
         setl 0.
         setr (y²).
         apply Rle_0_sqr.
      ++ subst.
         setr (- 0).
         apply Ropp_lt_contravar.
         apply Rmult_lt_0_compat.
         assumption.
         lra.
  Qed.

  Lemma circle_geometry_std_neg : forall x0 r0 r1 x y,
      0 < r1 < r0 ->
      x0 < 0 ->
      x² + y² <= r1² ->
      x0² < (r0 - r1)² ->
      (x - x0)² + y² < r0².
  Proof.
    intros *.
    intros zltr1ltr0 zltx0 isc ssc.
    set (x0' := -x0).
    set (x' := -x).
    assert (0 <= x0'); try (unfold x0'; lra).
    setl (((-x) - (-x0))² + y²).
    change ((x' - x0')² + y² < r0²).
    rewrite (Rsqr_neg x) in isc.
    rewrite (Rsqr_neg x0) in ssc.
    eapply circle_geometry_std_pos.
    apply zltr1ltr0.
    assumption.
    assumption.
    assumption.
  Qed.

  
  Lemma circle_geometry_std : forall x0 r0 r1 x y,
      0 < r1 < r0 ->
      x² + y² <= r1² ->
      x0² < (r0 - r1)² ->
      (x - x0)² + y² < r0².
  Proof.
    intros.
    destruct (Rle_dec 0 x0).
    eapply circle_geometry_std_pos;[apply H | | | ]; try assumption.
    apply Rnot_le_lt in n.
    eapply circle_geometry_std_neg;[apply H | | | ]; try assumption.
  Qed.
  
  Lemma circle_geometry_ncoinc : forall x0 y0 r0 x1 y1 r1 x y,
      ~ (x0 - x1 = 0 /\ y0 - y1 = 0) ->
      0 < r1 < r0 -> 
      (x - x1)² + (y - y1)² <= r1² ->
      (x0 - x1)² + (y0 - y1)² < (r0 - r1)² ->
      (x - x0)² + (y - y0)² < r0².
  Proof.
    intros *.
    intros nc [zltr1 r1ltr0] isc ssc.
    rewrite (circle_geometry_trans _ _ _ x1 y1).
    set (x' := x-x1) in *.
    set (y' := y-y1) in *.
    set (x0' := x0-x1) in *.
    set (y0' := y0-y1) in *.
    destruct (Req_dec y0' 0) as [y0'eq0 | y0'ne0].
    + rewrite y0'eq0 in *.
      autorewrite with null in *.
      eapply circle_geometry_std.
      split.
      apply zltr1.
      assumption.
      assumption.
      assumption.
    + set (θ := atan2 y0' x0').
      rewrite (circle_geometry_rot _ _ _ _ _ θ).
      rewrite <- (Rminus_0_r x'), <- (Rminus_0_r y') in isc.
      rewrite (circle_geometry_rot_le _ _ _ _ _ θ) in isc.
      set (x'' := x' * cos θ + y' * sin θ) in *.
      set (y'' := - x' * sin θ + y' * cos θ) in *.
      autorewrite with null in isc.
      set (x0'' := x0' * cos θ + y0' * sin θ) in *.
      set (y0'' := - x0' * sin θ + y0' * cos θ) in *.
      eapply circle_geometry_std.
      split.
      apply zltr1.
      assumption.
      assert (y0'' = 0) as id. {
        apply (align_x_rot x0' y0').
        assumption. }
      rewrite id.
      arn.
      assumption.
      clear - ssc nc.
      unfold x0''.
      clear x0''.
      unfold θ.
      rewrite atan2_sin_id, atan2_cos_id; try assumption.
      repeat rewrite <- Rsqr_pow2.
      setl (((x0'² + y0'²) * / sqrt (x0'² + y0'²))²).
      apply posss in nc;
      intro sseq0;
      apply sqrt_eq_0 in sseq0;
        [unfold Rsqr in nc;
         rewrite sseq0 in nc;
         lra|
         unfold Rsqr in nc;
         left; assumption].
      rewrite Rsqr_mult, Rsqr_inv, Rsqr_sqrt.
      setl (x0'² + y0'²).
      apply posss in nc.
      intro sseq0.
      unfold Rsqr in nc;
        rewrite sseq0 in nc;
        lra.
      assumption.
      apply posss in nc.
      left; assumption.
      unfold Rsqr.
      apply posss in nc;
      intro sseq0;
      apply sqrt_eq_0 in sseq0;
        [unfold Rsqr in nc;
         rewrite sseq0 in nc;
         lra|
         unfold Rsqr in nc;
         left; assumption].
  Qed.

  Lemma circle_geometry_coinc : forall x0 y0 r0 x1 y1 r1 x y,
      (x0 - x1 = 0 /\ y0 - y1 = 0) ->
      0 < r1 < r0 -> 
      (x - x1)² + (y - y1)² <= r1² ->
      (x0 - x1)² + (y0 - y1)² < (r0 - r1)² ->
      (x - x0)² + (y - y0)² < r0².
  Proof.
    intros *.
    intros [ncx ncy] [zltr1 r1ltr0] isc ssc.
    rewrite ncx, ncy in ssc.
    apply Rminus_diag_uniq in ncx.
    apply Rminus_diag_uniq in ncy.
    rewrite ncx, ncy in *.
    apply (Rle_lt_trans _ (r1²)).
    assumption.
    apply Rsqr_incrst_1.
    assumption.
    left; assumption.
    lra.
  Qed.
(* end hide *)

  Lemma circle_geometry : forall x0 y0 r0 x1 y1 r1 x y,
      0 < r1 < r0 -> 
      (x - x1)² + (y - y1)² <= r1² ->
      (x0 - x1)² + (y0 - y1)² < (r0 - r1)² ->
      (x - x0)² + (y - y0)² < r0².
  Proof.
    intros *.
    destruct (Req_dec (x0 - x1) 0) as [x1x00 | x1x0ne0].
    destruct (Req_dec (y0 - y1) 0) as [y1y00 | y1y0ne0].
    assert (x0 - x1 = 0 /\ y0 - y1 = 0) as coinc; try lra.
    apply circle_geometry_coinc; assumption.
    assert (~(x0 - x1 = 0 /\ y0 - y1 = 0)) as ncoinc; try lra.
    apply circle_geometry_ncoinc; assumption.
    assert (~(x0 - x1 = 0 /\ y0 - y1 = 0)) as ncoinc; try lra.
    apply circle_geometry_ncoinc; assumption.
  Qed.    

  Lemma kdef_poss : forall s,
      0 < s -> κ s = / oscr a s.
  Proof.
    intros * zles.
    specialize PI_RGT_0 as pigt0.
    unfold oscr.
    rewrite Rinv_involutive.
    unfold κ, tx, ty.
    specialize (Fx_deriv2 _ zlta s) as fxd.
    apply is_derive_unique in fxd.
    specialize (Fy_deriv2 _ zlta s) as fyd.
    apply is_derive_unique in fyd.
    unfold Derive_n in fxd, fyd.
    assert ((fun x : R => Derive (fun x0 : R => Fx a x0) x) = Derive (Fx a)) as xd. {
      apply functional_extensionality.
      intros.
      assert ((fun x0 : R => Fx a x0) = (Fx a)) as xd2.
      apply functional_extensionality.
      intros.
      reflexivity.
      rewrite xd2.
      reflexivity. }
    rewrite xd in fxd; clear xd.

    assert ((fun x : R => Derive (fun x0 : R => Fy a x0) x) = Derive (Fy a)) as yd. {
      apply functional_extensionality.
      intros.
      assert ((fun x0 : R => Fy a x0) = (Fy a)) as yd2.
      apply functional_extensionality.
      intros.
      reflexivity.
      rewrite yd2.
      reflexivity. }
    rewrite yd in fyd; clear yd.

    specialize (agt0_lagt0 _ zlta) as zltla.
    unfold fx, fy.
    rewrite fxd, fyd.
    fieldrewrite ((- PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²))² +
                  (PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²))²)
                 ((PI * s / (l a)²)² * ((sin (1 / 2 * PI * (s / l a)²))² +
                                        (cos (1 / 2 * PI * (s / l a)²))²)).
    lra.
    rewrite sin2_cos2.
    arn.
    rewrite sqrt_Rsqr.
    rewrite <- RmultRinv.
    apply (Rmult_eq_reg_r ((l a)²)).
    setl (PI * s); try lra.
    unfold l.
    rewrite Rsqr_sqrt.
    field.
    lra.
    rewrite <- RmultRinv.
    left.
    apply Rlt_mult_inv_pos.
    lra.
    assumption.
    apply Rmult_integral_contrapositive.
    split; lra.

    apply Rmult_le_pos.
    apply Rmult_le_pos.
    lra.
    left; assumption.
    left.
    apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; assumption.
    apply Rmult_integral_contrapositive_currified; lra.
  Qed.

  Lemma kpos_poss : forall s,
      0 < s -> 0 < κ s.
  Proof.
    intros.
    rewrite kdef_poss; try assumption.
    unfold oscr.
    rewrite Rinv_involutive.
    apply Rmult_lt_0_compat; assumption.
    apply Rmult_integral_contrapositive_currified; lra.
  Qed.

  Lemma kdef_negs : forall s,
      s < 0 -> - κ s = / oscr a s.
  Proof.
    intros * zles.
    specialize PI_RGT_0 as pigt0.
    unfold oscr.
    rewrite Rinv_involutive.
    unfold κ, tx, ty.
    specialize (Fx_deriv2 _ zlta s) as fxd.
    apply is_derive_unique in fxd.
    specialize (Fy_deriv2 _ zlta s) as fyd.
    apply is_derive_unique in fyd.
    unfold Derive_n in fxd, fyd.
    assert ((fun x : R => Derive (fun x0 : R => Fx a x0) x) = Derive (Fx a)) as xd. {
      apply functional_extensionality.
      intros.
      assert ((fun x0 : R => Fx a x0) = (Fx a)) as xd2.
      apply functional_extensionality.
      intros.
      reflexivity.
      rewrite xd2.
      reflexivity. }
    rewrite xd in fxd; clear xd.

    assert ((fun x : R => Derive (fun x0 : R => Fy a x0) x) = Derive (Fy a)) as yd. {
      apply functional_extensionality.
      intros.
      assert ((fun x0 : R => Fy a x0) = (Fy a)) as yd2.
      apply functional_extensionality.
      intros.
      reflexivity.
      rewrite yd2.
      reflexivity. }
    rewrite yd in fyd; clear yd.

    specialize (agt0_lagt0 _ zlta) as zltla.
    unfold fx, fy.
    rewrite fxd, fyd.
    fieldrewrite ((- PI * s / (l a)² * sin (1 / 2 * PI * (s / l a)²))² +
                  (PI * s / (l a)² * cos (1 / 2 * PI * (s / l a)²))²)
                 ((PI * s / (l a)²)² * ((sin (1 / 2 * PI * (s / l a)²))² +
                                        (cos (1 / 2 * PI * (s / l a)²))²)).
    lra.
    rewrite sin2_cos2.
    arn.
    fieldrewrite ((PI * s / (l a)²)²)
                 ((PI * (-s) / (l a)²)²); try lra.
    rewrite sqrt_Rsqr.
    rewrite <- RmultRinv.
    apply (Rmult_eq_reg_r ((l a)²)).
    setl (PI * s); try lra.
    unfold l.
    rewrite Rsqr_sqrt.
    field.
    lra.
    rewrite <- RmultRinv.
    left.
    apply Rlt_mult_inv_pos.
    lra.
    assumption.
    apply Rmult_integral_contrapositive.
    split; lra.

    apply Rmult_le_pos.
    apply Rmult_le_pos.
    lra.
    left; lra.
    left.
    apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; assumption.
    apply Rmult_integral_contrapositive_currified; lra.
  Qed.

  Lemma egeof_Ny_eq_Tx : forall (s:R) (zlts : 0 < s),
      ny s = tx s.
  Proof.
    intros * zlts.
    unfold ny, tx.
    rewrite dty, dfx.
    specialize (kpos_poss s zlts) as kps.
    rewrite (kdef_poss s zlts) in *.
    unfold oscr in *.
    rewrite Rinv_involutive in kps;
      [|apply Rmult_integral_contrapositive_currified; lra].
    rewrite Rinv_involutive;
      [|apply Rinv_neq_0_compat; lra].
    specialize PI_RGT_0 as pigt0.
    unfold l at 1.
    rewrite Rsqr_sqrt.
    2 : {
      setr (PI * / a); try lra.
      left;
        apply Rmult_lt_0_compat;
        [|apply Rinv_0_lt_compat]; lra. }
    fieldrewrite (/ (a * s) * (PI * s / (PI / a) *
                               cos (1 / 2 * PI * (s / l a)²))) (
                   cos (1 / 2 * PI * (s / l a)²)).
    lra.
    reflexivity.
  Qed.

  Lemma egeof_Nx_eq_nTy : forall (s:R) (zlts : 0 < s),
      nx s = - ty s.
  Proof.
    intros * zlts.
    unfold nx, ty.
    rewrite dtx, dfy.
    specialize (kpos_poss s zlts) as kps.
    rewrite (kdef_poss s zlts) in *.
    unfold oscr in *.
    rewrite Rinv_involutive in kps;
      [|apply Rmult_integral_contrapositive_currified; lra].
    rewrite Rinv_involutive;
      [|apply Rinv_neq_0_compat; lra].
    specialize PI_RGT_0 as pigt0.
    unfold l at 1.
    rewrite Rsqr_sqrt.
    2 : {
      setr (PI * / a); try lra.
      left;
        apply Rmult_lt_0_compat;
        [|apply Rinv_0_lt_compat]; lra. }
    fieldrewrite (/ (a * s) * (- PI * s / (PI / a) *
                                 sin (1 / 2 * PI * (s / l a)²)))
    (- sin (1 / 2 * PI * (s / l a)²)).
    lra.
    reflexivity.
  Qed.

  Lemma occx_def : forall (s:R) (zlts : 0 < s),
      occx a s = fx s + nx s * oscr a s.
  Proof.
    intros.
    unfold occx.
    change (fx s + - ty s / sqrt ((Derive fy s)² + (Derive fx s)²) *
                     oscr a s = fx s + nx s * oscr a s).
    specialize (uv s) as [e luv].
    specialize (luv s ltac:(apply ball_center)).
    unfold tx, ty in luv.
    rewrite Rplus_comm in luv.
    rewrite luv, sqrt_1, egeof_Nx_eq_nTy; try assumption.
    field.
  Qed.

  Lemma occy_def : forall (s:R) (zlts : 0 < s),
      occy a s = fy s + ny s * oscr a s.
  Proof.
    intros.
    unfold occy.
    change (fy s + tx s / sqrt ((Derive fy s)² + (Derive fx s)²) *
                     oscr a s = fy s + ny s * oscr a s).
    specialize (uv s) as [e luv].
    specialize (luv s ltac:(apply ball_center)).
    unfold tx, ty in luv.
    rewrite Rplus_comm in luv.
    rewrite luv, sqrt_1, egeof_Ny_eq_Tx; try assumption.
    field.
  Qed.

  Lemma d_evolute_x : forall s,
      0 < s ->
      Derive (occx a) s = Derive (oscr a) s * nx s.
  Proof.
    intros * zlts.
    unfold magnitude, comp, plus_fct.
    specialize occx_def as ocxd.
    assert (locally s (fun s => fx s + nx s * oscr a s = occx a s)) as ocxid. {
      exists (mkposreal _ zlts).
      simpl.
      intros * bssy.
      assert (0 < y) as zlty. {
        clear - bssy.
        unfold ball in bssy.
        simpl in bssy.
        unfold AbsRing_ball, abs, minus, plus, opp in bssy.
        simpl in bssy.
        unfold Rabs in bssy.
        destruct Rcase_abs;
          lra. }
      symmetry; apply ocxd; assumption. }

    assert (is_derive (occx a) s
                      (Derive fx s + Derive nx s * oscr a s + nx s * Derive (oscr a) s))
      as docxs. {
      apply (is_derive_ext_loc _ _ _ _ ocxid).
      simpl.
      auto_derive.
      + split.
        specialize (Fx_deriv a zlta s) as fxd.
        match goal with
        | fxd : is_derive ?A ?s ?B |- _=> change (is_derive fx s B) in fxd; exists B
        end.
        assumption.
        
        split.
        change (ex_derive nx s).
        unfold nx.
        assert (s <> 0) as sne0; try lra.
        specialize (ed2txk _ sne0) as [e ednx].
        specialize (ednx s ltac:(apply ball_center)).
        assumption.
        
        split; try constructor.
        change (ex_derive (oscr a) s).
        unfold oscr.
        auto_derive.
        intro aseq0.
        apply Rmult_integral in aseq0.
        destruct aseq0 ; lra.

      + change (1 * Derive fx s +
                (1 * Derive nx s * oscr a s +
                 nx s * (1 * Derive (oscr a) s)) =
                Derive fx s + Derive nx s * oscr a s + nx s * Derive (oscr a) s).
        field. }
    apply is_derive_unique in docxs.
    rewrite docxs.
    assert (s <> 0) as sne0; try lra.
    repeat rewrite (egeof_dNx_eq_nkTx _ sne0).
    rewrite kdef_poss; try assumption.
    setl (Derive fx s + - tx s + nx s * Derive (oscr a) s).
    unfold oscr.
    apply Rinv_neq_0_compat.
    apply Rmult_integral_contrapositive_currified; lra.

    unfold tx.
    field.
  Qed.

  Lemma d_evolute_y : forall s,
      0 < s ->
      Derive (occy a) s = Derive (oscr a) s * ny s.
  Proof.
    intros * zlts.
    unfold magnitude, comp, plus_fct.

    specialize occy_def as ocyd.
    assert (locally s (fun s => fy s + ny s * oscr a s = occy a s)) as ocyid. {
      exists (mkposreal _ zlts).
      simpl.
      intros * bssy.
      assert (0 < y) as zlty. {
        clear - bssy.
        unfold ball in bssy.
        simpl in bssy.
        unfold AbsRing_ball, abs, minus, plus, opp in bssy.
        simpl in bssy.
        unfold Rabs in bssy.
        destruct Rcase_abs;
          lra. }
      symmetry; apply ocyd; assumption. }

    assert (is_derive (occy a) s
                      (Derive fy s + Derive ny s * oscr a s + ny s * Derive (oscr a) s))
      as docys. {
      apply (is_derive_ext_loc _ _ _ _ ocyid).
      simpl.
      auto_derive.
      + split.
        specialize (Fy_deriv a zlta s) as fyd.
        match goal with
        | fyd : is_derive ?A ?s ?B |- _=> change (is_derive fy s B) in fyd; exists B
        end.
        assumption.
        
        split.
        change (ex_derive ny s).
        unfold nx.
        assert (s <> 0) as sne0; try lra.
        specialize (ed2tyk _ sne0) as [e edny].
        specialize (edny s ltac:(apply ball_center)).
        assumption.
        
        split; try constructor.
        change (ex_derive (oscr a) s).
        unfold oscr.
        auto_derive.
        intro aseq0.
        apply Rmult_integral in aseq0.
        destruct aseq0 ; lra.

      + change (1 * Derive fy s +
                (1 * Derive ny s * oscr a s +
                 ny s * (1 * Derive (oscr a) s)) =
                Derive fy s + Derive ny s * oscr a s + ny s * Derive (oscr a) s).
        field. }
    apply is_derive_unique in docys.
    rewrite docys.

    assert (s <> 0) as sne0; try lra.
    repeat rewrite (egeof_dNy_eq_nkTy _ sne0).
    rewrite kdef_poss; try assumption.
    setl (Derive fy s + - ty s + ny s * Derive (oscr a) s).
    unfold oscr.
    apply Rinv_neq_0_compat.
    apply Rmult_integral_contrapositive_currified; lra.

    unfold ty.
    field.
  Qed.
    
  Lemma d_evolute_magnitude : forall s,
      0 < s ->
      (magnitude (Derive (occx a)) (Derive (occy a))) s = (fun s => Rabs (Derive (oscr a) s)) s.
  Proof.
    intros * zlts.
    simpl.
    unfold magnitude, comp, plus_fct.
    rewrite (d_evolute_x _ zlts).
    rewrite (d_evolute_y _ zlts).
    repeat rewrite Rsqr_mult.

    assert (s <> 0) as sne0; try lra.
    specialize (unitN _ _ _ (anz _ sne0)) as un.
    simpl in un.
    change (locally s (fun s : R => (nx s)² + (ny s)² = 1)) in un.
    destruct un as [e un].
    specialize (un s ltac:(apply ball_center)).

    fieldrewrite ((Derive (oscr a) s)² * (nx s)² + (Derive (oscr a) s)² * (ny s)²)
                 ((Derive (oscr a) s)² * ((nx s)² + (ny s)²)).
    rewrite un.
    arn.
    rewrite sqrt_Rsqr_abs.
    reflexivity.
  Qed.

  Lemma evolute_path_length : forall (s0 s1:R),
      0 < s0 < s1 -> 
      is_RInt (magnitude (Derive (occx a)) (Derive (occy a))) s0 s1 (oscr a s0 - oscr a s1).
  Proof.
    intros * [zlts0 s0lts1].
    assert (forall x : R, Rmin s0 s1 < x < Rmax s0 s1 ->
                          (fun s => Rabs (Derive (oscr a) s)) x =
                          (magnitude (Derive (occx a)) (Derive (occy a))) x) as id0. {
      intros * [xlb xub].
      unfold Rmin, Rmax in *.
      destruct Rle_dec; try lra.
      symmetry.
      eapply (d_evolute_magnitude); lra. }
    apply (is_RInt_ext _ _ _ _ _ id0).

    assert (forall x : R, Rmin s0 s1 < x < Rmax s0 s1 ->
                          (fun s => Rabs (Derive (oscr a) s)) x =
                          (fun s => - Derive (oscr a) s) x) as id2. {
      intros * [xlb xub].
      unfold Rmin, Rmax in *.
      destruct Rle_dec; try lra.
      assert (Derive (oscr a) x < 0) as rneg. {
        unfold oscr.
        assert (forall t : R, (Rmult a) t = (fun s => a * s) t) as id3; auto.
        
        rewrite Derive_inv.
        rewrite <- Rsqr_pow2.
        setl (- (Derive (Rmult a) x * / (a * x)²)); try lra.
        setr (- 0).
        apply Ropp_lt_contravar.
        apply Rmult_lt_0_compat.

        rewrite (Derive_ext _ _ _ id3).
        rewrite Derive_scal.

        apply Rmult_lt_0_compat; try lra.
        rewrite Derive_id.
        lra.

        apply Rinv_0_lt_compat.
        apply Rsqr_pos_lt.
        apply Rmult_integral_contrapositive_currified; lra.

        exists a.
        symmetry in id3.
        apply (is_derive_ext _ _ _ _ id3).
        auto_derive.
        constructor.
        lra.

        apply Rmult_integral_contrapositive_currified; lra. }
      rewrite Rabs_left; try assumption.
      reflexivity. }
    symmetry in id2.
    apply (is_RInt_ext _ _ _ _ _ id2).

    assert (oscr a s0 - oscr a s1 = opp (oscr a s1 - oscr a s0)) as id4. {
      unfold opp.
      simpl.
      field. }
    rewrite id4.
    change (is_RInt (fun s : R => opp ((Derive (oscr a)) s)) s0 s1
                    (opp (minus (oscr a s1) (oscr a s0)))).
    apply (is_RInt_opp (Derive (oscr a))).
    apply (is_RInt_derive (oscr a)).

    intros * [xlb xub].
    unfold Rmin, Rmax in xlb, xub.
    destruct Rle_dec; try lra.
    apply Derive_correct.
    unfold oscr.

    auto_derive.
    apply Rmult_integral_contrapositive_currified; try lra.

    intros * [xlb xub].
    unfold Rmin, Rmax in xlb, xub.
    destruct Rle_dec; try lra.
    unfold oscr.

    assert (locally x (fun s => (fun s2 => - / (a * s2²)) s =
                                (Derive (fun s2 : R => / (a * s2))) s
                                )) as id5. {
      exists (mkposreal x ltac:(lra)).
      simpl.
      intros * bxy.
      unfold ball in bxy.
      simpl in bxy.
      unfold AbsRing_ball, abs, minus, opp, plus in bxy.
      simpl in bxy.
      assert (0 < y) as zlty. {
        apply Rabs_def2 in bxy.
        lra. }
    
      assert (forall s, 0 < s ->
                        is_derive (fun s2 : R => / (a * s2)) s (- / (a * s²))) as id6. {
        intros.
        auto_derive.
        apply Rmult_integral_contrapositive_currified; try lra.
        unfold Rsqr.
        field; lra. }
      specialize (id6 y zlty).
      apply is_derive_unique in id6.
      symmetry.
      assumption. }

    apply (continuous_ext_loc (Derive (fun s2 : R => / (a * s2))) (fun s2 : R => - / (a * s2²))).
    assumption.
    change (continuous (fun s2 : R => opp ((fun s3 => / (a * s3²)) s2)) x).
    apply (continuous_opp (fun s3 => / (a * s3²))).
    simpl.

    change (continuous (fun s3 : R => / ((fun s4 => scal a (Rsqr s4)) s3)) x).
    apply continuous_Rinv_comp.

    apply (continuous_scal_r a Rsqr).

    unfold Rsqr.
    change (continuous (fun r0 : R => mult (id r0) (id r0)) x).
    apply (continuous_mult id id x);
      apply continuous_id.

    unfold scal; simpl.
    unfold mult; simpl.
    apply Rmult_integral_contrapositive_currified; try lra.
    apply Rmult_integral_contrapositive_currified; try lra.
  Qed.

  Axiom straight_line_shortest_path : forall pathx pathy s0 s1 d,
      is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1 d ->
      sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²) <= d.
  
  Axiom straight_line_path_length : forall pathx pathy s0 s1,
      is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1
              (sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²)) <->
      (forall s, s0 < s < s1 ->
                pathx s = pathx s1 * (s - s0) / (s1 - s0) + pathx s0 /\
                pathy s = pathy s1 * (s - s0) / (s1 - s0) + pathy s0).

  Lemma shortest_path_lt_evolute_path : forall (s0 s1:R),
      sqrt ((occx a s0 - occx a s1)² + (occy a s0 - occy a s1)²) <
      RInt (magnitude (Derive (occx a)) (Derive (occy a))) s0 s1.
  Proof.
  Admitted.

  Theorem kneser_nesting : forall s0 s1 x y,
      0 < s0 < s1 -> 
      (x - occx a s1)² + (y - occy a s1)² <= (oscr a s1)² ->
      (x - occx a s0)² + (y - occy a s0)² < (oscr a s0)².
  Proof.
    intros *.
    intros [zlts0 s0lts1] isc.
    set (x1 := occx a s1) in *.
    set (y1 := occy a s1) in *.
    set (x0 := occx a s0) in *.
    set (y0 := occy a s0) in *.
    set (r0 := oscr a s0) in *.
    set (r1 := oscr a s1) in *.
    eapply circle_geometry;
      [instantiate (1 := r1) |
       apply isc| ].
    + unfold r1, r0, oscr.
      split.
      apply Rinv_0_lt_compat, Rmult_lt_0_compat; lra.
      apply (Rmult_lt_reg_r (a * s1 * s0)).
      repeat apply (Rmult_lt_0_compat); lra.
      setl s0; try lra.
      setr s1; lra.
    + unfold x0, x1, y0, y1, r0, r1.
      assert (0 < s1) as zlts1; try lra.

      apply sqrt_lt_0_alt.
      rewrite sqrt_Rsqr.
      2 : {
        apply (Rplus_le_reg_r (oscr a s1)).
        setr (oscr a s0).
        arn.
        unfold oscr.
        apply Rinv_le_contravar.
        apply Rmult_lt_0_compat; lra.
        apply Rmult_le_compat_l; lra. }
        
      apply (Rlt_le_trans _ (RInt (magnitude (Derive (occx a)) (Derive (occy a))) s0 s1)).
      ++ apply (shortest_path_lt_evolute_path s0 s1).
      ++ right.
         specialize (evolute_path_length s0 s1) as int.
         apply (is_RInt_unique (magnitude (Derive (occx a)) (Derive (occy a)))) in int.
         rewrite int.
         reflexivity.
         split; lra.
  Qed.

  Lemma osc_circ_approx_lt : forall p s (zlts : 0 < s),
      s < p -> (Fx a p - occx a s)² + (Fy a p - occy a s)² < (oscr a s)².
  Proof.
    intros * zlts sltp.
    eapply kneser_nesting.
    split; [apply zlts|apply sltp].
    specialize (osc_circ_equiv p p) as oce.
    right.
    rewrite <- oce.
    unfold cxf, oscx, cyf, oscy.
    fieldrewrite (p - p) 0.
    arn.
    fieldrewrite (oscr a p * sin (θt a p) +
                  (Fx a p - oscr a p * sin (θt a p)) - occx a p)
                 ((Fx a p ) - occx a p).
    fieldrewrite (oscr a p * (1 - cos (θt a p)) +
                  (Fy a p - oscr a p * (1 - cos (θt a p))) - occy a p)
                 ((Fy a p ) - occy a p).
    reflexivity.
  Qed.

  Lemma osc_circ_approx_le : forall p s (zlts : 0 < s),
      s <= p -> (Fx a p - occx a s)² + (Fy a p - occy a s)² <= (oscr a s)².
  Proof.
    intros.
    destruct H.
    left; apply osc_circ_approx_lt; assumption.
    right.
    subst.
    unfold occx, occy, oscr.
    assert (0 < (Derive (Fy a) p)² + (Derive (Fx a) p)²) as dgt0. {
      specialize (Fx_deriv _ zlta p) as fxd.
      apply is_derive_unique in fxd.
      specialize (Fy_deriv _ zlta p) as fyd.
      apply is_derive_unique in fyd.
      rewrite fxd, fyd, sin2_cos2.
      lra. }
    generalize dgt0; intro sdgt0.
    apply sqrt_lt_R0 in sdgt0.
    setl (((Derive (Fy a) p)² + (Derive (Fx a) p)²) *
          / (sqrt ((Derive (Fy a) p)² + (Derive (Fx a) p)²))² *
          / (a * p)²).
    repeat (split; try lra).
    intro deq0.
    unfold Rsqr in sdgt0.
    rewrite deq0 in sdgt0.
    lra.
    rewrite Rsqr_sqrt; try (left; assumption).
    rewrite Rinv_r.
    assert (a * p <> 0) as apne0. {
      apply Rmult_integral_contrapositive; lra. }
    rewrite Rsqr_inv; try assumption.
    field.
    apply Rmult_integral_contrapositive.
    split; assumption.
    lra.
  Qed.

(** The function euler_spiral_tangent_pt compute the value of s for
  which the direction of the derivative d/ds (Fx a s, Fy a s) matches
  the slope my/mx. The computation is insensitive the signs of the
  different components of the slope, so -my mx and my -mx are the same
  for our purposes. Selects the Nth solution. This computation implements
  Eq. 8 in the paper.

  This code, about which we prove safety properties, is directly
  extracted by the "Extraction euler_spiral_tangent_pt." command at
  the end of the file, producing formally verified code. This can be
  used as a building block and incorporated into a larger system,
  providing reliable properties matching the guarantees that we
  developed. *)


Definition euler_spiral_tangent_pt N :=
  let la := l a in
  let φ := match (Req_EM_T 0 mx) with
           | left _ => PI/2
           | right _ => atan (my/mx)
           end in
  match (Rge_dec (IZR N) 0) with
  | left _ =>
    match (Rlt_dec φ 0) with
    | left _ => la * sqrt (2/PI * ((φ+PI) + IZR N *PI))
    | right _ => la * sqrt (2/PI * (φ + IZR N*PI))
    end
  | right _ =>
    match (Rlt_dec φ 0) with
    | left _ => - la * sqrt (2/PI * ((φ+PI) - IZR (N+1) * PI))
    | right _ => - la * sqrt (2/PI * (φ - IZR (N+1) * PI))
    end
  end.

Definition estp := euler_spiral_tangent_pt.
(* begin hide *)

Lemma estp_simpl_arg :
  forall p q (zltq : 0 < q) (pqeqv : Rabs p = Rabs q) A (zleA : 0 <= A),
    let st := p * sqrt (2 / PI * A) in
    1 / 2 * PI * (st / q)² = A.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  unfold st.
  rewrite <- (RmultRinv _ q).
  repeat rewrite Rsqr_mult.
  rewrite Rsqr_inv; [|lra].
  rewrite Rsqr_sqrt; [|zltab].
  rewrite Rsqr_abs, (Rsqr_abs q), pqeqv, <- (Rsqr_abs q).
  setl A.
  split; lra.
  reflexivity.
Qed.

Ltac estpid H :=
  let rwa := fresh "rwa" in 
  match goal with
  | zlta : 0 < ?a, zltla : 0 < l ?a |- _ =>
    match H with 
    | context[- l a * sqrt (2 / PI * ?Q)] =>
      specialize (estp_simpl_arg (- l a) _ zltla
                       (Rabs_Ropp (l a)) Q) as rwa
    | context[l a * sqrt (2 / PI * ?Q)] =>
      specialize (estp_simpl_arg (l a) _ zltla
                       (eq_refl (Rabs (l a))) Q) as rwa
    | _ => idtac H
    end
  end.


Ltac rdsk2 H J:=
  let C1 := fresh "C1" in
  let C2 := fresh "C2" in
  let k := fresh "k" in
  let zltk := fresh "zltk" in
  let kltPI := fresh "kltPI" in
  let kdef := fresh "kdef" in
  let c1d := fresh "c1d" in
  let c2d := fresh "c2d" in
  match type of H with
  | context[if Rlt_dec (atan ?mymx) 0
            then ?la1 * sqrt (2 / PI * (?op1 (atan ?mymx + PI) (?N * PI)))
            else ?la1 * sqrt (2 / PI * (?op1 (atan ?mymx) (?N * PI)))] =>
    match type of J with 
    | context[if Rlt_dec (atan ?mymx) 0
              then ?la2 * sqrt (2 / PI * (?op2 (atan mymx + PI) (?M * PI)))
              else ?la2 * sqrt (2 / PI * (?op2 (atan mymx) (?M * PI)))] =>
      set (C1 := if Rlt_dec (atan mymx) 0
                 then la1 * sqrt (2 / PI * (op1 (atan mymx + PI) (N * PI)))
                 else la1 * sqrt (2 / PI * (op1 (atan mymx) (N * PI)))) in *;
      set (C2 := if Rlt_dec (atan mymx) 0
                 then la2 * sqrt (2 / PI * (op2 (atan mymx + PI) (M * PI)))
                 else la2 * sqrt (2 / PI * (op2 (atan mymx) (M * PI)))) in *;
      assert (exists k, 0 <= k /\ k < PI /\ (k = atan (mymx) \/ k = atan (mymx) + PI) /\
                        C1 = la1 * sqrt (2 / PI * (op1 k (N * PI))) /\
                        C2 = la2 * sqrt (2 / PI * (op2 k (M * PI))))
        as [k [zltk [kltPI [kdef [c1d c2d]]]]];
      [ specialize (atan_bound (mymx)) as [atl atu];
        destruct Rlt_dec;
        [ exists (atan mymx + PI);
          split; [lra |split]; [lra|];
          arn;
          split; try (right; reflexivity);
          split; reflexivity |
          exists (atan mymx);
          split; [lra |split]; [lra|];
          split; try (left; reflexivity);
          split; reflexivity] |
      ]
    | _ => assert (2 = 1); [lra|]; idtac J
    end
  | context[if Rlt_dec (atan ?mymx) 0
            then ?la1 * sqrt (2 / PI * (atan ?mymx + PI))
            else ?la1 * sqrt (2 / PI * (atan ?mymx))] =>
    match type of J with 
    | context[if Rlt_dec (atan ?mymx) 0
              then ?la2 * sqrt (2 / PI * (atan mymx + PI))
              else ?la2 * sqrt (2 / PI * (atan mymx))] =>
      set (C1 := if Rlt_dec (atan mymx) 0
                 then la1 * sqrt (2 / PI * (atan mymx + PI))
                 else la1 * sqrt (2 / PI * (atan mymx))) in *;
      set (C2 := if Rlt_dec (atan mymx) 0
                 then la2 * sqrt (2 / PI * (atan mymx + PI))
                 else la2 * sqrt (2 / PI * (atan mymx))) in *;
      assert (exists k, 0 <= k /\ k < PI /\ (k = atan (mymx) \/ k = atan (mymx) + PI) /\
                        C1 = la1 * sqrt (2 / PI * k) /\
                        C2 = la2 * sqrt (2 / PI * k))
        as [k [zltk [kltPI [kdef [c1d c2d]]]]];
      [ specialize (atan_bound (mymx)) as [atl atu];
        destruct Rlt_dec;
        [ exists (atan mymx + PI);
          split; [lra |split]; [lra|];
          arn;
          split; try (right; reflexivity);
          split; reflexivity |
          exists (atan mymx);
          split; [lra |split]; [lra|];
          split; try (left; reflexivity);
          split; reflexivity] |
      ]
    | _ => assert (2 = 2); [lra|]; idtac J
    end
  | _ => assert (1 = 1); [lra|]; idtac H
  end.

Ltac rdsk2t H J:=
  let C1 := fresh "C1" in
  let C2 := fresh "C2" in
  let k := fresh "k" in
  let zltk := fresh "zltk" in
  let kltPI := fresh "kltPI" in
  let kdef := fresh "kdef" in
  let c1d := fresh "c1d" in
  let c2d := fresh "c2d" in
  match H with
  | context[if Rlt_dec (atan ?mymx) 0
            then ?la1 * sqrt (2 / PI * (?op1 (atan ?mymx + PI) (?N * PI)))
            else ?la1 * sqrt (2 / PI * (?op1 (atan ?mymx) (?N * PI)))] =>
    match J with 
    | context[if Rlt_dec (atan mymx) 0
              then ?la2 * sqrt (2 / PI * (?op2 (atan mymx + PI) (?M * PI)))
              else ?la2 * sqrt (2 / PI * (?op2 (atan mymx) (?M * PI)))] =>
      set (C1 := if Rlt_dec (atan mymx) 0
                 then la1 * sqrt (2 / PI * (op1 (atan mymx + PI) (N * PI)))
                 else la1 * sqrt (2 / PI * (op1 (atan mymx) (N * PI)))) in *;
      set (C2 := if Rlt_dec (atan mymx) 0
                 then la2 * sqrt (2 / PI * (op2 (atan mymx + PI) (M * PI)))
                 else la2 * sqrt (2 / PI * (op2 (atan mymx) (M * PI)))) in *;
      assert (exists k, 0 <= k /\ k < PI /\ (k = atan (mymx) \/
                                             k = atan (mymx) + PI) /\
                        C1 = la1 * sqrt (2 / PI * (op1 k (N * PI))) /\
                        C2 = la2 * sqrt (2 / PI * (op2 k (M * PI))))
        as [k [zltk [kltPI [kdef [c1d c2d]]]]];
      [ specialize (atan_bound (mymx)) as [atl atu];
        destruct Rlt_dec;
        [ exists (atan mymx + PI);
          split; [lra |split]; [lra|];
          arn;
          split; try (right; reflexivity);
          split; reflexivity |
          exists (atan mymx);
          split; [lra |split]; [lra|];
          split; try (left; reflexivity);
          split; reflexivity] |
      ]
    | _ => assert (2 = 1); [lra|]
    end
  | context[if Rlt_dec (atan (?my / ?mx)) 0
            then ?la1 * sqrt (2 / PI * (atan (?my / ?mx) + PI))
            else ?la1 * sqrt (2 / PI * atan (?my / ?mx))] =>
    match J with 
    | context[if Rlt_dec (atan (my / mx)) 0
              then ?la2 * sqrt (2 / PI * (atan (my / mx) + PI))
              else ?la2 * sqrt (2 / PI * atan (my / mx))] =>
      let atlt0 := fresh "atlt0" in
      let atge0 := fresh "atge0" in
      set (C1 := if Rlt_dec (atan (my / mx)) 0
                 then la1 * sqrt (2 / PI * (atan (my / mx) + PI))
                 else la1 * sqrt (2 / PI * (atan (my / mx)))) in *;
      set (C2 := if Rlt_dec (atan (my / mx)) 0
                 then la2 * sqrt (2 / PI * (atan (my / mx) + PI))
                 else la2 * sqrt (2 / PI * (atan (my / mx)))) in *;
      match goal with
      | _ : 0 <> my |- _ =>
        assert (exists k, 0 < k /\ k < PI /\
                          (k = atan (my / mx) \/ k = atan (my / mx) + PI) /\
                          C1 = la1 * sqrt (2 / PI * k) /\
                          C2 = la2 * sqrt (2 / PI * k))
          as [k [zltk [kltPI [kdef [c1d c2d]]]]]; 
        [specialize (atan_bound (my / mx)) as [atl atu];
         destruct Rlt_dec as [atlt0 | atge0];
         [ exists (atan (my / mx) + PI);
           split; [lra |split]; [lra|];
           split; try (right; reflexivity);
           split; reflexivity |
           exists (atan (my / mx));
           apply Rnot_lt_le in atge0;
           destruct atge0 as [lt |eq];
           [split; [lra |split]; [lra|];
            split; try (left; reflexivity);
            split; reflexivity |
            exfalso;
            apply (f_equal tan) in eq;
            rewrite atan_right_inv, tan_0 in eq ];
           assert (my = 0) as myeq0;
           [ apply (Rmult_eq_reg_r (/ mx));
             [symmetry;
              lrag eq|
              zltab] | lra]
         ]
        | ]
      | _ => assert (exists k, 0 <= k /\ k < PI /\
                          (k = atan (my / mx) \/ k = atan (my / mx) + PI) /\
                          C1 = la1 * sqrt (2 / PI * k) /\
                          C2 = la2 * sqrt (2 / PI * k))
          as [k [zltk [kltPI [kdef [c1d c2d]]]]];
        [specialize (atan_bound (my / mx)) as [atl atu];
         destruct Rlt_dec as [atlt0 | atge0];
         [ exists (atan (my / mx) + PI);
           split; [lra |split]; [lra|];
           split; try (right; reflexivity);
           split; reflexivity |
           exists (atan (my / mx));
           apply Rnot_lt_le in atge0;
           split; [lra |split]; [lra|];
           arn;
           split; try (left; reflexivity);
           split; reflexivity] | ]
      end
    | _ => assert (2 = 2); [lra|]; idtac J
    end
  | _ => assert (1 = 1); [lra|]; idtac H
  end.



Lemma sincosatan2 : forall x N,
    exists pm, ((Z.Even N /\ pm=1)\/
                (Z.Odd N /\ pm=-1)) /\
               sin (atan x + IZR N * PI) = pm * x / sqrt (1 + x²) /\
               cos (atan x + IZR N * PI) = pm / sqrt (1 + x²).
Proof.
  intros.
  specialize (Z.Even_or_Odd N) as [neven| nodd].
  + exists 1.
    split; [left; split;
            [assumption|reflexivity]|].
    unfold Z.Even in neven.
    destruct neven as [p neven].
    rewrite neven.
    rewrite mult_IZR.
    rewrite cos_period1, sin_period1.
    split; [rewrite Rmult_1_l; apply sinatan| apply cosatan].
  + exists (-1).
    split;
      [right; split;
       [assumption|reflexivity]|].
    unfold Z.Odd in nodd.
    destruct nodd as [m nodd].
    rewrite nodd.
    rewrite plus_IZR, mult_IZR.
    fieldrewrite (atan x + (2 * IZR m + 1) * PI)
                 ((atan x + PI) + 2 * IZR m *PI).
    rewrite cos_period1, sin_period1, neg_cos, neg_sin.
    split; [rewrite sinatan | rewrite cosatan]; lra.
Qed.

(* end hide *)

(** The function euler_spiral_tangent_pt returns local extrema of the
safe_pt function; and there are no other local minima in the intervals
between values returned by euler_spiral_tangent_pt for subsequent
values of N.

The solutions are non-decreasing with N and under most conditions, 
have alternating signs. *)

Lemma euler_tan_pt_mxne0_derivefxne0 : forall N (mxne0 : mx<>0),
    let st := estp N in
    (Derive (Fx a) st) <> 0.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  unfold st, estp, euler_spiral_tangent_pt.

    assert (Derive (Fx a) =
            (fun s => cos (1 / 2 * PI * (s / l a)²))) as dfx. {
      apply functional_extensionality.
      intro s.
      specialize (Fx_deriv _ zlta s) as idfx.
      apply is_derive_unique in idfx.
      assumption. }

  destruct Rge_dec;
    destruct Req_EM_T; try lra.
  + match goal with
    | |- Derive (Fx a) ?A <> 0 => rdsk2t A A
    end.
    
    rewrite dfx. clear dfx.
    rewrite c1d.
    specialize (agt0_lagt0 _ zlta) as zltla.
    assert (0 <= k + IZR N * PI) as nna; try zltab.
    match goal with | |- cos ?A <> 0 => estpid A end.
    specialize (rwa nna).
    simpl in rwa.
    rewrite rwa.
    destruct kdef as [kdef|kdef].
    ++ rewrite kdef.
       specialize (sincosatan2 (my/mx) N) as [pm [oe [snq csq]]].
       rewrite csq.
       intro pmdeneq0.
       assert (pm = 0) as pmeq0. {
         assert (0 < 1 + (my / mx)²) as arggt0. {
           apply Rplus_lt_le_0_compat.
           lra.
           zltab. }
         
         apply (Rmult_eq_reg_r (/ sqrt (1 + (my / mx)²))).
         rewrite RmultRinv;
         arn; assumption.
         zltab.
         intro sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0; lra. }
       destruct oe as [[even pmd] | [odd pmd]];
                                   rewrite pmd in pmeq0; lra.
    ++ rewrite kdef.
       fieldrewrite (atan (my / mx) + PI + IZR N * PI)
                    (atan (my / mx) + (IZR N + IZR 1) * PI).
       rewrite <- plus_IZR.
       specialize (sincosatan2 (my/mx) (N+1)) as [pm [oe [snq csq]]].
       rewrite csq.
       intro pmdeneq0.
       assert (pm = 0) as pmeq0. {
         assert (0 < 1 + (my / mx)²) as arggt0. {
           apply Rplus_lt_le_0_compat.
           lra.
           zltab. }
         
         apply (Rmult_eq_reg_r (/ sqrt (1 + (my / mx)²))).
         rewrite RmultRinv;
         arn; assumption.
         zltab.
         intro sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0; lra. }
       destruct oe as [[even pmd] | [odd pmd]];
                                   rewrite pmd in pmeq0; lra.
  + match goal with
    | |- Derive (Fx a) ?A <> 0 => rdsk2t A A
    end.
    
    rewrite dfx. clear dfx.
    rewrite c1d.
    specialize (agt0_lagt0 _ zlta) as zltla.
    apply Rnot_ge_lt in n.
    assert (0 <= k - IZR (N+1) * PI) as nna. {
      assert (0 <= - IZR (N+1)) as np1. {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        apply IZR_le.
        apply lt_IZR in n.
        omega. }
      setr (k + (- IZR (N + 1)) * PI).
      zltab. }
    match goal with | |- cos ?A <> 0 => estpid A end.
    specialize (rwa nna).
    simpl in rwa.
    rewrite rwa.
    destruct kdef as [kdef|kdef].
    ++ rewrite kdef.
       specialize (sincosatan2 (my/mx) (-(N+1))) as [pm [oe [snq csq]]].
       rewrite opp_IZR in snq, csq.
       fieldrewrite (atan (my / mx) - IZR (N + 1) * PI)
                    (atan (my / mx) + - IZR (N + 1) * PI).
       rewrite csq.
       intro pmdeneq0.
       assert (pm = 0) as pmeq0. {
         assert (0 < 1 + (my / mx)²) as arggt0. {
           apply Rplus_lt_le_0_compat.
           lra.
           zltab. }
         
         apply (Rmult_eq_reg_r (/ sqrt (1 + (my / mx)²))).
         rewrite RmultRinv;
         arn; assumption.
         zltab.
         intro sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0; lra. }
       destruct oe as [[even pmd] | [odd pmd]];
                                   rewrite pmd in pmeq0; lra.
    ++ rewrite kdef.
       rewrite plus_IZR.
       fieldrewrite (atan (my / mx) + PI - (IZR N + 1) * PI)
                    (atan (my / mx) + - IZR N * PI).
       rewrite <- opp_IZR.
       specialize (sincosatan2 (my/mx) (- N)) as [pm [oe [snq csq]]].
       rewrite csq.
       intro pmdeneq0.
       assert (pm = 0) as pmeq0. {
         assert (0 < 1 + (my / mx)²) as arggt0. {
           apply Rplus_lt_le_0_compat.
           lra.
           zltab. }
         
         apply (Rmult_eq_reg_r (/ sqrt (1 + (my / mx)²))).
         rewrite RmultRinv;
         arn; assumption.
         zltab.
         intro sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0; lra. }
       destruct oe as [[even pmd] | [odd pmd]];
                                   rewrite pmd in pmeq0; lra.
Qed.


Lemma euler_tan_pt : forall N (mxne0 : mx<>0),
    let st := estp N in
    (Derive (Fy a) st)/(Derive (Fx a) st) = my/mx.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  specialize (agt0_lagt0 _ zlta) as lagt0.
  specialize (ane0_lane0 _ zlta) as lane0.
  unfold estp, euler_spiral_tangent_pt in *.
  specialize (Fy_deriv _ zlta st) as Fyd.
  apply is_derive_unique in Fyd.
  specialize (Fx_deriv _ zlta st) as Fxd.
  apply is_derive_unique in Fxd.
  rewrite Fyd, Fxd.

  destruct Rge_dec.
  destruct Req_EM_T.
  destruct Rlt_dec.
  + lra.
  + lra.
  + destruct Rlt_dec.
    ++ change (tan (1 / 2 * PI * (st / l a)²) = my / mx).
       clear n.
       unfold st.
       match goal with | |- tan ?A = my / mx => estpid A end.
       rewrite rwa.
       +++ rewrite tan_period, <- (Rmult_1_l PI).
           rewrite tan_period.
           ++++ rewrite atan_right_inv.
                reflexivity.
           ++++ intro.
                apply cos_eq_0_0 in H as [k cd].
                specialize (atan_bound (my/mx)) as [alb aub].
                rewrite cd in r0,alb,aub.
                clear - r0 alb pigt0.
                destruct k.
                - lra.
                - specialize (IZRposge1 p) as po.
                    assert (1 * PI + PI/2< 0). {
                      apply (Rle_lt_trans _ (IZR (Z.pos p) * PI + PI/2));
                        try assumption.
                      apply (Rplus_le_reg_r (-PI/2)).
                      apply (Rmult_le_reg_r (/PI)).
                      apply Rinv_0_lt_compat.
                      lra.
                      setl 1. lra.
                      setr (IZR (Z.pos p)). lra.
                      assumption. }
                    lra.
                - specialize (IZRneglen1 p) as po.
                  assert (-PI/2 < -1 * PI + PI/2). {
                    apply (Rlt_le_trans _ (IZR (Z.neg p) * PI + PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setr (-1). lra.
                    setl (IZR (Z.neg p)). lra.
                    assumption. }
                  lra.
           ++++ intro.
                apply cos_eq_0_0 in H as [k cdd].
                assert (atan (my / mx) = IZR k * PI - PI / 2) as cd. {
                  apply (Rplus_eq_reg_r PI).
                  lrag cdd. }
                specialize (atan_bound (my/mx)) as [alb aub].
                rewrite cd in r0,alb,aub.
                clear - r0 alb pigt0.
                destruct k.
                - lra.
                - specialize (IZRposge1 p) as po.
                  assert (1 * PI - PI/2< 0). {
                    apply (Rle_lt_trans _ (IZR (Z.pos p) * PI - PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setl 1. lra.
                    setr (IZR (Z.pos p)). lra.
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as po.
                  assert (-PI/2 < -1 * PI - PI/2). {
                    apply (Rlt_le_trans _ (IZR (Z.neg p) * PI - PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setr (-1). lra.
                    setl (IZR (Z.neg p)). lra.
                    assumption. }
                  lra.
       +++ apply (Rplus_le_reg_r (- IZR ( N + 1) * PI)).
           rewrite plus_IZR at 2.
           setr (atan (my/mx)).
           setl (- IZR (N + 1) * PI).
           assert (- IZR (N + 1) <= -1) as zo. {
             rewrite plus_IZR.
             lra. }
           apply (Rle_trans _ (-1*PI)).
           apply (Rmult_le_reg_r (/ PI)).
           apply Rinv_0_lt_compat.
           lra.
           lrag zo.
           specialize (atan_bound (my / mx)) as [atl atu].
           lra.
    ++ change (tan (1 / 2 * PI * (st / l a)²) = my / mx).
       clear n.
       unfold st.
       match goal with | |- tan ?A = my / mx => estpid A end.
       rewrite rwa.

       +++ rewrite tan_period.
           ++++ rewrite atan_right_inv.
                reflexivity.
           ++++ intro.
                apply cos_eq_0_0 in H as [k cd].
                specialize (atan_bound (my/mx)) as [alb aub].
                rewrite cd in n0,alb,aub.
                clear - alb aub pigt0.
                destruct k.
                - lra.
                - specialize (IZRposge1 p) as po.
                  assert (1 * PI + PI/2< PI/2). {
                    apply (Rle_lt_trans _ (IZR (Z.pos p) * PI + PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setl 1. lra.
                    setr (IZR (Z.pos p)). lra.
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as po.
                  assert (-PI/2 < -1 * PI + PI/2). {
                    apply (Rlt_le_trans _ (IZR (Z.neg p) * PI + PI/2)); try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setr (-1). lra.
                    setl (IZR (Z.neg p)). lra.
                    assumption. }
                  lra.
       +++ apply (Rplus_le_reg_r (- IZR N * PI)).
           setr (atan (my / mx)). 
           setl (- IZR N * PI).
           assert (- IZR N <= 0) as zo. {
             lra. }
           apply Rnot_lt_le in n0.
           apply (Rle_trans _ 0).
           apply (Rmult_le_reg_r (/ PI)).
           apply Rinv_0_lt_compat.
           lra.
           lrag zo.
           assumption.
  + destruct Req_EM_T;
      [exfalso; apply mxne0; auto|
       destruct Rlt_dec].
    change (tan (1 / 2 * PI * (st / l a)²) = my / mx).
    unfold st.

    match goal with | |- tan ?A = my / mx => estpid A end.
    rewrite rwa.

    +++ rewrite <- pm, plus_IZR.
        fieldrewrite (atan (my / mx) + PI + - ((IZR N + 1) * PI))
                     (atan (my / mx) + - IZR N * PI). 
        rewrite <- opp_IZR.
        rewrite tan_period.
        ++++ rewrite atan_right_inv.
             reflexivity.
        ++++ intro.
             apply cos_eq_0_0 in H as [k cd].
             specialize (atan_bound (my/mx)) as [alb aub].
             rewrite cd in r,alb,aub.
             clear - alb aub pigt0.
             destruct k.
                - lra.
                - specialize (IZRposge1 p) as po.
                  assert (1 * PI + PI/2< PI/2). {
                    apply (Rle_lt_trans _ (IZR (Z.pos p) * PI + PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setl 1. lra.
                    setr (IZR (Z.pos p)). lra.
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as po.
                  assert (-PI/2 < -1 * PI + PI/2). {
                    apply (Rlt_le_trans _ (IZR (Z.neg p) * PI + PI/2)); try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setr (-1). lra.
                    setl (IZR (Z.neg p)). lra.
                    assumption. }
                  lra.
       +++ apply (Rplus_le_reg_r (IZR N * PI)).
           rewrite plus_IZR.
           setr (atan (my / mx)). 
           setl (IZR N * PI).
           apply Rnot_ge_lt in n.
           apply (Rle_trans _ (-PI/2)).
           apply (Rmult_le_reg_r (/ PI)).
           apply Rinv_0_lt_compat.
           lra.
           destruct N. lra.
           specialize (IZRposge1 p) as olep.
           lra.
           specialize (IZRneglen1 p) as po.
           setl (IZR (Z.neg p)). lra.
           setr (-1/2). lra.
           lra.
           specialize (atan_bound (my/mx)) as [al au].
           left. assumption.
       +++ apply Rnot_lt_le in n1.
           change (tan (1 / 2 * PI * (st / l a)²) = my / mx).
           unfold st.

           match goal with | |- tan ?A = my / mx => estpid A end.
           rewrite rwa.
           ++++ rewrite <- pm, Ropp_mult_distr_l, <- opp_IZR.
                rewrite tan_period.
                +++++ rewrite atan_right_inv.
                reflexivity.
                +++++ intro.
                apply cos_eq_0_0 in H as [k cd].
                specialize (atan_bound (my/mx)) as [alb aub].
                rewrite cd in n1,alb,aub.
                clear - alb aub pigt0.
                destruct k.
                - lra.
                - specialize (IZRposge1 p) as po.
                  assert (1 * PI + PI/2< PI/2). {
                    apply (Rle_lt_trans _ (IZR (Z.pos p) * PI + PI/2));
                      try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setl 1. lra.
                    setr (IZR (Z.pos p)). lra.
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as po.
                  assert (-PI/2 < -1 * PI + PI/2). {
                    apply (Rlt_le_trans _ (IZR (Z.neg p) * PI + PI/2)); try assumption.
                    apply (Rplus_le_reg_r (-PI/2)).
                    apply (Rmult_le_reg_r (/PI)).
                    apply Rinv_0_lt_compat.
                    lra.
                    setr (-1). lra.
                    setl (IZR (Z.neg p)). lra.
                    assumption. }
                  lra.
                  ++++ apply (Rplus_le_reg_r (IZR (N+1) * PI)).
                       setr (atan (my / mx)). 
                       setl (IZR (N+1) * PI).
                       apply Rnot_ge_lt in n.
                       apply (Rle_trans _ 0).
                       apply (Rmult_le_reg_r (/ PI)).
                       apply Rinv_0_lt_compat.
                       lra.
                       destruct N. lra.
                       specialize (IZRposge1 p) as olep.
                       lra.
                       specialize (IZRneglen1 p) as po.
                       rewrite plus_IZR.
                       setl (IZR (Z.neg p) + 1). lra.
                       setr 0. lra.
                       lra.
                       assumption.
Qed.

Lemma euler_tan_pt2 : forall N (mxeq0 : mx = 0),
    let st := estp N in
    (Derive (Fy a) st) <> 0 /\ (Derive (Fx a) st) = 0.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  specialize (ane0_lane0 _ zlta) as lane0.
  unfold estp, euler_spiral_tangent_pt in *.
  specialize (Fy_deriv _ zlta st) as Fyd.
  apply is_derive_unique in Fyd.
  specialize (Fx_deriv _ zlta st) as Fxd.
  apply is_derive_unique in Fxd.
  rewrite Fyd, Fxd.
  
  destruct Req_EM_T.
  + destruct Rlt_dec. lra.
    destruct Rge_dec.
    ++ split.
       +++ clear n.
           unfold st.
           fieldrewrite (1 / 2 * PI * (l a * sqrt (2 / PI * (PI / 2 + IZR N * PI)) / l a)²)
                        (1 / 2 * PI * (sqrt (2 / PI * (PI / 2 + IZR N * PI)))²); try assumption.
           fieldrewrite (2 / PI * (PI / 2 + IZR N * PI)) (1 + 2*IZR N). lra.
           rewrite Rsqr_sqrt.
           ++++ fieldrewrite (1 / 2 * PI * (1 + 2 * IZR N))
                             (PI / 2 + IZR N * PI).
                rewrite <- cos_sin.
                intro coseq0.
                apply cos_eq_0_0 in coseq0 as [k def].
                assert (2 * IZR (N - k) = 1) as def2. {
                  apply (Rmult_eq_reg_r (PI/2)).
                  apply (Rplus_eq_reg_r (IZR k * PI)).
                  rewrite minus_IZR.
                  lrag def.
                  lra. }
                destruct (N - k)%Z.
                +++++ lra.
                +++++ specialize (IZRposge1 p) as po. lra.
                +++++ specialize (IZRneglen1 p) as po. lra.
           ++++ lra.
       +++ clear n.
           unfold st.
           fieldrewrite (1 / 2 * PI * (l a * sqrt (2 / PI * (PI / 2 + IZR N * PI)) / l a)²)
                        (1 / 2 * PI * (sqrt (2 / PI * (PI / 2 + IZR N * PI)))²); try assumption.
           fieldrewrite (2 / PI * (PI / 2 + IZR N * PI)) (1 + 2*IZR N). lra.
           rewrite Rsqr_sqrt.
           ++++ fieldrewrite (1 / 2 * PI * (1 + 2 * IZR N))
                             (PI / 2 + IZR N * PI).
                apply cos_eq_0_1.
                exists N.
                field.
           ++++ lra.
    ++ apply Rnot_ge_lt in n0.
       split.
       +++ clear n.
           unfold st.
           fieldrewrite (1 / 2 * PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N+1) * PI)) / l a)²)
                        (1 / 2 * PI * (sqrt (2 / PI * (PI / 2 - IZR (N+1) * PI)))²); try assumption.
           fieldrewrite (2 / PI * (PI / 2 - IZR (N+1) * PI)) (1 - 2*IZR (N+1)). lra.
           rewrite Rsqr_sqrt.
           ++++ fieldrewrite (1 / 2 * PI * (1 - 2 * IZR (N+1)))
                             (PI / 2 + - IZR (N+1) * PI).
                rewrite <- opp_IZR.
                rewrite <- cos_sin.
                intro coseq0.
                apply cos_eq_0_0 in coseq0 as [k def].
                assert (2 * IZR (-(N+1) - k) = 1) as def2. {
                  apply (Rmult_eq_reg_r (PI/2)).
                  apply (Rplus_eq_reg_r (IZR k * PI)).
                  rewrite minus_IZR.
                  lrag def.
                  lra. }
                destruct (-(N+1) - k)%Z.
                +++++ lra.
                +++++ specialize (IZRposge1 p) as po. lra.
                +++++ specialize (IZRneglen1 p) as po. lra.
           ++++ rewrite plus_IZR.
                destruct N.
                +++++ lra.
                +++++ specialize (IZRposge1 p) as po. lra.
                +++++ specialize (IZRneglen1 p) as po. lra.
       +++ clear n.
           unfold st.
           fieldrewrite (1 / 2 * PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N+1) * PI)) / l a)²)
                        (1 / 2 * PI * (sqrt (2 / PI * (PI / 2 - IZR (N+1) * PI)))²); try assumption.
           fieldrewrite (2 / PI * (PI / 2 - IZR (N+1) * PI)) (1 - 2*IZR (N+1)). lra.
           rewrite Rsqr_sqrt.
           ++++ fieldrewrite (1 / 2 * PI * (1 - 2 * IZR (N+1)))
                        (PI / 2 - IZR (N+1) * PI).
                apply cos_eq_0_1.
                exists (-(N+1))%Z.
                rewrite opp_IZR.
                field.
           ++++ rewrite plus_IZR.
                destruct N.
                +++++ lra.
                +++++ specialize (IZRposge1 p) as po. lra.
                +++++ specialize (IZRneglen1 p) as po. lra.
  + exfalso. lra.
Qed.


(* begin hide *)

Lemma euler_tan_pt_symm_mxne0 :
  forall N (mxne0 : mx <> 0)
         (Nge0 : IZR N >= 0),
    let stp := estp N in
    let stn := estp (-N-1) in
    stp = - stn.
Proof.
  intros.
  unfold stp, stn, estp, euler_spiral_tangent_pt.
  destruct Rge_dec; [clear r|exfalso; lra].
  destruct Rge_dec;
    [ exfalso;
      apply Rge_le in Nge0;
      apply le_IZR in Nge0;
      apply Rge_le in r;
      apply le_IZR in r;
      omega| apply Rnot_ge_lt in n].

  destruct Req_EM_T; [exfalso; lra| clear n0].
  assert (- N - 1 + 1 = - N)%Z as id. omega.
  rewrite id, opp_IZR. clear id.
  
  match goal with | |- ?P = - ?Q => rdsk2t P Q end.
  rewrite c1d, c2d.
  fieldrewrite (k - - IZR N * PI) (k + IZR N * PI).
  field.
Qed.

Lemma euler_tan_pt_symm_mxeq0 :
  forall N (mxeq0 : 0 = mx)
         (Nge0 : IZR N >= 0),
    let stp := estp N in
    let stn := estp (-N-1) in
    stp = - stn.
Proof.
  intros.
  unfold stp, stn, estp, euler_spiral_tangent_pt.
  destruct Rge_dec; [clear r|exfalso; lra].
  destruct Rge_dec;
    [ exfalso;
      apply Rge_le in Nge0;
      apply le_IZR in Nge0;
      apply Rge_le in r;
      apply le_IZR in r;
      omega| apply Rnot_ge_lt in n].

  destruct Req_EM_T; [clear e |exfalso; lra].
  specialize PI_RGT_0 as pigt0.
  destruct Rlt_dec; try lra.

  assert (- N - 1 + 1 = - N)%Z as id. omega.
  rewrite id, opp_IZR. clear id.
  
  fieldrewrite (PI / 2 - - IZR N * PI) (PI / 2 + IZR N * PI).
  field.
Qed.

(* end hide *)
Lemma euler_tan_pt_symm :
  forall N (Nge0 : IZR N >= 0),
    let stp := estp N in
    let stn := estp (-N-1) in
    stp = - stn.
Proof.
  intros.
  destruct (Req_dec 0 mx).
  apply euler_tan_pt_symm_mxeq0; try assumption.
  apply euler_tan_pt_symm_mxne0; try lra.
Qed.

  (* we assume ~ (mx = 0 /\ my = 0), that the slope is determinate *)
  (* The function euler_spiral_tangent_pt returns local extrema of the safe_pt function. *)
  Lemma sf_deriv_0 : forall N,
      let s := estp N in
      Derive sf s = 0.
  Proof.
    intros.
    
    unfold sf, estp in *.
    set (f := (fun q : R => safe_pt (Fx a q) (Fy a q))).
    specialize (sf_deriv s) as spdv.
    change (is_derive
              f s ((fun p => (mx * sin (1 / 2 * PI * (p / l a)²) +
                              - my * cos (1 / 2 * PI * (p / l a)²))) s))
      in spdv.
    set (f' := (fun p : R =>
                  mx * sin (1 / 2 * PI * (p / l a)²) +
                  - my * cos (1 / 2 * PI * (p / l a)²))) in *.
    apply is_derive_unique in spdv.
    rewrite spdv.
    unfold f', s.
    
    specialize (ane0_lane0 _ zlta) as lane0.
    specialize PI_RGT_0 as pigt0.
    
    assert (Fx a = (fun x => Fx a x)) as idx. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    assert (Fy a = (fun y => Fy a y)) as idy. {
      apply functional_extensionality.
      intros.
      reflexivity. }
    specialize (Fx_deriv _ zlta s) as fxd.
    specialize (Fy_deriv _ zlta s) as fyd.
    apply is_derive_unique in fxd.
    apply is_derive_unique in fyd.
    rewrite idx in fxd.
    rewrite idy in fyd.
    unfold estp, euler_spiral_tangent_pt.
    destruct Rge_dec;
      [destruct Req_EM_T
       ; [| destruct Rlt_dec ;
          [| apply Rnot_lt_le in n0]]
      | apply Rnot_ge_lt in n; destruct Req_EM_T;
      [|destruct Rlt_dec]].
    ++ rewrite <- e.
       autorewrite with null.
       destruct Rlt_dec;[ lra|].
       fieldrewrite (2 / PI * (PI / 2 + IZR N * PI)) (1 + 2* IZR N).
       intro; lra.
       fieldrewrite (l a * sqrt (1 + 2 * IZR N) / l a) (sqrt (1 + 2 * IZR N)).
       assumption.
       rewrite Rsqr_sqrt.
       +++ fieldrewrite (1 / 2 * PI * (1 + 2 * IZR N))
                        (IZR N * PI + PI/2).
           rewrite cos_eq_0_1.
           autorewrite with null.
           reflexivity.
           exists (N).
           lra.
       +++ lra.
    ++ assert (1 / 2 * PI *
               (l a * sqrt (2 / PI * (atan (my / mx) + PI + IZR N * PI)) / l a)²=
               atan (my / mx) + IZR (N+1) * PI) as id. {
         rewrite plus_IZR.
         fieldrewrite (atan (my / mx) + PI + IZR N * PI)
                      (atan (my / mx) + (IZR N + 1) * PI).
         fieldrewrite
           (1 / 2 * PI *
            (l a * sqrt (2 / PI * (atan (my / mx) + (IZR N + 1) * PI)) / l a)²)
           (1 / 2 * PI *
            (sqrt (2 / PI * (atan (my / mx) + (IZR N + 1) * PI)))²).
         apply ane0_lane0; try assumption.
         rewrite Rsqr_sqrt;
           [field; lra|
            apply Rmult_le_pos;
            [apply Rdiv_le_0_compat; lra|
             setr ((atan (my / mx) + PI) + IZR N * PI);
             apply Rplus_le_le_0_compat;
             [ specialize (atan_bound (my/mx)) as [al ah]; lra|
              apply Rmult_le_pos;
              [apply Rge_le in r; assumption|
               left; assumption]]]]. }
       rewrite id. clear id.
       specialize (sincosatan2 (my/mx) (N+1)) as [pm [pmd [sd cd]]].
       rewrite sd, cd.
       (* assert  (mx² + my² =  mx²*(1 + (my/mx)²)) as id. { *)
       (*   setr (mx² + my²). lra. reflexivity. } *)
       (* rewrite id. clear id. *)
       set (Q := (1 + (my / mx)²)) in *.
       assert (0 < 1 + (my / mx)²) as agt0;
         [apply Rplus_lt_le_0_compat;
          [lra |
           apply Rle_0_sqr] |].
       assert (my² - mx² * Q = - mx²). {
         unfold Q.
         rewrite Rmult_plus_distr_l.
         rewrite Rsqr_div.
         setl (- mx²). auto. reflexivity.
         auto. }
       assert (sqrt Q <> 0) as sqne0. {
         unfold Q.
         intro sqeq0;
           apply sqrt_eq_0 in sqeq0;
           try (left; assumption);lra. }
       setl 0; split; auto.
    ++ assert (1 / 2 * PI *
               (l a * sqrt (2 / PI * (atan (my / mx) + IZR N * PI)) / l a)²=
            atan (my / mx) + IZR N * PI) as id. {
         fieldrewrite
           (1 / 2 * PI *
            (l a * sqrt (2 / PI * (atan (my / mx) + IZR N * PI)) / l a)²)
           (1 / 2 * PI *
            (sqrt (2 / PI * (atan (my / mx) + IZR N * PI)))²).
         apply ane0_lane0; try assumption.
         rewrite Rsqr_sqrt;
           [field; lra|
            apply Rmult_le_pos;
            [apply Rdiv_le_0_compat; lra|
             apply Rplus_le_le_0_compat;
             [assumption|
              apply Rmult_le_pos;
              [apply Rge_le in r; assumption|
               left; assumption]]]]. }
       rewrite id. clear id.
       specialize (sincosatan2 (my/mx) N) as [pm [pmd [sd cd]]].
       rewrite sd, cd.
       (* assert  (mx² + my² =  mx²*(1 + (my/mx)²)) as id. { *)
       (*   setr (mx² + my²). lra. reflexivity. } *)
       (* rewrite id. clear id. *)
       set (Q := (1 + (my / mx)²)) in *.
       assert (0 < 1 + (my / mx)²) as agt0;
         [apply Rplus_lt_le_0_compat;
          [lra |
           apply Rle_0_sqr] |].
       assert (my² - mx² * Q = - mx²). {
         unfold Q.
         rewrite Rmult_plus_distr_l.
         rewrite Rsqr_div.
         setl (- mx²). auto. reflexivity.
         auto. }
       assert (sqrt Q <> 0) as sqne0. {
         unfold Q.
         intro sqeq0;
           apply sqrt_eq_0 in sqeq0;
           try (left; assumption);lra. }
       setl 0; split; auto.
    ++ rewrite <- e.
       autorewrite with null.
       destruct Rlt_dec;[ lra|].
       fieldrewrite (2 / PI * (PI / 2 - IZR (N+1) * PI)) (1 + 2* - IZR (N+1)).
       intro; lra.
       rewrite <- opp_IZR.
       fieldrewrite (- l a * sqrt (1 + 2 * IZR (-(N+1))) / l a) (- sqrt (1 + 2 * IZR (-(N+1)))).
       assumption.
       rewrite <- Rsqr_neg.
       rewrite Rsqr_sqrt.
       +++ fieldrewrite (1 / 2 * PI * (1 + 2 * IZR (-(N+1))))
                        (IZR (-(N+1)) * PI + PI/2).
           rewrite cos_eq_0_1.
           autorewrite with null.
           reflexivity.
           exists (-(N+1))%Z.
           lra.
       +++ destruct N%Z;
           rewrite opp_IZR, plus_IZR.
           ++++ lra.
           ++++ specialize (IZRposge1 p) as po. lra.
           ++++ specialize (IZRneglen1 p) as po. lra.
    ++ assert (1 / 2 * PI *
               (- l a * sqrt (2 / PI * (atan (my / mx) + PI - IZR (N+1) * PI)) / l a)² =
               atan (my / mx) + PI + IZR (-(N+1)) * PI) as id. {
         rewrite opp_IZR.
         fieldrewrite
           (1 / 2 * PI *
            (- l a * sqrt (2 / PI * (atan (my / mx) + PI - IZR (N+1) * PI)) / l a)²)
           (1 / 2 * PI *
            (sqrt (2 / PI * (atan (my / mx) + PI - IZR (N+1) * PI)))²).
         apply ane0_lane0; try assumption.
         rewrite Rsqr_sqrt;
           [field; lra|
            apply Rmult_le_pos;
            [apply Rdiv_le_0_compat; lra|
             setr ((atan (my / mx) + PI) + - IZR (N+1) * PI);
             apply Rplus_le_le_0_compat;
             [ specialize (atan_bound (my/mx)) as [al ah]; lra|
              apply Rmult_le_pos;
              [ rewrite plus_IZR;
                destruct N%Z;
                [lra | specialize (IZRposge1 p) as po; lra |
                 specialize (IZRneglen1 p) as po; lra] |
                left; assumption ]]]]. }
       rewrite id. clear id.
       rewrite opp_IZR, plus_IZR.
       fieldrewrite (atan (my / mx) + PI + - (IZR N + 1) * PI)
                    (atan (my / mx) + - IZR N * PI).
       rewrite <- opp_IZR.
       specialize (sincosatan2 (my/mx) (-N)) as [pm [pmd [sd cd]]].
       rewrite sd, cd.
       (* assert  (mx² + my² =  mx²*(1 + (my/mx)²)) as id. { *)
       (*   setr (mx² + my²). lra. reflexivity. } *)
       (* rewrite id. clear id. *)
       set (Q := (1 + (my / mx)²)) in *.
       assert (0 < 1 + (my / mx)²) as agt0;
         [apply Rplus_lt_le_0_compat;
          [lra |
           apply Rle_0_sqr] |].
       assert (my² - mx² * Q = - mx²). {
         unfold Q.
         rewrite Rmult_plus_distr_l.
         rewrite Rsqr_div.
         setl (- mx²). auto. reflexivity.
         auto. }
       assert (sqrt Q <> 0) as sqne0. {
         unfold Q.
         intro sqeq0;
           apply sqrt_eq_0 in sqeq0;
           try (left; assumption);lra. }
       setl 0; split; auto.
    ++ apply Rnot_lt_le in n1.
       assert (1 / 2 * PI *
               (- l a * sqrt (2 / PI * (atan (my / mx) - IZR (N+1) * PI)) / l a)²=
            atan (my / mx) + IZR (-(N+1)) * PI) as id. {
         fieldrewrite
           (1 / 2 * PI *
            (- l a * sqrt (2 / PI * (atan (my / mx) - IZR (N+1) * PI)) / l a)²)
           (1 / 2 * PI *
            (sqrt (2 / PI * (atan (my / mx) - IZR (N+1) * PI)))²).
         apply ane0_lane0; try assumption.
         rewrite opp_IZR.
         rewrite Rsqr_sqrt;
           [field; lra|
            apply Rmult_le_pos;
            [apply Rdiv_le_0_compat; lra|
             apply Rplus_le_le_0_compat;
             [assumption|
              setr (- IZR (N + 1) * PI);
              apply Rmult_le_pos;
              [rewrite plus_IZR;
               destruct N%Z;
               [lra | specialize (IZRposge1 p) as po ; lra|
                specialize (IZRneglen1 p) as po; lra]|
               left; assumption]]]]. }
       rewrite id. clear id.
       specialize (sincosatan2 (my/mx) (-(N+1))) as [pm [pmd [sd cd]]].
       rewrite sd, cd.
       (* assert  (mx² + my² =  mx²*(1 + (my/mx)²)) as id. { *)
       (*   setr (mx² + my²). lra. reflexivity. } *)
       (* rewrite id. clear id. *)
       set (Q := (1 + (my / mx)²)) in *.
       assert (0 < 1 + (my / mx)²) as agt0;
         [apply Rplus_lt_le_0_compat;
          [lra |
           apply Rle_0_sqr] |].
       assert (my² - mx² * Q = - mx²). {
         unfold Q.
         rewrite Rmult_plus_distr_l.
         rewrite Rsqr_div.
         setl (- mx²). auto. reflexivity.
         auto. }
       assert (sqrt Q <> 0) as sqne0. {
         unfold Q.
         intro sqeq0;
           apply sqrt_eq_0 in sqeq0;
           try (left; assumption);lra. }
       setl 0; split; auto.
  Qed.
  (* begin hide *)
  
  Lemma sf_deriv_ne0_mxeq0 : forall N s (e : 0 = mx) (zlta : 0 < a),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s < s2 -> Derive sf s <> 0.
  Proof.
    intros.
    unfold sf, estp in *.
    destruct H as [sl sh].
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    set (f := (fun q : R => safe_pt (Fx a q) (Fy a q))).
    specialize (sf_deriv s) as spdv.
    change (is_derive
              f s ((fun p => (mx * sin (1 / 2 * PI * (p / l a)²) +
                              - my * cos (1 / 2 * PI * (p / l a)²))) s))
      in spdv.
    set (f' := (fun p : R =>
                  mx * sin (1 / 2 * PI * (p / l a)²) +
                  - my * cos (1 / 2 * PI * (p / l a)²))) in *.
    apply is_derive_unique in spdv.
    rewrite spdv.
    unfold f'.
    clear spdv f'.
    unfold s1, estp, euler_spiral_tangent_pt in sl.
    unfold s2, estp, euler_spiral_tangent_pt in sh.

    destruct (Req_EM_T 0 mx);
      [clear e0| lra].

    rewrite <- e in *.
    destruct (Rlt_dec (PI/2) 0); [lra|].
    destruct (Req_EM_T (cos (1 / 2 * PI * (s / l a)²)) 0).
    ++ rewrite e0.
       autorewrite with null.
       exfalso.
       apply cos_eq_0_0 in e0.
       rewrite (plus_IZR (N+1)) in sh.
       destruct Rge_dec; destruct Rge_dec.
       +++ assert (IZR N < (1 / 2 * PI * (s / l a)² - PI / 2)/PI) as lb. {
             apply (Rmult_lt_reg_r PI); [assumption|].
             apply (Rplus_lt_reg_l (PI/2)).
             apply (Rmult_lt_reg_l (2/PI)).
             zltab.
             setr ((s / l a)²).
             split; lra.
             apply sqrt_lt_0_alt.
             apply (Rmult_lt_reg_l (l a)); [assumption|].
             rewrite sqrt_Rsqr.
             lrag sl.
             apply (Rmult_le_reg_l (l a)); [assumption|].
             setl 0. setr s; [ lra|].
             apply (Rle_trans _ (l a * sqrt (2 / PI * (PI / 2 + IZR N * PI)))).
             zltab.
             left;  assumption.
           }
           assert ((1 / 2 * PI * (s / l a)² - PI / 2)/PI < IZR (N+1)) as ub. {
             apply (Rmult_lt_reg_r PI); [assumption|].
             apply (Rplus_lt_reg_l (PI/2)).
             apply (Rmult_lt_reg_l (2/PI)).
             zltab.
             setl ((s / l a)²).
             split; lra.
             apply sqrt_lt_0_alt.
             apply (Rmult_lt_reg_l (l a)); [assumption|].
             rewrite sqrt_Rsqr.
             lrag sh.
             apply (Rmult_le_reg_l (l a)); [assumption|].
             setl 0. setr s; [ lra|].
             apply (Rle_trans _ (l a * sqrt (2 / PI * (PI / 2 + IZR N * PI)))).
             zltab.
             left;  assumption.  }
           clear sl sh.
           set (A :=  1 / 2 * PI * (s / l a)²) in *.
           destruct e0 as [k g].
           rewrite g in lb, ub.
           clear - lb ub pigt0.
           generalize ub;
             fieldrewrite ((IZR k * PI + PI / 2 - PI / 2) / PI) (IZR k);
             [lra| clear ub; intro ub].
           generalize lb;
             fieldrewrite ((IZR k * PI + PI / 2 - PI / 2) / PI) (IZR k);
             [lra| clear lb; intro lb].
           apply lt_IZR in ub.
           apply lt_IZR in lb.
           omega.
       +++ clear - r n0.
           apply Rnot_ge_lt in n0.
           apply lt_IZR in n0.
           apply Rge_le in r.
           apply le_IZR in r.
           omega.
       +++ apply Rnot_ge_lt in n0.
           assert (IZR (N+1) = 0) as n1z. {
             clear - n0 r.
             apply lt_IZR in n0.
             apply Rge_le in r.
             apply le_IZR in r.
             apply IZR_eq.
             omega. }
           rewrite n1z in sl, sh.
           autorewrite with null in sl, sh.
           assert (2 / PI * (PI / 2) = 1) as id;
             [ field; lra|].
           rewrite id, sqrt_1, Rmult_1_r in sl, sh.
           clear id n1z n0 r n e ds zlta s1 s2 N f.
           clear px py mx my.
           destruct e0 as [k adef].
           assert (-1 < s / l a) as lb. {
             apply (Rmult_lt_reg_r (l a)).
             assumption.
             lrag sl. }
           assert (s / l a < 1) as ub. {
             apply (Rmult_lt_reg_r (l a)).
             assumption.
             lrag sh. }
           assert ((s / l a)² = 2 * IZR k + 1) as eql2. {
             apply (Rmult_eq_reg_l (1 / 2 * PI)).
             lrag adef.
             apply Rmult_integral_contrapositive_currified; lra.
           }
           assert ((s / l a)² < 1) as aslt1. {
             setr (1²).
             apply Rsqr_lt_abs_1.
             rewrite Rabs_R1.
             destruct (Rge_dec (s / l a) 0).
             rewrite Rabs_right; assumption.
             apply Rnot_ge_lt in n.
             rewrite Rabs_left; [lra|assumption]. }
           rewrite eql2, <- mult_IZR, <- plus_IZR in aslt1.
           rewrite <- mult_IZR, <- plus_IZR in eql2.
           specialize (Rle_0_sqr (s/l a)) as ann.
           rewrite eql2 in ann.
           apply lt_IZR in aslt1.
           apply le_IZR in ann.
           clear - ann aslt1.
           omega.
       +++ assert ((1 / 2 * PI * (s / l a)² - PI / 2)/PI < - IZR (N+1)) as lb. {
             rewrite (Rsqr_neg (s/ l a)).
             apply (Rmult_lt_reg_r PI); [assumption|].
             apply (Rplus_lt_reg_l (PI/2)).
             setr (PI / 2 - IZR (N + 1) * PI).
             apply (Rmult_lt_reg_l (2/PI)).
             zltab.
             setl ((- s / l a)²).
             split; lra.
             apply sqrt_lt_0_alt.
             apply (Rmult_lt_reg_l (l a)); [assumption|].
             rewrite sqrt_Rsqr.
             apply Ropp_lt_cancel.
             lrag sl.
             apply (Rmult_le_reg_l (l a)); [assumption|].
             setl 0. setr (-s); [ lra|].
             apply Ropp_le_cancel.
             rewrite Ropp_involutive, Ropp_0.
             apply (Rle_trans _ (- l a * sqrt (2 / PI * (PI / 2 - (IZR (N+1)+1) * PI)))).
             left;  assumption.
             apply Ropp_le_cancel.
             rewrite Ropp_0.
             setr (l a * sqrt (2 / PI * (PI / 2 - (IZR (N + 1) + 1) * PI))).
             zltab.
           }
           assert (- (IZR (N + 1) + 1) <
                   (1 / 2 * PI * (s / l a)² - PI / 2)/PI) as ub. {
             apply (Rmult_lt_reg_r PI); [assumption|].
             apply (Rplus_lt_reg_l (PI/2)).
             setl (PI / 2 - (IZR (N + 1) + 1) * PI).
             apply (Rmult_lt_reg_l (2/PI)).
             zltab.
             setr ((- s / l a)²).
             split; lra.
             apply sqrt_lt_0_alt.
             apply (Rmult_lt_reg_l (l a)); [assumption|].
             rewrite sqrt_Rsqr.
             apply Ropp_lt_cancel.
             setl s; [lra|].
             lrag sh.
             apply (Rmult_le_reg_l (l a)); [assumption|].
             setl 0. setr (-s); [ lra|].
             apply Ropp_le_cancel.
             rewrite Ropp_involutive, Ropp_0.
             apply (Rle_trans _ (- l a *
                                   sqrt (2 / PI * (PI / 2 - (IZR (N + 1) + 1) * PI)))).
             left;  assumption.
             apply Ropp_le_cancel.
             rewrite Ropp_0.
             setr (l a * sqrt (2 / PI * (PI / 2 - (IZR (N + 1) + 1) * PI))).
             zltab.
           }
           clear sl sh.
           set (A :=  1 / 2 * PI * (s / l a)²) in *.
           destruct e0 as [k g].
           rewrite g in lb, ub.
           clear - lb ub pigt0.
           generalize ub;
             fieldrewrite ((IZR k * PI + PI / 2 - PI / 2) / PI) (IZR k);
             [lra| clear ub; intro ub].
           generalize lb;
             fieldrewrite ((IZR k * PI + PI / 2 - PI / 2) / PI) (IZR k);
             [lra| clear lb; intro lb].
           rewrite <- plus_IZR, <- opp_IZR in ub.
           rewrite <- opp_IZR in lb.
           apply lt_IZR in ub.
           apply lt_IZR in lb.
           omega.
    ++ autorewrite with null.
       intro.
       apply n0.
       destruct (Req_EM_T my 0).
       exfalso.
       apply ds. split; auto.
       apply (Rmult_eq_reg_l (- my)).
       autorewrite with null.
       assumption.
       apply Ropp_neq_0_compat.
       assumption.
  Qed.

  (* begin hide *)
  

  Lemma sf_deriv_ne0_mxne0 : forall N s (mvne0 : 0 <> mx),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s < s2 ->
      Derive sf s <> 0.
  Proof.
    intros.
    unfold sf, estp in *.
    destruct H as [sl sh].
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    set (f := (fun q : R => safe_pt (Fx a q) (Fy a q))).
    specialize (sf_deriv s) as spdv.
    change (is_derive
              f s ((fun p => (mx * sin (1 / 2 * PI * (p / l a)²) +
                              - my * cos (1 / 2 * PI * (p / l a)²))) s))
      in spdv.
    set (f' := (fun p : R =>
                  mx * sin (1 / 2 * PI * (p / l a)²) +
                  - my * cos (1 / 2 * PI * (p / l a)²))) in *.
    apply is_derive_unique in spdv.
    rewrite spdv.
    unfold f'.
    unfold s1, euler_spiral_tangent_pt in sl.
    unfold s2, euler_spiral_tangent_pt in sh.
    clear spdv f' f s1 s2.

    destruct (Req_EM_T 0 mx);
      [lra| clear n].

    destruct (Req_EM_T (cos (1 / 2 * PI * (s / l a)²)) 0)
      as [e | cne0 ];
      [rewrite e;
       autorewrite with null;
       apply Rmult_integral_contrapositive_currified; auto;
       apply coseq0_sinneq0; auto|].

    destruct Rge_dec;
      destruct Rge_dec;
      [| apply Rnot_ge_lt in n;
         rewrite plus_IZR in n;
         exfalso;
         lra | | ].

    + rdsk2 sl sh.
      assert (C1 < C2) as c1ltc2. lra.
      intro ne0.
      assert (tan (1 / 2 * PI * (s / l a)²) = my / mx) as tid. {
        apply (Rmult_eq_reg_l
                 (mx * cos (1 / 2 * PI * (s / l a)²))); auto.
        apply (Rplus_eq_reg_l
                 (- my * cos (1 / 2 * PI * (s / l a)²))).
        unfold tan.
        setr 0. auto.
        setl (mx * sin (1 / 2 * PI * (s / l a)²) +
              - my * cos (1 / 2 * PI * (s / l a)²)).
        auto.
        assumption. }

      rewrite c1d in sl.
      rewrite c2d in sh.

      assert (k + IZR N * PI <
              1 / 2 * PI * (s / l a)²) as ctra. {
        apply (Rmult_lt_reg_l (2 / PI)).
        setr (2 * / PI); try lra.
        zltab.
        setr ((s / l a)²).
        split; lra.
        apply sqrt_lt_0_alt.
        rewrite sqrt_Rsqr.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        setr s. lra.
        assumption.
        apply (Rle_lt_trans 0) in sl.
        left.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        setl 0. setr s.
        lra.
        assumption.
        zltab.
      }

      
      assert (1 / 2 * PI * (s / l a)² <
              k + IZR (N+1) * PI) as ctrb. {
        apply (Rmult_lt_reg_l (2 / PI)).
        setr (2 * / PI); try lra.
        zltab.
        setl ((s / l a)²).
        split; lra.
        apply sqrt_lt_0_alt.
        rewrite sqrt_Rsqr.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        setl s. lra.
        assumption.
        apply (Rle_lt_trans 0) in sl.
        left.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        setl 0. setr s.
        lra.
        assumption.
        zltab. }
      
      clear sl sh.
      specialize (inrange_mT2T2
                    (1 / 2 * PI * (s / l a)²) _ pigt0)
        as [p [alb aub]].

      destruct aub as [aub|aeq].
      ++ set (A := 1 / 2 * PI * (s / l a)² + IZR p * PI) in *.
         assert (k + IZR (N+p) * PI < A) as alb2. {
           rewrite plus_IZR.
           unfold A.
           apply (Rplus_lt_reg_r (- IZR p* PI)).
           lrag ctra. }
         clear ctra.
         
         assert (A < k + IZR ((N + p) + 1) * PI) as aub2. {
           rewrite <- Zplus_assoc, (Zplus_comm p), Zplus_assoc.
           rewrite plus_IZR.
           unfold A.
           apply (Rplus_lt_reg_r (- IZR p * PI)).
           lrag ctrb. }
         clear ctrb.
         
         set (M := (N+p)%Z) in *.

         rewrite <- (tan_period _ p) in tid; [|assumption].
         change (tan A = my / mx) in tid.

         apply (f_equal atan) in tid.
         unfold atan in tid at 1.
         destruct (pre_atan (tan A)) as [A' [[A'lb A'ub] ad]].
         apply tan_is_inj in ad; try (split; assumption).
         rewrite ad in tid.
         clear ad A'ub A'lb A'.
         destruct kdef as [kdef | kdef].
         +++ rewrite kdef, <- tid in alb2, aub2.
             assert (IZR M < 0) as mlt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag alb2. }
             assert (0 < IZR (M+1)) as mgt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag aub2. }
             apply lt_IZR in mlt.
             apply lt_IZR in mgt.
             omega.
         +++ rewrite kdef, <- tid in alb2, aub2.
             assert (IZR (M+1) < 0) as mlt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               rewrite plus_IZR.
               lrag alb2. }
             
             assert (0 < IZR (M+2)) as mgt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               rewrite plus_IZR.
               fieldrewrite 2 (1+1).
               rewrite <- Rplus_assoc.
               rewrite <- plus_IZR.
               lrag aub2. }
             apply lt_IZR in mlt.
             apply lt_IZR in mgt.
             omega.
      ++ assert (1/2 * PI * (s / l a)² = PI/2 + IZR (-p) * PI) as id;
           [apply (Rplus_eq_reg_r (IZR p * PI));
            rewrite opp_IZR;
            rewrite aeq;
            field|];
           rewrite id in cne0;
           apply cne0;
           specialize (Z.Even_or_Odd (-p)) as eoo;
           destruct eoo as [npe|npo].
         +++ unfold Z.Even in npe.
             destruct npe as [b def].
             rewrite def.
             rewrite mult_IZR.
             rewrite cos_period1.
             apply cos_PI2.
         +++ unfold Z.Odd in npo.
             destruct npo as [b def].
             rewrite def.
             rewrite plus_IZR, mult_IZR.
             fieldrewrite (PI / 2 + (2 * IZR b + 1) * PI)
                          (3 * (PI / 2) + 2 * IZR b * PI).
             rewrite cos_period1.
             apply cos_3PI2.
    + apply Rnot_ge_lt in n.
      destruct r as [p|z]; [
        clear - n p;
        apply lt_IZR in n;
        apply Rgt_lt in p;
        apply lt_IZR in p;
        omega |].

      rewrite z in *.
      autorewrite with null in *.
      rdsk2 sl sh.

      assert (C1 < C2) as c1ltc2. lra.
      rewrite c1d, c2d in *.
      intro ne0.
      assert (tan (1 / 2 * PI * (s / l a)²) = my / mx) as tid. {
        apply (Rmult_eq_reg_l
                 (mx * cos (1 / 2 * PI * (s / l a)²))); auto.
        apply (Rplus_eq_reg_l
                 (- my * cos (1 / 2 * PI * (s / l a)²))).
        unfold tan.
        setr 0. auto.
        setl (mx * sin (1 / 2 * PI * (s / l a)²) +
              - my * cos (1 / 2 * PI * (s / l a)²)).
        auto.
        assumption. }

      assert (1 / 2 * PI * (s / l a)² < k) as ctra. {
        destruct (Rle_dec s 0).
        - apply (Rmult_lt_reg_l (2 / PI)).
          setr (2 * / PI); try lra.
          zltab.
          setl ((- s  / l a)²).
          split; lra.
          apply sqrt_lt_0_alt.
          rewrite sqrt_Rsqr.
          apply (Rmult_lt_reg_l (l a)); try assumption.
          apply Ropp_lt_cancel.
          lrag sl.
          apply (Rmult_le_reg_r (l a)).
          assumption.
          apply Ropp_le_cancel.
          lrag r.
        - apply Rnot_le_lt in n0.
          apply (Rmult_lt_reg_l (2 / PI)).
          setr (2 * / PI); try lra.
          zltab.
          setl ((s / l a)²).
          split; lra.
          apply sqrt_lt_0_alt.
          rewrite sqrt_Rsqr.
          apply (Rmult_lt_reg_l (l a)); try assumption.
          setl s. lra.
          lrag sh.
          apply (Rmult_le_reg_r (l a)).
          assumption.
          lrag n0. }

      assert (0 <= 1 / 2 * PI * (s / l a)²) as ctrb;
                                                      [ zltab |].
      clear sl sh.

      specialize (inrange_mT2T2
                    (1 / 2 * PI * (s / l a)²) _ pigt0)
        as [p [alb aub]].

      destruct aub as [aub|aeq].
      ++ set (A := 1 / 2 * PI * (s / l a)² + IZR p * PI) in *.
         assert (IZR (p) * PI <= A) as alb2. {
           unfold A.
           apply (Rplus_le_reg_r (- IZR p * PI)).
           lrag ctrb. }
         clear ctrb.
         
         assert (A < k + IZR p * PI) as aub2. {
           unfold A.
           apply (Rplus_lt_reg_r (- IZR p * PI)).
           lrag ctra. }
         clear ctra.
         
         rewrite <- (tan_period _ p) in tid; [|assumption].
         change (tan A = my / mx) in tid.

         apply (f_equal atan) in tid.
         unfold atan in tid at 1.
         destruct (pre_atan (tan A)) as [A' [[A'lb A'ub] ad]].
         apply tan_is_inj in ad; try (split; assumption).
         rewrite ad in tid.
         clear ad A'ub A'lb A'.
         destruct kdef as [kdef | kdef].
         +++ rewrite <- kdef in tid.
             rewrite tid in alb2, aub2, aub, alb.
             assert (0 < IZR p) as pgt0.
             apply (Rmult_lt_reg_r PI).
             assumption.
             apply (Rplus_lt_reg_l k).
             lrag aub2.
             assert (1 <= IZR p) as olep. {
               apply lt_IZR in pgt0.
               apply IZR_le.
               omega. }
             clear - olep alb2 pigt0 aub alb.
             assert (PI/2 <= k) as ctr. {
               apply (Rle_trans _ (PI)); [ lra|].
               rewrite <- (Rmult_1_l PI).
               apply (Rle_trans _ (IZR p * PI)); [|assumption].
               apply (Rmult_le_reg_r (/ PI));
                 [ zltab| lrag olep]. }
             lra.
         +++ symmetry in kdef.
             assert (atan (my/mx) = k - PI) as atmymx. {
               apply (Rplus_eq_reg_r PI).
               lrag kdef. }
             rewrite atmymx in tid.
             rewrite tid in alb, aub, alb2, aub2.
             clear tid atmymx.
             
             assert (- PI < IZR p * PI) as pub. {
               lra. }
             assert (0 <= IZR p) as pge0. {
               assert (-1 < IZR p) as pgtn1. {
                 apply (Rmult_lt_reg_r PI).
                 lra.
                 lrag pub. }
               apply lt_IZR in pgtn1.
               apply IZR_le.
               omega. }
             clear aub2 aub pub.
             assert (PI <= k) as kub. {
               apply (Rplus_le_reg_r (-PI)).
               apply (Rle_trans _ (IZR p * PI)).
               setl 0.
               zltab.
               lrag alb2. }
             lra.
      ++ assert (1/2 * PI * (s / l a)² = PI/2 + IZR (-p) * PI) as id;
           [apply (Rplus_eq_reg_r (IZR p * PI));
            rewrite opp_IZR;
            rewrite aeq;
            field|];
           rewrite id in cne0;
           apply cne0;
           specialize (Z.Even_or_Odd (-p)) as eoo;
           destruct eoo as [npe|npo].
         +++ unfold Z.Even in npe.
             destruct npe as [b def].
             rewrite def.
             rewrite mult_IZR.
             rewrite cos_period1.
             apply cos_PI2.
         +++ unfold Z.Odd in npo.
             destruct npo as [b def].
             rewrite def.
             rewrite plus_IZR, mult_IZR.
             fieldrewrite (PI / 2 + (2 * IZR b + 1) * PI)
                          (3 * (PI / 2) + 2 * IZR b * PI).
             rewrite cos_period1.
             apply cos_3PI2.
    + apply Rnot_ge_lt in n.
      apply Rnot_ge_lt in n0.
      rdsk2 sl sh.
      assert (C1 < C2) as c1ltc2. lra.
      intro ne0.
      assert (tan (1 / 2 * PI * (s / l a)²) = my / mx) as tid. {
        apply (Rmult_eq_reg_l
                 (mx * cos (1 / 2 * PI * (s / l a)²))); auto.
        apply (Rplus_eq_reg_l
                 (- my * cos (1 / 2 * PI * (s / l a)²))).
        unfold tan.
        setr 0. auto.
        setl (mx * sin (1 / 2 * PI * (s / l a)²) +
              - my * cos (1 / 2 * PI * (s / l a)²)).
        auto.
        assumption. }

      rewrite c1d in sl.
      rewrite c2d in sh.

      assert (k - IZR (N + 1 + 1) * PI <
              1 / 2 * PI * (s / l a)²) as ctra. {
        apply (Rmult_lt_reg_l (2 / PI)).
        setr (2 * / PI); try lra.
        zltab.
        setr ((- s / l a)²).
        split; lra.
        apply sqrt_lt_0_alt.
        rewrite sqrt_Rsqr.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        apply Ropp_lt_cancel.
        setl s. lra.
        lrag sh.
        zltab.
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        apply (Rle_trans _ (- l a * sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI)))).
        left; assumption.
        apply Ropp_le_cancel.
        rewrite Ropp_0.
        setr (l a * sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI))).
        zltab. }

      
      assert (1 / 2 * PI * (s / l a)² <
              k - IZR (N+1) * PI) as ctrb. {
        apply (Rmult_lt_reg_l (2 / PI)).
        setr (2 * / PI); try lra.
        zltab.
        setl ((- s / l a)²).
        split; lra.
        apply sqrt_lt_0_alt.
        rewrite sqrt_Rsqr.
        apply (Rmult_lt_reg_l (l a)); try assumption.
        apply Ropp_lt_cancel.
        setr s. lra.
        lrag sl.
        zltab.
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        apply (Rle_trans _ (- l a * sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI)))).
        left; assumption.
        apply Ropp_le_cancel.
        rewrite Ropp_0.
        setr (l a * sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI))).
        zltab. }

      clear sl sh.
      specialize (inrange_mT2T2
                    (1 / 2 * PI * (s / l a)²) _ pigt0)
        as [p [alb aub]].

      destruct aub as [aub|aeq].
      ++ set (A := 1 / 2 * PI * (s / l a)² + IZR p * PI) in *.
         assert (k - IZR ((N-p)+1+1) * PI < A) as alb2. {
           repeat rewrite plus_IZR.
           rewrite minus_IZR.
           repeat rewrite plus_IZR in ctra.
           unfold A.
           apply (Rplus_lt_reg_r (- IZR p* PI)).
           lrag ctra. }
         clear ctra.
         
         assert (A < k - IZR ((N - p) + 1) * PI) as aub2. {
           rewrite plus_IZR, minus_IZR.
           rewrite plus_IZR in ctrb.
           unfold A.
           apply (Rplus_lt_reg_r (- IZR p* PI)).
           lrag ctrb. }
         clear ctrb.
         
         set (M := (N-p+1)%Z) in *.

         rewrite <- (tan_period _ p) in tid; [|assumption].
         change (tan A = my / mx) in tid.

         apply (f_equal atan) in tid.
         unfold atan in tid at 1.
         destruct (pre_atan (tan A)) as [A' [[A'lb A'ub] ad]].
         apply tan_is_inj in ad; try (split; assumption).
         rewrite ad in tid.
         clear ad A'ub A'lb A'.
         destruct kdef as [kdef | kdef].
         +++ rewrite kdef, <- tid in alb2, aub2.
             assert (IZR M < 0) as mlt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag alb2. }
             assert (0 < IZR (M+1)) as mgt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag aub2. }
             apply lt_IZR in mlt.
             apply lt_IZR in mgt.
             omega.
         +++ rewrite kdef, <- tid in alb2, aub2.
             assert (1 < IZR (M+1)) as mlt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag alb2. }
             
             assert (IZR M < 1) as mgt. {
               apply (Rmult_lt_reg_r PI).
               auto.
               apply (Rplus_lt_reg_l A).
               lrag aub2. }
             apply lt_IZR in mlt.
             apply lt_IZR in mgt.
             omega.
      ++ assert (1/2 * PI * (s / l a)² = PI/2 + IZR (-p) * PI) as id;
           [apply (Rplus_eq_reg_r (IZR p * PI));
            rewrite opp_IZR;
            rewrite aeq;
            field|];
           rewrite id in cne0;
           apply cne0;
           specialize (Z.Even_or_Odd (-p)) as eoo;
           destruct eoo as [npe|npo].
         +++ unfold Z.Even in npe.
             destruct npe as [b def].
             rewrite def.
             rewrite mult_IZR.
             rewrite cos_period1.
             apply cos_PI2.
         +++ unfold Z.Odd in npo.
             destruct npo as [b def].
             rewrite def.
             rewrite plus_IZR, mult_IZR.
             fieldrewrite (PI / 2 + (2 * IZR b + 1) * PI)
                          (3 * (PI / 2) + 2 * IZR b * PI).
             rewrite cos_period1.
             apply cos_3PI2.
  Qed.
(* end hide *)

  Lemma sf_deriv_ne0 : forall N s,
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s < s2 -> Derive sf s <> 0.
  Proof.
    intros.
    destruct (Req_EM_T 0 mx).
    eapply sf_deriv_ne0_mxeq0; try eassumption.
    eapply sf_deriv_ne0_mxne0; try eassumption.
  Qed.

(* begin hide *)
  Lemma spiral_posarm_N_order_mxne0 :
    forall N (mvne0 : 0 <> mx)
           (nnn : (0 <= N)%Z),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.

    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [lra| clear n].
    
    destruct Rge_dec;
      destruct Rge_dec;
      [| apply Rnot_ge_lt in n;
         rewrite plus_IZR in n;
         exfalso;
         lra | | ].

    + match goal with | |- ?A < ?B => rdsk2t A B end.
      rewrite c1d, c2d.
      apply (Rmult_lt_reg_r (/ l a)).
      zltab.
      setl (sqrt (2 / PI * (k + IZR N * PI))); [lra|].
      setr (sqrt (2 / PI * (k + IZR (N + 1) * PI))); [lra|].
      apply sqrt_lt_1.
      zltab.
      zltab.
      apply (Rplus_lt_reg_r (- 2 / PI * (k + IZR N * PI))).
      apply (Rmult_lt_reg_r (/ 2)). lra.
      setl 0. lra.
      setr (IZR (N + 1) - IZR N). lra.
      rewrite <- minus_IZR.
      apply IZR_lt.
      omega.

    + exfalso.
      apply Rnot_ge_lt in n.
      apply IZR_le in nnn.
      lra.
    + exfalso.
      apply Rnot_ge_lt in n.
      apply Rnot_ge_lt in n0.
      apply IZR_le in nnn.
      lra.
  Qed.

  Lemma spiral_negarm_N_order_mxne0 :
    forall N
           (mvne0 : 0 <> mx)
           (nnn : (N + 1 < 0)%Z),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.

    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [lra| clear n].
    
    destruct (Rge_dec (IZR (N+1)) 0);
      destruct Rge_dec;
      [ exfalso;
        apply IZR_lt in nnn;
        rewrite plus_IZR in nnn, r;
        lra
      | exfalso;
        apply Rnot_ge_lt in n;
        apply IZR_lt in nnn;
        rewrite plus_IZR in r, nnn;
        lra
      | exfalso;
        apply Rnot_ge_lt in n;
        rewrite plus_IZR in n;
        lra|].
    
    + apply Rnot_ge_lt in n.
      apply Rnot_ge_lt in n0.
      match goal with | |- ?A < ?B => rdsk2t A B end.
      rewrite c1d, c2d.
      apply (Rmult_lt_reg_r (/ l a)).
      zltab.
      setr (- sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI))); [lra|].
      setl (- sqrt (2 / PI * (k - IZR (N + 1) * PI))); [lra|].
      apply Ropp_lt_contravar.
      apply sqrt_lt_1.
      zltab.
      
      apply (Rle_trans _ (k - 0 * PI)).
      lra.
      apply (Rplus_le_reg_r (- k)).
      apply (Rmult_le_reg_r (/ PI)).
      zltab.
      setl (-0). lra.
      setr (- IZR (N + 1 + 1)). lra.
      apply Ropp_le_contravar.
      apply IZR_le.
      omega.

      apply (Rmult_le_reg_r (PI / 2)). lra.
      setl 0.
      setr (k - IZR (N + 1) * PI). lra.
      apply (Rle_trans _ (k - 0 * PI)).
      lra.
      apply (Rplus_le_reg_r (- k)).
      apply (Rmult_le_reg_r (/ PI)).
      zltab.
      setl (-0). lra.
      setr (- IZR (N + 1)). lra.
      apply Ropp_le_contravar.
      apply IZR_le.
      omega.

      apply (Rmult_lt_reg_r (PI / 2)). lra.
      apply (Rplus_lt_reg_r (- k)).
      apply (Rmult_lt_reg_r (/ PI)).
      zltab.
      setl (- IZR (N + 1 + 1)). lra.
      setr (- IZR (N + 1)). lra.
      apply Ropp_lt_contravar.
      apply IZR_lt.
      omega.
  Qed.


  Lemma spiral_midarm_N_order_mxmyne0 :
    forall N
           (myne0 : 0 <> my)
           (mxne0 : 0 <> mx)
           (nnge0 : ~ (IZR N >= 0))
           (np1ge0 : IZR (N + 1) >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.
    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [lra| clear n].
    
    destruct Rge_dec;
      destruct Rge_dec; try lra.
    apply Rnot_ge_lt in n.
    destruct r as [p|z]; [
      clear - n p;
      apply lt_IZR in n;
      apply Rgt_lt in p;
      apply lt_IZR in p;
      omega |].
    
    rewrite z in *.
    arn.
    match goal with | |- ?A < ?B => rdsk2t A B end.
    rewrite c1d, c2d.
    apply (Rlt_trans _ 0).
    rewrite <- Ropp_0.
    setl (- (l a * sqrt (2 / PI * k))).
    apply Ropp_lt_contravar.
    zltab.
    rewrite <- sqrt_0.
    apply sqrt_lt_1;
      [right; reflexivity| zltab| zltab].
    zltab.
    rewrite <- sqrt_0.
    apply sqrt_lt_1;
      [right; reflexivity| zltab| zltab].
  Qed.


  Lemma spiral_posarm_N_order_mxeq0 :
    forall N
           (mveq0 : 0 = mx)
           (nnn : (0 <= N)%Z),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.

    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [clear e| lra].
    
    destruct Rge_dec;
      destruct Rge_dec;
      [| apply Rnot_ge_lt in n;
         rewrite plus_IZR in n;
         exfalso;
         lra | | ];
      destruct Rlt_dec;
      [lra| |lra| |lra| ].

    + apply (Rmult_lt_reg_r (/ l a)).
      zltab.
      setl (sqrt (2 / PI * (PI / 2 + IZR N * PI))); [lra|].
      setr (sqrt (2 / PI * (PI / 2 + IZR (N + 1) * PI))); [lra|].
      apply sqrt_lt_1.
      zltab.
      zltab.
      apply (Rplus_lt_reg_r (- 2 / PI * (PI / 2 + IZR N * PI))).
      apply (Rmult_lt_reg_r (/ 2)). lra.
      setl 0. lra.
      setr (IZR (N + 1) - IZR N). lra.
      rewrite <- minus_IZR.
      apply IZR_lt.
      omega.

    + exfalso.
      apply Rnot_ge_lt in n.
      apply IZR_le in nnn.
      lra.
    + exfalso.
      apply Rnot_ge_lt in n.
      apply Rnot_ge_lt in n0.
      apply IZR_le in nnn.
      lra.
  Qed.

  Lemma spiral_negarm_N_order_mxeq0 :
    forall N
           (mveq0 : 0 = mx)
           (nnn : (N + 1 < 0)%Z),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.

    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [clear e| lra].
    
    destruct (Rge_dec (IZR (N+1)) 0);
      destruct Rge_dec;
      [ exfalso;
        apply IZR_lt in nnn;
        rewrite plus_IZR in nnn, r;
        lra
      | exfalso;
        apply Rnot_ge_lt in n;
        apply IZR_lt in nnn;
        rewrite plus_IZR in r, nnn;
        lra
      | exfalso;
        apply Rnot_ge_lt in n;
        rewrite plus_IZR in n;
        lra|];
      destruct Rlt_dec;
      [lra| ].

    + apply Rnot_ge_lt in n.
      apply Rnot_ge_lt in n0.
      set (k := PI / 2) in *.
      apply (Rmult_lt_reg_r (/ l a)).
      zltab.
      setr (- sqrt (2 / PI * (k - IZR (N + 1 + 1) * PI))); [lra|].
      setl (- sqrt (2 / PI * (k - IZR (N + 1) * PI))); [lra|].
      apply Ropp_lt_contravar.
      apply sqrt_lt_1.
      zltab.
      
      apply (Rle_trans _ (k - 0 * PI)).
      lra.
      apply (Rplus_le_reg_r (- k)).
      apply (Rmult_le_reg_r (/ PI)).
      zltab.
      setl (-0). lra.
      setr (- IZR (N + 1 + 1)). lra.
      apply Ropp_le_contravar.
      apply IZR_le.
      omega.

      apply (Rmult_le_reg_r (PI / 2)). lra.
      setl 0.
      setr (k - IZR (N + 1) * PI). lra.
      apply (Rle_trans _ (k - 0 * PI)).
      lra.
      apply (Rplus_le_reg_r (- k)).
      apply (Rmult_le_reg_r (/ PI)).
      zltab.
      setl (-0). lra.
      setr (- IZR (N + 1)). lra.
      apply Ropp_le_contravar.
      apply IZR_le.
      omega.

      apply (Rmult_lt_reg_r (PI / 2)). lra.
      apply (Rplus_lt_reg_r (- k)).
      apply (Rmult_lt_reg_r (/ PI)).
      zltab.
      setl (- IZR (N + 1 + 1)). lra.
      setr (- IZR (N + 1)). lra.
      apply Ropp_lt_contravar.
      apply IZR_lt.
      omega.
  Qed.


  Lemma spiral_midarm_N_order_mxeq0 :
    forall N
           (mveq0 : 0 = mx)
           (nnge0 : ~ (IZR N >= 0))
           (np1ge0 : IZR (N + 1) >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.
    clear s1 s2.

    destruct (Req_EM_T 0 mx);
      [clear e| lra].
    
    destruct Rge_dec;
      destruct Rge_dec; try lra.
    apply Rnot_ge_lt in n.
    destruct r as [p|z]; [
      clear - n p;
      apply lt_IZR in n;
      apply Rgt_lt in p;
      apply lt_IZR in p;
      omega |];
    destruct Rlt_dec;
    [lra|  ].
    rewrite z in *.
    arn.
    apply (Rlt_trans _ 0).
    rewrite <- Ropp_0.
    setl (- (l a * sqrt (2 / PI * (PI / 2)))).
    apply Ropp_lt_contravar.
    zltab.
    fieldrewrite (2 / PI * (PI / 2)) (1).
    lra.
    rewrite sqrt_1.
    lra.
    zltab.
    fieldrewrite (2 / PI * (PI / 2)) (1).
    lra.
    rewrite sqrt_1.
    lra.
  Qed.
(* end hide *)
  Lemma spiral_midarm_N_order : forall (zeqmy : 0 = my),
      let s1 := estp (-1)%Z in
      let s2 := estp 0%Z in
      s1 = 0 /\ s2 = 0.
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    exfalso.
    apply ds.
    split; auto.
    unfold s1, euler_spiral_tangent_pt in *.
    unfold s2, euler_spiral_tangent_pt in *.
    clear s1 s2.
    rewrite <- zeqmy.
    arn.
    destruct Rge_dec; [lra|].
    destruct (Req_EM_T 0 mx);[lra|].
    fieldrewrite (0 / mx) (0). auto.
    rewrite atan_0.
    destruct Rlt_dec; [lra|clear n0 n1].
    destruct Rge_dec; [clear r n|lra].
    arn.
    split; reflexivity.
  Qed.


  Lemma spiral_N_order : forall N (nv : ~(IZR N = -1 /\ my = 0)),
      let s1 := estp N in
      let s2 := estp (N+1) in
      s1 < s2.
  Proof.
    intros.
    unfold estp in *.
    destruct (Rlt_dec (IZR (N+1)) 0).
    apply lt_IZR in r.
    destruct (Req_dec 0 mx).
    apply spiral_negarm_N_order_mxeq0; try assumption.
    apply spiral_negarm_N_order_mxne0; try assumption.
    apply Rnot_lt_le in n.

    destruct (Rle_dec 0 (IZR N)).
    destruct (Req_dec 0 mx).
    apply spiral_posarm_N_order_mxeq0; try assumption.
    apply le_IZR in r; assumption.
    apply spiral_posarm_N_order_mxne0; try assumption.
    apply le_IZR in r; assumption.

    apply Rnot_le_lt in n0.
    destruct n as [p|z]; [
      apply lt_IZR in n0;
      apply Rgt_lt in p;
      apply lt_IZR in p;
      omega |].
    assert (IZR N = -1) as izrn. {
      apply IZR_eq.
      apply eq_IZR in z.
      omega. }
    destruct (Req_dec my 0).
    exfalso.
    apply nv.
    split; assumption.
    destruct (Req_dec mx 0).
    apply spiral_midarm_N_order_mxeq0; try lra.
    apply spiral_midarm_N_order_mxmyne0; try lra.
  Qed.

  Lemma spiral_N_neg : forall N (nlt0 : IZR N < -1),
      let s := estp N in s < 0.
  Proof.
    intros.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    unfold s, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra|].
    apply Rnot_ge_lt in n.
    clear n s.
    destruct Req_EM_T.
    + destruct Rlt_dec; [lra|clear n].
      setl (- (l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI)))).
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      zltab.
      apply agt0_lagt0; assumption.
      apply sqrt_lt_R0.
      zltab.
      apply (Rmult_lt_reg_r (2 / PI)).
      zltab.
      setr (1 - 2 * IZR (N + 1)).
      lra.
      arn.
      rewrite <- mult_IZR, <- minus_IZR.
      apply IZR_lt.
      apply lt_IZR in nlt0.
      omega.

    + match goal with | |- ?A < 0 => rdsk2t A A end.
      rewrite c1d.
      setl (- (l a * sqrt (2 / PI * (k - IZR (N + 1) * PI)))).
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      zltab.
      apply agt0_lagt0; assumption.
      apply sqrt_lt_R0.
      zltab.
      apply (Rplus_lt_reg_r (IZR (N + 1) * PI)).
      setr k.
      arn.
      apply (Rlt_le_trans _ 0); [|assumption].
      apply (Rmult_lt_reg_r (/ PI)).
      zltab.
      arn.
      setl (IZR (N + 1)).
      lra.
      apply IZR_lt.
      apply lt_IZR in nlt0.
      omega.
  Qed.

  Lemma spiral_N_neg1 : let s := estp (-1)%Z in s <= 0.
  Proof.
    intros.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    unfold s, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra|].
    apply Rnot_ge_lt in n.
    clear n s.
    destruct Req_EM_T.
    + destruct Rlt_dec; [lra|clear n].
      setl (- (l a * sqrt (2 / PI * (PI / 2 - IZR (-1 + 1) * PI)))).
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      zltab.
      left.
      apply agt0_lagt0; assumption.
    + assert (IZR (-1 + 1)= 0) as id. {
        rewrite plus_IZR. field. }
      rewrite id in *. clear id.
      arn.

      match goal with | |- ?A <= 0 => rdsk2t A A end.
      rewrite c1d.
      setl (- (l a * sqrt (2 / PI * (k)))).
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      zltab.
      left.
      apply agt0_lagt0; assumption.
  Qed.


  Lemma spiral_N_pos : forall N (nlt0 : 0 < IZR N),
      let s := estp N in 0 < s.
  Proof.
    intros.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    unfold s, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r s|lra].
    destruct Req_EM_T.
    + destruct Rlt_dec; [lra|clear n].
      zltab.
      apply agt0_lagt0; assumption.
      apply sqrt_lt_R0.
      zltab.
      apply (Rmult_lt_reg_r (2 / PI)).
      zltab.
      setr (1 + 2 * IZR (N )).
      lra.
      arn.
      rewrite <- mult_IZR, <- plus_IZR.
      apply IZR_lt.
      apply lt_IZR in nlt0.
      omega.

    + match goal with | |- 0 < ?A => rdsk2t A A end.
      rewrite c1d.
      zltab.
      apply agt0_lagt0; assumption.
      apply sqrt_lt_R0.
      zltab.
      apply (Rplus_lt_reg_r (- (IZR (N) * PI))).
      setr k.
      arn.
      apply (Rlt_le_trans _ 0); [|assumption].
      apply (Rmult_lt_reg_r (/ PI)).
      zltab.
      arn.
      setl (- IZR (N)).
      lra.
      lra.
  Qed.

  Lemma spiral_N_pos1 : let s := estp 0%Z in 0 <= s.
  Proof.
    intros.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    unfold s, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r s|lra].
    destruct Req_EM_T.
    + destruct Rlt_dec; [lra|clear n].
      zltab.
      left.
      apply agt0_lagt0; assumption.
    + arn.
      match goal with | |- 0 <= ?A => rdsk2t A A end.
      rewrite c1d.
      zltab.
      left.
      apply agt0_lagt0; assumption.
  Qed.

(* begin hide *)
  Lemma sf_2deriv_sign_Ngt0_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nge0 : IZR N > 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    apply Rgt_lt in Nge0.
    specialize (spiral_N_pos N Nge0) as s1gt0;
      change (0 < s1) in s1gt0.
    rewrite <- signeq1_eqv in s1gt0.
    assert (0 < IZR (N+1)) as N1ge0. rewrite plus_IZR. lra.
    specialize (spiral_N_pos (N+1) N1ge0) as s2gt0;
      change (0 < s2) in s2gt0.
    rewrite <- signeq1_eqv in s2gt0.
    rewrite s1gt0, s2gt0.
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r|lra].
    destruct Rge_dec; [clear r | rewrite plus_IZR in n; lra].
    destruct Req_EM_T; [lra| clear n].

    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      rdsk2t A B
    end.
    rewrite c1d, c2d.

    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0; try zltab.

    rewrite plus_IZR.
    fieldrewrite (k + (IZR N + 1) * PI) ((k + IZR N * PI) + PI).
    set (A := k + IZR N * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 2.
    destruct total_order_T; [destruct s|]; lra.
  Qed.

  Lemma sf_2deriv_sign_midarm_mxne0 :
    forall N
           (mxne0 : 0 <> mx)
           (nnge0 : IZR N < 0)
           (np1ge0 : IZR (N + 1) >= 0)
           (zlta : 0 < a)
           (ds : ~ (mx = 0 /\ my = 0)),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.

    assert (N = -1)%Z as ndef. {
      apply lt_IZR in nnge0.
      apply Rge_le in np1ge0.
      apply le_IZR in np1ge0.
      clear - nnge0 np1ge0.
      omega. }
    assert (0 = N + 1)%Z as zeq. {
      omega. }

    
    specialize (euler_tan_pt_symm _ np1ge0) as s1rs2.
    simpl in s1rs2.
    assert (- (N + 1) - 1 = N)%Z as zn. {
      rewrite ndef.
      omega. }
    rewrite zn in s1rs2. clear zn.
    change (s2 = - s1) in s1rs2.
    
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.


    specialize (spiral_N_neg1) as s1le0.
    rewrite <- ndef in s1le0.
    change (s1 <= 0) in s1le0.
    specialize (spiral_N_pos1) as s2ge0.
    simpl in s2ge0.
    rewrite zeq in s2ge0 at 2.
    change (0 <= s2) in s2ge0.

    destruct s1le0 as [s1lt0 |s1eq0].
    destruct s2ge0 as [s2gt0 |s2eq0].
    rewrite <- signeq1_eqv in s2gt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2gt0.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra|clear n].
    destruct Rge_dec; [clear r | lra].
    destruct Req_EM_T; [lra| clear n].

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      rdsk2t A B 
    end.
    rewrite c1d, c2d.

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa;
      [ |rewrite <- zeq;
         arn;
         assumption].
    rewrite rwa0;
      [ |rewrite <- zeq;
         arn;
         assumption].
    rewrite <- zeq.
    arn.
    field.

    rewrite s1rs2 in s2eq0.
    symmetry in s2eq0.
    apply Ropp_eq_0_compat in s2eq0.
    rewrite Ropp_involutive in s2eq0.
    rewrite s2eq0 in s1lt0.
    lra.

    rewrite s1eq0 in s1rs2.
    rewrite Ropp_0 in s1rs2.
    rewrite s1rs2, s1eq0.
    rewrite sign_0.
    field.
  Qed.

  Lemma sf_2deriv_sign_Nge0_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nge0 : IZR N >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall  (s1ne0 : s1 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    apply Rge_le in Nge0.
    assert (0 < s1) as s1gt0. {
      destruct Nge0 as [Ngt |Neq].
      apply (spiral_N_pos N Ngt).
      unfold s1 in *.
      clear s1.
      apply eq_IZR in Neq.
      rewrite <- Neq in *.
      set (s1 := euler_spiral_tangent_pt 0) in *.
      specialize (spiral_N_pos1) as s1ge0;
        change (0 <= s1) in s1ge0.
      destruct s1ge0 as [s1gt0 |s1eq0].
      assumption.
      lra. }
    rewrite <- signeq1_eqv in s1gt0.
    assert (0 < IZR (N+1)) as N1ge0. rewrite plus_IZR. lra.
    specialize (spiral_N_pos (N+1) N1ge0) as s2gt0;
      change (0 < s2) in s2gt0.
    rewrite <- signeq1_eqv in s2gt0.
    rewrite s1gt0, s2gt0.
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r|lra].
    destruct Rge_dec; [clear r | rewrite plus_IZR in n; lra].
    destruct Req_EM_T; [lra| clear n].

    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      rdsk2t A B
    end.
    rewrite c1d, c2d.

    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0; try zltab.

    rewrite plus_IZR.
    fieldrewrite (k + (IZR N + 1) * PI) ((k + IZR N * PI) + PI).
    set (A := k + IZR N * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 2.
    destruct total_order_T; [destruct s|]; lra.
  Qed.




  Lemma sf_2deriv_sign_Ngt0_mxeq0 :
    forall N
           (mveq0 : 0 = mx)
           (Nge0 : IZR N > 0)
           (zlta : 0 < a)
           (ds : ~ (mx = 0 /\ my = 0)),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    apply Rgt_lt in Nge0.
    specialize (spiral_N_pos N Nge0) as s1gt0;
      change (0 < s1) in s1gt0.
    rewrite <- signeq1_eqv in s1gt0.
    assert (0 < IZR (N+1)) as N1ge0. rewrite plus_IZR. lra.
    specialize (spiral_N_pos (N+1) N1ge0) as s2gt0;
      change (0 < s2) in s2gt0.
    rewrite <- signeq1_eqv in s2gt0.
    rewrite s1gt0, s2gt0.
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r|lra].
    destruct Rge_dec; [clear r | rewrite plus_IZR in n; lra].
    destruct Req_EM_T; [clear e| lra].
    destruct Rlt_dec; [lra | clear n].
    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.

    repeat rewrite RmultRinv.
    rewrite rwa, rwa0; try zltab.

    rewrite plus_IZR.
    fieldrewrite (PI/2 + (IZR N + 1) * PI) ((PI/2 + IZR N * PI) + PI).
    set (A := PI/2 + IZR N * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 2.
    destruct total_order_T; [destruct s|]; lra.
  Qed.

  Lemma sf_2deriv_sign_midarm_mxeq0 :
    forall N (mveq0 : 0 = mx)
           (nnge0 : IZR N < 0)
           (np1ge0 : IZR (N + 1) >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.


    assert (N = -1)%Z as ndef. {
      apply lt_IZR in nnge0.
      apply Rge_le in np1ge0.
      apply le_IZR in np1ge0.
      clear - nnge0 np1ge0.
      omega. }
    assert (0 = N + 1)%Z as zeq. {
      omega. }

    
    specialize (euler_tan_pt_symm _ np1ge0) as s1rs2.
    simpl in s1rs2.
    assert (- (N + 1) - 1 = N)%Z as zn. {
      rewrite ndef.
      omega. }
    rewrite zn in s1rs2. clear zn.
    change (s2 = - s1) in s1rs2.
    
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    specialize (spiral_N_neg1) as s1le0.
    rewrite <- ndef in s1le0.
    change (s1 <= 0) in s1le0.
    specialize (spiral_N_pos1) as s2ge0.
    simpl in s2ge0.
    rewrite zeq in s2ge0 at 2.
    change (0 <= s2) in s2ge0.

    destruct s1le0 as [s1lt0 |s1eq0].
    destruct s2ge0 as [s2gt0 |s2eq0].
    rewrite <- signeq1_eqv in s2gt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2gt0.

    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra|clear n].
    destruct Rge_dec ; [clear r | lra].
    destruct Req_EM_T; [ clear e|lra].
    destruct Rlt_dec; [lra | clear n].
    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.

    repeat rewrite RmultRinv.

    rewrite rwa, rwa0;
      rewrite <- zeq;
      arn; [field|lra|lra].

    rewrite s1rs2 in s2eq0.
    symmetry in s2eq0.
    apply Ropp_eq_0_compat in s2eq0.
    rewrite Ropp_involutive in s2eq0.
    rewrite s2eq0 in s1lt0.
    lra.

    rewrite s1eq0 in s1rs2.
    rewrite Ropp_0 in s1rs2.
    rewrite s1rs2, s1eq0.
    rewrite sign_0.
    field.
  Qed.



  Lemma sf_2deriv_sign_Nge0_mxeq0 :
    forall N (mveq0 : 0 = mx)
           (Nge0 : IZR N >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (s1ne0 : s1 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    apply Rge_le in Nge0.
    assert (0 < s1) as s1gt0. {
      destruct Nge0 as [Ngt |Neq].
      apply (spiral_N_pos N Ngt).
      unfold s1 in *.
      clear s1.
      apply eq_IZR in Neq.
      rewrite <- Neq in *.
      set (s1 := euler_spiral_tangent_pt 0) in *.
      specialize (spiral_N_pos1) as s1ge0;
        change (0 <= s1) in s1ge0.
      destruct s1ge0 as [s1gt0 |s1eq0].
      assumption.
      lra. }

    rewrite <- signeq1_eqv in s1gt0.
    assert (0 < IZR (N+1)) as N1ge0. rewrite plus_IZR. lra.
    specialize (spiral_N_pos (N+1) N1ge0) as s2gt0;
      change (0 < s2) in s2gt0.
    rewrite <- signeq1_eqv in s2gt0.
    rewrite s1gt0, s2gt0.
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [clear r|lra].
    destruct Rge_dec; [clear r | rewrite plus_IZR in n; lra].
    destruct Req_EM_T; [clear e| lra].
    destruct Rlt_dec; [lra | clear n].
    match goal with
    | |- sign
           (mx * cos (1 / 2 * PI * (?A * / l a)²) +
            my * sin (1 / 2 * PI * (?A * / l a)²)) =
         - (1) * sign
                   (mx * cos (1 / 2 * PI * (?B * / l a)²) +
                    my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.

    repeat rewrite RmultRinv.
    rewrite rwa, rwa0; try zltab.

    rewrite plus_IZR.
    fieldrewrite (PI/2 + (IZR N + 1) * PI) ((PI/2 + IZR N * PI) + PI).
    set (A := PI/2 + IZR N * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 2.
    destruct total_order_T; [destruct s|]; lra.
  Qed.

  Lemma sf_2deriv_sign_N1ltn1_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Np1ltn1 : IZR (N+1) < -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    specialize (spiral_N_neg (N+1) Np1ltn1) as s2lt0;
      change (s2 < 0) in s2lt0.
    rewrite <- signeqm1_eqv in s2lt0.
    assert (IZR N < -1) as N1ltm1.
    apply lt_IZR in Np1ltn1.
    apply IZR_lt. omega.
    specialize (spiral_N_neg N N1ltm1) as s1lt0;
      change (s1 < 0) in s1lt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2lt0.
    fieldrewrite (- -1) (1).
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra| clear n].
    destruct Rge_dec; [lra| clear n].
    destruct Req_EM_T; [lra| clear n].

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      rdsk2t A B
    end.
    rewrite c1d, c2d.

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0;
      [| apply (Rplus_le_reg_r (IZR (N + 1 + 1) * PI));
         setr k; arn;
         apply (Rle_trans _ 0);
         [apply lt_IZR in Np1ltn1;
          apply (Rmult_le_reg_r (/ PI));
          [zltab|
           setl (IZR (N + 1 + 1));
           [lra| arn; apply IZR_le; omega];
           assumption]|
          assumption]|
       apply (Rplus_le_reg_r (IZR (N + 1) * PI));
       setr k; arn;
       apply (Rle_trans _ 0);
       [apply lt_IZR in N1ltm1;
        apply (Rmult_le_reg_r (/ PI));
        [zltab|
         setl (IZR (N + 1));
         [lra| arn; apply IZR_le; omega];
         assumption]|
        assumption]].


    repeat rewrite plus_IZR.
    fieldrewrite (k - (IZR N + 1) * PI) ((k - (IZR N + 1 + 1) * PI) + PI).
    set (A := k - (IZR N + 1 + 1) * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 1.
    destruct total_order_T; [destruct s|]; lra.
  Qed.

  Lemma sf_2deriv_sign_N1len1_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Np1ltn1 : IZR (N+1) <= -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (s2ne0 : s2 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    assert (s2 < 0) as s2lt0. {
      destruct Np1ltn1 as [Nlt |Neq].
      apply (spiral_N_neg (N+1) Nlt).
      unfold s2 in *.
      clear s2.
      apply eq_IZR in Neq.
      rewrite Neq in *.
      set (s2 := euler_spiral_tangent_pt (-1)) in *.
      specialize (spiral_N_neg1) as s2ge0;
        change (s2 <= 0) in s2ge0.
      destruct s2ge0 as [s2gt0 |s2eq0].
      assumption.
      lra. }

    rewrite <- signeqm1_eqv in s2lt0.
    assert (IZR N < -1) as N1ltm1.
    apply le_IZR in Np1ltn1.
    apply IZR_lt. omega.
    specialize (spiral_N_neg N N1ltm1) as s1lt0;
      change (s1 < 0) in s1lt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2lt0.
    fieldrewrite (- -1) (1).
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra| clear n].
    destruct Rge_dec; [lra| clear n].
    destruct Req_EM_T; [lra| clear n].

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      rdsk2t A B
    end.
    rewrite c1d, c2d.

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0;
      [| apply (Rplus_le_reg_r (IZR (N + 1 + 1) * PI));
         setr k; arn;
         apply (Rle_trans _ 0);
         [apply le_IZR in Np1ltn1;
          apply (Rmult_le_reg_r (/ PI));
          [zltab|
           setl (IZR (N + 1 + 1));
           [lra| arn; apply IZR_le; omega];
           assumption]|
          assumption]|
       apply (Rplus_le_reg_r (IZR (N + 1) * PI));
       setr k; arn;
       apply (Rle_trans _ 0);
       [apply lt_IZR in N1ltm1;
        apply (Rmult_le_reg_r (/ PI));
        [zltab|
         setl (IZR (N + 1));
         [lra| arn; apply IZR_le; omega];
         assumption]|
        assumption]].


    repeat rewrite plus_IZR.
    fieldrewrite (k - (IZR N + 1) * PI) ((k - (IZR N + 1 + 1) * PI) + PI).
    set (A := k - (IZR N + 1 + 1) * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 1.
    destruct total_order_T; [destruct s|]; lra.
  Qed.


  Lemma sf_2deriv_sign_N1ltn1_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (Np1ltn1 : IZR (N+1) < -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.
    specialize (spiral_N_neg (N+1) Np1ltn1) as s2lt0;
      change (s2 < 0) in s2lt0.
    rewrite <- signeqm1_eqv in s2lt0.
    assert (IZR N < -1) as N1ltm1.
    apply lt_IZR in Np1ltn1.
    apply IZR_lt. omega.
    specialize (spiral_N_neg N N1ltm1) as s1lt0;
      change (s1 < 0) in s1lt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2lt0.
    fieldrewrite (- -1) (1).
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra| clear n].
    destruct Rge_dec; [lra| clear n].
    destruct Req_EM_T; [clear e|lra].
    destruct Rlt_dec; [lra | clear n].

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0;
      [|apply (Rplus_le_reg_r (IZR (N + 1 + 1) * PI));
        setr (PI/2); arn;
        apply (Rle_trans _ 0);
        [apply lt_IZR in Np1ltn1;
         apply (Rmult_le_reg_r (/ PI));
         [zltab|
          setl (IZR (N + 1 + 1));
          [lra| arn; apply IZR_le; omega]]|
         lra]
       |apply (Rplus_le_reg_r (IZR (N + 1) * PI));
        setr (PI/2); arn;
        apply (Rle_trans _ 0);
        [apply lt_IZR in N1ltm1;
         apply (Rmult_le_reg_r (/ PI));
         [zltab|
          setl (IZR (N + 1));
          [lra| arn; apply IZR_le; omega];
          assumption]|
         lra]].


    repeat rewrite plus_IZR.
    fieldrewrite ((PI/2) - (IZR N + 1) * PI) (((PI/2) - (IZR N + 1 + 1) * PI) + PI).
    set (A := (PI/2) - (IZR N + 1 + 1) * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 1.
    destruct total_order_T; [destruct s|]; lra.
  Qed.

  Lemma sf_2deriv_sign_N1len1_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (Np1ltn1 : IZR (N+1) <= -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (s2ne0 : s2 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.

    specialize (agt0_lagt0 _ zlta) as zltl.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s1) as d2s1.
    change (is_derive_n sf 2 s1 (PI * s1 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s1 * / l a)²))))
      in d2s1.
    specialize (sf_2deriv s2) as d2s2.
    change (is_derive_n sf 2 s2 (PI * s2 / (l a)² *
                                 (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                                  my * sin (1 / 2 * PI * (s2 * / l a)²)))) in d2s2.
    apply is_derive_n_unique in d2s1.
    apply is_derive_n_unique in d2s2.
    rewrite d2s1, d2s2.
    clear d2s1 d2s2.
    
    assert (sign PI = 1) as signPI. {
      rewrite signeq1_eqv. lra. }
    assert (sign (/ (l a)²) = 1) as signila2. {
      rewrite signeq1_eqv.
      zltab.
      unfold Rsqr.
      zltab. }

    rewrite <- (RmultRinv (PI * s1) _), <- (RmultRinv (PI * s2) _).
    repeat rewrite sign_mult.
    apply (Rmult_eq_reg_r (/ (sign PI) * / sign (/ (l a)²)));
      [| rewrite signPI, signila2; lra ].

    setl (sign s1 * sign (mx * cos (1 / 2 * PI * (s1 * / l a)²) +
                          my * sin (1 / 2 * PI * (s1 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    setr (- sign s2 * sign (mx * cos (1 / 2 * PI * (s2 * / l a)²) +
                            my * sin (1 / 2 * PI * (s2 * / l a)²))).
    unfold Rsqr in signila2.
    rewrite signPI, signila2.
    split; lra.

    assert (s2 < 0) as s2lt0. {
      destruct Np1ltn1 as [Nlt |Neq].
      apply (spiral_N_neg (N+1) Nlt).
      unfold s2 in *.
      clear s2.
      apply eq_IZR in Neq.
      rewrite Neq in *.
      set (s2 := euler_spiral_tangent_pt (-1)) in *.
      specialize (spiral_N_neg1) as s2ge0;
        change (s2 <= 0) in s2ge0.
      destruct s2ge0 as [s2gt0 |s2eq0].
      assumption.
      lra. }

    rewrite <- signeqm1_eqv in s2lt0.
    assert (IZR N < -1) as N1ltm1.
    apply le_IZR in Np1ltn1.
    apply IZR_lt. omega.
    specialize (spiral_N_neg N N1ltm1) as s1lt0;
      change (s1 < 0) in s1lt0.
    rewrite <- signeqm1_eqv in s1lt0.
    rewrite s1lt0, s2lt0.
    fieldrewrite (- -1) (1).
    arn.
    
    unfold s1,s2, euler_spiral_tangent_pt.
    destruct Rge_dec; [lra| clear n].
    destruct Rge_dec; [lra| clear n].
    destruct Req_EM_T; [clear e|lra].
    destruct Rlt_dec; [lra | clear n].

    match goal with
    | |- -1 * sign
                (mx * cos (1 / 2 * PI * (?A * / l a)²) +
                 my * sin (1 / 2 * PI * (?A * / l a)²)) =
         sign
           (mx * cos (1 / 2 * PI * (?B * / l a)²) +
            my * sin (1 / 2 * PI * (?B * / l a)²)) =>
      estpid A; estpid B
    end.
    repeat rewrite RmultRinv.
    rewrite rwa, rwa0;
      [|apply (Rplus_le_reg_r (IZR (N + 1 + 1) * PI));
        setr (PI/2); arn;
        apply (Rle_trans _ 0);
        [apply le_IZR in Np1ltn1;
         apply (Rmult_le_reg_r (/ PI));
         [zltab|
          setl (IZR (N + 1 + 1));
          [lra| arn; apply IZR_le; omega]]|
         lra]
       |apply (Rplus_le_reg_r (IZR (N + 1) * PI));
        setr (PI/2); arn;
        apply (Rle_trans _ 0);
        [apply lt_IZR in N1ltm1;
         apply (Rmult_le_reg_r (/ PI));
         [zltab|
          setl (IZR (N + 1));
          [lra| arn; apply IZR_le; omega];
          assumption]|
         lra]].


    repeat rewrite plus_IZR.
    fieldrewrite ((PI/2) - (IZR N + 1) * PI) (((PI/2) - (IZR N + 1 + 1) * PI) + PI).
    set (A := (PI/2) - (IZR N + 1 + 1) * PI) in *.
    rewrite neg_cos, neg_sin.
    fieldrewrite (mx * - cos A + my * - sin A)
                 ((-1)*(mx * cos A + my * sin A)).
    rewrite sign_mult.
    unfold sign at 1.
    destruct total_order_T; [destruct s|]; lra.
  Qed.




  (* end hide *)
  (* begin hide *)

  Lemma sf_2deriv_sign_Ngt0 :
    forall N (Nge0 : IZR N > 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    apply sf_2deriv_sign_Ngt0_mxeq0; try assumption.
    apply sf_2deriv_sign_Ngt0_mxne0; try assumption.
  Qed.

  Lemma sf_2deriv_sign_N1ltn1 :
    forall N (Nge0 : IZR (N+1) < -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    apply sf_2deriv_sign_N1ltn1_mxeq0; try assumption.
    apply sf_2deriv_sign_N1ltn1_mxne0; try assumption.
  Qed.

  Lemma sf_2deriv_sign_Nge0 :
    forall N (Nge0 : IZR N >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (s1ne0 : s1 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    apply sf_2deriv_sign_Nge0_mxeq0; try assumption.
    apply sf_2deriv_sign_Nge0_mxne0; try assumption.
  Qed.

  Lemma sf_2deriv_sign_N1len1 :
    forall N (Nge0 : IZR (N+1) <= -1),
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (s2ne0 : s2 <> 0),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    apply sf_2deriv_sign_N1len1_mxeq0; try assumption.
    apply sf_2deriv_sign_N1len1_mxne0; try assumption.
  Qed.

  Lemma sf_2deriv_sign_midarm :
    forall N (nnge0 : IZR N < 0)
           (np1ge0 : IZR (N + 1) >= 0),
      let s1 := estp N in
      let s2 := estp (N+1) in
      sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct (Req_dec 0 mx).
    apply sf_2deriv_sign_midarm_mxeq0; try assumption.
    apply sf_2deriv_sign_midarm_mxne0; try assumption.
  Qed.


  (* end hide *)

  Lemma sf_2deriv_sign: forall N,
      let s1 := estp N in
      let s2 := estp (N+1) in
      forall (cnst : ~ (IZR N = 0 /\ s1 = 0) /\ ~ (IZR N = -2 /\ s2 = 0)),
        sign (Derive_n sf 2 s1) = - sign (Derive_n sf 2 s2).
  Proof.
    intros.
    unfold estp in *.
    destruct cnst as [Neq0c Neqn2c].

    destruct (Rge_dec (IZR N) 0).
    destruct r as [Ngt0 |Neq0].
    + apply sf_2deriv_sign_Ngt0; try assumption.
    + destruct (Req_dec s1 0) as [s1eq0 |s1ne0].
      exfalso.
      apply Neq0c.
      split; assumption.
      apply sf_2deriv_sign_Nge0; try assumption.
      apply eq_IZR in Neq0.
      apply Rle_ge.
      apply IZR_le.
      omega.
    + apply Rnot_ge_lt in n.
      destruct (Req_dec (IZR N) (-1)) as [Neqn1 |Nnen1].
      assert (IZR (N + 1) >= 0) as np1ge0. {
        apply eq_IZR in Neqn1.
        apply IZR_ge.
        omega. }
      apply (sf_2deriv_sign_midarm _ n np1ge0).
      destruct (Req_dec (IZR N) (-2)) as [Neqn2 |Nnen2].
      destruct (Req_dec s2 0) as [s2eq0 |s2ne0];
        [exfalso;
         apply Neqn2c;
         split; assumption|].
      ++ destruct (Rle_dec (IZR (N + 1)) (-1)).
         apply sf_2deriv_sign_N1len1; try assumption.
         apply Rnot_le_gt in n0.
         apply Rgt_lt in n0.
         apply lt_IZR in n0.
         apply eq_IZR in Neqn2.
         exfalso.
         omega.
      ++ destruct (Rlt_dec (IZR (N + 1)) (-1)).
         apply sf_2deriv_sign_N1ltn1; try assumption.
         apply Rnot_lt_le in n0.
         exfalso.
         assert (N <> -1)%Z. {
           intro Neqn1.
           rewrite Neqn1 in Nnen1.
           lra. }
         assert (N <> -2)%Z. {
           intro Neqn2.
           rewrite Neqn2 in Nnen2.
           lra. }
         apply lt_IZR in n.
         apply le_IZR in n0.
         omega.
  Qed.

  (* begin hide *)

  Lemma sf_2deriv_ne0_Ngt0 : forall N (nge0 : IZR N > 0),
      let s := estp N in
      sign (Derive_n sf 2 s) <> 0.
  Proof.
    intros.
    unfold estp in *.
    intros s2dz.

    assert (s <> 0) as sne0. {
      intro seq0.
      specialize (spiral_N_pos _ nge0) as zlts.
      change (0 < s) in zlts.
      rewrite seq0 in zlts.
      lra. }
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.
    rewrite signeq0_eqv in s2dz.
    rewrite d2s in s2dz.

    set (A := (1 / 2 * PI * (s * / l a)²)) in *.
    set (B := PI * s / (l a)²) in *.
    
    assert (mx * cos A + my * sin A = 0) as cseq0.
    apply (Rmult_eq_reg_l B);
      [arn; assumption|
       unfold B;
       rewrite <- RmultRinv;
       apply Rmult_integral_contrapositive_currified;
       [apply Rmult_integral_contrapositive_currified;
        specialize PI_RGT_0 as pigt0;
        [lra| assumption]|
        apply Rinv_neq_0_compat;
        unfold Rsqr;
        apply ane0_lane0 in zlta;
        apply Rmult_integral_contrapositive_currified;
        assumption]].
    
    clear B s2dz d2s.
    unfold A in *.
    clear A.

    specialize (agt0_lagt0 _ zlta) as lagt0.
    specialize PI_RGT_0 as pigt0.
    
    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec.
    destruct Req_EM_T.
    destruct Rlt_dec.
    + lra.
    + clear n.
      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= PI / 2 + IZR N * PI) as argt0. {
        zltab. }
      specialize (rwa argt0).
      change (1 / 2 * PI * (s / l a)² = PI / 2 + IZR N * PI) in rwa.
      unfold s in rwa.
      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.
      rewrite <- cos_sin in cseq0.

      match goal with
      | H : ?mx * cos ?A + ?Q = 0 |- _ =>
        rewrite <- (Ropp_involutive (cos A)) in cseq0
      end.
      rewrite <- sin_cos in cseq0.
      rewrite <- e in cseq0.
      autorewrite with null in cseq0.
      apply Rmult_integral in cseq0 as [myeq0 | coseq0].
      apply ds.
      split; lra.
      specialize (Z.Even_or_Odd N) as [nev |nod].
      ++ destruct nev as [b Nd].
         rewrite <- (Rplus_0_l (IZR N* PI)), Nd, mult_IZR, cos_period1, cos_0 in coseq0.
         lra.
      ++ destruct nod as [b Nd].
         rewrite Nd, plus_IZR, mult_IZR, Rplus_comm, Rmult_plus_distr_r in coseq0.
         rewrite cos_period1, Rmult_1_l, cos_PI in coseq0.
         lra.
    + match goal with
      | cseq0 : ?mx * cos ?A + ?my * sin ?A = 0 |- _ => rdsk2t A A
      end.
      rewrite c1d in cseq0, sne0.

      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= k + IZR N * PI) as argt0. {
        zltab. }
      specialize (rwa argt0).
      unfold s in rwa.

      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.

      apply Rmult_neq_0_reg in sne0.
      destruct sne0 as [lane0 sqne0].
      assert ((k + IZR N * PI) <> 0) as sqne01.
      intro keq.
      apply sqne0.
      apply (Rmult_eq_compat_l (2 / PI)) in keq.
      autorewrite with null in keq.
      rewrite keq.
      apply sqrt_0.
      clear sqne0.

      assert (exists n, k + IZR N * PI = atan (my / mx) + IZR n * PI) as [m kdef2]. {
        specialize (Z.Even_or_Odd N) as [nev |nod].
        - destruct nev as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, mult_IZR.
             exists (2*b)%Z.
             rewrite mult_IZR.
             reflexivity.
          -- rewrite kdPI, Nd, mult_IZR.
             exists (2*b+1)%Z.
             rewrite plus_IZR, mult_IZR.
             field.
        - destruct nod as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, mult_IZR.
             exists (2*b+1)%Z.
             rewrite plus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, mult_IZR.
             exists (2*(b+1))%Z.
             rewrite mult_IZR, plus_IZR.
             field. }
      rewrite kdef2 in cseq0.

      specialize (sincosatan2 (my/mx) m) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in cseq0.

      assert (sqrt (1 + (my / mx)²) <> 0) as sqrtne0. {
        specialize (Rle_0_sqr (my / mx)) as sqrge0.
        intro sqrteq0.
        rewrite <- sqrt_0 in sqrteq0.
        apply sqrt_inj in sqrteq0.
        apply Rplus_opp_r_uniq in sqrteq0.
        rewrite sqrteq0 in sqrge0.
        lra.
        lra.
        right; reflexivity. }
      
      assert (mx² + my² = 0) as mxmyeq0. {
        unfold Rsqr.
        apply (Rmult_eq_reg_r (pm * / mx * / sqrt (1 + (my / mx)²))).
        arn.
        rewrite <- cseq0.
        field.
        lra.
        apply Rmult_integral_contrapositive_currified.
        apply Rmult_integral_contrapositive_currified.
        destruct cond as [[eo pmd] | [eo pmd]].
        rewrite pmd.
        discrR.
        rewrite pmd.
        discrR.
        zltab.
        zltab. }
      specialize (nzss) as mxmyne0.
      lra.
    + lra.
  Qed.

  Lemma sf_2deriv_ne0_N0 : forall N (nge0 : IZR N = 0),
      let s := estp N in
      forall (sne0 : s <> 0), sign (Derive_n sf 2 s) <> 0.
  Proof.
    intros.
    intros s2dz.
    unfold estp in *.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.
    rewrite signeq0_eqv in s2dz.
    rewrite d2s in s2dz.

    set (A := (1 / 2 * PI * (s * / l a)²)) in *.
    set (B := PI * s / (l a)²) in *.
    
    assert (mx * cos A + my * sin A = 0) as cseq0.
    apply (Rmult_eq_reg_l B);
      [arn; assumption|
       unfold B;
       rewrite <- RmultRinv;
       apply Rmult_integral_contrapositive_currified;
       [apply Rmult_integral_contrapositive_currified;
        specialize PI_RGT_0 as pigt0;
        [lra| assumption]|
        apply Rinv_neq_0_compat;
        unfold Rsqr;
        apply ane0_lane0 in zlta;
        apply Rmult_integral_contrapositive_currified;
        assumption]].
    
    clear B s2dz d2s.
    unfold A in *.
    clear A.

    specialize (agt0_lagt0 _ zlta) as lagt0.
    specialize PI_RGT_0 as pigt0.
    
    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec.
    destruct Req_EM_T.
    destruct Rlt_dec.
    + lra.
    + clear n.
      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= PI / 2 + IZR N * PI) as argt0. {
        zltab. }
      specialize (rwa argt0).
      change (1 / 2 * PI * (s / l a)² = PI / 2 + IZR N * PI) in rwa.
      unfold s in rwa.
      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.
      rewrite <- cos_sin in cseq0.

      match goal with
      | H : ?mx * cos ?A + ?Q = 0 |- _ =>
        rewrite <- (Ropp_involutive (cos A)) in cseq0
      end.
      rewrite <- sin_cos in cseq0.
      rewrite <- e in cseq0.
      autorewrite with null in cseq0.
      apply Rmult_integral in cseq0 as [myeq0 | coseq0].
      apply ds.
      split; lra.
      specialize (Z.Even_or_Odd N) as [nev |nod].
      ++ destruct nev as [b Nd].
         rewrite <- (Rplus_0_l (IZR N* PI)), Nd, mult_IZR, cos_period1, cos_0 in coseq0.
         lra.
      ++ destruct nod as [b Nd].
         rewrite Nd, plus_IZR, mult_IZR, Rplus_comm, Rmult_plus_distr_r in coseq0.
         rewrite cos_period1, Rmult_1_l, cos_PI in coseq0.
         lra.
    + match goal with
      | cseq0 : ?mx * cos ?A + ?my * sin ?A = 0 |- _ => rdsk2t A A
      end.
      rewrite c1d in cseq0, sne0.

      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= k + IZR N * PI) as argt0. {
        zltab. }
      specialize (rwa argt0).
      unfold s in rwa.

      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.

      apply Rmult_neq_0_reg in sne0.
      destruct sne0 as [lane0 sqne0].
      assert ((k + IZR N * PI) <> 0) as sqne01.
      intro keq.
      apply sqne0.
      apply (Rmult_eq_compat_l (2 / PI)) in keq.
      autorewrite with null in keq.
      rewrite keq.
      apply sqrt_0.
      clear sqne0.

      assert (exists n, k + IZR N * PI = atan (my / mx) + IZR n * PI) as [m kdef2]. {
        specialize (Z.Even_or_Odd N) as [nev |nod].
        - destruct nev as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, mult_IZR.
             exists (2*b)%Z.
             rewrite mult_IZR.
             reflexivity.
          -- rewrite kdPI, Nd, mult_IZR.
             exists (2*b+1)%Z.
             rewrite plus_IZR, mult_IZR.
             field.
        - destruct nod as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, mult_IZR.
             exists (2*b+1)%Z.
             rewrite plus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, mult_IZR.
             exists (2*(b+1))%Z.
             rewrite mult_IZR, plus_IZR.
             field. }
      rewrite kdef2 in cseq0.

      specialize (sincosatan2 (my/mx) m) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in cseq0.

      assert (sqrt (1 + (my / mx)²) <> 0) as sqrtne0. {
        specialize (Rle_0_sqr (my / mx)) as sqrge0.
        intro sqrteq0.
        rewrite <- sqrt_0 in sqrteq0.
        apply sqrt_inj in sqrteq0.
        apply Rplus_opp_r_uniq in sqrteq0.
        rewrite sqrteq0 in sqrge0.
        lra.
        lra.
        right; reflexivity. }
      
      assert (mx² + my² = 0) as mxmyeq0. {
        unfold Rsqr.
        apply (Rmult_eq_reg_r (pm * / mx * / sqrt (1 + (my / mx)²))).
        arn.
        rewrite <- cseq0.
        field.
        lra.
        apply Rmult_integral_contrapositive_currified.
        apply Rmult_integral_contrapositive_currified.
        destruct cond as [[eo pmd] | [eo pmd]].
        rewrite pmd.
        discrR.
        rewrite pmd.
        discrR.
        zltab.
        zltab. }
      specialize (nzss) as mxmyne0.
      lra.
    + lra.
  Qed.

  Lemma sf_2deriv_eq0_N0 : forall N (nge0 : IZR N = 0),
      let s := estp N in
      forall (seq0 : s = 0),
        sign (Derive_n sf 2 s) = 0.
  Proof.
    intros.
    unfold estp in *.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    rewrite signeq0_eqv.
    rewrite d2s, seq0.
    rewrite <- RmultRinv.
    arn.
    reflexivity.
  Qed.


  Lemma sf_2deriv_ne0_Nltn1 : forall N (nlt0 : IZR N < -1),
      let s := estp N in
      sign (Derive_n sf 2 s) <> 0.
  Proof.
    intros.
    intros s2dz.
    unfold estp in *.
    
    assert (s <> 0) as sne0. {
      intro seq0.
      specialize (spiral_N_neg _ nlt0) as zlts.
      change (s < 0) in zlts.
      rewrite seq0 in zlts.
      lra. }
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.
    rewrite signeq0_eqv in s2dz.
    rewrite d2s in s2dz.

    set (A := (1 / 2 * PI * (s * / l a)²)) in *.
    set (B := PI * s / (l a)²) in *.
    
    assert (mx * cos A + my * sin A = 0) as cseq0.
    apply (Rmult_eq_reg_l B);
      [arn; assumption|
       unfold B;
       rewrite <- RmultRinv;
       apply Rmult_integral_contrapositive_currified;
       [apply Rmult_integral_contrapositive_currified;
        specialize PI_RGT_0 as pigt0;
        [lra| assumption]|
        apply Rinv_neq_0_compat;
        unfold Rsqr;
        apply ane0_lane0 in zlta;
        apply Rmult_integral_contrapositive_currified;
        assumption]].
    
    clear B s2dz d2s.
    unfold A in *.
    clear A.

    specialize (agt0_lagt0 _ zlta) as lagt0.
    specialize PI_RGT_0 as pigt0.
    
    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec.
    lra.
    destruct Req_EM_T.
    destruct Rlt_dec.
    + lra.
    + clear n.
      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= PI / 2 - IZR (N + 1) * PI) as argt0. {
        rewrite <- pm.
        zltab.
        rewrite plus_IZR.
        setr (- (IZR N + 1) * PI).
        zltab.
      }
      specialize (rwa argt0).
      change (1 / 2 * PI * (s / l a)² = PI / 2 - IZR (N + 1) * PI) in rwa.
      unfold s in rwa.
      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.
      rewrite <- pm in cseq0.
      rewrite <- cos_sin in cseq0.
      match goal with
      | H : ?mx * cos ?A + ?Q = 0 |- _ =>
        rewrite <- (Ropp_involutive (cos A)) in cseq0
      end.
      rewrite <- sin_cos in cseq0.
      rewrite <- e in cseq0.
      autorewrite with null in cseq0.
      apply Rmult_integral in cseq0 as [myeq0 | coseq0].
      apply ds.
      split; lra.
      specialize (Z.Even_or_Odd N) as [nev |nod].
      ++ destruct nev as [b Nd].
         rewrite cos_neg, plus_IZR, Rplus_comm in coseq0.
         rewrite Rmult_plus_distr_r, Nd, mult_IZR, cos_period1 in coseq0.
         rewrite Rmult_1_l, cos_PI in coseq0.
         lra.
      ++ destruct nod as [b Nd].
         rewrite cos_neg, <- (Rplus_0_l (IZR (N + 1) * PI)) in coseq0.
         rewrite Nd in coseq0.
         assert (2 * b + 1 + 1 = 2 * (b + 1))%Z as id. omega. rewrite id in coseq0. clear id.
         rewrite mult_IZR, cos_period1, cos_0 in coseq0.
         lra.
         
    + match goal with
      | cseq0 : ?mx * cos ?A + ?my * sin ?A = 0 |- _ => rdsk2t A A
      end.
      rewrite c1d in cseq0, sne0.

      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= k - IZR (N+1) * PI) as argt0. {
        rewrite <- pm.
        zltab.
        rewrite plus_IZR.
        setr (-(IZR N + 1) * PI).
        zltab. }
      specialize (rwa argt0).
      unfold s in rwa.

      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.

      apply Rmult_neq_0_reg in sne0.
      destruct sne0 as [lane0 sqne0].

      assert ((k - IZR (N+1) * PI) <> 0) as sqne01.
      intro keq.
      apply sqne0.
      apply (Rmult_eq_compat_l (2 / PI)) in keq.
      autorewrite with null in keq.
      rewrite keq.
      apply sqrt_0.
      clear sqne0.

      assert (exists n, k - IZR (N+1) * PI = atan (my / mx) + IZR n * PI) as [m kdef2]. {
        specialize (Z.Even_or_Odd N) as [nev |nod].
        - destruct nev as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, mult_IZR.
             exists (- 2*b - 1)%Z.
             rewrite minus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, mult_IZR.
             exists (- 2*b)%Z.
             rewrite mult_IZR.
             field.
        - destruct nod as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, plus_IZR, mult_IZR.
             exists (-2*b-2)%Z.
             rewrite minus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, plus_IZR, mult_IZR.
             exists (-2*b - 1)%Z.
             rewrite minus_IZR, mult_IZR.
             field. }
      rewrite kdef2 in cseq0.

      specialize (sincosatan2 (my/mx) m) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in cseq0.

      assert (sqrt (1 + (my / mx)²) <> 0) as sqrtne0. {
        specialize (Rle_0_sqr (my / mx)) as sqrge0.
        intro sqrteq0.
        rewrite <- sqrt_0 in sqrteq0.
        apply sqrt_inj in sqrteq0.
        apply Rplus_opp_r_uniq in sqrteq0.
        rewrite sqrteq0 in sqrge0.
        lra.
        lra.
        right; reflexivity. }
      
      assert (mx² + my² = 0) as mxmyeq0. {
        unfold Rsqr.
        apply (Rmult_eq_reg_r (pm * / mx * / sqrt (1 + (my / mx)²))).
        arn.
        rewrite <- cseq0.
        field.
        lra.
        apply Rmult_integral_contrapositive_currified.
        apply Rmult_integral_contrapositive_currified.
        destruct cond as [[eo pmd] | [eo pmd]].
        rewrite pmd.
        discrR.
        rewrite pmd.
        discrR.
        zltab.
        zltab. }
      specialize (nzss) as mxmyne0.
      lra.
  Qed.

  Lemma sf_2deriv_ne0_Nn1 : forall N (nlt0 : IZR N = -1),
      let s := estp N in
      forall (sne0 : s <> 0),
        sign (Derive_n sf 2 s) <> 0.
  Proof.
    intros.
    intros s2dz.
    unfold estp in *.

    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.
    rewrite signeq0_eqv in s2dz.
    rewrite d2s in s2dz.

    set (A := (1 / 2 * PI * (s * / l a)²)) in *.
    set (B := PI * s / (l a)²) in *.
    
    assert (mx * cos A + my * sin A = 0) as cseq0.
    apply (Rmult_eq_reg_l B);
      [arn; assumption|
       unfold B;
       rewrite <- RmultRinv;
       apply Rmult_integral_contrapositive_currified;
       [apply Rmult_integral_contrapositive_currified;
        specialize PI_RGT_0 as pigt0;
        [lra| assumption]|
        apply Rinv_neq_0_compat;
        unfold Rsqr;
        apply ane0_lane0 in zlta;
        apply Rmult_integral_contrapositive_currified;
        assumption]].
    
    clear B s2dz d2s.
    unfold A in *.
    clear A.

    specialize (agt0_lagt0 _ zlta) as lagt0.
    specialize PI_RGT_0 as pigt0.
    
    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec.
    lra.
    destruct Req_EM_T.
    destruct Rlt_dec.
    + lra.
    + clear n.
      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= PI / 2 - IZR (N + 1) * PI) as argt0. {
        rewrite <- pm.
        zltab.
        rewrite plus_IZR.
        setr (- (IZR N + 1) * PI).
        zltab.
      }
      specialize (rwa argt0).
      change (1 / 2 * PI * (s / l a)² = PI / 2 - IZR (N + 1) * PI) in rwa.
      unfold s in rwa.
      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.
      rewrite <- pm in cseq0.
      rewrite <- cos_sin in cseq0.
      match goal with
      | H : ?mx * cos ?A + ?Q = 0 |- _ =>
        rewrite <- (Ropp_involutive (cos A)) in cseq0
      end.
      rewrite <- sin_cos in cseq0.
      rewrite <- e in cseq0.
      autorewrite with null in cseq0.
      apply Rmult_integral in cseq0 as [myeq0 | coseq0].
      apply ds.
      split; lra.
      specialize (Z.Even_or_Odd N) as [nev |nod].
      ++ destruct nev as [b Nd].
         rewrite cos_neg, plus_IZR, Rplus_comm in coseq0.
         rewrite Rmult_plus_distr_r, Nd, mult_IZR, cos_period1 in coseq0.
         rewrite Rmult_1_l, cos_PI in coseq0.
         lra.
      ++ destruct nod as [b Nd].
         rewrite cos_neg, <- (Rplus_0_l (IZR (N + 1) * PI)) in coseq0.
         rewrite Nd in coseq0.
         assert (2 * b + 1 + 1 = 2 * (b + 1))%Z as id. omega. rewrite id in coseq0. clear id.
         rewrite mult_IZR, cos_period1, cos_0 in coseq0.
         lra.
         
    + match goal with
      | cseq0 : ?mx * cos ?A + ?my * sin ?A = 0 |- _ => rdsk2t A A
      end.
      rewrite c1d in cseq0, sne0.

      match goal with | H : ?mx * cos ?A + ?Q = 0 |- _ => estpid A end.
      assert (0 <= k - IZR (N+1) * PI) as argt0. {
        rewrite <- pm.
        zltab.
        rewrite plus_IZR.
        setr (-(IZR N + 1) * PI).
        zltab. }
      specialize (rwa argt0).
      unfold s in rwa.

      rewrite RmultRinv in cseq0.
      rewrite rwa in cseq0.

      apply Rmult_neq_0_reg in sne0.
      destruct sne0 as [lane0 sqne0].

      assert ((k - IZR (N+1) * PI) <> 0) as sqne01.
      intro keq.
      apply sqne0.
      apply (Rmult_eq_compat_l (2 / PI)) in keq.
      autorewrite with null in keq.
      rewrite keq.
      apply sqrt_0.
      clear sqne0.

      assert (exists n, k - IZR (N+1) * PI = atan (my / mx) + IZR n * PI) as [m kdef2]. {
        specialize (Z.Even_or_Odd N) as [nev |nod].
        - destruct nev as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, mult_IZR.
             exists (- 2*b - 1)%Z.
             rewrite minus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, mult_IZR.
             exists (- 2*b)%Z.
             rewrite mult_IZR.
             field.
        - destruct nod as [b Nd].
          destruct kdef as [kd |kdPI].
          -- rewrite kd, Nd, plus_IZR, plus_IZR, mult_IZR.
             exists (-2*b-2)%Z.
             rewrite minus_IZR, mult_IZR.
             field.
          -- rewrite kdPI, Nd, plus_IZR, plus_IZR, mult_IZR.
             exists (-2*b - 1)%Z.
             rewrite minus_IZR, mult_IZR.
             field. }
      rewrite kdef2 in cseq0.

      specialize (sincosatan2 (my/mx) m) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in cseq0.

      assert (sqrt (1 + (my / mx)²) <> 0) as sqrtne0. {
        specialize (Rle_0_sqr (my / mx)) as sqrge0.
        intro sqrteq0.
        rewrite <- sqrt_0 in sqrteq0.
        apply sqrt_inj in sqrteq0.
        apply Rplus_opp_r_uniq in sqrteq0.
        rewrite sqrteq0 in sqrge0.
        lra.
        lra.
        right; reflexivity. }
      
      assert (mx² + my² = 0) as mxmyeq0. {
        unfold Rsqr.
        apply (Rmult_eq_reg_r (pm * / mx * / sqrt (1 + (my / mx)²))).
        arn.
        rewrite <- cseq0.
        field.
        lra.
        apply Rmult_integral_contrapositive_currified.
        apply Rmult_integral_contrapositive_currified.
        destruct cond as [[eo pmd] | [eo pmd]].
        rewrite pmd.
        discrR.
        rewrite pmd.
        discrR.
        zltab.
        zltab. }
      specialize (nzss) as mxmyne0.
      lra.
  Qed.

  Lemma sf_2deriv_eq0_Nn1 : forall N (nlt0 : IZR N = -1),
      let s := estp N in
      forall (seq0 : s = 0),
        sign (Derive_n sf 2 s) = 0.
  Proof.
    intros.

    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.


    rewrite signeq0_eqv.
    rewrite d2s, seq0.
    rewrite <- RmultRinv.
    arn.
    reflexivity.
  Qed.



  Lemma sf_2deriv_eq0 : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      forall (sne0 : s = 0),
        sign (Derive_n sf 2 s) = 0.
  Proof.
    intros.
    unfold estp in *.
    destruct nrng as [neq0 |neqn1].
    apply sf_2deriv_eq0_N0; try assumption.
    apply sf_2deriv_eq0_Nn1; try assumption.
  Qed.
  
  (* end hide *)
  Lemma sf_2deriv_ne0 : forall N,
      let s := estp N in
      forall (nrng : IZR N > 0 \/ IZR N < -1 \/
                     (s <> 0 /\ (IZR N = 0 \/ IZR N = -1))),
        sign (Derive_n sf 2 s) <> 0.
  Proof.
    intros.
    unfold estp in *.
    destruct nrng as [ngt0 |[nltn1 | [sne0 [neq0 | neqn1]]]].
    apply sf_2deriv_ne0_Ngt0; try assumption.
    apply sf_2deriv_ne0_Nltn1; try assumption.
    apply sf_2deriv_ne0_N0; try assumption.
    apply sf_2deriv_ne0_Nn1; try assumption.
  Qed.

  (* begin hide *)
  Lemma sf_2deriv_eq0_N0_impl : forall N (nrng : IZR N = 0 (* \/ IZR N = -1*)),
      let s := estp N in
      sign (Derive_n sf 2 s) = 0 -> s = 0.
  Proof.
    intros until 1.
    intros s sd2seq0.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s) as i2ds.
    apply is_derive_n_unique in i2ds.
    rewrite i2ds in sd2seq0. clear i2ds.
    rewrite signeq0_eqv in sd2seq0.
    apply Rmult_integral in sd2seq0.
    destruct sd2seq0 as [steq0 | ctr].
    + specialize (agt0_lagt0 a zlta) as zltla.
      assert (s = 0) as seq0. {
        apply (Rmult_eq_reg_l PI).
        apply (Rmult_eq_reg_r (/ (l a)²)).
        setr 0.
        lra.
        rewrite RmultRinv.
        assumption.
        zltab.
        intro la2eq0.
        unfold Rsqr in la2eq0.
        apply Rmult_integral in la2eq0.
        destruct la2eq0; lra.
        lra. }
      assumption.
    + exfalso.
      specialize (agt0_lagt0 _ zlta) as lagt0.
      unfold s, euler_spiral_tangent_pt in ctr.
      destruct Rge_dec.
      ++ destruct Req_EM_T.
         +++ destruct Rlt_dec.
             lra.
             match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               estpid A
             end.
             assert (0 <= PI / 2 + IZR N * PI) as guard; try zltab.
             specialize (rwa guard).
             simpl in rwa.
             rewrite RmultRinv in ctr.
             symmetry in e.
             rewrite rwa, e in ctr.
             autorewrite with null in ctr.
             apply Rmult_integral in ctr.
             destruct ctr as [myeq0|sineq0].
             apply ds.
             split; assumption.
             apply sin_eq_0_0 in sineq0 as [k def].
             assert (1 = 2 * (k - N))%Z as ctr. {
               apply eq_IZR.
               rewrite mult_IZR, minus_IZR.
               apply (Rmult_eq_reg_r (PI * / 2)); try zltab.
               setl (PI / 2).
               apply (Rplus_eq_reg_r (IZR N * PI)); try zltab.
               lrag def. }
             lia.

         +++ match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               rdsk2t A A
             end.
             rewrite c1d in ctr.
             match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               estpid A
             end.
             assert (0 <= k + IZR N * PI) as guard; try zltab.
             specialize (rwa guard).
             simpl in rwa.
             rewrite RmultRinv, rwa in ctr.
             specialize (Z.Even_or_Odd N) as [nev | nod].
             destruct nev as [m ndef].
             ++++ rewrite ndef, mult_IZR, cos_period1, sin_period1 in ctr.
                  specialize (cos_sin_0 k) as nbz.
                  apply Rplus_opp_r_uniq in ctr.
                  destruct (Req_dec (cos k) 0).
                  rewrite H in *.
                  autorewrite with null in ctr.
                  apply Rmult_integral in ctr.
                  destruct ctr;
                    [|apply nbz;
                      split; [reflexivity| assumption]].
                  apply cosθeq0 in H.
                  destruct kdef as [kdef|kdef].
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ lra.
                  +++++ assert (my/mx * tan k = -1) as id. {
                    unfold tan.
                    apply (Rmult_eq_reg_r (cos k * mx)).
                    lrag ctr.
                    apply Rmult_integral_contrapositive.
                    split; lra. }
                  destruct kdef.
                  rewrite H0, atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite H0, <- (Rmult_1_l PI), tan_period in id.
                  rewrite atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite cosatan.
                  rewrite <- RmultRinv.
                  intro eq0.
                  apply Rmult_integral in eq0.
                  destruct eq0 as [abs|abs].
                  lra.
                  generalize abs.
                  apply Rinv_neq_0_compat.
                  intro absi.
                  apply sqrt_eq_0 in absi.
                  apply Rplus_opp_r_uniq in absi.
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite absi in ord.
                  lra.
                  zltab.
                  lra.
             ++++ destruct nod as [m ndef].
                  rewrite ndef, plus_IZR, mult_IZR in ctr.
                  rewrite Rmult_plus_distr_r in ctr.
                  rewrite (Rplus_comm (2 * IZR m * PI)) in ctr.
                  rewrite <- Rplus_assoc in ctr.
                  rewrite cos_period1, sin_period1 in ctr.
                  autorewrite with null in ctr.
                  rewrite neg_cos, neg_sin in ctr.
                  specialize (cos_sin_0 k) as nbz.
                  apply Rplus_opp_r_uniq in ctr.
                  destruct (Req_dec (cos k) 0).
                  rewrite H in *.
                  autorewrite with null in ctr.
                  apply Rmult_integral in ctr.
                  destruct ctr;
                    [|apply nbz;
                      split; [reflexivity| lra]].
                  apply cosθeq0 in H.
                  destruct kdef as [kdef|kdef].
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ lra.
                  +++++ assert (my/mx * tan k = -1) as id. {
                    unfold tan.
                    apply (Rmult_eq_reg_r (- cos k * mx)).
                    lrag ctr.
                    apply Rmult_integral_contrapositive.
                    split; lra. }
                  destruct kdef.
                  rewrite H0, atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite H0, <- (Rmult_1_l PI), tan_period in id.
                  rewrite atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite cosatan.
                  rewrite <- RmultRinv.
                  intro eq0.
                  apply Rmult_integral in eq0.
                  destruct eq0 as [abs|abs].
                  lra.
                  generalize abs.
                  apply Rinv_neq_0_compat.
                  intro absi.
                  apply sqrt_eq_0 in absi.
                  apply Rplus_opp_r_uniq in absi.
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite absi in ord.
                  lra.
                  zltab.
                  lra.
      ++ lra.
  Qed.

  Lemma sf_2deriv_eq0_Nn1_impl : forall N (nrng : IZR N = -1),
      let s := estp N in
      sign (Derive_n sf 2 s) = 0 -> s = 0.
  Proof.
    intros until 1.
    intros s sd2seq0.
    unfold estp in *.
    specialize PI_RGT_0 as pigt0.
    specialize (sf_2deriv s) as i2ds.
    apply is_derive_n_unique in i2ds.
    rewrite i2ds in sd2seq0. clear i2ds.
    rewrite signeq0_eqv in sd2seq0.
    apply Rmult_integral in sd2seq0.
    destruct sd2seq0 as [steq0 | ctr].
    + specialize (agt0_lagt0 a zlta) as zltla.
      assert (s = 0) as seq0. {
        apply (Rmult_eq_reg_l PI).
        apply (Rmult_eq_reg_r (/ (l a)²)).
        setr 0.
        lra.
        rewrite RmultRinv.
        assumption.
        zltab.
        intro la2eq0.
        unfold Rsqr in la2eq0.
        apply Rmult_integral in la2eq0.
        destruct la2eq0; lra.
        lra. }
      assumption.
    + exfalso.
      specialize (agt0_lagt0 _ zlta) as lagt0.
      unfold s, euler_spiral_tangent_pt in ctr.
      destruct Rge_dec.
      ++ lra.
      ++ destruct Req_EM_T.
         +++ destruct Rlt_dec.
             lra.
             match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               estpid A
             end.
             assert (0 <= PI / 2 - IZR (N+1) * PI) as guard. {
               rewrite <- pm, plus_IZR.
               zltab.
               rewrite nrng.
               lra. }
             specialize (rwa guard).
             simpl in rwa.
             rewrite RmultRinv in ctr.
             symmetry in e.
             rewrite rwa, e in ctr.
             autorewrite with null in ctr.
             apply Rmult_integral in ctr.
             destruct ctr as [myeq0|sineq0].
             apply ds.
             split; assumption.
             apply sin_eq_0_0 in sineq0 as [k def].
             assert (1 = 2 * (k + N + 1))%Z as ctr. {
               apply eq_IZR.
               rewrite mult_IZR, plus_IZR, plus_IZR.
               apply (Rmult_eq_reg_r (PI * / 2)); try zltab.
               setl (PI / 2).
               apply (Rplus_eq_reg_r (- (IZR (N+1) * PI))).
               rewrite pm, plus_IZR.
               setr (IZR k * PI).
               rewrite <- def, plus_IZR.
               reflexivity. }
             lia.

         +++ match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               rdsk2t A A
             end.
             rewrite c1d in ctr.
             match goal with
             | zrs : ?mx * cos ?A + ?my * sin ?A = 0 |- _ =>
               estpid A
             end.
             assert (0 <= k - IZR (N + 1) * PI) as guard. {
               rewrite <- pm, plus_IZR.
               zltab.
               rewrite nrng.
               lra. }
             specialize (rwa guard).
             simpl in rwa.
             rewrite RmultRinv, rwa in ctr.
             specialize (Z.Even_or_Odd N) as [nev | nod].
             destruct nev as [m ndef].
             ++++ rewrite ndef, plus_IZR, mult_IZR in ctr.
                  rewrite (Rplus_comm _ 1), Rmult_plus_distr_r in ctr.
                  assert (k - (1 * PI + 2 * IZR m * PI) =
                          (k - PI + 2 * IZR (-m) * PI)) as id. {
                    rewrite opp_IZR.
                    lra. } rewrite id in ctr. clear id.
                  rewrite cos_period1, sin_period1 in ctr.
                  rewrite <- (cos_period1 _ 1), <- (sin_period1 _ 1) in ctr.
                  assert (k - PI + 2 * 1 * PI = k + PI) as id. lra.
                  rewrite id in ctr. clear id.
                  rewrite neg_cos, neg_sin in ctr.
                  specialize (cos_sin_0 k) as nbz.
                  apply Rplus_opp_r_uniq in ctr.
                  destruct (Req_dec (cos k) 0).
                  rewrite H in *.
                  autorewrite with null in ctr.
                  apply Rmult_integral in ctr.
                  destruct ctr;
                    [|apply nbz;
                      split; [reflexivity| lra]].
                  apply cosθeq0 in H.
                  destruct kdef as [kdef|kdef].
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ lra.
                  +++++ assert (my/mx * tan k = -1) as id. {
                    unfold tan.
                    apply (Rmult_eq_reg_r (- cos k * mx)).
                    lrag ctr.
                    apply Rmult_integral_contrapositive.
                    split; lra. }
                  destruct kdef.
                  rewrite H0, atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite H0, <- (Rmult_1_l PI), tan_period in id.
                  rewrite atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite cosatan.
                  rewrite <- RmultRinv.
                  intro eq0.
                  apply Rmult_integral in eq0.
                  destruct eq0 as [abs|abs].
                  lra.
                  generalize abs.
                  apply Rinv_neq_0_compat.
                  intro absi.
                  apply sqrt_eq_0 in absi.
                  apply Rplus_opp_r_uniq in absi.
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite absi in ord.
                  lra.
                  zltab.
                  lra.
             ++++ destruct nod as [m ndef].
                  assert (- (N + 1) = 2 * (-m-1))%Z as id; try lia.
                  rewrite <- pm, Ropp_mult_distr_l, <- opp_IZR in ctr.
                  rewrite id in ctr. clear id.
                  rewrite mult_IZR in ctr.
                  rewrite cos_period1, sin_period1 in ctr.
                  specialize (cos_sin_0 k) as nbz.
                  apply Rplus_opp_r_uniq in ctr.
                  destruct (Req_dec (cos k) 0).
                  rewrite H in *.
                  autorewrite with null in ctr.
                  apply Rmult_integral in ctr.
                  destruct ctr;
                    [|apply nbz;
                      split; [reflexivity| lra]].
                  apply cosθeq0 in H.
                  destruct kdef as [kdef|kdef].
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ destruct H.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  rewrite kdef, H0, <- RmultRinv in H.
                  autorewrite with null in H.
                  rewrite atan_0 in H.
                  lra.
                  +++++ lra.
                  +++++ assert (my/mx * tan k = -1) as id. {
                    unfold tan.
                    apply (Rmult_eq_reg_r (cos k * mx)).
                    lrag ctr.
                    apply Rmult_integral_contrapositive.
                    split; lra. }
                  destruct kdef.
                  rewrite H0, atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite H0, <- (Rmult_1_l PI), tan_period in id.
                  rewrite atan_right_inv in id.
                  assert ((my/mx)² = -1) as contr. {
                    unfold Rsqr.
                    assumption. }
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite contr in ord.
                  lra.
                  rewrite cosatan.
                  rewrite <- RmultRinv.
                  intro eq0.
                  apply Rmult_integral in eq0.
                  destruct eq0 as [abs|abs].
                  lra.
                  generalize abs.
                  apply Rinv_neq_0_compat.
                  intro absi.
                  apply sqrt_eq_0 in absi.
                  apply Rplus_opp_r_uniq in absi.
                  specialize (Rle_0_sqr (my / mx)) as ord.
                  rewrite absi in ord.
                  lra.
                  zltab.
                  lra.
  Qed.

  Lemma sf_2deriv_eq0_impl : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      sign (Derive_n sf 2 s) = 0 -> s = 0.
  Proof.
    intros.
    destruct nrng.
    apply sf_2deriv_eq0_N0_impl; try assumption.
    apply sf_2deriv_eq0_Nn1_impl; try assumption.
  Qed.

  (* end hide *)
  Lemma sf_2deriv_seq0_eqv : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      sign (Derive_n sf 2 s) = 0 <-> s = 0.
  Proof.
    intros.
    split.
    apply sf_2deriv_eq0_impl; try assumption.
    apply sf_2deriv_eq0; try assumption.
  Qed.

(* begin hide *)
  Lemma seq0_impl_N0 : forall N (nrng : IZR N = 0),
      let s := estp N in
      s = 0 -> my = 0.
  Proof.
    intros until 1.
    intros s seq0.

    specialize PI_RGT_0 as pigt0.
    specialize (agt0_lagt0 _ zlta) as zltla.
    
    unfold s, estp, euler_spiral_tangent_pt in seq0.
    destruct Rge_dec.
    + destruct Req_EM_T.
      ++ destruct Rlt_dec; try lra.
         apply Rmult_integral in seq0.
         destruct seq0 as [laeq0 | sqrteq0]; try lra.
         rewrite nrng in sqrteq0.
         autorewrite with null in sqrteq0.
         assert (2 / PI * (PI / 2) = 1) as id. {
           repeat rewrite <- RmultRinv.
           field.
           lra. }
         rewrite id, sqrt_1 in sqrteq0. clear id.
         lra.
      ++ rdsk2 seq0 seq0.
         rewrite c1d in *.
         apply Rmult_integral in seq0.
         destruct seq0 as [laeq0 | sqrteq0]; try lra.
         rewrite nrng in sqrteq0.
         autorewrite with null in sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0 ; [| zltab| right; reflexivity].
         apply Rmult_integral in sqrteq0.
         destruct sqrteq0 as [tpieq0 |keq0].
         rewrite <- RmultRinv in tpieq0.
         apply Rmult_integral in tpieq0.
         destruct tpieq0.
         lra.
         exfalso.
         generalize H.
         apply Rinv_neq_0_compat.
         lra.
         destruct kdef as [kd |kdpi].
         +++ rewrite kd in keq0.
             apply (f_equal tan) in keq0.
             rewrite atan_right_inv, tan_0 in keq0.
             apply (Rmult_eq_reg_r (/ mx)).
             arn.
             rewrite RmultRinv.
             assumption.
             zltab.
         +++ rewrite kdpi in keq0.
             rewrite Rplus_comm in keq0.
             apply Rplus_opp_r_uniq in keq0.
             specialize (atan_bound (my/mx)) as [atl atu].
             rewrite keq0 in atl.
             lra.
    + lra.
  Qed.

  Lemma seq0_impl_Nn1 : forall N (nrng : IZR N = -1),
      let s := estp N in
      s = 0 -> my = 0.
  Proof.
    intros until 1.
    intros s seq0.

    rename nrng into nno.
    specialize PI_RGT_0 as pigt0.
    specialize (agt0_lagt0 _ zlta) as zltla.
    
    unfold s, estp, euler_spiral_tangent_pt in seq0.
    destruct Rge_dec; try lra.
    assert (IZR (N + 1) = 0) as nrng. {
      rewrite plus_IZR.
      rewrite nno.
      field. }
    destruct Req_EM_T.
    ++ destruct Rlt_dec; try lra.
       apply Rmult_integral in seq0.
       destruct seq0 as [laeq0 | sqrteq0]; try lra.
       rewrite nrng in sqrteq0.
       autorewrite with null in sqrteq0.
       assert (2 / PI * (PI / 2) = 1) as id. {
         repeat rewrite <- RmultRinv.
         field.
         lra. }
       rewrite id, sqrt_1 in sqrteq0. clear id.
       lra.
    ++ rdsk2 seq0 seq0.
       rewrite c1d in *.
       apply Rmult_integral in seq0.
         destruct seq0 as [laeq0 | sqrteq0]; try lra.
         rewrite nrng in sqrteq0.
         autorewrite with null in sqrteq0.
         rewrite <- sqrt_0 in sqrteq0.
         apply sqrt_inj in sqrteq0 ; [| zltab| right; reflexivity].
         apply Rmult_integral in sqrteq0.
         destruct sqrteq0 as [tpieq0 |keq0].
         rewrite <- RmultRinv in tpieq0.
         apply Rmult_integral in tpieq0.
         destruct tpieq0.
         lra.
         exfalso.
         generalize H.
         apply Rinv_neq_0_compat.
         lra.
         destruct kdef as [kd |kdpi].
         +++ rewrite kd in keq0.
             apply (f_equal tan) in keq0.
             rewrite atan_right_inv, tan_0 in keq0.
             apply (Rmult_eq_reg_r (/ mx)).
             arn.
             rewrite RmultRinv.
             assumption.
             zltab.
         +++ rewrite kdpi in keq0.
             rewrite Rplus_comm in keq0.
             apply Rplus_opp_r_uniq in keq0.
             specialize (atan_bound (my/mx)) as [atl atu].
             rewrite keq0 in atl.
             lra.
  Qed.

  Lemma seq0_impl : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      s = 0 -> my = 0.
  Proof.
    intros until 1.
    intros s seq0.
    destruct nrng.
    eapply seq0_impl_N0; try eassumption.
    eapply seq0_impl_Nn1; try eassumption.
  Qed.


  Lemma myeq0_impl : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      my = 0 -> s = 0.
  Proof.
    intros until 1.
    intros s myeq0.
    destruct nrng.
    + unfold estp, euler_spiral_tangent_pt in *.
      destruct Rge_dec; try lra.
      destruct Req_EM_T; try lra.
      assert (atan (my / mx) = 0) as at0. {
        rewrite myeq0, <- RmultRinv.
        arn.
        rewrite atan_0.
        reflexivity. }
      unfold s.
      rewrite at0 in *.
      clear s.
      destruct Rlt_dec.
      lra.
      rewrite H.
      arn.
      reflexivity.
    + unfold estp, euler_spiral_tangent_pt in *.
      destruct Rge_dec; try lra.
      destruct Req_EM_T; try lra.
      assert (atan (my / mx) = 0) as at0. {
        rewrite myeq0, <- RmultRinv.
        arn.
        rewrite atan_0.
        reflexivity. }
      unfold s.
      rewrite at0 in *.
      clear s.
      destruct Rlt_dec; try lra.
      rewrite plus_IZR, H, Rplus_comm.
      fieldrewrite (1 + - 1) 0.
      arn.
      reflexivity.
  Qed.


  (* end hide *)

  Lemma seq0_bimpl_myeq0 : forall N (nrng : IZR N = 0 \/ IZR N = -1),
      let s := estp N in
      s = 0 <-> my = 0.
  Proof.
    intros.
    split.
    apply seq0_impl; try assumption.
    apply myeq0_impl; try assumption.
  Qed.

(* begin hide *)
  Lemma sf_2deriv_neg_N0_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (N0 : IZR N = 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      my < 0.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    assert (0 <> my) as myne0. {
      intro myeq0.
      symmetry in myeq0.
      assert (IZR N = 0 \/ IZR N = -1) as c; try lra.
      rewrite <- (seq0_bimpl_myeq0 N), <- sf_2deriv_seq0_eqv in myeq0;
        try assumption.
      rewrite signeq0_eqv in myeq0.
      unfold s in sf2d.
      unfold estp in myeq0.
      rewrite myeq0 in sf2d.
      lra. }

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [lra|].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    destruct zltk as [zltk | zeqk].
    2 : { exfalso.
          rewrite <- zeqk in *.
          clear - myne0 n kdef.
          destruct kdef as [atz |apz].
          - symmetry in atz.
            unfold atan in atz.
            destruct pre_atan as [a [[arl aru] ata]].
            rewrite atz, tan_0 in ata.
            rewrite <- RmultRinv in ata.
            assert (0 = my) as zeqmy. {
              apply (Rmult_eq_reg_r (/ mx)).
              arn.
              assumption.
              zltab. }
            lra.
          - specialize PI_RGT_0 as pigt0.
            symmetry in apz.
            unfold atan in apz.
            destruct pre_atan as [a [[arl aru] ata]].
            lra.
    }

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k + IZR N * PI) as ineq; try zltab.
    left; assumption.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (k + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0] ;
     [ | rewrite <- k0 in sf2d;
         autorewrite with null in sf2d;
         lra].
    
    assert (k = atan (my / mx) /\
            0 < atan (my / mx) \/
            k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : ?K * (mx * cos ?A + my * sin ?A) < 0,
          I : 0 < ?K |- _ =>
      assert (mx * cos A + my * sin A < 0) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]
    end.
    assert (k + IZR N * PI = atan (my / mx) + IZR N * PI /\
            0 < atan (my / mx) \/
            k + IZR N * PI = atan (my / mx) + IZR (N+1) * PI /\ atan (my / mx) < 0)
      as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) N) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 < my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        (* destruct atnn as [atp |ate]. *)
        specialize (tan_increasing _ _ zl atnn ph) as tord.
        rewrite td, tan_0 in tord.
        assumption.
        (* rewrite <- ate, tan_0 in td. *)
        (* right. *)
        (* assumption. *) }
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         (* left. *)
         (* split; try assumption. *)
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setl (- (my * / mx)); auto.
         setr (-0).
         apply Ropp_lt_contravar.
         assumption.
      ++ unfold Z.Odd in Ncond;
         clear - Ncond N0;
         destruct Ncond as [b Nd];
         apply eq_IZR in N0;
         lia.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (N+1)) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      rewrite Z.add_1_r in cond.
      rewrite Z.Even_succ, Z.Odd_succ in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ unfold Z.Odd in Ncond;
         clear - Ncond N0;
         destruct Ncond as [b Nd];
         apply eq_IZR in N0;
         lia.

      ++ rewrite pmd in sf2ds.
         (* right. *)
         (* split; try assumption. *)
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
  Qed.


  Lemma sf_2deriv_pos_N0_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (N0 : IZR N = 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      0 < my.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    assert (0 <> my) as myne0. {
      intro myeq0.
      symmetry in myeq0.
      assert (IZR N = 0 \/ IZR N = -1) as c; try lra.
      rewrite <- (seq0_bimpl_myeq0 N), <- sf_2deriv_seq0_eqv in myeq0;
        try assumption.
      rewrite signeq0_eqv in myeq0.
      unfold s in sf2d.
      unfold estp in myeq0.
      rewrite myeq0 in sf2d.
      lra. }

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [lra|].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    destruct zltk as [zltk | zeqk].
    2 : { exfalso.
          rewrite <- zeqk in *.
          clear - myne0 n kdef.
          destruct kdef as [atz |apz].
          - symmetry in atz.
            unfold atan in atz.
            destruct pre_atan as [a [[arl aru] ata]].
            rewrite atz, tan_0 in ata.
            rewrite <- RmultRinv in ata.
            assert (0 = my) as zeqmy. {
              apply (Rmult_eq_reg_r (/ mx)).
              arn.
              assumption.
              zltab. }
            lra.
          - specialize PI_RGT_0 as pigt0.
            symmetry in apz.
            unfold atan in apz.
            destruct pre_atan as [a [[arl aru] ata]].
            lra.
    }

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k + IZR N * PI) as ineq; try zltab.
    left; assumption.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (k + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0] ;
        [ | rewrite <- k0 in sf2d;
            autorewrite with null in sf2d;
            lra].
    
    assert (k = atan (my / mx) /\
            0 < atan (my / mx) \/
            k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : 0 < ?K * (mx * cos ?A + my * sin ?A),
          I : 0 < ?K |- _ =>
      assert (0 < mx * cos A + my * sin A) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]

    end.
    assert (k + IZR N * PI = atan (my / mx) + IZR N * PI /\
            0 < atan (my / mx) \/
            k + IZR N * PI = atan (my / mx) + IZR (N+1) * PI /\
            atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) N) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 < my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        (* destruct atnn as [atp |ate]. *)
        specialize (tan_increasing _ _ zl atnn ph) as tord.
        rewrite td, tan_0 in tord.
        (* left. *)
        assumption.
        (* rewrite <- ate, tan_0 in td. *)
        (* right. *)
        (* assumption. *) }

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         (* left. *)
         (* split; try assumption. *)
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         (* split; try assumption. *)

         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         lra.
         arn.
         assumption.
      ++ unfold Z.Odd in Ncond;
         clear - Ncond N0;
         destruct Ncond as [b Nd];
         apply eq_IZR in N0;
         lia.

    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (N+1)) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      rewrite Z.add_1_r in cond.
      rewrite Z.Even_succ, Z.Odd_succ in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ unfold Z.Odd in Ncond;
         clear - Ncond N0;
         destruct Ncond as [b Nd];
         apply eq_IZR in N0;
         lia.

      ++ rewrite pmd in sf2ds.
         (* right. *)
         (* split; try assumption. *)
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         (* split; try assumption. *)
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setl (-0).
         setr (- (my * / mx)).
         lra.
         apply Ropp_lt_contravar.
         assumption.
  Qed.

  Lemma sf_2deriv_neg_Nn1_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Neqn1 : IZR N = -1),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      0 < my.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    assert (0 <> my) as myne0. {
      intro myeq0.
      symmetry in myeq0.
      assert (IZR N = 0 \/ IZR N = -1) as c; try lra.
      rewrite <- (seq0_bimpl_myeq0 N), <- sf_2deriv_seq0_eqv in myeq0;
        try assumption.
      rewrite signeq0_eqv in myeq0.
      unfold s in sf2d.
      unfold estp in myeq0.
      rewrite myeq0 in sf2d.
      lra. }
    
    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec; [lra|].
    destruct Req_EM_T; [lra|clear n].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    destruct zltk as [zltk | zeqk].
    2 : { exfalso.
          rewrite <- zeqk in *.
          clear - myne0 n0 kdef.
          destruct kdef as [atz |apz].
          - symmetry in atz.
            unfold atan in atz.
            destruct pre_atan as [a [[arl aru] ata]].
            rewrite atz, tan_0 in ata.
            rewrite <- RmultRinv in ata.
            assert (0 = my) as zeqmy. {
              apply (Rmult_eq_reg_r (/ mx)).
              arn.
              assumption.
              zltab. }
            lra.
          - specialize PI_RGT_0 as pigt0.
            symmetry in apz.
            unfold atan in apz.
            destruct pre_atan as [a [[arl aru] ata]].
            lra.
    }
    
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k - IZR (N + 1) * PI) as ineq; try zltab.

    fieldrewrite (k - IZR (N + 1) * PI) (k + - IZR (N + 1) * PI).
    zltab.
    left; assumption.
    rewrite <- opp_IZR.
    apply IZR_le.
    apply eq_IZR in Neqn1.
    rewrite Neqn1.
    omega.
    
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
                                                                                                 [ | apply (Rmult_eq_compat_l (-1)) in k0;
                                                                                                     assert (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI)))
                                                                                                                    / (l a)² = 0) as eq0; try lra;
                                                                                                     rewrite eq0 in sf2d;
                                                                                                     autorewrite with null in sf2d;
                                                                                                     lra].


    
    assert (k = atan (my / mx) /\
            0 < atan (my / mx) \/
            k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : ?K * (mx * cos ?A + my * sin ?A) < 0,
          I : 0 < - ?K |- _ =>
      assert (0 < mx * cos A + my * sin A) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.
    
    assert (k - IZR (N + 1) * PI = atan (my / mx) + - IZR (N + 1) * PI /\
            0 < atan (my / mx) \/
            k - IZR (N + 1) * PI = atan (my / mx) + - IZR N * PI /\ atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      rewrite <- opp_IZR in sf2ds.
      specialize (sincosatan2 (my/mx) (- (N + 1))) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 < my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ zl atnn ph) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      rewrite Z.add_1_r in cond.
      rewrite Z.opp_succ in cond.
      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.even_pred, Z.odd_pred, Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas mxne0.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         lra.
         arn.
         assumption.
      ++ unfold Z.Even in Ncond;
         clear - Ncond Neqn1;
         destruct Ncond as [b Nd];
         apply eq_IZR in Neqn1;
         lia.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (-N)) as [pm [cond [sadef cadef]]].
      rewrite opp_IZR in sadef, cadef.
      rewrite sadef, cadef in sf2ds.

      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ unfold Z.Even in Ncond;
         clear - Ncond Neqn1;
         destruct Ncond as [b Nd];
         apply eq_IZR in Neqn1;
         lia.
      ++ rewrite pmd in sf2ds.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         apply Ropp_lt_cancel.
         lrag sf2ds2.
  Qed.

  Lemma sf_2deriv_pos_Nn1_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Neqn1 : IZR N = -1),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      my < 0.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    assert (0 <> my) as myne0. {
      intro myeq0.
      symmetry in myeq0.
      assert (IZR N = 0 \/ IZR N = -1) as c; try lra.
      rewrite <- (seq0_bimpl_myeq0 N), <- sf_2deriv_seq0_eqv in myeq0;
        try assumption.
      rewrite signeq0_eqv in myeq0.
      unfold s in sf2d.
      unfold estp in myeq0.
      rewrite myeq0 in sf2d.
      lra. }

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec; [lra|].
    destruct Req_EM_T; [lra|clear n].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    destruct zltk as [zltk | zeqk].
    2 : { exfalso.
          rewrite <- zeqk in *.
          clear - myne0 n0 kdef.
          destruct kdef as [atz |apz].
          - symmetry in atz.
            unfold atan in atz.
            destruct pre_atan as [a [[arl aru] ata]].
            rewrite atz, tan_0 in ata.
            rewrite <- RmultRinv in ata.
            assert (0 = my) as zeqmy. {
              apply (Rmult_eq_reg_r (/ mx)).
              arn.
              assumption.
              zltab. }
            lra.
          - specialize PI_RGT_0 as pigt0.
            symmetry in apz.
            unfold atan in apz.
            destruct pre_atan as [a [[arl aru] ata]].
            lra.
    }

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k - IZR (N + 1) * PI) as ineq; try zltab.

    fieldrewrite (k - IZR (N + 1) * PI) (k + - IZR (N + 1) * PI).
    zltab.
    left; assumption.
    rewrite <- opp_IZR.
    apply IZR_le.
    apply eq_IZR in Neqn1.
    omega.
    
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
      [ | apply (Rmult_eq_compat_l (-1)) in k0;
          assert (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI)))
                         / (l a)² = 0) as eq0; try lra;
          rewrite eq0 in sf2d;
          autorewrite with null in sf2d;
          lra].
    
    assert (k = atan (my / mx) /\
            0 < atan (my / mx) \/
            k = atan (my / mx) + PI /\
            atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : 0 < ?K * (mx * cos ?A + my * sin ?A),
          I : 0 < - ?K |- _ =>
      assert (mx * cos A + my * sin A < 0) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.
    
    assert (k - IZR (N + 1) * PI = atan (my / mx) + - IZR (N + 1) * PI /\
            0 < atan (my / mx) \/
            k - IZR (N + 1) * PI = atan (my / mx) + - IZR N * PI /\
            atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      rewrite <- opp_IZR in sf2ds.
      specialize (sincosatan2 (my/mx) (- (N + 1))) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 < my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ zl atnn ph) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      rewrite Z.add_1_r in cond.
      rewrite Z.opp_succ in cond.
      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.even_pred, Z.odd_pred, Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas mxne0.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setl (- (my * / mx)); try lra.
      ++ unfold Z.Even in Ncond;
         clear - Ncond Neqn1;
         destruct Ncond as [b Nd];
         apply eq_IZR in Neqn1;
         lia.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (-N)) as [pm [cond [sadef cadef]]].
      rewrite opp_IZR in sadef, cadef.
      rewrite sadef, cadef in sf2ds.

      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ unfold Z.Even in Ncond;
         clear - Ncond Neqn1;
         destruct Ncond as [b Nd];
         apply eq_IZR in Neqn1;
         lia.
      ++ rewrite pmd in sf2ds.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         lra.
         arn.
         assumption.
  Qed.
  
  Lemma sf_2deriv_neg_posN_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nge0 : IZR N >= 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      ((Z.Even N /\ mx < 0 /\ my <= 0) \/ (Z.Even N /\ 0 < mx /\ my < 0) \/
       (Z.Odd N /\ 0 < mx /\ 0 <= my) \/ (Z.Odd N /\ mx < 0 /\ 0 < my)).
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [lra|].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k + IZR N * PI) as ineq; try zltab.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (k + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0] ;
                                                                                     [ | rewrite <- k0 in sf2d;
                                                                                         autorewrite with null in sf2d;
                                                                                         lra].
    
    assert (k = atan (my / mx) /\ 0 <= atan (my / mx) \/
                                  k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : ?K * (mx * cos ?A + my * sin ?A) < 0,
          I : 0 < ?K |- _ =>
      assert (mx * cos A + my * sin A < 0) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]
    end.
    assert (k + IZR N * PI = atan (my / mx) + IZR N * PI /\ 0 <= atan (my / mx) \/
                                                            k + IZR N * PI = atan (my / mx) + IZR (N+1) * PI /\ atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) N) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 <= my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        destruct atnn as [atp |ate].
        specialize (tan_increasing _ _ zl atp ph) as tord.
        rewrite td, tan_0 in tord.
        left.
        assumption.
        rewrite <- ate, tan_0 in td.
        right.
        assumption. }
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_le_reg_r (- / mx)).
         lra.
         arn.
         setl (- (my * / mx)); auto.
         setr (-0).
         apply Ropp_le_contravar.
         assumption.
      ++ rewrite pmd in sf2ds.
         right.
         right.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_le_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (N+1)) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      rewrite Z.add_1_r in cond.
      rewrite Z.Even_succ, Z.Odd_succ in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         right.
         right.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setr (- (my * / mx)); auto.
         setl (-0).
         apply Ropp_lt_contravar.
         assumption.
      ++ rewrite pmd in sf2ds.
         right.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
  Qed.
  
  Lemma sf_2deriv_pos_posN_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nge0 : IZR N >= 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      ((Z.Even N /\ 0 < mx /\ 0 <= my) \/ (Z.Even N /\ mx < 0 /\ 0 < my) \/
       (Z.Odd N /\ mx < 0/\ my <= 0) \/ (Z.Odd N /\ 0 < mx /\ my < 0)).
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [lra|].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k + IZR N * PI) as ineq; try zltab.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (k + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0] ;
        [ | rewrite <- k0 in sf2d;
            autorewrite with null in sf2d;
            lra].
    
    assert (k = atan (my / mx) /\ 0 <= atan (my / mx) \/
                                  k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : 0 < ?K * (mx * cos ?A + my * sin ?A),
          I : 0 < ?K |- _ =>
      assert (0 < mx * cos A + my * sin A) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]

    end.
    assert (k + IZR N * PI = atan (my / mx) + IZR N * PI /\
            0 <= atan (my / mx) \/
            k + IZR N * PI = atan (my / mx) + IZR (N+1) * PI /\
            atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) N) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 <= my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        destruct atnn as [atp |ate].
        specialize (tan_increasing _ _ zl atp ph) as tord.
        rewrite td, tan_0 in tord.
        left.
        assumption.
        rewrite <- ate, tan_0 in td.
        right.
        assumption. }

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.

         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_le_reg_r (/ mx)).
         lra.
         arn.
         assumption.
      ++ rewrite pmd in sf2ds.
         right.
         right.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0 ) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_le_reg_r (/ - mx)).
         rewrite <- Ropp_inv_permute.
         lra.
         lra.
         arn.
         setl (- (my * / mx)); try lra.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (N+1)) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      rewrite Z.add_1_r in cond.
      rewrite Z.Even_succ, Z.Odd_succ in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         right.
         right.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
      ++ rewrite pmd in sf2ds.
         right.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setl (-0).
         setr (- (my * / mx)).
         lra.
         apply Ropp_lt_contravar.
         assumption.
  Qed.


  Lemma sf_2deriv_neg_negN_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nlt0 : IZR N < 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      ((Z.Even N /\ mx < 0/\ my <= 0) \/ (Z.Even N /\ 0 < mx /\ my < 0) \/
       (Z.Odd N /\ 0 < mx /\ 0 <= my) \/ (Z.Odd N /\ mx < 0 /\ 0 < my)).
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec; [lra|].
    destruct Req_EM_T; [lra|clear n].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k - IZR (N + 1) * PI) as ineq; try zltab.

    fieldrewrite (k - IZR (N + 1) * PI) (k + - IZR (N + 1) * PI).
    zltab.
    rewrite <- opp_IZR.
    apply IZR_le.
    apply lt_IZR in Nlt0.
    omega.
    
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
                                                                                                 [ | apply (Rmult_eq_compat_l (-1)) in k0;
                                                                                                     assert (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI)))
                                                                                                                    / (l a)² = 0) as eq0; try lra;
                                                                                                     rewrite eq0 in sf2d;
                                                                                                     autorewrite with null in sf2d;
                                                                                                     lra].


    
    assert (k = atan (my / mx) /\ 0 <= atan (my / mx) \/
                                  k = atan (my / mx) + PI /\ atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : ?K * (mx * cos ?A + my * sin ?A) < 0,
          I : 0 < - ?K |- _ =>
      assert (0 < mx * cos A + my * sin A) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.
    
    assert (k - IZR (N + 1) * PI = atan (my / mx) + - IZR (N + 1) * PI /\ 0 <= atan (my / mx) \/
                                                                          k - IZR (N + 1) * PI = atan (my / mx) + - IZR N * PI /\ atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      rewrite <- opp_IZR in sf2ds.
      specialize (sincosatan2 (my/mx) (- (N + 1))) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 <= my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        destruct atnn as [atp |ate].
        specialize (tan_increasing _ _ zl atp ph) as tord.
        rewrite td, tan_0 in tord.
        left.
        assumption.
        rewrite <- ate, tan_0 in td.
        right.
        assumption. }
      rewrite Z.add_1_r in cond.
      rewrite Z.opp_succ in cond.
      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.even_pred, Z.odd_pred, Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         right.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas mxne0.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_le_reg_r (/ mx)).
         lra.
         arn.
         assumption.
      ++ rewrite pmd in sf2ds.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_le_reg_r (- / mx)).
         lra.
         arn.
         lra.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (-N)) as [pm [cond [sadef cadef]]].
      rewrite opp_IZR in sadef, cadef.
      rewrite sadef, cadef in sf2ds.

      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
      ++ rewrite pmd in sf2ds.
         right.
         right.
         right.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         apply Ropp_lt_cancel.
         lrag sf2ds2.
  Qed.

  Lemma sf_2deriv_pos_negN_mxne0 :
    forall N (mxne0 : 0 <> mx)
           (Nlt0 : IZR N < 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      ((Z.Even N /\ 0 < mx /\ 0 <= my) \/ (Z.Even N /\ mx < 0 /\ 0 < my) \/
       (Z.Odd N /\ mx < 0 /\ my <= 0) \/ (Z.Odd N /\ 0 < mx /\ my< 0)).
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec; [lra|].
    destruct Req_EM_T; [lra|clear n].
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => rdsk2t A B
    end.
    rewrite c1d in d2s, sf2d.
    specialize (agt0_lagt0 _ zlta) as zltla.

    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (mx * cos ?B + my * sin ?B) |- _ => estpid B
    end.
    specialize PI_RGT_0 as pigt0.
    assert (0 <= k - IZR (N + 1) * PI) as ineq; try zltab.

    fieldrewrite (k - IZR (N + 1) * PI) (k + - IZR (N + 1) * PI).
    zltab.
    rewrite <- opp_IZR.
    apply IZR_le.
    apply lt_IZR in Nlt0.
    omega.
    
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (k - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
      [ | apply (Rmult_eq_compat_l (-1)) in k0;
          assert (PI * (- l a * sqrt (2 / PI * (k - IZR (N + 1) * PI)))
                         / (l a)² = 0) as eq0; try lra;
          rewrite eq0 in sf2d;
          autorewrite with null in sf2d;
          lra].
    
    assert (k = atan (my / mx) /\
            0 <= atan (my / mx) \/
            k = atan (my / mx) + PI /\
            atan (my/mx) < 0) as kdef2. {
      destruct kdef.
      left.
      split; lra.
      right.
      split; lra. }
    clear kdef.

    match goal with
    | H : 0 < ?K * (mx * cos ?A + my * sin ?A),
          I : 0 < - ?K |- _ =>
      assert (mx * cos A + my * sin A < 0) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.
    
    assert (k - IZR (N + 1) * PI = atan (my / mx) + - IZR (N + 1) * PI /\
            0 <= atan (my / mx) \/
            k - IZR (N + 1) * PI = atan (my / mx) + - IZR N * PI /\
            atan (my / mx) < 0) as kdef3. {
      destruct kdef2 as [[kdef ats]| [kdef ats]];
        [left|right];
        rewrite kdef;
        (split; [try rewrite plus_IZR; field|assumption]).
    }
    clear kdef2.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    destruct kdef3 as [[kdef atnn] |[kdef atn]].
    + rewrite kdef in sf2ds.
      rewrite <- opp_IZR in sf2ds.
      specialize (sincosatan2 (my/mx) (- (N + 1))) as [pm [cond [sadef cadef]]].
      rewrite sadef, cadef in sf2ds.
      assert (0 <= my * / mx) as atas. {
        rewrite RmultRinv.
        unfold atan in atnn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        destruct atnn as [atp |ate].
        specialize (tan_increasing _ _ zl atp ph) as tord.
        rewrite td, tan_0 in tord.
        left.
        assumption.
        rewrite <- ate, tan_0 in td.
        right.
        assumption. }
      rewrite Z.add_1_r in cond.
      rewrite Z.opp_succ in cond.
      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.even_pred, Z.odd_pred, Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         right.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas mxne0.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_le_reg_r (- / mx)).
         lra.
         arn.
         setl (- (my * / mx)); try lra.
      ++ rewrite pmd in sf2ds.
         left.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_le_reg_r (/ mx)).
         assumption.
         arn.
         assumption.
    + rewrite kdef in sf2ds.
      specialize (sincosatan2 (my/mx) (-N)) as [pm [cond [sadef cadef]]].
      rewrite opp_IZR in sadef, cadef.
      rewrite sadef, cadef in sf2ds.

      rewrite <- Z.even_spec, <- Z.odd_spec in cond.
      rewrite Z.odd_opp, Z.even_opp in cond.
      rewrite Z.even_spec, Z.odd_spec in cond.

      assert (my * / mx < 0) as atas. {
        rewrite RmultRinv.
        unfold atan in atn.
        destruct pre_atan as [φ [[pl ph] td]].
        assert (-PI / 2 < 0) as zl. lra.
        assert (0 < PI / 2) as zh. lra.
        specialize (tan_increasing _ _ pl atn zh) as tord.
        rewrite td, tan_0 in tord.
        assumption. }
      
      destruct cond as [[Ncond pmd]|[Ncond pmd]].
      ++ rewrite pmd in sf2ds.
         right.
         left.
         split; try assumption.
         assert (mx + my * (my / mx) < 0) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (mx < 0) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_lt_0_compat in mxlt0.
         apply (Rmult_lt_reg_r (- / mx)).
         lra.
         arn.
         setr (- ( my * / mx)).
         lra.
         setl (-0).
         lra.
      ++ rewrite pmd in sf2ds.
         right.
         right.
         right.
         split; try assumption.
         assert (0 < mx + my * (my / mx)) as sf2ds2. {
           apply (Rmult_lt_reg_r (/ sqrt (1 + (my / mx)²))).
           zltab.
           lra. }
         clear - n0 sf2ds2 dpos atas.
         assert (0 < mx) as mxlt0. {
           apply (Rmult_lt_reg_r (1 + (my / mx)²));
             try assumption.
           arn.
           lrag sf2ds2. }
         split; try assumption.
         apply Rinv_0_lt_compat in mxlt0.
         apply (Rmult_lt_reg_r (/ mx)).
         lra.
         arn.
         assumption.
  Qed.


  Lemma sf_2deriv_neg_posN_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (myne0 : 0 <> my)
           (Nge0 : IZR N >= 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      Z.Even N /\ my < 0 \/ Z.Odd N /\ 0 < my.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [|lra].
    specialize PI_RGT_0 as pigt0.
    destruct Rlt_dec; [lra|].
    specialize (agt0_lagt0 _ zlta) as zltla.
    rewrite <- mxeq0 in d2s.
    autorewrite with null in d2s.
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (my * sin ?B) |- _ => estpid B
    end.
    assert (0 <= PI/2 + IZR N * PI) as ineq; try zltab.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (PI/2 + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0];
                                                                                        [ | rewrite <- k0 in sf2d;
                                                                                            autorewrite with null in sf2d;
                                                                                            lra].

    match goal with
    | H : ?K * (my * sin ?A) < 0,
          I : 0 < ?K |- _ =>
      assert (my * sin A < 0) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]
    end.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    (* specialize (atan_bound (my/mx)) as atb. *)
    (* assert (-PI / 2 < 0 < PI / 2) as zir. lra. *)

    specialize (Z.Even_or_Odd N) as [nev |nod].
    + left.
      split; try assumption.
      destruct nev as [m Ndef].
      rewrite Ndef, mult_IZR, sin_period1, sin_PI2 in sf2ds.
      lra.
    + right.
      split; try assumption.
      destruct nod as [m Ndef].
      rewrite Ndef, plus_IZR, mult_IZR, (Rplus_comm _ 1),
      Rmult_plus_distr_r, <- Rplus_assoc, sin_period1,
      Rmult_1_l, neg_sin, sin_PI2 in sf2ds.
      lra.
  Qed.


  Lemma sf_2deriv_pos_posN_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (myne0 : 0 <> my)
           (Nge0 : IZR N >= 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      Z.Even N /\ 0 < my \/ Z.Odd N /\ my < 0.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [|lra].
    destruct Req_EM_T; [|lra].
    specialize PI_RGT_0 as pigt0.
    destruct Rlt_dec; [lra|].
    specialize (agt0_lagt0 _ zlta) as zltla.
    rewrite <- mxeq0 in d2s.
    autorewrite with null in d2s.
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (my * sin ?B) |- _ => estpid B
    end.
    assert (0 <= PI/2 + IZR N * PI) as ineq; try zltab.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.
    
    assert (0 <= PI * (l a * sqrt (2 / PI * (PI/2 + IZR N * PI))) / (l a)²) as poszK. {
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK |k0];
          [ | rewrite <- k0 in sf2d;
              autorewrite with null in sf2d;
              lra].

    match goal with
    | H : 0 < ?K * (my * sin ?A),
          I : 0 < ?K |- _ =>
      assert (0 < my * sin A) as sf2ds;
        [apply (Rmult_lt_reg_l K);
         [assumption|
          arn; assumption]|]
    end.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    specialize (Z.Even_or_Odd N) as [nev |nod].
    + left.
      split; try assumption.
      destruct nev as [m Ndef].
      rewrite Ndef, mult_IZR, sin_period1, sin_PI2 in sf2ds.
      lra.
    + right.
      split; try assumption.
      destruct nod as [m Ndef].
      rewrite Ndef, plus_IZR, mult_IZR, (Rplus_comm _ 1),
      Rmult_plus_distr_r, <- Rplus_assoc, sin_period1,
      Rmult_1_l, neg_sin, sin_PI2 in sf2ds.
      lra.
  Qed.

  
  Lemma sf_2deriv_neg_negN_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (myne0 : 0 <> my)
           (Nlt0 : IZR N < 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      Z.Even N /\ my < 0 \/ Z.Odd N /\ 0 < my.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [lra|clear n].
    destruct Req_EM_T; [clear e|lra].
    specialize PI_RGT_0 as pigt0.
    destruct Rlt_dec; [lra|].
    specialize (agt0_lagt0 _ zlta) as zltla.
    rewrite <- mxeq0 in d2s.
    autorewrite with null in d2s.
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (my * sin ?B) |- _ => estpid B
    end.
    assert (0 <= PI/2 - IZR (N + 1) * PI) as ineq.
    rewrite plus_IZR.
    setr ((- 1 / 2 + - IZR (N)) * PI).
    rewrite <- opp_IZR.
    apply Ropp_lt_contravar in Nlt0.
    rewrite Ropp_0, <- opp_IZR in Nlt0.
    apply (Rmult_le_reg_r (2 / PI)).
    zltab.
    arn.
    setr (-1 + 2 * IZR (- N)); try lra.
    rewrite <- mult_IZR, <- plus_IZR.
    apply IZR_le.
    apply lt_IZR in Nlt0.
    omega.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.

    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
    [ | apply (Rmult_eq_compat_l (-1)) in k0;
        assert (PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI)))
                       / (l a)² = 0) as eq0; try lra;
        rewrite eq0 in sf2d;
        autorewrite with null in sf2d;
        lra].
    

    match goal with
    | H : ?K * (my * sin ?A) < 0,
          I : 0 < - ?K |- _ =>
      assert (0 < my * sin A) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    specialize (Z.Even_or_Odd N) as [nev |nod].
    + left.
      split; try assumption.
      destruct nev as [m Ndef].
      rewrite Ndef, plus_IZR, mult_IZR in sf2ds.
      assert (PI / 2 - (2 * IZR m + 1) * PI =
              - (PI / 2) + 2 * IZR (- m) * PI) as id. {
        rewrite opp_IZR.
        field. }
      rewrite id, sin_period1, sin_neg, sin_PI2 in sf2ds.
      lra.
    + right.
      split; try assumption.
      destruct nod as [m Ndef].
      rewrite Ndef in sf2ds.
      assert (PI / 2 - IZR (2 * m + 1 + 1) * PI = (PI / 2 + 2 * IZR (- (m + 1)) * PI)) as id. {
        rewrite opp_IZR, plus_IZR, plus_IZR, plus_IZR, mult_IZR.
        field. }
      rewrite id, sin_period1, sin_PI2, Rmult_1_r in sf2ds.
      assumption.
  Qed.


  Lemma sf_2deriv_pos_negN_mxeq0 :
    forall N (mxeq0 : 0 = mx)
           (myne0 : 0 <> my)
           (Nlt0 : IZR N < 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      Z.Even N /\ 0 < my \/ Z.Odd N /\ my < 0.
  Proof.
    intros.
    unfold estp in *.
    rename H into sf2d.
    specialize (sf_2deriv s) as d2s.
    change (is_derive_n sf 2 s (PI * s / (l a)² *
                                (mx * cos (1 / 2 * PI * (s * / l a)²) +
                                 my * sin (1 / 2 * PI * (s * / l a)²))))
      in d2s.
    apply is_derive_n_unique in d2s.

    unfold s, euler_spiral_tangent_pt in *.
    destruct Rge_dec ; [lra|clear n].
    destruct Req_EM_T; [clear e|lra].
    specialize PI_RGT_0 as pigt0.
    destruct Rlt_dec; [lra|].
    specialize (agt0_lagt0 _ zlta) as zltla.
    rewrite <- mxeq0 in d2s.
    autorewrite with null in d2s.
    match goal with
    | Q : Derive_n sf 2 ?A =
          PI * ?A / (l a)² * (my * sin ?B) |- _ => estpid B
    end.
    assert (0 <= PI/2 - IZR (N + 1) * PI) as ineq.
    rewrite plus_IZR.
    setr ((- 1 / 2 + - IZR (N)) * PI).
    rewrite <- opp_IZR.
    apply Ropp_lt_contravar in Nlt0.
    rewrite Ropp_0, <- opp_IZR in Nlt0.
    apply (Rmult_le_reg_r (2 / PI)).
    zltab.
    arn.
    setr (-1 + 2 * IZR (- N)); try lra.
    rewrite <- mult_IZR, <- plus_IZR.
    apply IZR_le.
    apply lt_IZR in Nlt0.
    omega.
    specialize (rwa ineq).
    simpl in rwa.
    rewrite RmultRinv in d2s.
    rewrite rwa in d2s.
    rewrite d2s in sf2d.

    assert (0 <= - (PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI))) / (l a)²)) as poszK. {
      setr (PI * (l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI))) / (l a)²).
      apply ane0_lane0; try assumption.
      zltab.
      unfold Rsqr.
      zltab. }

    destruct poszK as [posK | k0];
      [ | apply (Rmult_eq_compat_l (-1)) in k0;
          assert (PI * (- l a * sqrt (2 / PI * (PI / 2 - IZR (N + 1) * PI)))
                         / (l a)² = 0) as eq0; try lra;
          rewrite eq0 in sf2d;
          autorewrite with null in sf2d;
          lra].


    match goal with
    | H : 0 < ?K * (my * sin ?A),
          I : 0 < - ?K |- _ =>
      assert (my * sin A < 0) as sf2ds;
        [apply Ropp_lt_cancel;
         apply (Rmult_lt_reg_r (-K));
         [assumption|arn; lrag sf2d]
        |]
    end.

    assert (0 < 1 + (my / mx)²) as dpos;
      [apply Rplus_lt_le_0_compat;
       [lra|apply Rle_0_sqr]|].
    
    assert (0 < sqrt (1 + (my / mx)²)) as sdpos;
      [apply sqrt_lt_R0; assumption|].

    specialize (Z.Even_or_Odd N) as [nev |nod].
    + left.
      split; try assumption.
      destruct nev as [m Ndef].
      rewrite Ndef, plus_IZR, mult_IZR in sf2ds.
      assert (PI / 2 - (2 * IZR m + 1) * PI =
              - (PI / 2) + 2 * IZR (- m) * PI) as id. {
        rewrite opp_IZR.
        field. }
      rewrite id, sin_period1, sin_neg, sin_PI2 in sf2ds.
      lra.
    + right.
      split; try assumption.
      destruct nod as [m Ndef].
      rewrite Ndef in sf2ds.
      assert (PI / 2 - IZR (2 * m + 1 + 1) * PI = (PI / 2 + 2 * IZR (- (m + 1)) * PI)) as id. {
        rewrite opp_IZR, plus_IZR, plus_IZR, plus_IZR, mult_IZR.
        field. }
      rewrite id, sin_period1, sin_PI2, Rmult_1_r in sf2ds.
      assumption.
  Qed.

  Lemma sf_2deriv_neg_N0 :
    forall N (Nge0 : IZR N = 0),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      my < 0.
  Proof.
    intros * N0 * d2sf.
    destruct (Req_dec mx 0) as [mx0 |mxne0].
    + symmetry in mx0.
      assert (0 <> my) as znemy; try lra.
      assert (IZR N >= 0) as Nge0; try lra.
      specialize (sf_2deriv_neg_posN_mxeq0 _ mx0 znemy Nge0 d2sf)
        as [[ev myv] | [od myv]].
      assumption.
      unfold Z.Odd in od;
        clear - od N0;
        destruct od as [b Nd];
        apply eq_IZR in N0;
        lia.      
    + assert (0 <> mx) as znemx; try lra.
      apply (sf_2deriv_neg_N0_mxne0 _ znemx N0 d2sf).
  Qed.

  Lemma sf_2deriv_pos_N0 :
    forall N (Nge0 : IZR N = 0),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      0 < my.
  Proof.
    intros * N0 * d2sf.
    destruct (Req_dec mx 0) as [mx0 |mxne0].
    + symmetry in mx0.
      assert (0 <> my) as znemy; try lra.
      assert (IZR N >= 0) as Nge0; try lra.
      specialize (sf_2deriv_pos_posN_mxeq0 _ mx0 znemy Nge0 d2sf)
        as [[ev myv] | [od myv]].
      assumption.
      unfold Z.Odd in od;
        clear - od N0;
        destruct od as [b Nd];
        apply eq_IZR in N0;
        lia.      
    + assert (0 <> mx) as znemx; try lra.
      apply (sf_2deriv_pos_N0_mxne0 _ znemx N0 d2sf).
  Qed.

  Lemma sf_2deriv_neg_Nn1 :
    forall N (Nn1 : IZR N = -1),
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      0 < my.
  Proof.
    intros * Nn1 * d2sf.
    destruct (Req_dec mx 0) as [mx0 |mxne0].
    + symmetry in mx0.
      assert (0 <> my) as znemy; try lra.
      assert (IZR N < 0) as Nge0; try lra.
      specialize (sf_2deriv_neg_negN_mxeq0 _ mx0 znemy Nge0 d2sf)
        as [[ev myv] | [od myv]].
      unfold Z.Even in ev.
        clear - ev Nn1.
        destruct ev as [b Nd].
        apply eq_IZR in Nn1.
        lia.
      assumption.
    + assert (0 <> mx) as znemx; try lra.
      apply (sf_2deriv_neg_Nn1_mxne0 _ znemx Nn1 d2sf).
  Qed.

  Lemma sf_2deriv_pos_Nn1 :
    forall N (Nn1 : IZR N = -1),
      let s := estp N in
      0 < Derive_n sf 2 s ->
      my < 0.
  Proof.
    intros * Nn1 * d2sf.
    destruct (Req_dec mx 0) as [mx0 |mxne0].
    + symmetry in mx0.
      assert (0 <> my) as znemy; try lra.
      assert (IZR N < 0) as Nge0; try lra.
      specialize (sf_2deriv_pos_negN_mxeq0 _ mx0 znemy Nge0 d2sf)
        as [[ev myv] | [od myv]].
      unfold Z.Even in ev.
        clear - ev Nn1.
        destruct ev as [b Nd].
        apply eq_IZR in Nn1.
        lia.
      assumption.
    + assert (0 <> mx) as znemx; try lra.
      apply (sf_2deriv_pos_Nn1_mxne0 _ znemx Nn1 d2sf).
  Qed.

  (* end hide *)

  Lemma sf_2deriv_N0 :
    forall N (N0 : IZR N = 0),
      let s := estp N in
      sign (Derive_n sf 2 s) = sign my.
  Proof.
    intros.
    unfold sign.
    destruct total_order_T; [destruct s0|].
    destruct total_order_T; [destruct s0|].
    + reflexivity.
    + exfalso.
      apply sf_2deriv_pos_N0 in r; try assumption.
      lra.
    + exfalso.
      apply sf_2deriv_pos_N0 in r; try assumption.
      lra.
    + symmetry in e.
      assert (IZR N = 0 \/ IZR N = -1) as nrng; try lra.
      unfold s in e.
      rewrite <- signeq0_eqv, sf_2deriv_seq0_eqv, seq0_bimpl_myeq0 in e;
        try assumption.
      destruct total_order_T; [destruct s0|]; lra.
    + apply Rgt_lt in r.
      destruct total_order_T; [destruct s0|].
    ++ exfalso.
      apply sf_2deriv_neg_N0 in r; try assumption.
      lra.
    ++ exfalso.
      apply sf_2deriv_neg_N0 in r; try assumption.
      lra.
    ++ reflexivity.
  Qed.

  Lemma sf_2deriv_Nn1 :
    forall N (Nn1 : IZR N = -1),
      let s := estp N in
      sign (Derive_n sf 2 s) = - sign my.
  Proof.
    intros.
    unfold sign.
    destruct total_order_T; [destruct s0|].
    destruct total_order_T; [destruct s0|].
    + exfalso.
      apply sf_2deriv_pos_Nn1 in r; try assumption.
      lra.
    + exfalso.
      apply sf_2deriv_pos_Nn1 in r; try assumption.
      lra.
    + lra.
    + symmetry in e.
      assert (IZR N = 0 \/ IZR N = -1) as nrng; try lra.
      unfold s in e.
      rewrite <- signeq0_eqv, sf_2deriv_seq0_eqv, seq0_bimpl_myeq0 in e;
        try assumption.
      destruct total_order_T; [destruct s0|]; lra.
    + apply Rgt_lt in r.
      destruct total_order_T; [destruct s0|].
      ++ lra.
      ++ exfalso.
         apply sf_2deriv_neg_Nn1 in r; try assumption.
         lra.
      ++ exfalso.
         apply sf_2deriv_neg_Nn1 in r; try assumption.
         lra.
  Qed.

  Lemma sf_2deriv_neg : forall N,
      let s := estp N in
      Derive_n sf 2 s < 0 ->
      ((Z.Even N /\ mx < 0 /\ my <= 0) \/ (Z.Even N /\ 0 <= mx /\ my < 0) \/
       (Z.Odd N /\ 0 < mx /\ 0 <= my) \/ (Z.Odd N /\ mx <= 0 /\ 0 < my)).
  Proof.
    intros.
    unfold estp in *.
    destruct (Rge_dec (IZR N) 0).
    destruct (Req_dec 0 mx).
    destruct (Req_dec 0 my).
    exfalso.
    apply ds.
    split; lra.
    specialize (sf_2deriv_neg_posN_mxeq0 N H0 H1 r H)
      as [[ze myn] |[zo myp]].
    right;
      left;
      split;
      [assumption|
       split;
       [right; assumption|
        assumption]].
    right;
      right;
      right;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].

    specialize (sf_2deriv_neg_posN_mxne0 N H0 r H)
      as [[c1a [c1b c1c]]
         |[[c2a [c2b c2c]]
          |[[c3a [c3b c3c]] |
            [c4a [c4b c4c]]]]].
    left; repeat (split || assumption).
    right; left; repeat (split || assumption || lra).
    right; right; left; repeat (split || assumption).
    right; right; right;  repeat (split || assumption || lra).

    apply Rnot_ge_lt in n.
    destruct (Req_dec 0 mx).
    destruct (Req_dec 0 my).
    exfalso.
    apply ds.
    split; lra.
    specialize (sf_2deriv_neg_negN_mxeq0 N H0 H1 n H)
      as [[ze myn] |[zo myp]].
    right;
      left;
      split;
      [assumption|
       split;
       [right; assumption|
        assumption]].
    right;
      right;
      right;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].

    specialize (sf_2deriv_neg_negN_mxne0 N H0 n H)
      as [[c1a [c1b c1c]]
         |[[c2a [c2b c2c]]
          |[[c3a [c3b c3c]] |
            [c4a [c4b c4c]]]]].
    left; repeat (split || assumption).
    right; left; repeat (split || assumption || lra).
    right; right; left; repeat (split || assumption).
    right; right; right;  repeat (split || assumption || lra).

  Qed.

  Lemma sf_2deriv_pos : forall N,
      let s := estp N in
      0 < Derive_n sf 2 s ->
      ((Z.Even N /\ 0 < mx /\ 0 <= my) \/ (Z.Even N /\ mx <= 0 /\ 0 < my) \/
       (Z.Odd N /\ mx < 0 /\ my <= 0) \/ (Z.Odd N /\ 0 <= mx /\ my < 0)).
  Proof.
    intros.
    unfold estp in *.
    destruct (Rge_dec (IZR N) 0).
    destruct (Req_dec 0 mx).
    destruct (Req_dec 0 my).
    exfalso.
    apply ds.
    split; lra.
    specialize (sf_2deriv_pos_posN_mxeq0 N H0 H1 r H)
      as [[ze myn] |[zo myp]].
    right;
      left;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].
    right;
      right;
      right;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].

    specialize (sf_2deriv_pos_posN_mxne0 N H0 r H)
      as [[c1a [c1b c1c]]
         |[[c2a [c2b c2c]]
          |[[c3a [c3b c3c]] |
            [c4a [c4b c4c]]]]].
    left; repeat (split || assumption).
    right; left; repeat (split || assumption || lra).
    right; right; left; repeat (split || assumption).
    right; right; right;  repeat (split || assumption || lra).

    apply Rnot_ge_lt in n.
    destruct (Req_dec 0 mx).
    destruct (Req_dec 0 my).
    exfalso.
    apply ds.
    split; lra.
    specialize (sf_2deriv_pos_negN_mxeq0 N H0 H1 n H)
      as [[ze myn] |[zo myp]].
    right;
      left;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].
    right;
      right;
      right;
      split;
      [assumption|
       split;
       [right; auto|
        assumption]].

    specialize (sf_2deriv_pos_negN_mxne0 N H0 n H)
      as [[c1a [c1b c1c]]
         |[[c2a [c2b c2c]]
          |[[c3a [c3b c3c]] |
            [c4a [c4b c4c]]]]].
    left; repeat (split || assumption).
    right; left; repeat (split || assumption || lra).
    right; right; left; repeat (split || assumption).
    right; right; right;  repeat (split || assumption || lra).

  Qed.

  Lemma cond_sf_2deriv_neg : forall N,
      let s := estp N in
      ((Z.Even N /\ my < 0) \/
       (Z.Even N /\ mx < 0 /\ my = 0 /\ IZR N <> 0) \/
       (Z.Odd N /\ 0 < my) \/
       (Z.Odd N /\ 0 < mx /\ 0 = my /\ IZR N <> -1)) ->
      Derive_n sf 2 s < 0.
  Proof.
    intros * c.
    destruct (total_order_T (Derive_n sf 2 s) 0) as [le | gt];
      [destruct le|].
    + assumption.
    + exfalso.
      destruct (Rgt_dec (IZR N) 0) as [ngt0 |nle0];
        [|destruct (Rlt_dec (IZR N) (-1)) as [nltn1 |ngen1]].
      ++ assert (IZR N > 0 \/ IZR N < -1 \/
                 (s <> 0 /\ (IZR N = 0 \/ IZR N = -1))) as sc; try lra.
         unfold s in *.
         apply (sf_2deriv_ne0 N); try assumption.
         rewrite signeq0_eqv.
         assumption.
      ++ assert (IZR N > 0 \/ IZR N < -1 \/
                 (s <> 0 /\ (IZR N = 0 \/ IZR N = -1))) as sc; try lra.
         unfold s in *.
         apply (sf_2deriv_ne0 N); try assumption.
         rewrite signeq0_eqv.
         assumption.
      ++ apply Rnot_gt_le in nle0.
         apply Rnot_lt_le in ngen1.
         assert (IZR N = 0 \/ IZR N = -1) as np. {
           apply le_IZR in nle0.
           apply le_IZR in ngen1.
           assert (N = 0 \/ N = -1)%Z as nv; try lia.
           destruct nv as [n0 | nn1].
           left; subst; reflexivity.
           right; subst; reflexivity. }
         unfold s in e.
         generalize e; intro f;
           rewrite <- signeq0_eqv in f.
         rewrite <- signeq0_eqv, sf_2deriv_seq0_eqv, seq0_bimpl_myeq0 in e;
           try assumption.
         clear nle0 ngen1.
         destruct np as [N0 |Nn1].
         +++ assert (Z.Even N) as zen. {
               unfold Z.Even.
               exists 0%Z.
               apply eq_IZR in N0.
               rewrite N0.
               lia. }
             destruct c as [[ev1 myc] |[ev2 |[od1 |[od2 [mxd [myd IZRd]]]]]]; try lra.
             destruct od2 as [b2 Nd2].
             destruct zen as [b1 Nd1].
             lia.
         +++ assert (Z.Odd N) as zen. {
               unfold Z.Odd.
               exists (-1)%Z.
               apply eq_IZR in Nn1.
               rewrite Nn1.
               lia. }
             destruct c as [ev1 |[[ev2 [mxd [my0 Nd]]] |[od1 |od2]]]; try lra.
             destruct ev2 as [b2 Nd2].
             destruct zen as [b1 Nd1].
             lia.
    + exfalso.
      apply Rgt_lt in gt.
      apply sf_2deriv_pos in gt.
      destruct c as [[ze1 myd] |
                     [[ze2 [mxd [myd Nd]]] |
                      [[zo1  myd]| [zo2 rst2]]]];
        destruct gt as [[ze3 rst]|
                        [[ze4 rst] |
                         [[zo3 rst] |[zo4 rst]]]]; try lra.
      destruct zo3 as [b2 Nd2];
        destruct ze1 as [b1 Nd1];
        lia.
      destruct zo4 as [b2 Nd2];
        destruct ze1 as [b1 Nd1];
        lia.
      destruct zo3 as [b2 Nd2];
        destruct ze2 as [b1 Nd1];
        lia.
      destruct zo1 as [b2 Nd2];
        destruct ze3 as [b1 Nd1];
        lia.
      destruct zo1 as [b2 Nd2];
        destruct ze4 as [b1 Nd1];
        lia.
      destruct zo2 as [b2 Nd2];
        destruct ze3 as [b1 Nd1];
        lia.
  Qed.

  Lemma cond_sf_2deriv_pos : forall N,
      let s := estp N in
      ((Z.Even N /\0 < my) \/
       (Z.Even N /\ 0 < mx /\ 0 = my /\ IZR N <> 0) \/
       (Z.Odd N /\ my < 0) \/
       (Z.Odd N /\ mx < 0 /\ my = 0 /\ IZR N <> -1)) ->
      0 < Derive_n sf 2 s.
  Proof.
    intros * c.
    destruct (total_order_T (Derive_n sf 2 s) 0) as [le | gt];
      [destruct le|].
    + exfalso.
      apply sf_2deriv_neg in r.
      destruct c as [[ze1 myd] |
                     [[ze2 [mxd [myd Nd]]] |
                      [[zo1  myd]| [zo2 rst2]]]];
        destruct r as [[ze3 rst]|
                        [[ze4 rst] |
                         [[zo3 rst] |[zo4 rst]]]]; try lra.
      destruct zo3 as [b2 Nd2];
        destruct ze1 as [b1 Nd1];
        lia.
      destruct zo4 as [b2 Nd2];
        destruct ze1 as [b1 Nd1];
        lia.
      destruct zo3 as [b2 Nd2];
        destruct ze2 as [b1 Nd1];
        lia.
      destruct zo1 as [b2 Nd2];
        destruct ze3 as [b1 Nd1];
        lia.
      destruct zo1 as [b2 Nd2];
        destruct ze4 as [b1 Nd1];
        lia.
      destruct zo2 as [b2 Nd2];
        destruct ze3 as [b1 Nd1];
        lia.
    + exfalso.
      destruct (Rgt_dec (IZR N) 0) as [ngt0 |nle0];
        [|destruct (Rlt_dec (IZR N) (-1)) as [nltn1 |ngen1]].
      ++ assert (IZR N > 0 \/ IZR N < -1 \/
                 (s <> 0 /\ (IZR N = 0 \/ IZR N = -1))) as sc; try lra.
         unfold s in *.
         apply (sf_2deriv_ne0 N); try assumption.
         rewrite signeq0_eqv.
         assumption.
      ++ assert (IZR N > 0 \/ IZR N < -1 \/
                 (s <> 0 /\ (IZR N = 0 \/ IZR N = -1))) as sc; try lra.
         unfold s in *.
         apply (sf_2deriv_ne0 N); try assumption.
         rewrite signeq0_eqv.
         assumption.
      ++ apply Rnot_gt_le in nle0.
         apply Rnot_lt_le in ngen1.
         assert (IZR N = 0 \/ IZR N = -1) as np. {
           apply le_IZR in nle0.
           apply le_IZR in ngen1.
           assert (N = 0 \/ N = -1)%Z as nv; try lia.
           destruct nv as [n0 | nn1].
           left; subst; reflexivity.
           right; subst; reflexivity. }
         unfold s in e.
         generalize e; intro f;
           rewrite <- signeq0_eqv in f.
         rewrite <- signeq0_eqv, sf_2deriv_seq0_eqv, seq0_bimpl_myeq0 in e;
           try assumption.
         clear nle0 ngen1.
         destruct np as [N0 |Nn1].
         +++ assert (Z.Even N) as zen. {
               unfold Z.Even.
               exists 0%Z.
               apply eq_IZR in N0.
               rewrite N0.
               lia. }
             destruct c as [[ev1 myc] |[ev2 |[od1 |[od2 [mxd [myd IZRd]]]]]]; try lra.
             destruct od2 as [b2 Nd2].
             destruct zen as [b1 Nd1].
             lia.
         +++ assert (Z.Odd N) as zen. {
               unfold Z.Odd.
               exists (-1)%Z.
               apply eq_IZR in Nn1.
               rewrite Nn1.
               lia. }
             destruct c as [ev1 |[[ev2 [mxd [my0 Nd]]] |[od1 |od2]]]; try lra.
             destruct ev2 as [b2 Nd2].
             destruct zen as [b1 Nd1].
             lia.
    + assumption.
  Qed.

  
(* begin hide *)
  Lemma interv_allpos_allneg : forall sn s0 f,
      (forall s : R, sn <= s <= s0 -> continuity_pt f s) ->
      sn < s0 -> 
      f sn = 0 ->
      f s0 = 0 ->
      (forall s : R, sn < s < s0 -> f s <> 0) -> 
      (forall s : R, sn < s < s0 -> 0 < f s) \/
      (forall s : R, sn < s < s0 -> f s < 0).
  Proof.
    intros *.
    intros cnt snlts0 fsneq0 fs0eq0 fmne0.
    set (q := (sn + s0)/2).
    assert (q < s0) as ub; try (unfold q; lra).
    assert (sn < q) as lb; try (unfold q; lra).
    destruct (total_order_T (f q) 0); [destruct s|].
    + right.
      intros s sbnd.
      destruct (Rlt_dec (f s) 0); try assumption.
      apply Rnot_lt_le in n.
      destruct n as [fslt0 |fseq0];
        [ | specialize (fmne0 _ sbnd); lra].
      destruct (Rlt_dec q s) as [qlts |qges].
      ++ exfalso.
         assert (forall t : R, q <= t <= s ->
                               continuity_pt f t) as qscnt. {
           intros t [tlb tub].
           apply cnt.
           split; lra. }

         specialize (IVT_interv _ _ _ qscnt qlts r fslt0)
           as [z [[zlb zub] fzeq0]].
         assert (sn < z < s0) as znrng;
           [split; lra|].
         specialize (fmne0 _ znrng).
         apply fmne0.
         assumption.
      ++ exfalso.
         apply Rnot_lt_le in qges.
         destruct qges as [sltq |seqq].
         set (g := opp_fct f).
         assert (g s < 0) as gslt0;
           [unfold g, opp_fct; lra|].
         assert (0 < g q) as gqgt0;
           [unfold g, opp_fct; lra|].

         assert (forall t : R, s <= t <= q ->
                               continuity_pt g t) as qscnt. {
           intros t [tlb tub].
           unfold g.
           apply continuity_pt_opp.
           apply cnt.
           split; lra. }

         specialize (IVT_interv _ _ _ qscnt sltq gslt0 gqgt0)
           as [z [[zlb zub] fzeq0]].
         assert (sn < z < s0) as znrng;
           [split; lra|].
         specialize (fmne0 _ znrng).
         apply fmne0.
         apply (Rmult_eq_reg_l (-1)); try lra.
         setl (- f z).
         setr 0.
         assumption.

         rewrite seqq in fslt0.
         lra.
         
    + exfalso.
      apply (fmne0 q).
      split; assumption.
      assumption.

    + left.
      apply Rgt_lt in r.
      intros s sbnd.
      destruct (Rlt_dec 0 (f s)); try assumption.
      apply Rnot_lt_le in n.
      destruct n as [fslt0 |fseq0];
        [ | specialize (fmne0 _ sbnd); lra].
      destruct (Rlt_dec s q) as [qlts |qges].
      ++ exfalso.
         assert (forall t : R, s <= t <= q ->
                               continuity_pt f t) as qscnt. {
           intros t [tlb tub].
           apply cnt.
           split; lra. }

         specialize (IVT_interv _ _ _ qscnt qlts fslt0 r)
           as [z [[zlb zub] fzeq0]].
         assert (sn < z < s0) as znrng;
           [split; lra|].
         specialize (fmne0 _ znrng).
         apply fmne0.
         assumption.
      ++ exfalso.
         apply Rnot_lt_le in qges.
         destruct qges as [sltq |seqq].
         set (g := opp_fct f).
         assert (g q < 0) as gslt0;
           [unfold g, opp_fct; lra|].
         assert (0 < g s) as gqgt0;
           [unfold g, opp_fct; lra|].

         assert (forall t : R, q <= t <= s ->
                               continuity_pt g t) as qscnt. {
           intros t [tlb tub].
           unfold g.
           apply continuity_pt_opp.
           apply cnt.
           split; lra. }

         specialize (IVT_interv _ _ _ qscnt sltq gslt0 gqgt0)
           as [z [[zlb zub] fzeq0]].
         assert (sn < z < s0) as znrng;
           [split; lra|].
         specialize (fmne0 _ znrng).
         apply fmne0.
         apply (Rmult_eq_reg_l (-1)); try lra.
         setl (- f z).
         setr 0.
         assumption.

         rewrite seqq in r.
         lra.
  Qed.

  (* Coquilecot also provides IVT_Rbar_incr, IVT_Rbar_decr, IVT_gen *)
  
  Lemma closest_N_LHS1 : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      ~(IZR N = 1 /\ my = 0) -> 0 < Derive_n sf 2 s0 -> 
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sb < sf sa.
  Proof.
    intros *.
    intros notN1my0 sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N-1)%Z) as sfdn;
      simpl in sfdn;
      change (Derive sf sn = 0) in sfdn.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N-1)%Z) as nzdn0;
      simpl in nzdn0.
    assert (N - 1 + 1 = N)%Z as id;
      [lia|rewrite id in nzdn0].
    change (forall s, sn < s < s0 -> Derive sf s <> 0) in nzdn0.
    
    assert (sn < s0) as ord0. {
      
      assert (~ (IZR (N-1)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Nm1eqn1 myeq0].
        destruct (Req_dec (IZR (N-1)%Z) 1) as [Nm1eq1 |Nm1ne1];
          try lra.
        assert (N = 0)%Z as neq0;
          [apply eq_IZR in Nm1eqn1; lia| apply eq_IZR in Nm1eqn1].
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        rewrite <- neq0 in s1s2d at 2.
        rewrite <- Nm1eqn1 in s1s2d.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in s0eq0; try (apply IZR_eq in neq0; lra).
        rewrite signeq0_eqv in s0eq0.
        change (Derive_n sf 2 s0 = 0) in s0eq0.
        lra. }
      unfold sn, s0.
      specialize (spiral_N_order _ cnd0) as ord.
      simpl in ord.
      rewrite id in ord.
      assumption. }
        
    
    assert (Derive_n sf 2 sn < 0) as sfsn. {
      rewrite <- signeqm1_eqv.
      unfold sn.
      rewrite sf_2deriv_sign.
      rewrite id.
      apply (Rmult_eq_reg_r (-1)); try lra.
      setl (sign (Derive_n sf 2 (estp N))).
      setr (1).
      rewrite signeq1_eqv; assumption.
      split; intros [eq arg]; try lra.
      change (sn = 0) in arg.
      rewrite arg in ord0.
      unfold sn in arg.
      rewrite (seq0_bimpl_myeq0 (N-1)) in arg;
        [|left; assumption].
      apply notN1my0.
      split; try assumption.
      apply eq_IZR in eq.
      apply IZR_eq.
      lia.
      rewrite id in arg.
      change (s0 = 0) in arg.
      rewrite arg in ord0.
      unfold s0 in arg.
      rewrite <- sf_2deriv_seq0_eqv in arg;
        [|right;
          apply eq_IZR in eq;
          apply IZR_eq;
          lia].
      rewrite signeq0_eqv in arg.
      unfold s0 in sf2dlt0.
      clear - sf2dlt0 arg.
      lra. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (0 < Derive (Derive sf) s0) in sf2dlt0.
    change (Derive (Derive sf) sn < 0) in sfsn.

    
    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, sn <= s <= s0 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s1) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, sn <= s <= s0 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s1) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdn sfdz nzdn0) as apan.

    assert (exists r, sn < r < s0 /\ Derive sf r < 0) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal ((h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmax ((sn+s0)/2) (s0 - (d/2)))).
      assert (sn < q < s0) as [ql qu]. {
        intros.
        unfold q, Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, q < r < s0 -> 0 < h r) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, q < t < s0 -> 0 < derive_pt g t (dervg t)) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (q < s0) as qlts0. lra.
      assert (q <= q <= s0) as qinr. lra.
      assert (q <= s0 <= s0) as s0inr. lra.
      specialize (derive_increasing_interv
                    _ _ _ dervg qlts0 pd _ _  qinr s0inr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (g r < 0) in rpos.

    destruct apan as [ap |an];
      [exfalso;
        specialize (ap _ rbnd);
        lra |].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption.
    }
    
    destruct sbub as [su |se];
      [| rewrite se in *];
    eapply (derive_decreasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply an;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.


  Lemma closest_N_LHS2 : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      (IZR N = 1 /\ my = 0) -> 0 < Derive_n sf 2 s0 -> 
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sb < sf sa.
  Proof.
    intros * [N1 my0] sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N-1)%Z) as sfdn;
      simpl in sfdn;
      change (Derive sf sn = 0) in sfdn.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N-1)%Z) as nzdn0;
      simpl in nzdn0.
    assert (N - 1 + 1 = N)%Z as id;
      [lia|rewrite id in nzdn0].
    change (forall s, sn < s < s0 -> Derive sf s <> 0) in nzdn0.
    
    assert (sn < s0) as ord0. {
      
      assert (~ (IZR (N-1)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Nm1eqn1 myeq0].
        destruct (Req_dec (IZR (N-1)%Z) 1) as [Nm1eq1 |Nm1ne1];
          try lra.
        assert (N = 0)%Z as neq0;
          [apply eq_IZR in Nm1eqn1; lia| apply eq_IZR in Nm1eqn1].
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        rewrite <- neq0 in s1s2d at 2.
        rewrite <- Nm1eqn1 in s1s2d.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in s0eq0; try (apply IZR_eq in neq0; lra). }
      unfold sn, s0.
      specialize (spiral_N_order _ cnd0) as ord.
      simpl in ord.
      rewrite id in ord.
      assumption. }

    assert (Derive_n sf 2 sn = 0) as sfsn. {
      assert (N - 1 = 0)%Z as Nm1eq0; try (apply eq_IZR in N1; lia).
      rewrite <- (seq0_bimpl_myeq0 (N-1)%Z) in my0;
        [|left; rewrite minus_IZR; lra].
      rewrite <- sf_2deriv_seq0_eqv in my0;
        [|left; rewrite minus_IZR; lra].
      rewrite signeq0_eqv in my0.
      change (Derive_n sf 2 sn = 0) in my0.
      assumption. }

    
    unfold Derive_n in sf2dlt0, sfsn.
    change (0 < Derive (Derive sf) s0) in sf2dlt0.
    change (Derive (Derive sf) sn = 0) in sfsn.
    
    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, sn <= s <= s0 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s1) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, sn <= s <= s0 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s1) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdn sfdz nzdn0) as apan.

    assert (exists r, sn < r < s0 /\ Derive sf r < 0) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal ((h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmax ((sn+s0)/2) (s0 - (d/2)))).
      assert (sn < q < s0) as [ql qu]. {
        intros.
        unfold q, Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, q < r < s0 -> 0 < h r) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, q < t < s0 -> 0 < derive_pt g t (dervg t)) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (q < s0) as qlts0. lra.
      assert (q <= q <= s0) as qinr. lra.
      assert (q <= s0 <= s0) as s0inr. lra.
      specialize (derive_increasing_interv
                    _ _ _ dervg qlts0 pd _ _  qinr s0inr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (g r < 0) in rpos.

    destruct apan as [ap |an];
      [exfalso;
        specialize (ap _ rbnd);
        lra |].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption.
    }

    destruct sbub as [su |se];
      [| rewrite se in *];
    eapply (derive_decreasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply an;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.
  (* end hide *)
  Lemma closest_N_LHS : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      0 < Derive_n sf 2 s0 ->
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sb < sf sa.
  Proof.
    intros.
    assert (~(IZR N = 1 /\ my = 0)\/(IZR N = 1 /\ my = 0))
      as [ncnd |cnd]. {
      destruct (Req_dec (IZR N) 1).
      destruct (Req_dec my 0).
      right.
      split; assumption.
      left; lra.
      left; lra. }
    eapply closest_N_LHS1; eassumption.
    eapply closest_N_LHS2; eassumption.
  Qed.
    
  (* begin hide *)
  Lemma closest_N_RHS1 : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      ~(IZR N = -2 /\ my = 0) -> 0 < Derive_n sf 2 s0 -> 
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sa < sf sb.
  Proof.
    intros *.
    intros myne0 sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N+1)%Z) as sfdo;
      simpl in sfdo;
      change (Derive sf s1 = 0) in sfdo.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N)%Z) as nzdn0;
      simpl in nzdn0;
      change (forall s, s0 < s < s1 -> Derive sf s <> 0) in nzdn0.

    assert (s0 < s1) as ord0. {
      
      assert (~ (IZR (N)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Neqn1 myeq0].
        destruct (Req_dec (IZR (N+1)%Z) 0) as [Nm1eq1 |Nm1ne1];
          try lra.
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        apply eq_IZR in Neqn1.
        rewrite <- Neqn1 in s1s2d.
        apply eq_IZR in Nm1eq1.
        rewrite <- Nm1eq1 in s1s2d at 2.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in sneq0;
          [| right; apply IZR_eq; assumption].
        rewrite signeq0_eqv in sneq0.
        change (Derive_n sf 2 s0 = 0) in sneq0.
        lra.
        apply Nm1ne1.
        rewrite plus_IZR.
        lra. }
      unfold s0, s1.
      apply (spiral_N_order _ cnd0).  }

    assert (Derive_n sf 2 s1 < 0) as sfsn. {
      rewrite <- signeqm1_eqv.
      unfold s1.
      rewrite <- (Ropp_involutive (sign (Derive_n sf 2 (estp (N + 1))))).
      rewrite <- sf_2deriv_sign.
      apply (Rmult_eq_reg_r (-1)); try lra.
      setl (sign (Derive_n sf 2 (estp N))).
      setr (1).
      rewrite signeq1_eqv; assumption.
      split; intros [eq arg]; try lra.
      change (s0 = 0) in arg.
      rewrite arg in ord0.
      unfold s0 in arg.
      rewrite <- sf_2deriv_seq0_eqv in arg;
        [|left;
          apply eq_IZR in eq;
          apply IZR_eq;
          lia].
      rewrite signeq0_eqv in arg.
      unfold s0 in sf2dlt0.
      clear - sf2dlt0 arg.
      lra.

      change (s1 = 0) in arg.
      rewrite arg in ord0.
      unfold s1 in arg.
      rewrite (seq0_bimpl_myeq0 (N+1)%Z) in arg;
        [|right; rewrite plus_IZR; lra].
      apply myne0.
      split; try assumption. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (0 < Derive (Derive sf) s0) in sf2dlt0.
    change (Derive (Derive sf) s1 < 0) in sfsn.

    
    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, s0 <= s <= s1 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s2) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, s0 <= s <= s1 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s2) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdz sfdo nzdn0) as apan.

    assert (exists r, s0 < r < s1 /\ 0 < Derive sf r) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal ((h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmin ((s0+s1)/2) (s0 + (d/2)))).
      assert (s0 < q < s1) as [ql qu]. {
        intros.
        unfold q, Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; try lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, s0 < r < q -> 0 < h r) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, s0 < t < q -> 0 < derive_pt g t (dervg t)) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (s0 < q) as qlts0. lra.
      assert (s0 <= s0 <= q) as s0inr. lra.
      assert (s0 <= q <= q) as qinr. lra.
      specialize (derive_increasing_interv
                    _ _ _ dervg qlts0 pd _ _ s0inr qinr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (0 < g r) in rpos.

    destruct apan as [ap |an];
      [|exfalso;
        specialize (an _ rbnd);
        lra].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption. }
    
    destruct salb as [su |se];
      [| rewrite se in *];
    eapply (derive_increasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply ap;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.

  Lemma closest_N_RHS2 : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      (IZR N = -2 /\ my = 0) -> 0 < Derive_n sf 2 s0 -> 
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sa < sf sb.
  Proof.
    intros * [N1 my0] sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N+1)%Z) as sfdo;
      simpl in sfdo;
      change (Derive sf s1 = 0) in sfdo.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N)%Z) as nzdn0;
      simpl in nzdn0;
      change (forall s, s0 < s < s1 -> Derive sf s <> 0) in nzdn0.

    assert (s0 < s1) as ord0. {
      
      assert (~ (IZR (N)%Z = -1 /\ my = 0)) as cnd0. {
        lra. }
      unfold s0, s1.
      apply (spiral_N_order _ cnd0).  }

    assert (Derive_n sf 2 s1 = 0) as sfsn. {
      assert (N + 1 = -1)%Z as Nm1eq0; try (apply eq_IZR in N1; lia).
      rewrite <- (seq0_bimpl_myeq0 (N+1)%Z) in my0;
        [|right; apply IZR_eq; assumption].
      rewrite <- sf_2deriv_seq0_eqv in my0;
        [|right; apply IZR_eq; assumption].
      rewrite signeq0_eqv in my0.
      change (Derive_n sf 2 s1 = 0) in my0.
      assumption. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (0 < Derive (Derive sf) s0) in sf2dlt0.
    change (Derive (Derive sf) s1 = 0) in sfsn.

    
    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, s0 <= s <= s1 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s2) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, s0 <= s <= s1 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s2) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdz sfdo nzdn0) as apan.

    assert (exists r, s0 < r < s1 /\ 0 < Derive sf r) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal ((h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmin ((s0+s1)/2) (s0 + (d/2)))).
      assert (s0 < q < s1) as [ql qu]. {
        intros.
        unfold q, Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; try lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, s0 < r < q -> 0 < h r) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, s0 < t < q -> 0 < derive_pt g t (dervg t)) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (s0 < q) as qlts0. lra.
      assert (s0 <= s0 <= q) as s0inr. lra.
      assert (s0 <= q <= q) as qinr. lra.
      specialize (derive_increasing_interv
                    _ _ _ dervg qlts0 pd _ _ s0inr qinr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (0 < g r) in rpos.

    destruct apan as [ap |an];
      [|exfalso;
        specialize (an _ rbnd);
        lra].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption. }

    destruct salb as [su |se];
      [| rewrite se in *];
    eapply (derive_increasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply ap;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.

  (* end hide *)
  Lemma closest_N_RHS : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      0 < Derive_n sf 2 s0 ->
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sa < sf sb.
  Proof.
    intros.
    assert (~(IZR N = -2 /\ my = 0)\/(IZR N = -2 /\ my = 0))
      as [ncnd |cnd]. {
      destruct (Req_dec (IZR N) (-2)).
      destruct (Req_dec my 0).
      right.
      split; assumption.
      left; lra.
      left; lra. }
    eapply closest_N_RHS1; eassumption.
    eapply closest_N_RHS2; eassumption.
  Qed.
  
  Lemma closest_N : forall s N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      0 < Derive_n sf 2 s0 ->
      sn <= s <= s1 ->
      sf s0 <= sf s.
  Proof.
    intros.
    destruct (total_order_T s s0) as [sles0 |sgts0];
      [destruct sles0 as [slts0 | seqs0]|].
    left.
    eapply (closest_N_LHS _ _ _ H);
      [destruct H0; assumption|
       assumption|
       right; reflexivity].
    right; rewrite seqs0; reflexivity.
    apply Rgt_lt in sgts0.
    left.
    eapply (closest_N_RHS _ _ _ H);
      [right; reflexivity |
       assumption |
       destruct H0; assumption ].
  Qed.

  (* begin hide *)

  Lemma furthest_N_LHS1 : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      ~(IZR N = 1 /\ my = 0) -> Derive_n sf 2 s0 < 0 -> 
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sa < sf sb.
  Proof.
    intros *.
    intros notN1my0 sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N-1)%Z) as sfdn;
      simpl in sfdn;
      change (Derive sf sn = 0) in sfdn.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N-1)%Z) as nzdn0;
      simpl in nzdn0.
    assert (N - 1 + 1 = N)%Z as id;
      [lia|rewrite id in nzdn0].
    change (forall s, sn < s < s0 -> Derive sf s <> 0) in nzdn0.
    
    assert (sn < s0) as ord0. {
      
      assert (~ (IZR (N-1)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Nm1eqn1 myeq0].
        destruct (Req_dec (IZR (N-1)%Z) 1) as [Nm1eq1 |Nm1ne1];
          try lra.
        assert (N = 0)%Z as neq0;
          [apply eq_IZR in Nm1eqn1; lia| apply eq_IZR in Nm1eqn1].
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        rewrite <- neq0 in s1s2d at 2.
        rewrite <- Nm1eqn1 in s1s2d.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in s0eq0; try (apply IZR_eq in neq0; lra).
        rewrite signeq0_eqv in s0eq0.
        change (Derive_n sf 2 s0 = 0) in s0eq0.
        lra. }
      unfold sn, s0.
      specialize (spiral_N_order _ cnd0) as ord.
      simpl in ord.
      rewrite id in ord.
      assumption. }
        
    
    assert (0 < Derive_n sf 2 sn) as sfsn. {
      rewrite <- signeq1_eqv.
      unfold sn.
      rewrite sf_2deriv_sign.
      rewrite id.
      apply (Rmult_eq_reg_r (-1)); try lra.
      setl (sign (Derive_n sf 2 (estp N))).
      setr (-1).
      rewrite signeqm1_eqv; assumption.
      split; intros [eq arg]; try lra.
      change (sn = 0) in arg.
      rewrite arg in ord0.
      unfold sn in arg.
      rewrite (seq0_bimpl_myeq0 (N-1)) in arg;
        [|left; assumption].
      apply notN1my0.
      split; try assumption.
      apply eq_IZR in eq.
      apply IZR_eq.
      lia.
      rewrite id in arg.
      change (s0 = 0) in arg.
      rewrite arg in ord0.
      unfold s0 in arg.
      rewrite <- sf_2deriv_seq0_eqv in arg;
        [|right;
          apply eq_IZR in eq;
          apply IZR_eq;
          lia].
      rewrite signeq0_eqv in arg.
      unfold s0 in sf2dlt0.
      clear - sf2dlt0 arg.
      lra. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (Derive (Derive sf) s0 < 0) in sf2dlt0.
    change (0 < Derive (Derive sf) sn) in sfsn.

    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, sn <= s <= s0 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s1) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, sn <= s <= s0 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s1) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdn sfdz nzdn0) as apan.

    assert (exists r, sn < r < s0 /\ 0 < Derive sf r) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < - (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal (- (h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmax ((sn+s0)/2) (s0 - (d/2)))).
      assert (sn < q < s0) as [ql qu]. {
        intros.
        unfold q, Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, q < r < s0 -> h r < 0) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, q < t < s0 -> derive_pt g t (dervg t) < 0)
        as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (q < s0) as qlts0. lra.
      assert (q <= q <= s0) as qinr. lra.
      assert (q <= s0 <= s0) as s0inr. lra.
      specialize (derive_decreasing_interv
                    _ _ _ dervg qlts0 pd _ _  qinr s0inr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (0 < g r) in rpos.

    destruct apan as [ap |an];
      [| exfalso;
        specialize (an _ rbnd);
        lra ].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption.
    }
    
    destruct sbub as [su |se];
      [| rewrite se in *];
    eapply (derive_increasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply ap;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.

  Lemma furthest_N_LHS2 : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      (IZR N = 1 /\ my = 0) -> Derive_n sf 2 s0 < 0 -> 
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sa < sf sb.
  Proof.
    intros * [N1 my0] sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N-1)%Z) as sfdn;
      simpl in sfdn;
      change (Derive sf sn = 0) in sfdn.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N-1)%Z) as nzdn0;
      simpl in nzdn0.
    assert (N - 1 + 1 = N)%Z as id;
      [lia|rewrite id in nzdn0].
    change (forall s, sn < s < s0 -> Derive sf s <> 0) in nzdn0.
    
    assert (sn < s0) as ord0. {
      
      assert (~ (IZR (N-1)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Nm1eqn1 myeq0].
        destruct (Req_dec (IZR (N-1)%Z) 1) as [Nm1eq1 |Nm1ne1];
          try lra.
        assert (N = 0)%Z as neq0;
          [apply eq_IZR in Nm1eqn1; lia| apply eq_IZR in Nm1eqn1].
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        rewrite <- neq0 in s1s2d at 2.
        rewrite <- Nm1eqn1 in s1s2d.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in s0eq0; try (apply IZR_eq in neq0; lra). }
      unfold sn, s0.
      specialize (spiral_N_order _ cnd0) as ord.
      simpl in ord.
      rewrite id in ord.
      assumption. }

    assert (Derive_n sf 2 sn = 0) as sfsn. {
      assert (N - 1 = 0)%Z as Nm1eq0; try (apply eq_IZR in N1; lia).
      rewrite <- (seq0_bimpl_myeq0 (N-1)%Z) in my0;
        [|left; rewrite minus_IZR; lra].
      rewrite <- sf_2deriv_seq0_eqv in my0;
        [|left; rewrite minus_IZR; lra].
      rewrite signeq0_eqv in my0.
      change (Derive_n sf 2 sn = 0) in my0.
      assumption. }

    
    unfold Derive_n in sf2dlt0, sfsn.
    change (Derive (Derive sf) s0 < 0) in sf2dlt0.
    change (Derive (Derive sf) sn = 0) in sfsn.
    
    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, sn <= s <= s0 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s1) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, sn <= s <= s0 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, sn <= s <= s0 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s1) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdn sfdz nzdn0) as apan.

    assert (exists r, sn < r < s0 /\ 0 < Derive sf r) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < - (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal (- (h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmax ((sn+s0)/2) (s0 - (d/2)))).
      assert (sn < q < s0) as [ql qu]. {
        intros.
        unfold q, Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmax.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, q < r < s0 -> h r < 0) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, q < t < s0 -> derive_pt g t (dervg t) < 0) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (q < s0) as qlts0. lra.
      assert (q <= q <= s0) as qinr. lra.
      assert (q <= s0 <= s0) as s0inr. lra.
      specialize (derive_decreasing_interv
                    _ _ _ dervg qlts0 pd _ _  qinr s0inr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (0 < g r) in rpos.

    destruct apan as [ap |an];
      [| exfalso;
        specialize (an _ rbnd);
        lra ].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption.
    }

    destruct sbub as [su |se];
      [| rewrite se in *];
    eapply (derive_increasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply ap;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.
(* end hide *)

  Lemma furthest_N_LHS : forall sa sb N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      Derive_n sf 2 s0 < 0 ->
      sn <= sa -> sa < sb -> sb <= s0 ->
      sf sa < sf sb.
  Proof.
    intros.
    assert (~(IZR N = 1 /\ my = 0)\/(IZR N = 1 /\ my = 0))
      as [ncnd |cnd]. {
      destruct (Req_dec (IZR N) 1).
      destruct (Req_dec my 0).
      right.
      split; assumption.
      left; lra.
      left; lra. }
    eapply furthest_N_LHS1; eassumption.
    eapply furthest_N_LHS2; eassumption.
  Qed.

  (* begin hide *)
  Lemma furthest_N_RHS1 : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      ~(IZR N = -2 /\ my = 0) -> Derive_n sf 2 s0 < 0-> 
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sb < sf sa.
  Proof.
    intros *.
    intros myne0 sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N+1)%Z) as sfdo;
      simpl in sfdo;
      change (Derive sf s1 = 0) in sfdo.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N)%Z) as nzdn0;
      simpl in nzdn0;
      change (forall s, s0 < s < s1 -> Derive sf s <> 0) in nzdn0.

    assert (s0 < s1) as ord0. {
      
      assert (~ (IZR (N)%Z = -1 /\ my = 0)) as cnd0. {
        intros [Neqn1 myeq0].
        destruct (Req_dec (IZR (N+1)%Z) 0) as [Nm1eq1 |Nm1ne1];
          try lra.
        symmetry in myeq0.
        specialize (spiral_midarm_N_order myeq0) as s1s2d.
        simpl in s1s2d.
        apply eq_IZR in Neqn1.
        rewrite <- Neqn1 in s1s2d.
        apply eq_IZR in Nm1eq1.
        rewrite <- Nm1eq1 in s1s2d at 2.
        destruct s1s2d as [sneq0 s0eq0].
        rewrite <- sf_2deriv_seq0_eqv in sneq0;
          [| right; apply IZR_eq; assumption].
        rewrite signeq0_eqv in sneq0.
        change (Derive_n sf 2 s0 = 0) in sneq0.
        lra.
        apply Nm1ne1.
        rewrite plus_IZR.
        lra. }
      unfold s0, s1.
      apply (spiral_N_order _ cnd0).  }

    assert (0 < Derive_n sf 2 s1) as sfsn. {
      rewrite <- signeq1_eqv.
      unfold s1.
      rewrite <- (Ropp_involutive (sign (Derive_n sf 2 (estp (N + 1))))).
      rewrite <- sf_2deriv_sign.
      apply (Rmult_eq_reg_r (-1)); try lra.
      setl (sign (Derive_n sf 2 (estp N))).
      setr (-1).
      rewrite signeqm1_eqv; assumption.
      split; intros [eq arg]; try lra.
      change (s0 = 0) in arg.
      rewrite arg in ord0.
      unfold s0 in arg.
      rewrite <- sf_2deriv_seq0_eqv in arg;
        [|left;
          apply eq_IZR in eq;
          apply IZR_eq;
          lia].
      rewrite signeq0_eqv in arg.
      unfold s0 in sf2dlt0.
      clear - sf2dlt0 arg.
      lra.

      change (s1 = 0) in arg.
      rewrite arg in ord0.
      unfold s1 in arg.
      rewrite (seq0_bimpl_myeq0 (N+1)%Z) in arg;
        [|right; rewrite plus_IZR; lra].
      apply myne0.
      split; try assumption. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (Derive (Derive sf) s0 < 0) in sf2dlt0.
    change (0 < Derive (Derive sf) s1) in sfsn.

    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, s0 <= s <= s1 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s2) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, s0 <= s <= s1 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s2) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdz sfdo nzdn0) as apan.

    assert (exists r, s0 < r < s1 /\ Derive sf r < 0) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < - (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal (- (h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmin ((s0+s1)/2) (s0 + (d/2)))).
      assert (s0 < q < s1) as [ql qu]. {
        intros.
        unfold q, Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; try lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, s0 < r < q -> h r < 0) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, s0 < t < q -> derive_pt g t (dervg t) < 0) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (s0 < q) as qlts0. lra.
      assert (s0 <= s0 <= q) as s0inr. lra.
      assert (s0 <= q <= q) as qinr. lra.
      specialize (derive_decreasing_interv
                    _ _ _ dervg qlts0 pd _ _ s0inr qinr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (g r < 0) in rpos.

    destruct apan as [ap |an];
      [exfalso;
        specialize (ap _ rbnd);
        lra|].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption. }
    
    destruct salb as [su |se];
      [| rewrite se in *];
    eapply (derive_decreasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply an;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.

  Lemma furthest_N_RHS2 : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      (IZR N = -2 /\ my = 0) -> Derive_n sf 2 s0 < 0-> 
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sb < sf sa.
  Proof.
    intros * [N1 my0] sf2dlt0 salb saltsb sbub.

    specialize (sf_deriv_0 (N+1)%Z) as sfdo;
      simpl in sfdo;
      change (Derive sf s1 = 0) in sfdo.

    specialize (sf_deriv_0 (N)%Z) as sfdz;
      simpl in sfdz;
      change (Derive sf s0 = 0) in sfdz.

    specialize (sf_deriv_ne0 (N)%Z) as nzdn0;
      simpl in nzdn0;
      change (forall s, s0 < s < s1 -> Derive sf s <> 0) in nzdn0.

    assert (s0 < s1) as ord0. {
      
      assert (~ (IZR (N)%Z = -1 /\ my = 0)) as cnd0. {
        lra. }
      unfold s0, s1.
      apply (spiral_N_order _ cnd0).  }

    assert (Derive_n sf 2 s1 = 0) as sfsn. {
      assert (N + 1 = -1)%Z as Nm1eq0; try (apply eq_IZR in N1; lia).
      rewrite <- (seq0_bimpl_myeq0 (N+1)%Z) in my0;
        [|right; apply IZR_eq; assumption].
      rewrite <- sf_2deriv_seq0_eqv in my0;
        [|right; apply IZR_eq; assumption].
      rewrite signeq0_eqv in my0.
      change (Derive_n sf 2 s1 = 0) in my0.
      assumption. }

    unfold Derive_n in sf2dlt0, sfsn.
    change (Derive (Derive sf) s0 < 0) in sf2dlt0.
    change (Derive (Derive sf) s1 = 0) in sfsn.

    
    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive sf) s) as dscnt. {
      intros.
      assert (forall s, s0 <= s <= s1 ->
                      is_derive (Derive sf) s
                      (PI * s / (l a)² *
                       (mx * cos (1 / 2 * PI * (s * / l a)²) +
                        my * sin (1 / 2 * PI * (s * / l a)²)))) as d2s. {
      intros.
      specialize (sf_2deriv s2) as d2s.
      unfold is_derive_n, Derive_n in d2s.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive sf) s).
      unfold ex_derive.
      specialize (d2s s H).
      match goal with
      | d2s: is_derive (Derive sf) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (g := Derive sf) in *.

    assert (forall s : R, s0 <= s <= s1 ->
                          continuity_pt (Derive g) s) as dgscnt. {
      intros.

      assert (forall s, s0 <= s <= s1 ->
                        is_derive (Derive g) s
                                  (PI * / (l a)² *
                                   ((my - PI * s² * / (l a)² * mx) *
                                    sin (1 / 2 * PI * (s * / l a)²) +
                                    (mx + PI * s² * / (l a)² * my) *
                                    cos (1 / 2 * PI * (s * / l a)²)))) as d3s. {
      intros.
      specialize (sf_3deriv s2) as d3s.
      unfold is_derive_n, Derive_n in d3s.
      unfold g.
      assumption. }

      apply continuous_pt_impl_continuity_pt.
      apply (ex_derive_continuous (Derive g) s).
      unfold ex_derive.
      specialize (d3s s H).
      match goal with
      | d2s: is_derive (Derive g) ?s ?d2sf |- _ => exists d2sf
      end.
      assumption. }
    set (h := Derive g) in *.

    specialize (interv_allpos_allneg
                  _ _ _ dscnt ord0 sfdz sfdo nzdn0) as apan.

    assert (exists r, s0 < r < s1 /\ Derive sf r < 0) as [r [rbnd rpos]]. {
      assert (continuous h s0) as cs0. {
        apply (continuity_pt_impl_continuous_pt).
        apply dgscnt; lra. }
      rewrite reasonable_continuity in cs0.
      assert (0 < - (h s0)/2) as hs02ps. lra.
      set (phs0 := (mkposreal (- (h s0)/2) hs02ps)).
      specialize (cs0 phs0).
      destruct cs0 as [d cs0].
      set (q := (Rmin ((s0+s1)/2) (s0 + (d/2)))).
      assert (s0 < q < s1) as [ql qu]. {
        intros.
        unfold q, Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        split; try lra. }
      
      assert (Rabs (q - s0) < d) as wd. {
        unfold Rabs.
        destruct Rcase_abs; try lra.
        unfold q.
        unfold Rmin.
        destruct Rle_dec;
        destruct d;
        simpl in *;
        lra. }

      assert (forall r, s0 < r < q -> h r < 0) as posh. {
        intros r [rl rh].
        assert (Rabs (r - s0) < d) as rd. {
          unfold Rabs.
          unfold Rabs in wd.
          destruct Rcase_abs; try lra.
          destruct Rcase_abs; try lra. }

        specialize (cs0 r rd).
        unfold Rabs in cs0.
        unfold phs0 in cs0.
        simpl in cs0.
        destruct Rcase_abs;
        lra. }

      unfold h in posh.
      assert (derivable g) as dervg. {
        unfold derivable.
        intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        unfold g.
        specialize (sf_2deriv x) as sf2d.
        unfold is_derive_n, Derive_n in sf2d.
        match goal with
        | sf2d: is_derive ?f ?x ?R |- _ =>
          change (is_derive (Derive sf) x R) in sf2d;
            exists R;
            assumption
        end. }

      assert (forall t : R, s0 < t < q -> derive_pt g t (dervg t) < 0) as pd. {
        intros.
        rewrite (Derive_Reals g t (dervg t)).
        apply posh.
        assumption. }
      assert (s0 < q) as qlts0. lra.
      assert (s0 <= s0 <= q) as s0inr. lra.
      assert (s0 <= q <= q) as qinr. lra.
      specialize (derive_decreasing_interv
                    _ _ _ dervg qlts0 pd _ _ s0inr qinr qlts0) as gqlt0.
      rewrite sfdz in gqlt0.
      unfold g in gqlt0.
      exists q.
      split; lra. }
    change (g r < 0) in rpos.

    destruct apan as [ap |an];
      [exfalso;
        specialize (ap _ rbnd);
        lra|].

    assert (derivable sf) as dsf. {
      unfold derivable.
      intros.
      apply ex_derive_Reals_0.
      specialize (sf_deriv x) as dsf.
      match goal with
      | d1s: is_derive sf x ?dsf |- _ => exists dsf
      end.
      assumption. }

    destruct salb as [su |se];
      [| rewrite se in *];
    eapply (derive_decreasing_interv _ _ _ _ ord0) ; try lra;
    intros * trng;
    rewrite (Derive_Reals);
    apply an;
    assumption.

    Unshelve.
    assumption.
    assumption.
  Qed.

  (* end hide *)
  Lemma furthest_N_RHS : forall sa sb N,
      let s0 := estp N in
      let s1 := estp (N+1) in
      Derive_n sf 2 s0 < 0 ->
      s0 <= sa -> sa < sb -> sb <= s1 ->
      sf sb < sf sa.
  Proof.
    intros.
    assert (~(IZR N = -2 /\ my = 0)\/(IZR N = -2 /\ my = 0))
      as [ncnd |cnd]. {
      destruct (Req_dec (IZR N) (-2)).
      destruct (Req_dec my 0).
      right.
      split; assumption.
      left; lra.
      left; lra. }
    eapply furthest_N_RHS1; eassumption.
    eapply furthest_N_RHS2; eassumption.
  Qed.
  
  Lemma furthest_N : forall s N,
      let sn := estp (N-1)%Z in
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      Derive_n sf 2 s0 < 0 ->
      sn <= s <= s1 ->
      sf s <= sf s0.
  Proof.
    intros.
    destruct (total_order_T s s0) as [sles0 |sgts0];
      [destruct sles0 as [slts0 | seqs0]|].
    left.
    eapply (furthest_N_LHS _ _ _ H);
      [destruct H0; assumption|
       assumption|
       right; reflexivity].
    right; rewrite seqs0; reflexivity.
    apply Rgt_lt in sgts0.
    left.
    eapply (furthest_N_RHS _ _ _ H);
      [right; reflexivity |
       assumption |
       destruct H0; assumption ].
  Qed.

  Lemma osc_circ_safe_R : forall x y s,
      0 < s -> 
      (x - (occx a s))² + (y - (occy a s))² <= (oscr a s)² ->
      0 <= Derive (Fx a) s * (y - Fy a s) - Derive (Fy a) s * (x - Fx a s).
  Proof.
    intros *.
    intros sne0 sc.
    apply (linear_dominates_circle
             x y (Derive (Fx a) s) (Derive (Fy a) s) (Fx a s) (Fy a s) (oscr a s)).
    unfold oscr.
    apply Rlt_gt.
    zltab.

    intros [dx0 dy0].
    specialize (Fx_deriv _ zlta s) as dfxa.
    apply is_derive_unique in dfxa.
    specialize (Fy_deriv _ zlta s) as dfya.
    apply is_derive_unique in dfya.
    rewrite dfxa in dx0.
    rewrite dfya in dy0.
    apply (cos_sin_0 (1 / 2 * PI * (s / l a)²)); split; assumption.
    unfold occx, occy in sc.
    assumption.
  Qed.

  Lemma osc_circ_safe_R_lt : forall x y s,
      0 < s -> 
      (x - (occx a s))² + (y - (occy a s))² < (oscr a s)² ->
      0 < Derive (Fx a) s * (y - Fy a s) - Derive (Fy a) s * (x - Fx a s).
  Proof.
    intros *.
    intros sne0 sc.
    apply (linear_dominates_circle_lt
             x y (Derive (Fx a) s) (Derive (Fy a) s) (Fx a s) (Fy a s) (oscr a s)).
    unfold oscr.
    apply Rlt_gt.
    zltab.

    intros [dx0 dy0].
    specialize (Fx_deriv _ zlta s) as dfxa.
    apply is_derive_unique in dfxa.
    specialize (Fy_deriv _ zlta s) as dfya.
    apply is_derive_unique in dfya.
    rewrite dfxa in dx0.
    rewrite dfya in dy0.
    apply (cos_sin_0 (1 / 2 * PI * (s / l a)²)); split; assumption.
    unfold occx, occy in sc.
    assumption.
  Qed.


  Lemma osc_circ_safe_L : forall x y s,
      s < 0 -> 
      (x - (occx a s))² + (y - (occy a s))² <= (oscr a s)² ->
      0 <= (- Derive (Fx a) s) * (y - Fy a s) - (- Derive (Fy a) s) * (x - Fx a s).
  Proof.
    intros *.
    intros sne0 sc.
    apply (linear_dominates_circle
             x y (- Derive (Fx a) s) (- Derive (Fy a) s)
             (Fx a s) (Fy a s) (- (oscr a s))).
    unfold oscr.
    apply Rlt_gt.
    rewrite Ropp_inv_permute; zltab.
    setr (a * -s); zltab.
    apply Rmult_integral_contrapositive_currified; lra.

    intros [dx0 dy0].
    specialize (Fx_deriv _ zlta s) as dfxa.
    apply is_derive_unique in dfxa.
    specialize (Fy_deriv _ zlta s) as dfya.
    apply is_derive_unique in dfya.
    apply Ropp_eq_0_compat in dx0.
    rewrite Ropp_involutive in dx0.
    apply Ropp_eq_0_compat in dy0.
    rewrite Ropp_involutive in dy0.
    rewrite dfxa in dx0.
    rewrite dfya in dy0.
    apply (cos_sin_0 (1 / 2 * PI * (s / l a)²)); split; assumption.
    unfold occx, occy in sc.
    rewrite <- (Rsqr_neg (oscr a s)), <- (Rsqr_neg (Derive (Fy a) s)),
    <- (Rsqr_neg (Derive (Fx a) s)), Ropp_involutive.
    repeat rewrite <- RmultRinv in *.
    set (Q := / sqrt ((Derive (Fy a) s)² + (Derive (Fx a) s)²)) in *.
    fieldrewrite (Derive (Fy a) s * Q * - oscr a s)
                 (- Derive (Fy a) s * Q * oscr a s).
    fieldrewrite (- Derive (Fx a) s * Q * - oscr a s)
                 (Derive (Fx a) s * Q * oscr a s).
    assumption.
  Qed.

  Lemma euler_tan_pt_gen : forall N,
      let st := estp N in
      my * Derive (Fx a) st = mx * Derive (Fy a) st.
  Proof.
    intros.
    destruct (Req_dec mx 0) as [mxeq0 | mxne0].
    + specialize (euler_tan_pt2 N mxeq0) as [dfyne0 dfxeq0].
      change (Derive (Fy a) st <> 0) in dfyne0.
      change (Derive (Fx a) st = 0) in dfxeq0.
      rewrite mxeq0, dfxeq0.
      field.
    + specialize (euler_tan_pt_mxne0_derivefxne0 N mxne0) as dfxne0.
      change (Derive (Fx a) st <> 0) in dfxne0.
      apply (Rmult_eq_reg_r (/ (mx * Derive (Fx a) st)));
        try (zltab;
             apply Rmult_integral_contrapositive_currified;
             assumption).
      setl (my / mx); try lra.
      setr (Derive (Fy a) st / Derive (Fx a) st); try lra.
      symmetry.
      apply euler_tan_pt; assumption.
  Qed.
      
  Lemma sign_insensitive_pattern : forall jx jy gx gy,
      ~(jx = 0 /\ jy = 0) ->
      ~(gx = 0 /\ gy = 0) ->
      jy * gx = jx * gy ->
      let M := sqrt((jx² + jy²)/(gx² + gy²)) in
      (0 < M) /\
      ((jy = M * gy /\ jx = M * gx) \/ (jy = M * - gy /\ jx = M * - gx)).
  Proof.
    intros *.
    intros fno gno inv.
    specialize (posss _ _ fno) as zltf2.
    specialize (posss _ _ gno) as zltg2.
    assert (0 < / (gx² + gy²)) as zltgi; try zltab.
    assert (0 < / (jx² + jy²)) as zltfi; try zltab.
    generalize zltf2; intro zltf3.
    generalize zltg2; intro zltg3.
    generalize zltgi; intro zltgj.
    generalize zltfi; intro zltfj.
    apply sqrt_lt_R0 in zltgj.
    apply sqrt_lt_R0 in zltfj.
    apply sqrt_lt_R0 in zltg3.
    apply sqrt_lt_R0 in zltf3.
    intro M.
    assert (0 < M) as zltm. {
      unfold M.
      rewrite <- RmultRinv.
      rewrite sqrt_mult_alt; try assumption.
      zltab.
      left; assumption. }
      
    split; try assumption.
    unfold M.
    destruct (Req_dec gy 0) as [gyeq0 | gyne0];
      [|destruct (Req_dec gx 0) as [gxeq0 | gxne0]].
    + rewrite gyeq0 in *.
      assert (gx <> 0) as gxne0; try lra.
      assert (jy = 0) as jyeq0. {
        apply (Rmult_eq_reg_r gx); try lra. }
      rewrite jyeq0.
      autorewrite with null in *.
      specialize (Rle_0_sqr jx) as zlejx2.
      rewrite <- RmultRinv.
      rewrite sqrt_mult_alt; try assumption.
      destruct (Rle_dec 0 jx) as [zlejx|zgtjx].
      ++ rewrite sqrt_Rsqr; try lra.
         rewrite <- Rsqr_inv; try lra.
         destruct (Rlt_dec 0 gx) as [zlegx|zgtgx].
         assert (0 < / gx) as zlegx2; try zltab.
         rewrite sqrt_Rsqr; try lra.
         left.
         split; try auto.
         field; assumption.
         apply Rnot_lt_le in zgtgx.
         destruct zgtgx as [gxlt0 | gxeq0]; try lra.
         assert (/ gx < 0) as zlegx2. {
           apply Ropp_lt_cancel.
           setl 0.
           rewrite Ropp_inv_permute; try lra.
           zltab; lra. }
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         right.
         split; auto.
         field; lra.
      ++ apply Rnot_le_lt in zgtjx.
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         rewrite <- Rsqr_inv; try lra.
         destruct (Rlt_dec 0 gx) as [zlegx|zgtgx].
         assert (0 < / gx) as zlegx2; try zltab.
         rewrite sqrt_Rsqr; try lra.
         right.
         split; try auto.
         field; assumption.
         apply Rnot_lt_le in zgtgx.
         destruct zgtgx as [gxlt0 | gxeq0]; try lra.
         assert (/ gx < 0) as zlegx2. {
           apply Ropp_lt_cancel.
           setl 0.
           rewrite Ropp_inv_permute; try lra.
           zltab; lra. }
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         left.
         split; auto.
         field; lra.
    + rewrite gxeq0 in *.
      assert (jx = 0) as jxeq0. {
        apply (Rmult_eq_reg_r gy); try lra. }
      rewrite jxeq0.
      autorewrite with null in *.
      specialize (Rle_0_sqr jy) as zlejy2.
      rewrite <- RmultRinv.
      rewrite sqrt_mult_alt; try assumption.
      destruct (Rle_dec 0 jy) as [zlejy|zgtjy].
      ++ rewrite sqrt_Rsqr; try lra.
         rewrite <- Rsqr_inv; try lra.
         destruct (Rlt_dec 0 gy) as [zlegy|zgtgy].
         assert (0 < / gy) as zlegy2; try zltab.
         rewrite sqrt_Rsqr; try lra.
         left.
         split; try auto.
         field; assumption.
         apply Rnot_lt_le in zgtgy.
         destruct zgtgy as [gylt0 | gyeq0]; try lra.
         assert (/ gy < 0) as zlegy2. {
           apply Ropp_lt_cancel.
           setl 0.
           rewrite Ropp_inv_permute; try lra.
           zltab; lra. }
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         right.
         split; auto.
         field; lra.
      ++ apply Rnot_le_lt in zgtjy.
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         rewrite <- Rsqr_inv; try lra.
         destruct (Rlt_dec 0 gy) as [zlegy|zgtgy].
         assert (0 < / gy) as zlegy2; try zltab.
         rewrite sqrt_Rsqr; try lra.
         right.
         split; try auto.
         field; assumption.
         apply Rnot_lt_le in zgtgy.
         destruct zgtgy as [gylt0 | gyeq0]; try lra.
         assert (/ gy < 0) as zlegy2. {
           apply Ropp_lt_cancel.
           setl 0.
           rewrite Ropp_inv_permute; try lra.
           zltab; lra. }
         rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
         left.
         split; auto.
         field; lra.
    + rewrite <- RmultRinv.
      rewrite sqrt_mult_alt; try lra.

      assert (jx <> 0) as jxne0. {
        intro jxeq0.
        rewrite jxeq0 in *.
        autorewrite with null in *.
        assert (jy = 0) as jyeq0;
          try (apply (Rmult_eq_reg_r gx); lra).
        apply fno; lra. }

      assert (jy <> 0) as jyne0. {
        intro jyeq0.
        rewrite jyeq0 in *.
        autorewrite with null in *.
        apply jxne0.
        apply (Rmult_eq_reg_r gy); lra. }
      
      destruct (Rle_dec 0 jy) as [zlejy|zgtjy];
          [destruct zlejy as [zltjy|zeqjy];
           [|exfalso;
             symmetry in zeqjy;
             apply jyne0;
             assumption]|
           apply Rnot_le_lt in zgtjy].
      ++ destruct (Rlt_dec 0 gy) as [zlegy|zgtgy].
         left.
         assert (jy = sqrt (jx² + jy²) * sqrt (/ (gx² + gy²)) * gy) as id. {
           apply (Rmult_eq_reg_l (sqrt (/ (jx² + jy²)))); try lra.
           repeat rewrite <- Rmult_assoc.
           rewrite <- sqrt_mult_alt; try lra.
           fieldrewrite (/ (jx² + jy²) * (jx² + jy²)) 1;
             try (unfold Rsqr in zltf2; lra).
           rewrite sqrt_1.
           arn.
           rewrite <- (sqrt_Rsqr jy) at 2; try lra.
           rewrite <- (sqrt_Rsqr gy) at 2; try lra.
           repeat rewrite <- sqrt_mult_alt; try lra.
           apply f_equal.
           specialize (Rlt_0_sqr jy ltac:(lra)) as zltjy2.
           specialize (Rlt_0_sqr gy ltac:(lra)) as zltgy2.
           rewrite <- (Rinv_involutive (jy²)) at 2; try lra.
           rewrite <- (Rinv_involutive (gy²)) at 2; try lra.
           rewrite <- Rinv_mult_distr; try zltab.
           rewrite <- Rinv_mult_distr; try zltab.
           fieldrewrite ((jx² + jy²) * / jy²) ((jx/jy)² + 1); try lra.
           fieldrewrite ((gx² + gy²) * / gy²) ((gx/gy)² + 1); try lra.
           apply f_equal.
           apply (Rplus_eq_reg_r (-1)).
           setl (jx / jy)²; try lra.
           setr (gx / gy)²; try lra.
           apply f_equal.
           apply (Rmult_eq_reg_r (jy * gy));
             try (apply Rmult_integral_contrapositive_currified; lra).
           setr (jy * gx); try lra.
           setl (jx * gy); try lra. }
         split; try assumption.
         apply (Rmult_eq_reg_r gy); try lra.
         rewrite <- inv.
         apply (Rmult_eq_reg_r (/gx)); try zltab.
         lrag id.

         right.
         apply Rnot_lt_le in zgtgy.
         destruct zgtgy as [gylt0 |gyeq0]; try lra.
         assert (0 < - gy) as zlthz; try lra.
         rewrite (Rsqr_neg gy).
         rewrite (Rsqr_neg gx).
         set (hx := (-gx)) in *.
         set (hy := (-gy)) in *.
         assert (0 < hx² + hy²) as zlth2. {
           unfold hx, hy.
           repeat rewrite <- Rsqr_neg.
           assumption. }
         assert (0 < / (hx² + hy²)) as zlthi; try zltab.
         
         assert (jy = sqrt (jx² + jy²) * sqrt (/ (hx² + hy²)) * hy) as id. {
           apply (Rmult_eq_reg_l (sqrt (/ (jx² + jy²)))); try lra.
           repeat rewrite <- Rmult_assoc.
           rewrite <- sqrt_mult_alt; try lra.
           fieldrewrite (/ (jx² + jy²) * (jx² + jy²)) 1;
             try (unfold Rsqr in zltf2; lra).
           rewrite sqrt_1.
           arn.
           rewrite <- (sqrt_Rsqr jy) at 2; try lra.
           rewrite <- (sqrt_Rsqr hy) at 2; try lra.
           repeat rewrite <- sqrt_mult_alt; try lra.
           apply f_equal.
           specialize (Rlt_0_sqr jy ltac:(lra)) as zltjy2.
           specialize (Rlt_0_sqr hy ltac:(lra)) as zltgy2.
           rewrite <- (Rinv_involutive (jy²)) at 2; try lra.
           rewrite <- (Rinv_involutive (hy²)) at 2; try lra.
           rewrite <- Rinv_mult_distr; try zltab.
           rewrite <- Rinv_mult_distr; try zltab.
           fieldrewrite ((jx² + jy²) * / jy²) ((jx/jy)² + 1); try lra.
           fieldrewrite ((hx² + hy²) * / hy²) ((hx/hy)² + 1); try lra.
           apply f_equal.
           apply (Rplus_eq_reg_r (-1)).
           setl (jx / jy)²; try lra.
           setr (hx / hy)²; try lra.
           apply f_equal.
           apply (Rmult_eq_reg_r (jy * hy));
             try (apply Rmult_integral_contrapositive_currified; lra).
           unfold hx, hy.
           apply (Rmult_eq_reg_r (-1)); try discrR.
           setr (jy * gx); try lra.
           setl (jx * gy); try lra. }
         split; try assumption.
         apply (Rmult_eq_reg_r (gy)); try lra.
         rewrite <- inv.
         unfold hx at 2.
         apply (Rmult_eq_reg_r (/gx)); try zltab.
         unfold hy at 2 in id.
         lrag id.

      ++ assert (0 < - jy) as zltdz; try lra.
         rewrite (Rsqr_neg jy).
         rewrite (Rsqr_neg jx).
         rewrite <- (Ropp_involutive jy) at 1 4.
         rewrite <- (Ropp_involutive jx) at 2 5.
         set (cx := (-jx)) in *.
         set (cy := (-jy)) in *.
         assert (0 < cx² + cy²) as zltc2. {
           unfold cx, cy.
           repeat rewrite <- Rsqr_neg.
           assumption. }
         assert (0 < / (cx² + cy²)) as zltci; try zltab.
         generalize zltci; intro zltcj.
         apply sqrt_lt_R0 in zltcj.
         
         destruct (Rlt_dec 0 gy) as [zlegy|zgtgy].
         right.
         assert (cy = sqrt (cx² + cy²) * sqrt (/ (gx² + gy²)) * gy) as id. {
           apply (Rmult_eq_reg_l (sqrt (/ (cx² + cy²)))); try lra.
           repeat rewrite <- Rmult_assoc.
           rewrite <- sqrt_mult_alt; try lra.
           fieldrewrite (/ (cx² + cy²) * (cx² + cy²)) 1;
             try (unfold Rsqr in zltc2; lra).
           rewrite sqrt_1.
           arn.
           rewrite <- (sqrt_Rsqr cy) at 2; try lra.
           rewrite <- (sqrt_Rsqr gy) at 2; try lra.
           repeat rewrite <- sqrt_mult_alt; try lra.
           apply f_equal.
           specialize (Rlt_0_sqr cy ltac:(lra)) as zltjy2.
           specialize (Rlt_0_sqr gy ltac:(lra)) as zltgy2.
           rewrite <- (Rinv_involutive (cy²)) at 2; try lra.
           rewrite <- (Rinv_involutive (gy²)) at 2; try lra.
           rewrite <- Rinv_mult_distr; try zltab.
           rewrite <- Rinv_mult_distr; try zltab.
           fieldrewrite ((cx² + cy²) * / cy²) ((cx/cy)² + 1); try lra.
           fieldrewrite ((gx² + gy²) * / gy²) ((gx/gy)² + 1); try lra.
           apply f_equal.
           apply (Rplus_eq_reg_r (-1)).
           setl (cx / cy)²; try lra.
           setr (gx / gy)²; try lra.
           apply f_equal.
           apply (Rmult_eq_reg_r (cy * gy));
             try (apply Rmult_integral_contrapositive_currified; lra).
           unfold cx, cy.
           setr (- (jy * gx)); try lra.
           setl (- (jx * gy)); try lra. }
         split; try lra.
         apply (Rmult_eq_reg_r gy); try lra.
         unfold cx at 1.
         setl (jx * gy).
         rewrite <- inv.
         apply (Rmult_eq_reg_r (- /gx)); try zltab.
         setl (- jy); try lra.
         setr (sqrt (cx² + cy²) * sqrt (/ (gx² + gy²)) * gy); try lra.
         assumption.

         left.
         apply Rnot_lt_le in zgtgy.
         destruct zgtgy as [gylt0 |gyeq0]; try lra.
         assert (0 < - gy) as zlthz; try lra.
         rewrite (Rsqr_neg gy).
         rewrite (Rsqr_neg gx).
         set (hx := (-gx)) in *.
         set (hy := (-gy)) in *.
         assert (0 < hx² + hy²) as zlth2. {
           unfold hx, hy.
           repeat rewrite <- Rsqr_neg.
           assumption. }
         assert (0 < / (hx² + hy²)) as zlthi; try zltab.
         
         assert (cy = sqrt (cx² + cy²) * sqrt (/ (hx² + hy²)) * hy) as id. {
           apply (Rmult_eq_reg_l (sqrt (/ (cx² + cy²)))); try lra.
           repeat rewrite <- Rmult_assoc.
           rewrite <- sqrt_mult_alt; try lra.
           fieldrewrite (/ (cx² + cy²) * (cx² + cy²)) 1;
             try (unfold Rsqr in zltc2; lra).
           rewrite sqrt_1.
           arn.
           rewrite <- (sqrt_Rsqr cy) at 2; try lra.
           rewrite <- (sqrt_Rsqr hy) at 2; try lra.
           repeat rewrite <- sqrt_mult_alt; try lra.
           apply f_equal.
           specialize (Rlt_0_sqr cy ltac:(lra)) as zltjy2.
           specialize (Rlt_0_sqr hy ltac:(lra)) as zltgy2.
           rewrite <- (Rinv_involutive (cy²)) at 2; try lra.
           rewrite <- (Rinv_involutive (hy²)) at 2; try lra.
           rewrite <- Rinv_mult_distr; try zltab.
           rewrite <- Rinv_mult_distr; try zltab.
           fieldrewrite ((cx² + cy²) * / cy²) ((cx/cy)² + 1); try lra.
           fieldrewrite ((hx² + hy²) * / hy²) ((hx/hy)² + 1); try lra.
           apply f_equal.
           apply (Rplus_eq_reg_r (-1)).
           setl (cx / cy)²; try lra.
           setr (hx / hy)²; try lra.
           apply f_equal.
           apply (Rmult_eq_reg_r (cy * hy));
             try (apply Rmult_integral_contrapositive_currified; lra).
           unfold hx, hy.
           apply (Rmult_eq_reg_r (-1)); try discrR.
           unfold cx, cy.
           setr (- (jy * gx)); try lra.
           setl (- (jx * gy)); try lra. }
         unfold hy in id at 2.
         split; try lra.
         apply (Rmult_eq_reg_r (- gy)); try lra.
         unfold cx at 1.
         setl (- (jx * gy)).
         rewrite <- inv.
         apply (Rmult_eq_reg_r (/gx)); try zltab.
         setl (- jy); try lra.
         setr (sqrt (cx² + cy²) * sqrt (/ (hx² + hy²)) * - gy); try lra.
         assumption.
  Qed.         
         
  Lemma safe_orientation : forall N (nge0 : IZR N >= 0),
      let s := estp N in
      let dFx := Derive (Fx a) s in
      let dFy := Derive (Fy a) s in
      let MdF := sqrt (dFx² + dFy²) in
      let M := sqrt (mx² + my²) in
      0 < Derive_n sf 2 s ->
      0 < M * / MdF /\ mx = (M * / MdF) * dFx /\ my = (M * / MdF) * dFy.
  Proof.
    intros * nge0 * zltd2.
    specialize (sf_2deriv s) as sf2d.
    apply is_derive_n_unique in sf2d.
    rewrite sf2d in zltd2.
    clear sf2d.

    specialize (agt0_lagt0 _ zlta) as zltla.
    specialize PI_RGT_0 as pigt0.
    assert (0 < s) as zlts. {
      destruct nge0 as [ngt0 | neq0].
      apply spiral_N_pos; assumption.
      specialize spiral_N_pos1 as zles.
      apply eq_IZR in neq0.
      simpl in zles.
      rewrite <- neq0 in zles at 2.
      change (0 <= s) in zles.
      destruct zles as [zlts|zeqs].
      assumption.
      symmetry in zeqs.
      rewrite zeqs, <- RmultRinv in zltd2.
      autorewrite with null in zltd2.
      lra. }

    specialize (Fx_deriv _ zlta s) as dfxi.
    apply is_derive_unique in dfxi.
    change (dFx = cos (1 / 2 * PI * (s / l a)²)) in dfxi.
    rewrite <- (RmultRinv s) in dfxi.
    specialize (Fy_deriv _ zlta s) as dfyi.
    apply is_derive_unique in dfyi.
    change (dFy = sin (1 / 2 * PI * (s / l a)²)) in dfyi.
    rewrite <- (RmultRinv s) in dfyi.
    rewrite <- dfxi, <- dfyi in zltd2.

    assert (0 < mx * dFx + my * dFy) as zlt. {
      apply (Rmult_lt_reg_l (PI * s / (l a)²)).
      unfold Rsqr.
      zltab.
      setl 0.
      zltab.
      assumption. }

    specialize (posss _ _ ds) as zltm2.
    generalize zltm2; intro zltsm.
    apply sqrt_lt_R0 in zltsm.
    change (0 < M) in zltsm.

    assert (~ (dFx = 0 /\ dFy = 0)) as nfo. {
      intros [dfxeq0 dfyeq0].
      rewrite dfxeq0, dfyeq0 in *.
      autorewrite with null in *.
      lra. }

    specialize (posss _ _ nfo) as zltf2.
    generalize zltf2; intro zltsf.
    apply sqrt_lt_R0 in zltsf.
    change (0 < MdF) in zltsf.
    assert (0 < / MdF) as zltsfi; try zltab.

    assert (0 < M * / MdF) as zltmdf; try zltab.

    specialize (euler_tan_pt_gen N) as rti.
    change (my * dFx = mx * dFy) in rti.

    rewrite RmultRinv in *.
    assert (M / MdF = sqrt ((mx² + my²) / (dFx² + dFy²))) as ceq. {
      unfold M, MdF.
      rewrite sqrt_div_alt; try assumption.
      auto.  }

    specialize (sign_insensitive_pattern _ _ _ _ ds nfo rti) as
        [gtz  [[myeq mxeq] | [myeqn mxeqn]]]; rewrite <- ceq in *.

    + repeat split; assumption.
    + exfalso.
      rewrite myeqn, mxeqn in zlt.
      clear - zlt zltf2 gtz zltsf.
      assert (0 < - (dFx² + dFy²)) as nfoc. {
        apply (Rmult_lt_reg_l (M/ MdF)); try assumption.
        setl 0; try lra.
        unfold Rsqr.
        lrag zlt. }
      lra.
  Qed.

  Lemma safe_orientation_neg : forall N (nge0 : IZR N >= 0),
      let s := estp N in
      let dFx := Derive (Fx a) s in
      let dFy := Derive (Fy a) s in
      let MdF := sqrt (dFx² + dFy²) in
      let M := sqrt (mx² + my²) in
      Derive_n sf 2 s < 0 ->
      0 < M * / MdF /\ mx = (M * / MdF) * - dFx /\ my = (M * / MdF) * - dFy.
  Proof.
    intros * nge0 * zltd2.
    specialize (sf_2deriv s) as sf2d.
    apply is_derive_n_unique in sf2d.
    rewrite sf2d in zltd2.
    clear sf2d.

    specialize (agt0_lagt0 _ zlta) as zltla.
    specialize PI_RGT_0 as pigt0.
    assert (0 < s) as zlts. {
      destruct nge0 as [ngt0 | neq0].
      apply spiral_N_pos; assumption.
      specialize spiral_N_pos1 as zles.
      apply eq_IZR in neq0.
      simpl in zles.
      rewrite <- neq0 in zles at 2.
      change (0 <= s) in zles.
      destruct zles as [zlts|zeqs].
      assumption.
      symmetry in zeqs.
      rewrite zeqs, <- RmultRinv in zltd2.
      autorewrite with null in zltd2.
      lra. }

    specialize (Fx_deriv _ zlta s) as dfxi.
    apply is_derive_unique in dfxi.
    change (dFx = cos (1 / 2 * PI * (s / l a)²)) in dfxi.
    rewrite <- (RmultRinv s) in dfxi.
    specialize (Fy_deriv _ zlta s) as dfyi.
    apply is_derive_unique in dfyi.
    change (dFy = sin (1 / 2 * PI * (s / l a)²)) in dfyi.
    rewrite <- (RmultRinv s) in dfyi.
    rewrite <- dfxi, <- dfyi in zltd2.

    assert (mx * dFx + my * dFy < 0) as zlt. {
      apply (Rmult_lt_reg_l (PI * s / (l a)²)).
      unfold Rsqr.
      zltab.
      setr 0.
      zltab.
      assumption. }

    specialize (posss _ _ ds) as zltm2.
    generalize zltm2; intro zltsm.
    apply sqrt_lt_R0 in zltsm.
    change (0 < M) in zltsm.

    assert (~ (dFx = 0 /\ dFy = 0)) as nfo. {
      intros [dfxeq0 dfyeq0].
      rewrite dfxeq0, dfyeq0 in *.
      autorewrite with null in *.
      lra. }

    specialize (posss _ _ nfo) as zltf2.
    generalize zltf2; intro zltsf.
    apply sqrt_lt_R0 in zltsf.
    change (0 < MdF) in zltsf.
    assert (0 < / MdF) as zltsfi; try zltab.

    assert (0 < M * / MdF) as zltmdf; try zltab.

    specialize (euler_tan_pt_gen N) as rti.
    change (my * dFx = mx * dFy) in rti.

    rewrite RmultRinv in *.
    assert (M / MdF = sqrt ((mx² + my²) / (dFx² + dFy²))) as ceq. {
      unfold M, MdF.
      rewrite sqrt_div_alt; try assumption.
      auto.  }

    specialize (sign_insensitive_pattern _ _ _ _ ds nfo rti) as
        [gtz  [[myeq mxeq] | [myeqn mxeqn]]]; rewrite <- ceq in *.

    + exfalso.
      rewrite myeq, mxeq in zlt.
      clear - zlt zltf2 gtz zltsf.
      assert (0 < - (dFx² + dFy²)) as nfoc. {
        apply (Rmult_lt_reg_l (M/ MdF)); try assumption.
        setl (-0); try lra.
        unfold Rsqr.
        setr (-(M / MdF * (dFx * dFx + dFy * dFy))).
        lra.
        apply Ropp_lt_contravar.
        lrag zlt. }
      lra.
    + repeat split; assumption.
  Qed.


  Lemma neg_2derivsf_late_safety_maxima_dominate : forall N,
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      let s2 := estp (N+2)%Z in
      IZR N >= 0 -> Derive_n sf 2 s0 < 0 ->
      sf s2 < sf s0.
  Proof.
    intros * s1 s2 nge0 s0m.

    assert (0 < s0) as zlts0. {
      destruct nge0 as [ngt0 |neq0].
      apply spiral_N_pos; assumption.
      specialize spiral_N_pos1 as zles.
      simpl in zles.
      apply eq_IZR in neq0.
      rewrite <- neq0 in zles at 2.
      change (0 <= s0) in zles.
      destruct zles as [zlts0 | zeqs0]; try assumption.
      exfalso.
      symmetry in zeqs0.
      unfold s0 in zeqs0.
      rewrite <- sf_2deriv_seq0_eqv, signeq0_eqv in zeqs0.
      unfold s0 in s0m.
      rewrite zeqs0 in s0m.
      lra.
      left.
      apply IZR_eq.
      assumption. }
      
    
    unfold sf, safe_pt.
    rewrite <- lin_pt_ineq_lt.
    specialize (safe_orientation_neg _ nge0 s0m) as [zltM [mxd myd]].
    set (dFx := Derive (Fx a) s0) in *.
    set (dFy := Derive (Fy a) s0) in *.
    set (M := sqrt (mx² + my²) * / sqrt (dFx² + dFy²)) in *.
    change (0 < M) in zltM.
    change (mx = M * - dFx) in mxd.
    change (my = M * - dFy) in myd.
    rewrite mxd, myd.
    apply (Rmult_lt_reg_r (/ M)); try lra.
    zltab.
    setl 0; try lra.
    setr (dFx * (Fy a s2 - Fy a s0) - dFy * (Fx a s2 - Fx a s0)); try lra.
    apply osc_circ_safe_R_lt; try assumption.
    apply osc_circ_approx_lt; try assumption.
    apply (Rlt_trans _ s1).
    assert (~ (IZR N = -1 /\ my = 0)) as cndn; try lra.
    apply (spiral_N_order _ cndn).
    assert (~ (IZR (N+1) = -1 /\ my = 0)) as cndn1. {
      intros [n1n1 myeq0].
      rewrite plus_IZR in n1n1.
      lra. }
    specialize (spiral_N_order _ cndn1) as s1lts2.
    simpl in s1lts2.
    assert (N + 1 + 1 = N + 2)%Z as nid; try lia.
    rewrite nid in s1lts2.
    assumption.
  Qed.

  
  Lemma pos_2derivsf_early_safety_minima_dominate : forall N,
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      let s2 := estp (N+2)%Z in
      IZR N >= 0 -> 0 < Derive_n sf 2 s0 ->
      sf s0 < sf s2.
  Proof.
    intros * s1 s2 nge0 s0m.

    assert (0 < s0) as zlts0. {
      destruct nge0 as [ngt0 |neq0].
      apply spiral_N_pos; assumption.
      specialize spiral_N_pos1 as zles.
      simpl in zles.
      apply eq_IZR in neq0.
      rewrite <- neq0 in zles at 2.
      change (0 <= s0) in zles.
      destruct zles as [zlts0 | zeqs0]; try assumption.
      exfalso.
      symmetry in zeqs0.
      unfold s0 in zeqs0.
      rewrite <- sf_2deriv_seq0_eqv, signeq0_eqv in zeqs0.
      unfold s0 in s0m.
      rewrite zeqs0 in s0m.
      lra.
      left.
      apply IZR_eq.
      assumption. }
      
    
    unfold sf, safe_pt.
    rewrite <- lin_pt_ineq_lt.
    specialize (safe_orientation _ nge0 s0m) as [zltM [mxd myd]].
    set (dFx := Derive (Fx a) s0) in *.
    set (dFy := Derive (Fy a) s0) in *.
    set (M := sqrt (mx² + my²) * / sqrt (dFx² + dFy²)) in *.
    change (0 < M) in zltM.
    change (mx = M * dFx) in mxd.
    change (my = M * dFy) in myd.
    rewrite mxd, myd.
    apply (Rmult_lt_reg_r (/ M)); try lra.
    zltab.
    setl 0; try lra.
    setr (dFx * (Fy a s2 - Fy a s0) - dFy * (Fx a s2 - Fx a s0)); try lra.
    apply osc_circ_safe_R_lt; try assumption.
    apply osc_circ_approx_lt; try assumption.
    apply (Rlt_trans _ s1).
    assert (~ (IZR N = -1 /\ my = 0)) as cndn; try lra.
    apply (spiral_N_order _ cndn).
    assert (~ (IZR (N+1) = -1 /\ my = 0)) as cndn1. {
      intros [n1n1 myeq0].
      rewrite plus_IZR in n1n1.
      lra. }
    specialize (spiral_N_order _ cndn1) as s1lts2.
    simpl in s1lts2.
    assert (N + 1 + 1 = N + 2)%Z as nid; try lia.
    rewrite nid in s1lts2.
    assumption.
  Qed.


  Lemma trajectory_point_safety_order : forall N,
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      let s2 := estp (N+2)%Z in
      IZR N >= 0 ->
      ((Z.Even N /\0 < my) \/
       (Z.Even N /\ 0 < mx /\ 0 = my /\ IZR N <> 0) \/
       (Z.Odd N /\ my < 0) \/
       (Z.Odd N /\ mx < 0 /\ my = 0 /\ IZR N <> -1)) ->
      (forall sa sb, s0 <= sa -> sa < sb -> sb <= s1 -> sf sa < sf sb) /\
      (forall sa sb, s1 <= sa -> sa < sb -> sb <= s2 -> sf sb < sf sa) /\
      sf s0 < sf s2.
  Proof.
    intros * nge0 c.
    apply cond_sf_2deriv_pos in c.
    split.
    + assert (N = (N+1)-1)%Z as id; try lia.
      unfold s0.
      rewrite id.
      unfold s1.
      intros.
      apply (furthest_N_LHS _ _ (N+1)%Z); try lra.
      rewrite <- signeqm1_eqv.
      rewrite <- signeq1_eqv in c.
      rewrite sf_2deriv_sign in c.
      lra.
      split; try lra.
      intros [Neq0 s0eq0].
      rewrite <- sf_2deriv_seq0_eqv in s0eq0.
      lra.
      lra.
    + split.
      assert (N+2 = (N+1)+1)%Z as id; try lia.
      unfold s2.
      rewrite id.
      unfold s1.
      intros.
      apply (furthest_N_RHS _ _ (N+1)%Z); try lra.
      rewrite <- signeqm1_eqv.
      rewrite <- signeq1_eqv in c.
      rewrite sf_2deriv_sign in c.
      lra.
      split; try lra.
      intros [Neq0 s0eq0].
      rewrite <- sf_2deriv_seq0_eqv in s0eq0.
      lra.
      lra.
    apply pos_2derivsf_early_safety_minima_dominate; try assumption.
  Qed.

  Lemma trajectory_point_safety_order_2 : forall N,
      let s0 := estp N in
      let s1 := estp (N+1)%Z in
      let s2 := estp (N+2)%Z in
      IZR N >= 0 ->
      ((Z.Even N /\ my < 0) \/
       (Z.Even N /\ mx < 0 /\ my = 0 /\ IZR N <> 0) \/
       (Z.Odd N /\ 0 < my) \/
       (Z.Odd N /\ 0 < mx /\ 0 = my /\ IZR N <> -1)) ->
      (forall sa sb, s0 <= sa -> sa < sb -> sb <= s1 -> sf sb < sf sa) /\
      (forall sa sb, s1 <= sa -> sa < sb -> sb <= s2 -> sf sa < sf sb) /\
      sf s2 < sf s0.
  Proof.
    intros * nge0 c.
    apply cond_sf_2deriv_neg in c.
    split.
    + assert (N = (N+1)-1)%Z as id; try lia.
      unfold s0.
      rewrite id.
      unfold s1.
      intros.
      apply (closest_N_LHS _ _ (N+1)%Z); try lra.
      rewrite <- signeq1_eqv.
      rewrite <- signeqm1_eqv in c.
      rewrite sf_2deriv_sign in c.
      lra.
      split; try lra.
      intros [Neq0 s0eq0].
      rewrite <- sf_2deriv_seq0_eqv in s0eq0.
      lra.
      lra.
    + split.
      assert (N+2 = (N+1)+1)%Z as id; try lia.
      unfold s2.
      rewrite id.
      unfold s1.
      intros.
      apply (closest_N_RHS _ _ (N+1)%Z); try lra.
      rewrite <- signeq1_eqv.
      rewrite <- signeqm1_eqv in c.
      rewrite sf_2deriv_sign in c.
      lra.
      split; try lra.
      intros [Neq0 s0eq0].
      rewrite <- sf_2deriv_seq0_eqv in s0eq0.
      lra.
      lra.
      apply neg_2derivsf_late_safety_maxima_dominate; try assumption.
  Qed.


  (* begin hide *)  
  Lemma spiral_tangent_closest_approach_helper : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 ->
      sn < sa <= s0 -> 
      0 <= sa -> 
      (forall s, sa <= s <= sb -> sf sa <= sf s) \/
      (forall s, sa <= s <= sb -> sf sb <= sf s) \/
      (forall s, sa <= s <= sb -> sf s0 <= sf s) \/
      (forall s, sa <= s <= sb -> sf s1 <= sf s).
  Proof.
    intros *.
    intros Nge0 [snltsa sales0] zlesa.
    destruct (Rlt_dec sa sb).
    2 : { left.
          intros r [p q].
          apply Rnot_lt_le in n.
          destruct n.
          exfalso; lra.
          subst.
          assert (r = sa). lra.
          subst.
          right; reflexivity. }

    
    destruct (Rlt_dec sb s0).
    + destruct sales0; try lra.
      (* sn < [sa < sb] < s0 *)
      destruct (total_order_T 0 (Derive_n sf 2 s0));
        try destruct s.
      ++ (* s0 is a local minimum *)
        right; left.
        intros s [sl [su| se]].
        left.
        eapply (closest_N_LHS s sb).
        apply r1.
        change (sn <= s).
        lra.
        assumption.
        change (sb <= s0).
        left; assumption.
        subst; right; reflexivity.
      ++ (* s0 is a saddle point *)
        symmetry in e.
        rewrite <- signeq0_eqv in e.
        assert (sn<s0) as snlts0; try lra.
        destruct (Rlt_dec (IZR N) (-1));
          [|destruct (Rlt_dec 0 (IZR N))].
        +++ specialize (spiral_N_neg N r1) as s0lt0.
            change (s0 < 0) in s0lt0.
            exfalso.
            lra.
        +++ specialize (spiral_N_pos N r1) as zlts0.
            change (0 < s0) in zlts0.
            exfalso.
            clear n.
            generalize e.
            apply sf_2deriv_ne0.
            left.
            auto.
        +++ apply Rnot_lt_le in n.
            apply Rnot_lt_le in n0.
            assert (N = -1 \/ N = 0)%Z as neqm10. {
              apply le_IZR in n.
              apply le_IZR in n0.
              lia. }
            exfalso.
            apply (sf_2deriv_ne0 N).
            right; right; split.
            change (s0 <> 0).
            lra.
            destruct neqm10 as [neq | neq]; rewrite neq; auto.
            assumption.
      ++ (* s0 is a local maximum *)
        apply Rgt_lt in r1.
        (****)
        left.
        intros s [[sl |se] su].
        left.
        eapply (furthest_N_LHS).
        apply r1.
        change (sn <= sa).
        lra.
        assumption.
        change (s <= s0).
        lra.
        subst; right; reflexivity.

    + apply Rnot_lt_le in n.
      (* sn < [sa < s0 <= sb ]*)
      destruct (total_order_T 0 (Derive_n sf 2 s0));
        try destruct s.
      ++ right; right; left.
         intros s [sl su].
         unfold sf, safe_pt.

         rewrite <- (lin_pt_ineq).

         specialize (safe_orientation _ Nge0 r0) as [zltM [mxd myd]].
         set (M := sqrt (mx² + my²) *
                   / sqrt ((Derive (Fx a) (estp N))² +
                           (Derive (Fy a) (estp N))²)) in *.
         change (mx = M * Derive (Fx a) s0) in mxd.
         change (my = M * Derive (Fy a) s0) in myd.
         set (dFx := Derive (Fx a) s0) in *.
         set (dFy := Derive (Fy a) s0) in *.
         rewrite mxd, myd.
         apply (Rmult_le_reg_r (/ M)); try zltab.
         setr (dFx * (Fy a s - Fy a s0) - dFy * (Fx a s - Fx a s0)); try lra.
         setl 0; try lra.

         assert (0 <= s0) as zles0. {
           destruct Nge0 as [Ngt0 |Neq0].
           specialize (spiral_N_pos N Ngt0) as zlts.
           change (0 < s0) in zlts.
           left; assumption.
           specialize (spiral_N_pos1) as zeqs.
           apply eq_IZR in Neq0.
           simpl in zeqs.
           rewrite <- Neq0 in zeqs at 2.
           change (0 <= s0) in zeqs.
           assumption. }
         destruct zles0 as [zlts0 | zeqs0].
         +++ destruct (Rlt_dec s0 s) as [s0lts | s0ges].
             apply osc_circ_safe_R; try assumption.
             apply osc_circ_approx_le; lra.

             apply Rnot_lt_le in s0ges.
             rewrite (lin_pt_ineq).
             instantiate (1:=px).
             instantiate (2:=py).
             apply (Rmult_le_reg_l M); try lra.
             setl ((M * dFx) * (Fy a s0 - py) - (M * dFy) * (Fx a s0 - px)).
             setr ((M * dFx) * (Fy a s - py) - (M * dFy) * (Fx a s - px)).
             rewrite <- mxd, <- myd.
             change (sf s0 <= sf s).
             destruct s0ges as [slts0 | seqs0];
               try (rewrite seqs0; right; reflexivity).
             left.
             apply (closest_N_LHS _ _ _ r0).
             change (sn <= s); lra.
             assumption.
             change (s0 <= s0); right; reflexivity.

         +++ exfalso.
             symmetry in zeqs0.

             unfold s0 in zeqs0.
             rewrite <- (sf_2deriv_seq0_eqv N) in zeqs0.
             rewrite signeq0_eqv in zeqs0.
             change (Derive_n sf 2 s0 = 0) in zeqs0.
             rewrite zeqs0 in r0.
             clear - r0.
             lra.
             change (s0 = 0) in zeqs0.
             specialize (Z_dec 0 N) as [[zltn |zgtn]| zeq0].
             ++++ exfalso.
                  apply IZR_lt in zltn.
                  specialize (spiral_N_pos _ zltn) as zlts0.
                  change (0<s0)in zlts0.
                  lra.
             ++++ destruct (Z_lt_le_dec N (-1)%Z).
                  exfalso.
                  apply IZR_lt in l0.
                  specialize (spiral_N_neg _ l0) as zlts0.
                  change (s0 < 0)in zlts0.
                  lra.
                  assert (IZR N = -1) as neqn1.
                  apply IZR_eq.
                  lia.
                  right; assumption.
             ++++ left; rewrite <- zeq0; auto.

      ++ exfalso.
         symmetry in e.
         rewrite <- signeq0_eqv in e.
         assert ((IZR N = 0 \/ IZR N = -1) \/ IZR N > 0 \/ IZR N < -1) as nv. {
           assert (N = 0 \/ N = -1 \/ N > 0 \/ N < -1)%Z as nvz; try lia.
           destruct nvz as [nvz|nvz].
           left; left; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           left; right; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           right; left;
             apply Rlt_gt; apply IZR_lt; lia.
           right; right;
             apply IZR_lt; assumption. }
         destruct nv as [nv|nv].
         apply (sf_2deriv_seq0_eqv N) in e; try assumption.
         change (s0 = 0) in e.
         destruct nv as [nv|nv].
         assert (IZR N >= 0) as nge0; try lra.
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         simpl in s1rs2.
         apply eq_IZR in nv.
         assert (- N - 1 = N - 1)%Z as id; try lia.
         rewrite id in s1rs2.
         change (s0 = - sn) in s1rs2.
         rewrite e, <- Ropp_0 in s1rs2.
         apply Ropp_eq_compat in s1rs2.
         repeat rewrite Ropp_involutive in s1rs2.
         symmetry in s1rs2.
         lra.

         assert (IZR (- 1 - N) >= 0) as nge0;
           try (rewrite minus_IZR, nv; lra).
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         apply eq_IZR in nv.
         assert (- 1 - N = N + 1)%Z as id;
           try (rewrite nv; lia).
         assert (- (-1 - N) - 1 = N)%Z as id2;
           try (rewrite nv; lia).
         rewrite id2, id in s1rs2.
         simpl in s1rs2.
         change (s1 = -s0) in s1rs2.
         rewrite e, Ropp_0 in s1rs2.
         clear id id2 nge0.
         rewrite nv in Nge0.
         lra.

         generalize e.
         apply sf_2deriv_ne0.
         destruct nv as [nv|nv].
         left; assumption.
         right; left; assumption.
         
      ++ apply Rgt_lt in r0.
         (* sn < [sa < s0 <= sb ]*)
         (* but now s0 is a maximum *)
         (* rename everything *)

         assert (0 < Derive_n sf 2 s1) as r1. {
           assert (~ (IZR N = 0 /\ s0 = 0) /\
                   ~ (IZR N = -2 /\ s1 = 0)) as cd. {
             split.
             intros [neq0 s0eq0].
             unfold s0 in s0eq0, r0.
             rewrite <- (sf_2deriv_seq0_eqv N ltac:(lra)) in s0eq0.
             rewrite signeq0_eqv in s0eq0.
             rewrite s0eq0 in r0.
             lra.
             lra. }
           rewrite <- signeqm1_eqv in r0.
           rewrite <- signeq1_eqv.
           unfold s0 in r0.
           rewrite (sf_2deriv_sign N cd) in r0.
           apply Ropp_eq_compat in r0.
           rewrite Ropp_involutive in r0.
           change (sign (Derive_n sf 2 s1) = - -1) in r0.
           assert (- -1 = 1) as id; lra. }

         unfold sn, s0, s1 in *.
         clear sn s0 s1.
         set (snn := estp (N-1)) in *.
         set (sn := estp (N)) in *.
         set (s0 := estp (N+1)) in *.

         destruct (Rlt_dec sb s0).
         ++++ (* renamed s0 is a local minimum, not contained *)
           destruct (Rle_dec (sf sa) (sf sb)) as
               [ssalessb | ssagtssb].
           +++++ left.
           intros s [sl su].
           destruct sl as [sl | saeqs];
             try (rewrite saeqs; right; reflexivity).
           destruct su as [su | sbeqs];
             try (rewrite sbeqs; left; assumption).
           left.
           destruct (Rle_dec sn s).
           apply (Rle_lt_trans _ (sf sb)); try assumption.
           eapply furthest_N_RHS.
           apply r0.
           assumption.
           assumption.
           change (sb <= s0).
           left; assumption.
           apply Rnot_le_lt in n0.
           eapply furthest_N_LHS.
           apply r0.
           change (snn <= sa).
           lra.
           assumption.
           change (s <= sn).
           lra.
           rewrite sbeqs.
           assumption.
           +++++ apply Rnot_le_lt in ssagtssb.
           right; left.
           intros s [sl su].
           destruct sl as [sl | saeqs];
             try (rewrite <- saeqs; left; assumption).
           destruct su as [su | sbeqs];
             try (rewrite sbeqs; right; reflexivity).
           left.
           destruct (Rle_dec sn s).
           eapply furthest_N_RHS.
           apply r0.
           assumption.
           assumption.
           change (sb <= s0).
           left; assumption.

           apply Rnot_le_lt in n0.
           apply (Rle_lt_trans _ (sf sa)); try assumption.
           left; assumption.
           eapply furthest_N_LHS.
           apply r0.
           change (snn <= sa).
           lra.
           assumption.
           change (s <= sn).
           lra.
      ++++ apply Rnot_lt_le in n0.

           assert (forall s, sn <= s <= sb -> sf s0 <= sf s) as imd. {
             intros s [sl su].
             unfold sf, safe_pt.
             rewrite <- (lin_pt_ineq).
             assert (IZR (N + 1) >=0) as N1ge0;
               try (rewrite plus_IZR; lra).
             specialize (safe_orientation _ N1ge0 r1) as [zltM [mxd myd]].
             set (M := sqrt (mx² + my²) *
                       / sqrt ((Derive (Fx a) (estp (N+1)))² +
                               (Derive (Fy a) (estp (N+1)))²)) in *.
             change (mx = M * Derive (Fx a) s0) in mxd.
             change (my = M * Derive (Fy a) s0) in myd.
             set (dFx := Derive (Fx a) s0) in *.
             set (dFy := Derive (Fy a) s0) in *.
             rewrite mxd, myd.
             apply (Rmult_le_reg_r (/ M)); try zltab.
             setr (dFx * (Fy a s - Fy a s0) - dFy * (Fx a s - Fx a s0)); try lra.
             setl 0; try lra.
             
             assert (0 < s0) as zlts0. {
               apply (spiral_N_pos (N+1)).
               rewrite plus_IZR.
               lra. }
             
             destruct (Rlt_dec s0 s) as [s0lts | s0ges].
             apply osc_circ_safe_R; try assumption.
             apply osc_circ_approx_le; lra.
             
             apply Rnot_lt_le in s0ges.
             rewrite (lin_pt_ineq).
             instantiate (1:=px).
             instantiate (2:=py).
             apply (Rmult_le_reg_l M); try lra.
             setl ((M * dFx) * (Fy a s0 - py) - (M * dFy) * (Fx a s0 - px)).
             setr ((M * dFx) * (Fy a s - py) - (M * dFy) * (Fx a s - px)).
             rewrite <- mxd, <- myd.
             change (sf s0 <= sf s).
             destruct s0ges as [slts0 | seqs0];
               try (rewrite seqs0; right; reflexivity).
             left.
             apply (closest_N_LHS _ _ _ r1).
             assert (N+1-1 = N)%Z as id; try lia.
             rewrite id; clear id.
             change (sn <= s).
             assumption.
             assumption.
             change (s0 <= s0); right; reflexivity. }

           destruct (Rle_dec (sf sa) (sf s0)) as [sfalesf0|sfalesf0].
           - left.
             intros s [sl sh].
             destruct (Rlt_dec s sn) as [sltsn |sgesn].
             destruct sl as [sl | se];
               try (rewrite se; right; reflexivity).
             left.
             eapply furthest_N_LHS.
             apply r0.
             change (snn <= sa).
             lra.
             assumption.
             change (s <= sn).
             lra.
             apply Rnot_lt_le in sgesn.
             apply (Rle_trans _ (sf s0)); try assumption.
             apply imd; try lra.

           - apply Rnot_le_lt in sfalesf0.
             right; right; right.
             intros s [sl sh].
             destruct (Rlt_dec s sn) as [sltsn |sgesn].
             left.
             apply (Rlt_le_trans _ (sf sa)); try assumption.
             destruct sl as [sl | se];
               try (rewrite se; right; reflexivity).
             left.
             eapply furthest_N_LHS.
             apply r0.
             change (snn <= sa).
             lra.
             assumption.
             change (s <= sn).
             lra.
             apply Rnot_lt_le in sgesn.
             apply imd; try lra.
  Qed.

  Lemma stca1 : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 ->
      sn < sa <= s0 -> 
      0 <= sa ->
      sb < s0 -> 
      (forall s, sa <= s <= sb -> sf sa <= sf s) \/
      (forall s, sa <= s <= sb -> sf sb <= sf s).
  Proof.
    intros *.
    intros s1 Nge0 [snltsa sales0] zlesa sblts0.
    destruct (Rlt_dec sa sb).
    2 : { left.
          intros r [p q].
          apply Rnot_lt_le in n.
          destruct n.
          exfalso; lra.
          subst.
          assert (r = sa). lra.
          subst.
          right; reflexivity. }

    
    + destruct sales0; try lra.
      (* sn < [sa < sb] < s0 *)
      destruct (total_order_T 0 (Derive_n sf 2 s0));
        try destruct s.
      ++ (* s0 is a local minimum *)
        right.
        intros s [sl [su| se]].
        left.
        eapply (closest_N_LHS s sb).
        apply r0.
        change (sn <= s).
        lra.
        assumption.
        change (sb <= s0).
        left; assumption.
        subst; right; reflexivity.
      ++ (* s0 is a saddle point *)
        symmetry in e.
        rewrite <- signeq0_eqv in e.
        assert (sn<s0) as snlts0; try lra.
        destruct (Rlt_dec (IZR N) (-1));
          [|destruct (Rlt_dec 0 (IZR N))].
        +++ specialize (spiral_N_neg N r0) as s0lt0.
            change (s0 < 0) in s0lt0.
            exfalso.
            lra.
        +++ specialize (spiral_N_pos N r0) as zlts0.
            change (0 < s0) in zlts0.
            exfalso.
            clear n.
            generalize e.
            apply sf_2deriv_ne0.
            left.
            auto.
        +++ apply Rnot_lt_le in n.
            apply Rnot_lt_le in n0.
            assert (N = -1 \/ N = 0)%Z as neqm10. {
              apply le_IZR in n.
              apply le_IZR in n0.
              lia. }
            exfalso.
            apply (sf_2deriv_ne0 N).
            right; right; split.
            change (s0 <> 0).
            lra.
            destruct neqm10 as [neq | neq]; rewrite neq; auto.
            assumption.
      ++ (* s0 is a local maximum *)
        apply Rgt_lt in r0.
        (****)
        left.
        intros s [[sl |se] su].
        left.
        eapply (furthest_N_LHS).
        apply r0.
        change (sn <= sa).
        lra.
        assumption.
        change (s <= s0).
        lra.
        subst; right; reflexivity.
  Qed.

  Lemma stca2 : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 ->
      sn < sa <= s0 -> 
     0 <= sa ->
      s0 <= sb -> 
      sb < s1 -> 
      (forall s, sa <= s <= sb -> sf sa <= sf s) \/
      (forall s, sa <= s <= sb -> sf sb <= sf s) \/
      (forall s, sa <= s <= sb -> sf s0 <= sf s).
  Proof.
    intros *.
    intros Nge0 [snltsa sales0] zlesa sllesb sblts1.
    destruct (Rlt_dec sa sb).
    2 : { left.
          intros r [p q].
          apply Rnot_lt_le in n.
          destruct n.
          exfalso; lra.
          subst.
          assert (r = sa). lra.
          subst.
          right; reflexivity. }
  
    + (* sn < [sa < s0 <= sb ]*)
      destruct (total_order_T 0 (Derive_n sf 2 s0));
        try destruct s.
      ++ right; right.
         intros s [sl su].
         unfold sf, safe_pt.

         rewrite <- (lin_pt_ineq).

         specialize (safe_orientation _ Nge0 r0) as [zltM [mxd myd]].
         set (M := sqrt (mx² + my²) *
                   / sqrt ((Derive (Fx a) (estp N))² +
                           (Derive (Fy a) (estp N))²)) in *.
         change (mx = M * Derive (Fx a) s0) in mxd.
         change (my = M * Derive (Fy a) s0) in myd.
         set (dFx := Derive (Fx a) s0) in *.
         set (dFy := Derive (Fy a) s0) in *.
         rewrite mxd, myd.
         apply (Rmult_le_reg_r (/ M)); try zltab.
         setr (dFx * (Fy a s - Fy a s0) - dFy * (Fx a s - Fx a s0)); try lra.
         setl 0; try lra.

         assert (0 <= s0) as zles0. {
           destruct Nge0 as [Ngt0 |Neq0].
           specialize (spiral_N_pos N Ngt0) as zlts.
           change (0 < s0) in zlts.
           left; assumption.
           specialize (spiral_N_pos1) as zeqs.
           apply eq_IZR in Neq0.
           simpl in zeqs.
           rewrite <- Neq0 in zeqs at 2.
           change (0 <= s0) in zeqs.
           assumption. }
         destruct zles0 as [zlts0 | zeqs0].
         +++ destruct (Rlt_dec s0 s) as [s0lts | s0ges].
             apply osc_circ_safe_R; try assumption.
             apply osc_circ_approx_le; lra.

             apply Rnot_lt_le in s0ges.
             rewrite (lin_pt_ineq).
             instantiate (1:=px).
             instantiate (2:=py).
             apply (Rmult_le_reg_l M); try lra.
             setl ((M * dFx) * (Fy a s0 - py) - (M * dFy) * (Fx a s0 - px)).
             setr ((M * dFx) * (Fy a s - py) - (M * dFy) * (Fx a s - px)).
             rewrite <- mxd, <- myd.
             change (sf s0 <= sf s).
             destruct s0ges as [slts0 | seqs0];
               try (rewrite seqs0; right; reflexivity).
             left.
             apply (closest_N_LHS _ _ _ r0).
             change (sn <= s); lra.
             assumption.
             change (s0 <= s0); right; reflexivity.

         +++ exfalso.
             symmetry in zeqs0.

             unfold s0 in zeqs0.
             rewrite <- (sf_2deriv_seq0_eqv N) in zeqs0.
             rewrite signeq0_eqv in zeqs0.
             change (Derive_n sf 2 s0 = 0) in zeqs0.
             rewrite zeqs0 in r0.
             clear - r0.
             lra.
             change (s0 = 0) in zeqs0.
             specialize (Z_dec 0 N) as [[zltn |zgtn]| zeq0].
             ++++ exfalso.
                  apply IZR_lt in zltn.
                  specialize (spiral_N_pos _ zltn) as zlts0.
                  change (0<s0)in zlts0.
                  lra.
             ++++ destruct (Z_lt_le_dec N (-1)%Z).
                  exfalso.
                  apply IZR_lt in l0.
                  specialize (spiral_N_neg _ l0) as zlts0.
                  change (s0 < 0)in zlts0.
                  lra.
                  assert (IZR N = -1) as neqn1.
                  apply IZR_eq.
                  lia.
                  right; assumption.
             ++++ left; rewrite <- zeq0; auto.

      ++ exfalso.
         symmetry in e.
         rewrite <- signeq0_eqv in e.
         assert ((IZR N = 0 \/ IZR N = -1) \/ IZR N > 0 \/ IZR N < -1) as nv. {
           assert (N = 0 \/ N = -1 \/ N > 0 \/ N < -1)%Z as nvz; try lia.
           destruct nvz as [nvz|nvz].
           left; left; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           left; right; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           right; left;
             apply Rlt_gt; apply IZR_lt; lia.
           right; right;
             apply IZR_lt; assumption. }
         destruct nv as [nv|nv].
         apply (sf_2deriv_seq0_eqv N) in e; try assumption.
         change (s0 = 0) in e.
         destruct nv as [nv|nv].
         assert (IZR N >= 0) as nge0; try lra.
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         simpl in s1rs2.
         apply eq_IZR in nv.
         assert (- N - 1 = N - 1)%Z as id; try lia.
         rewrite id in s1rs2.
         change (s0 = - sn) in s1rs2.
         rewrite e, <- Ropp_0 in s1rs2.
         apply Ropp_eq_compat in s1rs2.
         repeat rewrite Ropp_involutive in s1rs2.
         symmetry in s1rs2.
         lra.

         assert (IZR (- 1 - N) >= 0) as nge0;
           try (rewrite minus_IZR, nv; lra).
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         apply eq_IZR in nv.
         assert (- 1 - N = N + 1)%Z as id;
           try (rewrite nv; lia).
         assert (- (-1 - N) - 1 = N)%Z as id2;
           try (rewrite nv; lia).
         rewrite id2, id in s1rs2.
         simpl in s1rs2.
         change (s1 = -s0) in s1rs2.
         rewrite e, Ropp_0 in s1rs2.
         clear id id2 nge0.
         rewrite nv in Nge0.
         lra.

         generalize e.
         apply sf_2deriv_ne0.
         destruct nv as [nv|nv].
         left; assumption.
         right; left; assumption.
         
      ++ apply Rgt_lt in r0.
         (* sn < [sa < s0 <= sb ]*)
         (* but now s0 is a maximum *)
         (* rename everything *)

         assert (0 < Derive_n sf 2 s1) as r1. {
           assert (~ (IZR N = 0 /\ s0 = 0) /\
                   ~ (IZR N = -2 /\ s1 = 0)) as cd. {
             split.
             intros [neq0 s0eq0].
             unfold s0 in s0eq0, r0.
             rewrite <- (sf_2deriv_seq0_eqv N ltac:(lra)) in s0eq0.
             rewrite signeq0_eqv in s0eq0.
             rewrite s0eq0 in r0.
             lra.
             lra. }
           rewrite <- signeqm1_eqv in r0.
           rewrite <- signeq1_eqv.
           unfold s0 in r0.
           rewrite (sf_2deriv_sign N cd) in r0.
           apply Ropp_eq_compat in r0.
           rewrite Ropp_involutive in r0.
           change (sign (Derive_n sf 2 s1) = - -1) in r0.
           assert (- -1 = 1) as id; lra. }

         unfold sn, s0, s1 in *.
         clear sn s0 s1.
         set (snn := estp (N-1)) in *.
         set (sn := estp (N)) in *.
         set (s0 := estp (N+1)) in *.

         ++++ (* renamed s0 is a local minimum, not contained *)
           destruct (Rle_dec (sf sa) (sf sb)) as
               [ssalessb | ssagtssb].
           +++++ left.
           intros s [sl su].
           destruct sl as [sl | saeqs];
             try (rewrite saeqs; right; reflexivity).
           destruct su as [su | sbeqs];
             try (rewrite sbeqs; left; assumption).
           left.
           destruct (Rle_dec sn s).
           apply (Rle_lt_trans _ (sf sb)); try assumption.
           eapply furthest_N_RHS.
           apply r0.
           assumption.
           assumption.
           change (sb <= s0).
           left; assumption.
           apply Rnot_le_lt in n.
           eapply furthest_N_LHS.
           apply r0.
           change (snn <= sa).
           lra.
           assumption.
           change (s <= sn).
           lra.
           rewrite sbeqs.
           assumption.
           +++++ apply Rnot_le_lt in ssagtssb.
           right; left.
           intros s [sl su].
           destruct sl as [sl | saeqs];
             try (rewrite <- saeqs; left; assumption).
           destruct su as [su | sbeqs];
             try (rewrite sbeqs; right; reflexivity).
           left.
           destruct (Rle_dec sn s).
           eapply furthest_N_RHS.
           apply r0.
           assumption.
           assumption.
           change (sb <= s0).
           left; assumption.

           apply Rnot_le_lt in n.
           apply (Rle_lt_trans _ (sf sa)); try assumption.
           left; assumption.
           eapply furthest_N_LHS.
           apply r0.
           change (snn <= sa).
           lra.
           assumption.
           change (s <= sn).
           lra.
  Qed.


  Lemma stca3 : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 ->
      sn < sa <= s0 -> 
      0 <= sa ->
      s0 <= sb -> 
      s1 <= sb -> 
      (forall s, sa <= s <= sb -> sf sa <= sf s) \/
      (forall s, sa <= s <= sb -> sf sb <= sf s) \/
      (forall s, sa <= s <= sb -> sf s0 <= sf s) \/
      (forall s, sa <= s <= sb -> sf s1 <= sf s).
  Proof.
    intros *.
    intros Nge0 [snltsa sales0] zlesa s0lesb s1lesb.
    destruct (Rlt_dec sa sb).
    2 : { left.
          intros r [p q].
          apply Rnot_lt_le in n.
          destruct n.
          exfalso; lra.
          subst.
          assert (r = sa). lra.
          subst.
          right; reflexivity. }
  
    + (* sn < [sa < s0 <= sb ]*)
      destruct (total_order_T 0 (Derive_n sf 2 s0));
        try destruct s.
      ++ right; right; left.
         intros s [sl su].
         unfold sf, safe_pt.

         rewrite <- (lin_pt_ineq).

         specialize (safe_orientation _ Nge0 r0) as [zltM [mxd myd]].
         set (M := sqrt (mx² + my²) *
                   / sqrt ((Derive (Fx a) (estp N))² +
                           (Derive (Fy a) (estp N))²)) in *.
         change (mx = M * Derive (Fx a) s0) in mxd.
         change (my = M * Derive (Fy a) s0) in myd.
         set (dFx := Derive (Fx a) s0) in *.
         set (dFy := Derive (Fy a) s0) in *.
         rewrite mxd, myd.
         apply (Rmult_le_reg_r (/ M)); try zltab.
         setr (dFx * (Fy a s - Fy a s0) - dFy * (Fx a s - Fx a s0)); try lra.
         setl 0; try lra.

         assert (0 <= s0) as zles0. {
           destruct Nge0 as [Ngt0 |Neq0].
           specialize (spiral_N_pos N Ngt0) as zlts.
           change (0 < s0) in zlts.
           left; assumption.
           specialize (spiral_N_pos1) as zeqs.
           apply eq_IZR in Neq0.
           simpl in zeqs.
           rewrite <- Neq0 in zeqs at 2.
           change (0 <= s0) in zeqs.
           assumption. }
         destruct zles0 as [zlts0 | zeqs0].
         +++ destruct (Rlt_dec s0 s) as [s0lts | s0ges].
             apply osc_circ_safe_R; try assumption.
             apply osc_circ_approx_le; lra.

             apply Rnot_lt_le in s0ges.
             rewrite (lin_pt_ineq).
             instantiate (1:=px).
             instantiate (2:=py).
             apply (Rmult_le_reg_l M); try lra.
             setl ((M * dFx) * (Fy a s0 - py) - (M * dFy) * (Fx a s0 - px)).
             setr ((M * dFx) * (Fy a s - py) - (M * dFy) * (Fx a s - px)).
             rewrite <- mxd, <- myd.
             change (sf s0 <= sf s).
             destruct s0ges as [slts0 | seqs0];
               try (rewrite seqs0; right; reflexivity).
             left.
             apply (closest_N_LHS _ _ _ r0).
             change (sn <= s); lra.
             assumption.
             change (s0 <= s0); right; reflexivity.

         +++ exfalso.
             symmetry in zeqs0.

             unfold s0 in zeqs0.
             rewrite <- (sf_2deriv_seq0_eqv N) in zeqs0.
             rewrite signeq0_eqv in zeqs0.
             change (Derive_n sf 2 s0 = 0) in zeqs0.
             rewrite zeqs0 in r0.
             clear - r0.
             lra.
             change (s0 = 0) in zeqs0.
             specialize (Z_dec 0 N) as [[zltn |zgtn]| zeq0].
             ++++ exfalso.
                  apply IZR_lt in zltn.
                  specialize (spiral_N_pos _ zltn) as zlts0.
                  change (0<s0)in zlts0.
                  lra.
             ++++ destruct (Z_lt_le_dec N (-1)%Z).
                  exfalso.
                  apply IZR_lt in l0.
                  specialize (spiral_N_neg _ l0) as zlts0.
                  change (s0 < 0)in zlts0.
                  lra.
                  assert (IZR N = -1) as neqn1.
                  apply IZR_eq.
                  lia.
                  right; assumption.
             ++++ left; rewrite <- zeq0; auto.

      ++ exfalso.
         symmetry in e.
         rewrite <- signeq0_eqv in e.
         assert ((IZR N = 0 \/ IZR N = -1) \/ IZR N > 0 \/ IZR N < -1) as nv. {
           assert (N = 0 \/ N = -1 \/ N > 0 \/ N < -1)%Z as nvz; try lia.
           destruct nvz as [nvz|nvz].
           left; left; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           left; right; apply IZR_eq; assumption.
           destruct nvz as [nvz|nvz].
           right; left;
             apply Rlt_gt; apply IZR_lt; lia.
           right; right;
             apply IZR_lt; assumption. }
         destruct nv as [nv|nv].
         apply (sf_2deriv_seq0_eqv N) in e; try assumption.
         change (s0 = 0) in e.
         destruct nv as [nv|nv].
         assert (IZR N >= 0) as nge0; try lra.
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         simpl in s1rs2.
         apply eq_IZR in nv.
         assert (- N - 1 = N - 1)%Z as id; try lia.
         rewrite id in s1rs2.
         change (s0 = - sn) in s1rs2.
         rewrite e, <- Ropp_0 in s1rs2.
         apply Ropp_eq_compat in s1rs2.
         repeat rewrite Ropp_involutive in s1rs2.
         symmetry in s1rs2.
         lra.

         assert (IZR (- 1 - N) >= 0) as nge0;
           try (rewrite minus_IZR, nv; lra).
         specialize (euler_tan_pt_symm _ nge0) as s1rs2.
         apply eq_IZR in nv.
         assert (- 1 - N = N + 1)%Z as id;
           try (rewrite nv; lia).
         assert (- (-1 - N) - 1 = N)%Z as id2;
           try (rewrite nv; lia).
         rewrite id2, id in s1rs2.
         simpl in s1rs2.
         change (s1 = -s0) in s1rs2.
         rewrite e, Ropp_0 in s1rs2.
         clear id id2 nge0.
         rewrite nv in Nge0.
         lra.

         generalize e.
         apply sf_2deriv_ne0.
         destruct nv as [nv|nv].
         left; assumption.
         right; left; assumption.
         
      ++ apply Rgt_lt in r0.
         (* sn < [sa < s0 <= sb ]*)
         (* but now s0 is a maximum *)
         (* rename everything *)

         assert (0 < Derive_n sf 2 s1) as r1. {
           assert (~ (IZR N = 0 /\ s0 = 0) /\
                   ~ (IZR N = -2 /\ s1 = 0)) as cd. {
             split.
             intros [neq0 s0eq0].
             unfold s0 in s0eq0, r0.
             rewrite <- (sf_2deriv_seq0_eqv N ltac:(lra)) in s0eq0.
             rewrite signeq0_eqv in s0eq0.
             rewrite s0eq0 in r0.
             lra.
             lra. }
           rewrite <- signeqm1_eqv in r0.
           rewrite <- signeq1_eqv.
           unfold s0 in r0.
           rewrite (sf_2deriv_sign N cd) in r0.
           apply Ropp_eq_compat in r0.
           rewrite Ropp_involutive in r0.
           change (sign (Derive_n sf 2 s1) = - -1) in r0.
           assert (- -1 = 1) as id; lra. }

         unfold sn, s0, s1 in *.
         clear sn s0 s1.
         set (snn := estp (N-1)) in *.
         set (sn := estp (N)) in *.
         set (s0 := estp (N+1)) in *.

      ++++ assert (forall s, sn <= s <= sb -> sf s0 <= sf s) as imd. {
             intros s [sl su].
             unfold sf, safe_pt.
             rewrite <- (lin_pt_ineq).
             assert (IZR (N + 1) >=0) as N1ge0;
               try (rewrite plus_IZR; lra).
             specialize (safe_orientation _ N1ge0 r1) as [zltM [mxd myd]].
             set (M := sqrt (mx² + my²) *
                       / sqrt ((Derive (Fx a) (estp (N+1)))² +
                               (Derive (Fy a) (estp (N+1)))²)) in *.
             change (mx = M * Derive (Fx a) s0) in mxd.
             change (my = M * Derive (Fy a) s0) in myd.
             set (dFx := Derive (Fx a) s0) in *.
             set (dFy := Derive (Fy a) s0) in *.
             rewrite mxd, myd.
             apply (Rmult_le_reg_r (/ M)); try zltab.
             setr (dFx * (Fy a s - Fy a s0) - dFy * (Fx a s - Fx a s0)); try lra.
             setl 0; try lra.
             
             assert (0 < s0) as zlts0. {
               apply (spiral_N_pos (N+1)).
               rewrite plus_IZR.
               lra. }
             
             destruct (Rlt_dec s0 s) as [s0lts | s0ges].
             apply osc_circ_safe_R; try assumption.
             apply osc_circ_approx_le; lra.
             
             apply Rnot_lt_le in s0ges.
             rewrite (lin_pt_ineq).
             instantiate (1:=px).
             instantiate (2:=py).
             apply (Rmult_le_reg_l M); try lra.
             setl ((M * dFx) * (Fy a s0 - py) - (M * dFy) * (Fx a s0 - px)).
             setr ((M * dFx) * (Fy a s - py) - (M * dFy) * (Fx a s - px)).
             rewrite <- mxd, <- myd.
             change (sf s0 <= sf s).
             destruct s0ges as [slts0 | seqs0];
               try (rewrite seqs0; right; reflexivity).
             left.
             apply (closest_N_LHS _ _ _ r1).
             assert (N+1-1 = N)%Z as id; try lia.
             rewrite id; clear id.
             change (sn <= s).
             assumption.
             assumption.
             change (s0 <= s0); right; reflexivity. }

           destruct (Rle_dec (sf sa) (sf s0)) as [sfalesf0|sfalesf0].
           - left.
             intros s [sl sh].
             destruct (Rlt_dec s sn) as [sltsn |sgesn].
             destruct sl as [sl | se];
               try (rewrite se; right; reflexivity).
             left.
             eapply furthest_N_LHS.
             apply r0.
             change (snn <= sa).
             lra.
             assumption.
             change (s <= sn).
             lra.
             apply Rnot_lt_le in sgesn.
             apply (Rle_trans _ (sf s0)); try assumption.
             apply imd; try lra.

           - apply Rnot_le_lt in sfalesf0.
             right; right; right.
             intros s [sl sh].
             destruct (Rlt_dec s sn) as [sltsn |sgesn].
             left.
             apply (Rlt_le_trans _ (sf sa)); try assumption.
             destruct sl as [sl | se];
               try (rewrite se; right; reflexivity).
             left.
             eapply furthest_N_LHS.
             apply r0.
             change (snn <= sa).
             lra.
             assumption.
             change (s <= sn).
             lra.
             apply Rnot_lt_le in sgesn.
             apply imd; try lra.
  Qed.

  (* end hide *)
(** These lemmas collectively express Theorem 4 from the paper,
    various aspects of our overall safety guarantee. The last,
    spiral_tangent_closest_approach, summarizes the overall
    guarantee. The three prevous lemmas provide tighter bounds that
    apply to the different geometries: stca1s corresponds with
    Fig. 6d; stca2s corresponds with Fig. 6a and 6c; and stca3s
    corresponds with Fig. 6b. *)

  Definition min L := hd 0 (sort L).

  Lemma stca1s : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 -> sn < sa <= s0 -> 0 <= sa -> sb < s0 -> 
      (forall s, sa <= s <= sb -> min [sf sa; sf sb] <= sf s).
  Proof.
    intros *.
    intros s1 nge0 sarng zlesa sbltso s srng.
    unfold min.
    set (cp := [sf sa; sf sb]) in *.
    specialize (ROrd.leb_trans) as tleb.
    specialize (StronglySorted_sort cp tleb) as ssd.
    specialize (Permuted_sort cp) as pm.
    assert ((fun x1 y : R =>
               if total_order_T x1 y then true else false) = ROrd.leb) as id. {
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      reflexivity. }
    rewrite id in ssd.
    clear id.
    change (StronglySorted (fun x y : R => ROrd.leb x y) (sort cp)) in ssd.
    inversion ssd as [cpd | h b sst fa sd].
    exfalso.
    apply Permutation_length in pm.
    rewrite <- cpd in pm.
    unfold cp in pm.
    inversion pm.
    simpl.
    rewrite <- sd in ssd.
    specialize (stca1 _ _ _ nge0 sarng zlesa sbltso) as hlpr.
    destruct hlpr as [sac |sbc].
    + specialize (sac s srng).
      set (si := sa) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (sbc s srng).
      set (si := sb) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
  Qed.

  Lemma stca2s : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 -> sn < sa <= s0 -> 0 <= sa -> s0 <= sb -> sb < s1 -> 
      (forall s, sa <= s <= sb -> min [sf sa; sf sb; sf s0] <= sf s).
  Proof.
    intros *.
    intros nge0 sarng zlesa soltsb sblts1 s srng.
    unfold min.
    set (cp := [sf sa; sf sb; sf s0]) in *.
    specialize (ROrd.leb_trans) as tleb.
    specialize (StronglySorted_sort cp tleb) as ssd.
    specialize (Permuted_sort cp) as pm.
    assert ((fun x1 y : R =>
               if total_order_T x1 y then true else false) = ROrd.leb) as id. {
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      reflexivity. }
    rewrite id in ssd.
    clear id.
    change (StronglySorted (fun x y : R => ROrd.leb x y) (sort cp)) in ssd.
    inversion ssd as [cpd | h b sst fa sd].
    exfalso.
    apply Permutation_length in pm.
    rewrite <- cpd in pm.
    unfold cp in pm.
    inversion pm.
    simpl.
    rewrite <- sd in ssd.
    specialize (stca2 _ _ _ nge0 sarng zlesa soltsb sblts1) as hlpr.
    destruct hlpr as [sac |[sbc|soc]].
    + specialize (sac s srng).
      set (si := sa) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (sbc s srng).
      set (si := sb) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (soc s srng).
      set (si := s0) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
  Qed.

  Lemma stca3s : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 -> sn < sa <= s0 -> 0 <= sa -> s0 <= sb -> s1 <= sb -> 
      (forall s, sa <= s <= sb -> min [sf sa; sf sb; sf s0; sf s1] <= sf s).
  Proof.
    intros *.
    intros nge0 sarng zlesa solesb s1lesb s srng.
    unfold min.
    set (cp := [sf sa; sf sb; sf s0; sf s1]) in *.
    specialize (ROrd.leb_trans) as tleb.
    specialize (StronglySorted_sort cp tleb) as ssd.
    specialize (Permuted_sort cp) as pm.
    assert ((fun x1 y : R =>
               if total_order_T x1 y then true else false) = ROrd.leb) as id. {
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      reflexivity. }
    rewrite id in ssd.
    clear id.
    change (StronglySorted (fun x y : R => ROrd.leb x y) (sort cp)) in ssd.
    inversion ssd as [cpd | h b sst fa sd].
    exfalso.
    apply Permutation_length in pm.
    rewrite <- cpd in pm.
    unfold cp in pm.
    inversion pm.
    simpl.
    rewrite <- sd in ssd.
    specialize (stca3 _ _ _ nge0 sarng zlesa solesb s1lesb) as hlpr.
    destruct hlpr as [sac |[sbc|[soc|s1c]]].
    + specialize (sac s srng).
      set (si := sa) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (sbc s srng).
      set (si := sb) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (soc s srng).
      set (si := s0) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (s1c s srng).
      set (si := s1) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; right; right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
  Qed.

  Theorem spiral_tangent_closest_approach : forall sa sb N,
      let sn := estp (N-1) in
      let s0 := estp N in
      let s1 := estp (N+1) in
      IZR N >= 0 -> sn < sa <= s0 -> 0 <= sa ->
      (forall s, sa <= s <= sb -> min [sf sa; sf sb; sf s0; sf s1] <= sf s).
  Proof.
    intros *.
    intros nge0 sarng zlesa s srng.
    unfold min.
    set (cp := [sf sa; sf sb; sf s0; sf s1]) in *.
    specialize (ROrd.leb_trans) as tleb.
    specialize (StronglySorted_sort cp tleb) as ssd.
    specialize (Permuted_sort cp) as pm.
    assert ((fun x1 y : R =>
               if total_order_T x1 y then true else false) = ROrd.leb) as id. {
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      reflexivity. }
    rewrite id in ssd.
    clear id.
    change (StronglySorted (fun x y : R => ROrd.leb x y) (sort cp)) in ssd.
    inversion ssd as [cpd | h b sst fa sd].
    exfalso.
    apply Permutation_length in pm.
    rewrite <- cpd in pm.
    unfold cp in pm.
    inversion pm.
    simpl.
    rewrite <- sd in ssd.
    specialize (spiral_tangent_closest_approach_helper
                  sa sb _ nge0 sarng zlesa) as hlpr.
    destruct hlpr as [sac |[sbc|[soc|s1c]]].
    + specialize (sac s srng).
      set (si := sa) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (sbc s srng).
      set (si := sb) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (soc s srng).
      set (si := s0) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
    + specialize (s1c s srng).
      set (si := s1) in *.
      assert (In (sf si) cp) as insa. {
        unfold cp.
        simpl.
        right; right; right; left; auto. }
      apply (Permutation_in (sf si)) in pm; try assumption.
      rewrite <- sd in pm.
      unfold In in pm.
      fold (In (sf si) b) in pm.
      destruct pm as [hd |bd].
      rewrite hd; auto.
      rewrite Forall_forall in fa.
      specialize (fa (sf si) bd).
      unfold ROrd.leb in fa.
      destruct total_order_T in fa.
      assert (h <= sf si) as tr. {
        destruct s2.
        left; assumption.
        rewrite e.
        right; reflexivity. }
      apply (Rle_trans _ (sf si)); assumption.
      inversion fa.
  Qed.

End egeof.

(* To see axioms, use, e.g. *)
(* Print Assumptions stca3s. *)

Require Extraction.
Extraction Language OCaml.
Extraction euler_spiral_tangent_pt.
