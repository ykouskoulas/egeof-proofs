# Predictive selection of trajectories for autonomous, fast-moving
  aircraft for guaranteed avoidance of collision with geofence
  boundaries

## What is this?

This repostory contains a peer-reviewed publication describing a new
collision avoidance algorithm that accounts for realistic turning
dynamics to help fast moving fixed-wing aircraft avoid virtual
walls. The paper includes flight testing results, and the repository
includes a series of machine checked proofs that guarantee the safety
and correctness of the approach.

## Documentation

The paper is titled

*"Good Fences Make Good Neighbors: Using Formally Verified Safe
Trajectories to Design a Predictive Geofence Algorithm"*

and was presented at the NASA Formal Methods Conference in 2021. 

Abstract:

For AI-controlled mobile platforms, avoiding collisions with
walls and boundaries is an important safety requirement. This is a prob-
lem especially for fast-moving aerial vehicles, such as ﬁxed-wing aircraft,
that cannot be brought to a stop in an emergency. To enable geographic
conﬁnement of such AI-controlled vehicles, we present a formally veriﬁed
algorithm for predicting geofence violations and selecting a safe maneu-
ver that will keep the vehicle within the designated operations area. The
algorithm is based on a higher-order dynamics model that generalizes
circular turns using linearly changing centripetal acceleration and allows
handling of uncertainty in model parameters. The proposed algorithm
was implemented along with extensions to handle non-determinism, and
ﬂight-tested on an autonomous aircraft.

## Documentation

In the doc folder

## Dependencies

Proofs were developed with the Coq proof assistant and the Coquelicot
real library.

One reliable way to get set up to check these proofs is to use the
opam package manager.

First use the package manager on your system to install opam, e.g.

``
$ sudo apt-get install opam
```

In some environments (e.g. if opam is already on your system)
it might be necessary to 

```
$ opam init

$ opam init env
```

Then you can install coq and coquelicot, letting opam handle
dependencies:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released

$ opam install coq

$ opam install coq-coquelicot
```

## To build and check documentation, proofs, and generate certified code

The following commands check the proofs, extracts the core function
that analyzes safety, and generates documentation suitable for use
during certification:

```
$ date
Thu Apr  9 01:22:07 EDT 2020

$ coqtop --version
The Coq Proof Assistant, version 8.10.2 (December 2019)
compiled on Dec 8 2019 9:00:07 with OCaml 4.07.1

$ time make
coqc util.v
coqc atan2.v
coqdoc -g -utf8 atan2.v
coqc egeof.v
File "./egeof.v", line 12616, characters 0-35:
Warning: The extraction is currently set to bypass opacity, the following
opaque constant bodies have been accessed
: Rsqrt_exists exists_atan_in_frame Req_EM_T Rcase_abs AlembertC3_step2
  Rlt_dec Rle_dec Rge_dec IVT IVT_interv dicho_up_cv exist_cos PI_2_aux
  decreasing_cv growing_cv frame_tan IVT_cor pre_atan.
 [extraction-opaque-accessed,extraction]
File "./egeof.v", line 12616, characters 0-35:
Warning: The following axioms must be realized in the extracted
code: total_order_T completeness Rplus Rmult Ropp Rinv R1 R0 R.
 [extraction-axiom-to-realize,extraction]
(** val euler_spiral_tangent_pt : r -> r -> r -> z -> r **)

let euler_spiral_tangent_pt mx my a n =
  let la = l a in
  let _UU03c6_ =
    match req_EM_T (iZR Z0) mx with
    | Left -> rdiv pI (iZR (Zpos (XO XH)))
    | Right -> atan (rdiv my mx)
  in
  (match rge_dec (iZR n) (iZR Z0) with
   | Left ->
     (match rlt_dec _UU03c6_ (iZR Z0) with
      | Left ->
        rmult la
          (sqrt
            (rmult (rdiv (iZR (Zpos (XO XH))) pI)
              (rplus (rplus _UU03c6_ pI) (rmult (iZR n) pI))))
      | Right ->
        rmult la
          (sqrt
            (rmult (rdiv (iZR (Zpos (XO XH))) pI)
              (rplus _UU03c6_ (rmult (iZR n) pI)))))
   | Right ->
     (match rlt_dec _UU03c6_ (iZR Z0) with
      | Left ->
        rmult (ropp la)
          (sqrt
            (rmult (rdiv (iZR (Zpos (XO XH))) pI)
              (rminus (rplus _UU03c6_ pI)
                (rmult (iZR (Z.add n (Zpos XH))) pI))))
      | Right ->
        rmult (ropp la)
          (sqrt
            (rmult (rdiv (iZR (Zpos (XO XH))) pI)
              (rminus _UU03c6_ (rmult (iZR (Z.add n (Zpos XH))) pI))))))
coqdoc -g -utf8 egeof.v

real	0m46.133s
user	0m43.950s
sys	0m1.366s
```

You can Print Assumptions to see axioms of the development.

## About me

Work/projects: www.linkedin.com/in/ykouskoulas
Publications:  orcid.org/0000-0001-7347-7473
This repo:     github.com/ykouskoulas/egeof-proofs
