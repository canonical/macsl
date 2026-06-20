(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C) Inria - CNRS - Paris-Sud University                     *)
(*  This file is originally part of the Why3 Verification Platform        *)
(*                                                                        *)
(**************************************************************************)

Require Import BuiltIn.

Definition func : forall (a:Type) (b:Type), Type.
intros a b.
exact (a -> b).
Defined.

Definition infix_at: forall {a:Type} {a_WT:WhyType a}
  {b:Type} {b_WT:WhyType b}, (a -> b) -> a -> b.
intros a aWT b bWT f x.
exact (f x).
Defined.

Definition pred (a: Type) := func a bool.
