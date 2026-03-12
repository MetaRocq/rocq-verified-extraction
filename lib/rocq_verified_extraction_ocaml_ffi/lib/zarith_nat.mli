(************************************************************************)
(*         *   The Rocq Proof Assistant / The Rocq Development Team     *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Bindings from nat to zarith GMP integers *)
type t

(* eliminator *)
val case : t -> (unit -> 'a) -> (t -> 'a) -> 'a

(* higher-level functions *)

val pow : t -> t -> t
