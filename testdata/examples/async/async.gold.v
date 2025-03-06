(* autogenerated from github.com/goose-lang/goose/testdata/examples/async *)
From New.golang Require Import defn.
Require Export New.code.github_com.goose_lang.primitive.async_disk.

From New Require Import async_disk_prelude.
Module async.
Section code.


(* go: async.go:6:6 *)
Definition TakesDisk : val :=
  rec: "TakesDisk" "d" :=
    exception_do (let: "d" := (ref_ty disk.Disk "d") in
    do:  #()).

(* go: async.go:8:6 *)
Definition UseDisk : val :=
  rec: "UseDisk" "d" :=
    exception_do (let: "d" := (ref_ty disk.Disk "d") in
    let: "v" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make2 byteT #(W64 4096)) in
    do:  ("v" <-[sliceT] "$r0");;;
    do:  (let: "$a0" := #(W64 0) in
    let: "$a1" := (![sliceT] "v") in
    (interface.get "Write" (![disk.Disk] "d")) "$a0" "$a1");;;
    do:  ((interface.get "Barrier" (![disk.Disk] "d")) #())).

Definition pkg_name' : go_string := "github.com/goose-lang/goose/testdata/examples/async".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("TakesDisk"%go, TakesDisk); ("UseDisk"%go, UseDisk)].

Definition msets' : list (go_string * (list (go_string * val))) := [].

#[global] Instance info' : PkgInfo pkg_name' :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [async_disk.pkg_name'];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  async_disk.initialize')
      ).

End code.
End async.
