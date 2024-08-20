(* autogenerated from github.com/goose-lang/goose/testdata/examples/async *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.async_disk.

From New Require Import async_disk_prelude.

(* go: async.go:6:6 *)
Definition TakesDisk : val :=
  rec: "TakesDisk" "d" :=
    exception_do (let: "d" := (ref_ty disk.Disk "d") in
    do:  #()).

(* go: async.go:8:6 *)
Definition UseDisk : val :=
  rec: "UseDisk" "d" :=
    exception_do (let: "d" := (ref_ty disk.Disk "d") in
    let: "v" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (slice.make2 byteT #(W64 4096)) in
    do:  ("v" <-[sliceT byteT] "$r0");;;
    do:  (let: "$a0" := #(W64 0) in
    let: "$a1" := (![sliceT byteT] "v") in
    (interface.get "Write" (![disk.Disk] "d")) "$a0" "$a1");;;
    do:  ((interface.get "Barrier" (![disk.Disk] "d")) #())).
