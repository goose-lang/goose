(* autogenerated from github.com/goose-lang/goose/testdata/examples/interfacerecursion *)
From New.golang Require Import defn.

Module interfacerecursion.
Section code.
Context `{ffi_syntax}.


Definition A : go_type := interfaceT.

Definition B : go_type := interfaceT.

Definition c : go_type := structT [
].

(* go: x.go:14:13 *)
Definition c__Foo : val :=
  rec: "c__Foo" "c" <> :=
    exception_do (let: "c" := (ref_ty ptrT "c") in
    let: "y" := (ref_ty B (zero_val B)) in
    let: "$r0" := (interface.make #pkg_name' #"c'ptr" (![ptrT] "c")) in
    do:  ("y" <-[B] "$r0");;;
    do:  ((interface.get "Bar" (![B] "y")) #())).

(* go: x.go:19:13 *)
Definition c__Bar : val :=
  rec: "c__Bar" "c" <> :=
    exception_do (let: "c" := (ref_ty ptrT "c") in
    let: "y" := (ref_ty A (zero_val A)) in
    let: "$r0" := (interface.make #pkg_name' #"c'ptr" (![ptrT] "c")) in
    do:  ("y" <-[A] "$r0");;;
    do:  ((interface.get "Foo" (![A] "y")) #())).

Definition pkg_name' : go_string := "github.com/goose-lang/goose/testdata/examples/interfacerecursion".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("c"%go, []); ("c'ptr"%go, [("Bar"%go, c__Bar); ("Foo"%go, c__Foo)])].

#[global] Instance info' : PkgInfo pkg_name' :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  #())
      ).

End code.
End interfacerecursion.
