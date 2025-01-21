(* autogenerated from github.com/goose-lang/goose/testdata/examples/mutualrec *)
From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Definition pkg_name' : go_string := "github.com/goose-lang/goose/testdata/examples/mutualrec".

(* go: mutualrec.go:3:6 *)
Definition A : val :=
  rec: "A" <> :=
    exception_do (do:  ((func_call #pkg_name' #"B"%go) #())).

(* go: mutualrec.go:7:6 *)
Definition B : val :=
  rec: "B" <> :=
    exception_do (do:  ((func_call #pkg_name' #"A"%go) #())).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("A"%go, A); ("B"%go, B)].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  #())
      ).

End code.
