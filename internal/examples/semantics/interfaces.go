package semantics

import "fmt"

type greeting interface {
	intro() string
}

// Definition greeting := struct.decl [
//		"method" :: struct.decl [
//			"intro" :: string;
//		];
//		"typeDescriptor" :: #"greeting";
//		"value" :: anyT;
//   ].

type food interface {
	dish() string
}

// Definition food := struct.decl [
//		"method" :: struct.decl [
//			"dish" :: string;
//		];
//		"typeDescriptor" :: #"food";
//		"value" :: anyT;
//   ].

type person struct {
	name  string
	meal string
}

type animal struct {
	bark string
	kibble string
}

func (p person) intro() string {
	return p.name
}

func (a animal) intro() string {
	return a.bark
}

func (p person) feed() string {
	return p.meal
}

func (a animal) feed() string {
	return a.kibble
}

func greet(g greeting) {
	fmt.Printf("%s\n", g.intro())
}

func eating(f food) {
	fmt.Printf("%s\n", g.dish())
}

// Definition greet: val :=
//   rec: "greet" "s" :=
//     ((intro), greeting, anyT).
// Theorem greet_t: ⊢ greet : (shape -> unitT).
// Proof. typecheck. Qed.
// Hint Resolve greet_t : types.

func main() {
	greeting(person{name: "Bob"})
	food(animal{kibble: "Buster's Feed"})
}

// Empty interface

var x interface{}

// Definition x := struct.decl [
//   ].

// Type assertion

var x interface{} = "foo"

// Definition x := struct.decl [
//		"method" :: struct.decl [];
//		"typeDescriptor" :: #"x";
//		"value" :: string;
//   ].

var s string = x.(string) // "foo"

s, ok := x.(string)

// Type switch

switch v := x.(type) {
case nil:
    fmt.Println("x is nil")
case int: 
    fmt.Println("x is", v)
case bool, string:
    fmt.Println("x is bool or string")
default:
    fmt.Println("type unknown")
}

// Downcast

// Double pointers
