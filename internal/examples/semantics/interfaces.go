package semantics

import "fmt"

type greeting interface {
	intro() string
}

type food interface {
	dish() string
}

type person struct {
	name string
	meal string
}

type animal struct {
	bark   string
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

	// Empty interface

	var x interface{}

	// Type assertion

	var y interface{} = "foo"

	var s string = y.(string)

	// Type switch

	switch v := y.(type) {
	case nil:
		fmt.Println("y is nil")
	case int:
		fmt.Println("y is", v)
	case bool, string:
		fmt.Println("y is bool or string")
	default:
		fmt.Println("type unknown")
	}
}

// Downcast

// No interface to interface casting

// Double pointers
