ci:
	gofmt -d -s .
	go vet -composites=false ./...
	go test ./...

fix:
	gofmt -w -s .

.PHONY: ci fix
