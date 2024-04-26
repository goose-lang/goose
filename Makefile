fix:
	gofmt -w -s .
	go generate ./...

.PHONY: fix
