package channel_spec_test

import (
	"fmt"
	"sync"
)

// A mocked out version of https://go.dev/blog/pipelines/bounded.go using only Goose
// supported features for testing and demonstrate channel specifications.
// TODO: Uncomment select and range for once we have these supported for translation

// DummyFile represents a file in our mock filesystem
type DummyFile struct {
	path     string
	contents string
}

// result contains the path and a checksum value
type result struct {
	path     string
	checksum uint64
	err      string
}

// createMockFiles constructs our mock filesystem one file at a time
func createMockFiles() []DummyFile {
	var files []DummyFile

	// Add file 1
	file1 := DummyFile{
		path:     "/root/file1.txt",
		contents: "This is a sample file with some simple content.",
	}
	files = append(files, file1)

	// Add file 2
	file2 := DummyFile{
		path:     "/root/file2.txt",
		contents: "Another file with different content that we can checksum.",
	}
	files = append(files, file2)

	// Add file 3
	file3 := DummyFile{
		path:     "/root/dir1/file3.txt",
		contents: "A third file in a subdirectory. It has unique text.",
	}
	files = append(files, file3)

	// Add file 4
	file4 := DummyFile{
		path:     "/root/dir2/file4.txt",
		contents: "The fourth and final test file for our mock filesystem.",
	}
	files = append(files, file4)

	return files
}

// mockReadFile simulates reading a file
func mockReadFile(path string) (string, string) {
	var contents string = ""
	var err string = "file not found: " + path
	var foundFile bool = false

	files := createMockFiles()
	for i := uint64(0); i < uint64(len(files)); i++ {
		if files[i].path == path {
			contents = files[i].contents
			err = ""
			foundFile = true
			break
		}
	}

	if foundFile {
		return contents, ""
	} else {
		return "", err
	}
}

// mockWalk simulates walking a directory tree
func mockWalk(root string) []string {
	var paths []string
	files := createMockFiles()

	for i := uint64(0); i < uint64(len(files)); i++ {
		file := files[i]
		if len(file.path) >= len(root) && file.path[:len(root)] == root {
			paths = append(paths, file.path)
		}
	}

	return paths
}

// calculateChecksum creates a simple checksum from string length
func calculateChecksum(data string) uint64 {
	length := uint64(len(data))

	// Simple hash function based on length
	return length*1103515245 + 12345
}

// sourceStage sends file paths to the paths channel
func sourceStage(done <-chan uint64, root string, paths chan<- string, errc chan<- string) {
	go func() {
		filePaths := mockWalk(root)
		sendingComplete := false

		for i := uint64(0); i < uint64(len(filePaths)) && !sendingComplete; i++ {
			/*
				select {
				case paths <- filePaths[i]:
					// Continue sending
				case <-done:
					errc <- "walk canceled"
					close(paths)
					sendingComplete = true
				}
			*/
		}

		if !sendingComplete {
			errc <- "" // No error
			close(paths)
		}
	}()
}

// digester processes file paths by calculating their checksum
func digester(done <-chan uint64, paths <-chan string, results chan<- result, wg *sync.WaitGroup) {
	/*
		var done_processing = false
			for path := range paths {
				if done_processing {
					break
				}

				contents, err := mockReadFile(path)

				if err != "" {
					var select_complete = false

					select {
					case results <- result{path, 0, err}:
						// Result sent
					case <-done:
						done_processing = true
						break
					}

					if select_complete {
						break
					}
				}

				checksum := calculateChecksum(contents)
				var select_complete = false

				select {
				case results <- result{path, checksum, ""}:
					// Result sent
				case <-done:
					done_processing = true
					select_complete = true
				}

				if select_complete {
					break
				}
			}
	*/

	wg.Done()
}

// parallelProcessorStage launches multiple digesters
func parallelProcessorStage(done <-chan uint64, paths <-chan string, results chan<- result, numDigesters uint64) {
	var wg *sync.WaitGroup = new(sync.WaitGroup)
	wg.Add(int(numDigesters))

	for i := uint64(0); i < numDigesters; i++ {
		//go digester(done, paths, results, wg)
	}

	go func() {
		wg.Wait()
		close(results)
	}()
}

// sinkStage collects results from the results channel
func sinkStage(results <-chan result) (map[string]uint64, string) {
	m := make(map[string]uint64)
	var error_occurred = false
	var error_msg = ""

	/*
		for r := range results {
			if r.err != "" {
				error_occurred = true
				error_msg = r.err
				break
			}

			m[r.path] = r.checksum
		}
	*/

	if error_occurred {
		return nil, error_msg
	} else {
		return m, ""
	}
}

// ChecksumAll processes all files in the given root directory
func ChecksumAll(root string) (map[string]uint64, string) {
	// Create channels for the pipeline stages
	done := make(chan uint64)
	paths := make(chan string)
	results := make(chan result)
	errc := make(chan string, 1)

	// Launch the source stage
	sourceStage(done, root, paths, errc)

	// Launch the parallel processor stage with 3 digesters
	var numDigesters uint64 = 3
	parallelProcessorStage(done, paths, results, numDigesters)

	// Run the sink stage to collect results
	var err string
	var m map[string]uint64
	m, err = sinkStage(results)
	var error_occurred = false

	if err != "" {
		close(done)
		error_occurred = true
	}

	if !error_occurred {
		// Check whether the Walk failed
		err = <-errc
		if err != "" {
			close(done)
			error_occurred = true
		}
	}

	// Clean shutdown
	if !error_occurred {
		close(done)
		return m, ""
	} else {
		return nil, err
	}
}

func main() {
	// Run ChecksumAll on the mock root directory
	checksums, err := ChecksumAll("/root")

	if err != "" {
		fmt.Println("Error:", err)
		return
	}

	// Print results
	fmt.Println("File checksums:")
	for path, checksum := range checksums {
		fmt.Printf("%d  %s\n", checksum, path)
	}
}
