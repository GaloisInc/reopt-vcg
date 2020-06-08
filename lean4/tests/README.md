`test.sh` will for each `*.lean` file in the directory (except
`Main.lean`) call the executable defined in `Main.lean` with the file
name in order to run its test (also specified in `Main.lean`),
comparing the stdout to the respective `*.lean.expected.out`
file. `test.sh` can also be called

`test_single.sh PATH_TO_LEAN_FILE` can be used to test a single lean
file's test output against it's respective `.expected.out` file.
