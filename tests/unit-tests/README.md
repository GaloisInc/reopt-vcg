`src/Test/test.sh` will for each `*.lean` file in the `src/Test` directory
call the executable defined in `app/Main.lean` with the file
name in order to run its test (also specified in `Main.lean`),
comparing the stdout to the respective `*.lean.expected.out`
file.

`test_single.sh PATH_TO_LEAN_FILE` can be used to test a single lean
file's test output against it's respective `.expected.out` file.

To add a new test, define a `.lean` file in `src/Test`
similar to those already there, and add an appropriate entry
to the `tests` RBMap in `app/Main.lean`.
