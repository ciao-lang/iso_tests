# ISO Prolog tests for Ciao

This is a ISO Prolog conformance test for Ciao implemented using the
Ciao unit test assertion framework.

See [iso_test.pl](src/iso_tests.pl) documentation for more details.
It is recommended to use `outli-mode` (for folding sections) and
`emacs` to browse the tests.

## Usage

Clone this repository into your workspace or install with `ciao get
iso_tests`. Then run:
```sh
ciao test iso_tests
```

To run specific tests you can use test filters. For example:

 - tests for arithmetic predicates:
```
?- run_tests(iso_tests(iso_tests), [filter(regexp(".* arith .*"))], [check, show_results]).
```

 - test for `open/4`:
```
?- run_tests(iso_tests(iso_tests), [filter(regexp(".* open/4 .*"))], [check, show_results]).
```

## Status

This is the current status of running the test suite:
```
Note: {Total:
Passed: 889 (84.91%) Failed: 158 (15.09%) Precond Failed: 0 (0.00%) Aborted: 0 (0.00%) Timeouts: 0 (0.00%) Total: 1047 Run-Time Errors: 158
}
```

