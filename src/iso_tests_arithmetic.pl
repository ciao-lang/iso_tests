:- module(iso_tests_arithmetic, _, [assertions, nativeprops, unittestdecls, iso]).

:- doc(title, "ISO tests for arithmetic").
:- doc(author, "Lorea Galech").
:- doc(author, "R@'{e}my Haemmerl@'{e}").

:- doc(module, "ISO standard tests for arithmetic (see `iso_tests.pl`)").

% ===========================================================================
%% 8.6.1.4 These tests are specified in page 74 of the ISO standard %%%%

%test 1
:- test is_test1(Result) => (Result=14.0)
# "[ISO] 'is'/2: ...".

is_test1(Result) :- 'is'(Result, 3 +11.0).

%test 2
:- test is_test2(X, Y) => (X=(1 +2), Y=9)
# "[ISO] 'is'2: ...".

is_test2(X, Y) :- X=1 +2, Y 'is' X*3.

%test 3
:- test is_test3 + not_fails
# "[ISO] 'is'/2: ...".

is_test3 :- 'is'(3, 3).

%test 4
:- test is_test4 + fails
# "[ISO] 'is'/2: ...".

is_test4 :- 'is'(3, 3.0).

%test 5
:- test is_test5 + fails
# "[ISO] 'is'/2: ...".

is_test5 :- 'is'(foo, 77).

%test 6 
:- test is_test6(N) + exception(error(instantiation_error, Imp_dep))
# "[ISO] 'is'/2: ...".

is_test6(N) :- 'is'(77, N).


% ===========================================================================
%% 8.7.1.4 These tests are specified in page 76 of the ISO standard %%%%


%test 1
:- test arithmetic_comparison_test1 + fails
# "[ISO] '=:='/2: ...".

arithmetic_comparison_test1 :- '=:='(0, 1).

%test 2
:- test arithmetic_comparison_test2 + not_fails
# "[ISO] '=\\='/2: ...".

arithmetic_comparison_test2 :- '=\\='(0, 1).


%test 3
:- test arithmetic_comparison_test3 + not_fails
# "[ISO] '<'/2: ...".

arithmetic_comparison_test3 :- '<'(0, 1).

%test 4
:- test arithmetic_comparison_test4 + fails
# "[ISO] '>'/2: ...".

arithmetic_comparison_test4 :- '>'(0, 1).


%test 5
:- test arithmetic_comparison_test5 + fails
# "[ISO] '>='/2: ...".

arithmetic_comparison_test5 :- '>='(0, 1).

%test 6
:- test arithmetic_comparison_test6 + not_fails
# "[ISO] '=<'/2: ...".

arithmetic_comparison_test6 :- '=<'(0, 1).

%test 7
:- test arithmetic_comparison_test7 + not_fails
# "[ISO] '=:='/2: ...".

arithmetic_comparison_test7 :- '=:='(1.0, 1).

%test 8
:- test arithmetic_comparison_test8 + fails
# "[ISO] '=\='/2: ...".

arithmetic_comparison_test8 :- '=\='(1.0, 1).

%test 9
:- test arithmetic_comparison_test9 + fails
# "[ISO] '<'/2: ...".

arithmetic_comparison_test9 :- '<'(1.0, 1).

%test 10
:- test arithmetic_comparison_test10 + fails
# "[ISO] '>'/2: ...".

arithmetic_comparison_test10 :- '>'(1.0, 1).

%test 11
:- test arithmetic_comparison_test11 + not_fails
# "[ISO] '>='/2: ...".

arithmetic_comparison_test11 :- '>='(1.0, 1).

%test 12
:- test arithmetic_comparison_test12 + not_fails
# "[ISO] '=<'/2: ...".

arithmetic_comparison_test12 :- '=<'(1.0, 1).

%test 13
:- test arithmetic_comparison_test13 + not_fails
# "[ISO] '=:='/2: ...".

arithmetic_comparison_test13 :- '=:='(3*2, 7 -1).

%test 14
:- test arithmetic_comparison_test14 + fails
# "[ISO] '=\\='/2: ...".

arithmetic_comparison_test14 :- '=\\='(3*2, 7 -1).

%test 15
:- test arithmetic_comparison_test15 + fails
# "[ISO] '<'/2: ...".

arithmetic_comparison_test15 :- '<'(3*2, 7 -1).

%test 16
:- test arithmetic_comparison_test16 + fails
# "[ISO] '>'/2: ...".

arithmetic_comparison_test16 :- '>'(3*2, 7 -1).

%test 17
:- test arithmetic_comparison_test17 + not_fails
# "[ISO] '>='/2: ...".

arithmetic_comparison_test17 :- '>='(3*2, 7 -1).

%test 18
:- test arithmetic_comparison_test18 + not_fails
# "[ISO] '=<'/2: ...".

arithmetic_comparison_test18 :- '=<'(3*2, 7 -1).

%test 19 
:- test arithmetic_comparison_test19(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '=:='/2: ...".

arithmetic_comparison_test19(X) :- '=:='(X, 5).

%test 20 
:- test arithmetic_comparison_test20(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '=\='/2: ...".

arithmetic_comparison_test20(X) :- '=\\='(X, 5).

%test 21 
:- test arithmetic_comparison_test21(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '<'/2: ...".

arithmetic_comparison_test21(X) :- '<'(X, 5).

%test 22 
:- test arithmetic_comparison_test22(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '>'/2: ...".

arithmetic_comparison_test22(X) :- '>'(X, 5).

%test 23 
:- test arithmetic_comparison_test23(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '>='/2: ...".

arithmetic_comparison_test23(X) :- '>='(X, 5).

%test 24 
:- test arithmetic_comparison_test24(X)
    + exception(error(instantiation_error, Imp_dep))
# "[ISO] '=<'/2: ...".

arithmetic_comparison_test24(X) :- '=<'(X, 5).
