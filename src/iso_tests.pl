:- module(iso_tests, _, [assertions, nativeprops, unittestdecls, iso_strict, dynamic]).

% TODO: use a package containing all reexports so the file is cleaner

% TODO: rewrite with use test modules?
:- reexport(engine(runtime_control)).
%:- reexport(library(streams)).
:- reexport(library(streams), [current_input/1, current_output/1, open/3, get_code/1]).
:- reexport(library(iso_incomplete)).
:- reexport(library(read), [
    read/1,
    read_term/2
]).
:- reexport(library(write), [
    write_term/2,
    write/1, writeq/1,
    write_canonical/1
]).
:- reexport(library(operators)).
:- reexport(library(iso_char), [
    char_code/2, atom_chars/2, number_chars/2,char_codes/2,
    get_char/1,
    peek_char/1,
    put_char/1
]).
:- reexport(library(iso_incomplete)).
:- reexport(library(compiler)).
%:- reexport(library(dynamic)).

:- doc(title, "ISO tests for Ciao").
:- doc(author, "The Ciao Development Team").
:- doc(author, "Lorea Galech").
:- doc(author, "Jose F. Morales (simplified)").
:- doc(author, "Jose Luis Bueno").

:- doc(module, "This module contains a collection of test assertions
for checking compliance of Ciao with the ISO Prolog standard. The
description of each test annotates the predicate or feature to be
tested:

 - `[ISO] f/a`: checks that a predicate `f/a` behaves according to the
   ISO standard.
 - `[ISO] operands`: the relationships among operands and operators
   are stablished according to the ISO standard.
 - `[ISO] arguments`: syntax for term arguments is compliant with the
   ISO standard.
 - `[Non-ISO] f/a`: other non-ISO tests for the predicate `f/a`.

the expected behavior:

 - `...`: (not documented yet, probably the test is expected to succeed).
 - `expected(undefined)`: The expected result for this test is undefined.
 - `expected(impldep)`: The expected result is implementation-dependent.
 - `expected(succeed)`: This test is expected to succeed in Ciao.
 - `expected(fail)`: This test is expected to fail in Ciao.

and the current status in Ciao:

 - `bug(succeed)`: The predicate succeeds, but it should not.
 - `bug(fail)`: The predicate fails, but it should not.
 - `bug(error)`: The predicate raises an exception (error), but it should not.
 - `bug(not_implemented)`: The predicate is not implemented in Ciao.
 - `bug(wrong_succeed)`: The predicate succeeds but the solution is not the expected.
 - `bug(wrong_error)`: The predicate raises an exception (error), but
   it is not the expected.
").

%:- compilation_fact(fixed_utf8). % TODO: Enable when UTF8 support is completed

% TODO: stream_property(_,output) is not implemented
% TODO: type(binary) not implemented
% TODO: type(text) not implemented

% ---------------------------------------------------------------------------
% TODO: fix

%%Labels:
%% 
%%Wrong_vs_iso: Wrong solution
%%Nothrow_vs_iso: Doesn't throw exception
%%Diffthrow_vs_iso: Throws a different exception
%%Label_4: Warnings
%%Label_5: Nondet
%%Label_6: Aborted
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The following predicates are not implemented, but here a dummy
% version is provided in order to avoid compilation errors. -- EMM
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

moose(_) :- fail.
x :- fail.
f(_) :- fail.
animal(_) :- fail.
:- push_prolog_flag(multi_arity_warnings, off).
foo :- fail.
foo(_, _) :- fail.
:- pop_prolog_flag(multi_arity_warnings).
bird(_) :- fail.
at_end_of_stream(_) :- fail. % TODO: Non-ISO and not implemented
set_stream_position(_, _) :- fail. % TODO: Non-ISO and not implemented
char_conversion(_, _) :- fail.
current_char_conversion(_, _) :- fail.

% ---------------------------------------------------------------------------

:- load_test_module(iso_tests(iso_tests_common)).

% ===========================================================================
%% 7.8.1.4 These tests are specified in page 43 of the ISO standard. %%%%

:- test true # "[ISO] true/0: expected(succeed)".

% ===========================================================================
%% 7.8.2.4 These tests are specified in page 44 of the ISO standard. %%%%

:- test fail/0 + fails # "[ISO] fail/0: expected(fail)".

% ===========================================================================
%% 7.8.3.4 These tests are specified in page 45 of the ISO standard. %%%%

%test 1
:- test call_test1
# "[ISO] call/1: expected(succeed)".

call_test1 :- call(!).
 
%test 2
:- test call_test2 + fails
# "[ISO] call/1: expected(fail)".

call_test2 :- call(fail).

%test 3
:- test call_test3(X) + fails
# "[ISO] call/1: expected(fail)".

call_test3(X) :- call((fail, X)).

%test 4
:- test call_test4 + fails
# "[ISO] call/1: expected(error)".

call_test4 :- call((fail, call(1))).


% ---------------------------------------------------------------------------
%% These predicates are used in the following tests %%%%%%%%%%%%%%%%%%%%%%%%%%

bb(X) :-
	Y=(write(X), X),
	call(Y).
aa(1).

aa(2).

% ---------------------------------------------------------------------------

%test 5 
:- test call_test5 + exception(error(instantiation_error, Imp_dep))
# "[ISO] call/1: expected(error)".

call_test5 :- call(bb(_)).


%test 6 
:- test call_test6
	+ ( user_output("3"),
	    exception(error(type_error(callable, 3), Imp_dep)) )
# "[ISO] call/1: expected(error)".

call_test6 :- call(bb(3)).

%% REVIEW:PENDING                ** wrong_vs_iso**
%%   [gprolog]: it is correct
%%   [ciao]: returns a different result
%test 7 
:- test call_test7(Result) => (Result=[[1, !]])
# "[ISO] call/1: expected(succeed) bug(wrong_succeed)".

call_test7(Result) :- findall([X, Z], (Z= !, call((Z= !, aa(X), Z))), Result).


%test 8
:- test call_test8(Result) => (Result=[[1, !], [2, !]])
# "[ISO] call/1: expected(succeed)".

call_test8(Result) :- findall([X, Z], (call((Z= !, aa(X), Z))), Result).

%test 9 
:- test call_test9(X)
	+ (user_output("3"), exception(error(instantiation_error, Imp_dep)))
# "[ISO] call/1: expected(error)".

call_test9(X) :- call((write(3), X)).

%test 10 
:- test call_test10
	+ ( user_output("3"),
	    exception(error(type_error(callable, 1), Imp_dep)) )
# "[ISO] call/1: expected(error)".

call_test10 :- call((write(3), call(1))).

%test 11
:- test call_test11 + exception(error(instantiation_error, Imp_dep))
# "[ISO] call/1: expected(error)".

call_test11 :- call(_).

%test 12
:- test call_test12 + exception(error(type_error(callable, 1), Imp_dep))
# "[ISO] call/1: expected(error)".

call_test12 :- call(1).

%% REVIEW:PENDING                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, (fail, 1)),_))
%%   [ciao]: no throws
%test 13 
:- test call_test13
	+ exception(error(type_error(callable, (fail, 1)), Imp_dep))
# "[ISO] call/1: expected(error) bug(fail)".

call_test13 :- call((fail, 1)).

%% REVIEW:PENDING                               **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, (write(3), 1)),_))
%%   [ciao]:  throws exception(error(type_error(callable,1),'in metacall'))
%test 14
:- test call_test14
	+ exception(error(type_error(callable, (write(3), 1)), Imp_dep))
# "[ISO] call/1: expected(error) bug(wrong_error)".

call_test14 :- call((write(3), 1)).

%% REVIEW:PENDING                                **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, (1;true)),_))
%%   [ciao]:  throws exception(error(type_error(callable,1),'in metacall'))
%test 15 
:- test call_test15 + exception(error(type_error(callable, (1;true)), Imp_dep))
# "[ISO] call/1: expected(error) bug(wrong_error)".

call_test15 :- call((1;true)).


% ===========================================================================
%% 7.8.4.4 These tests are specified in page 46 of the ISO standard %%%%

% ---------------------------------------------------------------------------
% (these predicates are used in the following tests)
:- dynamic(twice/1).
twice(!) :- write('C ').
twice(true) :- write('Moss ').

:- dynamic(goal/1).
goal((twice(_), !)).
goal(write('Three ')).
% ---------------------------------------------------------------------------

%test 1
:- test cut_test1
# "[ISO] cut: expected(succeed)".

cut_test1 :- !.

%test 2
:- test cut_test2/0 + fails
# "[ISO] cut: expected(fail)".

cut_test2 :- !, fail;true.

%test 3
:- test cut_test3/0
# "[ISO] cut: expected(succeed)".

cut_test3 :- call(!), fail;true.

%test 4  
:- test cut_test4/0 + (user_output("C Forwards "), fails)
# "[ISO] cut: expected(fail)".

cut_test4 :- twice(_), !, write('Forwards '), fail.

%test 5
:- test cut_test5 + (user_output("Cut disjunction"), fails)
# "[ISO] cut: expected(fail)".

cut_test5 :- (! ;write('No ')), write('Cut disjunction'), fail.

%test 6 
:- test cut_test6 + (user_output("C No Cut Cut "), fails)
# "[ISO] cut: expected(fail)".

cut_test6 :- twice(_), (write('No ') ; !), write('Cut '), fail.

%test 7 
:- test cut_test7 + (user_output("C "), fails)
# "[ISO] cut: expected(fail)".

cut_test7 :- twice(_), (!, fail, write('No ')).

%test 8 
:- test cut_test8 + (user_output("C Forwards Moss Forwards "), fails)
# "[ISO] cut: expected(fail)".

cut_test8 :- twice(X), call(X), write('Forwards '), fail.

%test 9  
:- test cut_test9 + (user_output("C Forwards Three Forwards "), fails)
# "[ISO] cut: expected(fail)".

cut_test9 :- goal(X), call(X), write('Forwards '), fail.

% % test 10 
% :- test cut_test10 
%       + (user_output("C Forwards Moss Forwards "),fails)
% # "[ISO] cut: expected(fail)".
%
% cut_test10 :- twice(_),(\+(\+(!))),write('Forwards '),fail.

%test 11 
:- test cut_test11 + (user_output("C Forwards Moss Forwards "), fails)
# "[ISO] cut: expected(fail)".

cut_test11 :- twice(_), once(!), write('Forwards '), fail.

%test 12 
:- test cut_test12 + (user_output("C Forwards Moss Forwards "), fails)
# "[ISO] cut: expected(fail)".

cut_test12 :- twice(_), call(!), write('Forwards '), fail.


% ===========================================================================
%% 7.8.5.4 These tests are specified in page 47 of the ISO standard %%%%

%test 1
:- test and_test1 + fails
# "[ISO] ',': expected(fail)".

and_test1 :- ','(X=1, var(X)).

%test 2 
:-test and_test2(X) => (X=1)
# "[ISO] ',': expected(succeed)".

and_test2(X) :- ','(var(X), X=1).

%test 3 
:- test and_test3(X) => (X=true)
# "[ISO] ',': expected(succeed)".

and_test3(X) :- ','(X=true, call(X)).


% ===========================================================================
%% 7.8.6.4 These tests are specified in page 48 of the ISO standard %%%%

%test 1
:- test or_test1
# "[ISO] ';': expected(fail)".

or_test1 :- ';'(true, fail).

%test 2 
:- test or_test2 + fails
# "[ISO] ';': expected(fail)".

or_test2 :-';'((!, fail), true).


%test 3
:- test or_test3
# "[ISO] ';': expected(succeed)".

or_test3 :- ';'(!, call(3)).

%test 4  
:- test or_test4(X) => (X=1)
# "[ISO] ';': expected(succeed)".

or_test4(X) :- ';'((X=1, !), X=2).

%test 5
:- test or_test5(Result) => (Result=[1, 1])
# "[ISO] ';': expected(succeed)".

or_test5(Result) :- findall(X, call((;(X=1, X=2), ;(true, !))), Result).

% ===========================================================================
%% 7.8.7.4 These tests are specified in page 49 of the ISO standard %%%%

%test 1
:- test ifthen_test1
# "[ISO] '->': expected(succeed)".

ifthen_test1 :- '->'(true, true).

%test 2
:- test ifthen_test2 + fails
# "[ISO] '->': expected(fail)".

ifthen_test2:- '->'(true, fail).

%test 3
:- test ifthen_test3 + fails
# "[ISO] '->': expected(fail)".

ifthen_test3 :- '->'(fail, true).

%test 4
:- test ifthen_test4(Result) => (Result=[1])
# "[ISO] '->': expected(succeed)".

ifthen_test4(Result) :- findall(X, '->'(true, X=1), Result).

%test 5 
:- test ifthen_test5(Result) => (Result=[1])
# "[ISO] '->': expected(succeed)".

ifthen_test5(Result) :- findall(X, '->'(';'(X=1, X=2), true), Result).

%test 6.
:- test ifthen_test6(Result) => (Result=[1, 2])
# "[ISO] '->': expected(succeed)".

ifthen_test6(Result) :- findall(X, '->'(true, ';'(X=1, X=2)), Result).


% ===========================================================================
%% 7.8.8.4 These tests are specified in page 51 of the ISO standard %%%%

%test 1
:- test ifthenelse_test1
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test1 :- ';'('->'(true, true), fail).

%test1
:- test ifthenelse_test2
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test2 :- ';'('->'(fail, true), true).

%test3
:- test ifthenelse_test3 + fails
# "[ISO] if-then-else: expected(fail)".

ifthenelse_test3 :- ';'('->'(true, fail), fail).

%test4
:- test ifthenelse_test4 + fails
# "[ISO] if-then-else: expected(fail)".

ifthenelse_test4 :- ';'('->'(fail, true), fail).

%test 5 
:- test ifthenelse_test5(X) => (X=1)
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test5(X) :- ';'('->'(true, X=1), X=2).

%test 6 
:- test ifthenelse_test6(X) => (X=2)
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test6(X) :- ';'('->'(fail, X=1), X=2).

:- test ifthenelse_test7(Result) => (Result=[1, 2])
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test7(Result) :-
	findall(X, ';'('->'(true, ';'(X=1, X=2)), true), Result).

%test 8 
:- test ifthenelse_test8(X) => (X=1)
# "[ISO] if-then-else: expected(succeed)".

ifthenelse_test8(X) :- ';'('->'(';'(X=1, X=2), true), true).

% % test 9 
% :- test ifthenelse_test9
% # "[ISO] if-then-else: expected(succeed)".
%
% ifthenelse_test9 :- ';'('->'(!,fail),true).


% ===========================================================================
%% 7.8.9.4 These tests are specified in page 52 of the ISO standard %%%%

% ---------------------------------------------------------------------------
% (these predicates are used in the following tests)
:- push_prolog_flag(multi_arity_warnings, off).
:- dynamic(foo/1).
foo(X) :- Y is X*2, throw(test(Y)).
:- pop_prolog_flag(multi_arity_warnings).

:- dynamic(bar/1).
bar(X) :- X = Y, throw(Y).

:- dynamic(coo/1).
coo(X) :- throw(X).

:- dynamic(car/1).
car(X) :- X=1, throw(X).

:- dynamic(g/0).
g :- catch(p, _B, write(h2)), coo(c).

:- dynamic(p/0).
p.

p :- throw(b).
% ---------------------------------------------------------------------------

%test1 
:- test catch_test1(Y) => (Y=10)
# "[ISO] catch: expected(succeed)".

catch_test1(Y) :- catch(foo(5), test(Y), true).

%test2 
:- test catch_test2(Z) : (Z=3)
# "[ISO] catch: expected(succeed)".

catch_test2(Z) :- catch(bar(3), Z, true).

%test3
:- test catch_test3
# "[ISO] catch: expected(succeed)".

catch_test3 :- catch(true, _, 3).

%% REVIEW:PENDING                                **Diffthrow_vs_iso**
%test4
%%   [gprolog]: throws exception(bla)
%%   [ciao]:  throws  exception(bla)
:- test catch_test4 + exception(error(system_error, Imp_dep))
# "[ISO] catch: expected(error) bug(wrong_error)".

catch_test4 :- catch(true, _C, write(demoen)), throw(bla). % TODO: wrong test?

%test5
:- test catch_test5(Y) => (Y=1)
# "[ISO] catch: expected(succeed)".

catch_test5(Y) :- catch(car(_X), Y, true).

%test6 
:- test catch_test6 + fails
# "[ISO] catch: expected(fail)".

catch_test6 :-
    catch(number_chars(_X, ['1', 'a', '0']), error(syntax_error(_), _),
          fail).

%test 7 
:- test catch_test7(Result) => (Result=[c]) + (user_output("h1"))
# "[ISO] catch: expected(succeed)".

catch_test7(Result) :- findall(C, catch(g, C, write(h1)), Result).

%tes 8
:- test catch_test8(Y) => (Y=error(instantiation_error, Imp_def))
# "[ISO] catch: expected(succeed)".

catch_test8(Y) :- catch(coo(_X), Y, true).


% ===========================================================================
%% 8.6.1.4 These tests are specified in page 74 of the ISO standard %%%%


%test 1
:- test is_test1(Result) => (Result=14.0)
# "[ISO] 'is'/2: expected(succeed)".

is_test1(Result) :- 'is'(Result, 3 +11.0).

%test 2
:- test is_test2(X, Y) => (X=(1 +2), Y=9)
# "[ISO] 'is'2: expected(succeed)".

is_test2(X, Y) :- X=1 +2, Y 'is' X*3.

%test 3
:- test is_test3
# "[ISO] 'is'/2: expected(succeed)".

is_test3 :- 'is'(3, 3).

%test 4
:- test is_test4 + fails
# "[ISO] 'is'/2: expected(fail)".

is_test4 :- 'is'(3, 3.0).

%test 5
:- test is_test5 + fails
# "[ISO] 'is'/2: expected(fail)".

is_test5 :- 'is'(foo, 77).

%test 6 
:- test is_test6(N) + exception(error(instantiation_error, Imp_dep))
# "[ISO] 'is'/2: expected(error) bug(fail)".

is_test6(N) :- 'is'(77, N).


% ===========================================================================
%% 8.7.1.4 These tests are specified in page 76 of the ISO standard %%%%


%test 1
:- test arithmetic_comparision_test1 + fails
# "[ISO] '=:='/2: expected(fail)".

arithmetic_comparision_test1 :- '=:='(0, 1).

%test 2
:- test arithmetic_comparision_test2
# "[ISO] '=\\='/2: expected(succeed)".

arithmetic_comparision_test2 :- '=\\='(0, 1).


%test 3
:- test arithmetic_comparision_test3
# "[ISO] '<'/2: expected(succeed)".

arithmetic_comparision_test3 :- '<'(0, 1).

%test 4
:- test arithmetic_comparision_test4 + fails
# "[ISO] '>'/2: expected(fail)".

arithmetic_comparision_test4 :- '>'(0, 1).


%test 5
:- test arithmetic_comparision_test5 + fails
# "[ISO] '>='/2: expected(fail)".

arithmetic_comparision_test5 :- '>='(0, 1).

%test 6
:- test arithmetic_comparision_test6
# "[ISO] '=<'/2: expected(succeed)".

arithmetic_comparision_test6 :- '=<'(0, 1).

%test 7
:- test arithmetic_comparision_test7
# "[ISO] '=:='/2: expected(succeed)".

arithmetic_comparision_test7 :- '=:='(1.0, 1).

%test 8
:- test arithmetic_comparision_test8 + fails
# "[ISO] '=\='/2: expected(fail)".

arithmetic_comparision_test8 :- '=\='(1.0, 1).

%test 9
:- test arithmetic_comparision_test9 + fails
# "[ISO] '<'/2: expected(fail)".

arithmetic_comparision_test9 :- '<'(1.0, 1).

%test 10
:- test arithmetic_comparision_test10 + fails
# "[ISO] '>'/2: expected(fail)".

arithmetic_comparision_test10 :- '>'(1.0, 1).

%test 11
:- test arithmetic_comparision_test11
# "[ISO] '>='/2: expected(succeed)".

arithmetic_comparision_test11 :- '>='(1.0, 1).

%test 12
:- test arithmetic_comparision_test12
# "[ISO] '=<'/2: expected(succeed)".

arithmetic_comparision_test12 :- '=<'(1.0, 1).

%test 13
:- test arithmetic_comparision_test13
# "[ISO] '=:='/2: expected(succeed)".

arithmetic_comparision_test13 :- '=:='(3*2, 7 -1).

%test 14
:- test arithmetic_comparision_test14 + fails
# "[ISO] '=\\='/2: expected(fail)".

arithmetic_comparision_test14 :- '=\\='(3*2, 7 -1).

%test 15
:- test arithmetic_comparision_test15 + fails
# "[ISO] '<'/2: expected(fail)".

arithmetic_comparision_test15 :- '<'(3*2, 7 -1).

%test 16
:- test arithmetic_comparision_test16 + fails
# "[ISO] '>'/2: expected(fail)".

arithmetic_comparision_test16 :- '>'(3*2, 7 -1).

%test 17
:- test arithmetic_comparision_test17
# "[ISO] '>='/2: expected(succeed)".

arithmetic_comparision_test17 :- '>='(3*2, 7 -1).

%test 18
:- test arithmetic_comparision_test18
# "[ISO] '=<'/2: expected(succeed)".

arithmetic_comparision_test18 :- '=<'(3*2, 7 -1).

%test 19 
:- test arithmetic_comparision_test19(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '=:='/2: expected(error) bug(fail)".

arithmetic_comparision_test19(X) :- '=:='(X, 5).

%% REVIEW:PENDING                                **Nothrow_vs_iso**
%%   [gprolog]: error(instantiation_error,(=\=)/2)
%%   [ciao]: no throws
%test 20 
:- test arithmetic_comparision_test20(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '=\='/2: expected(error) bug(fail)".

arithmetic_comparision_test20(X) :- '=\='(X, 5).

%% REVIEW:DONE
%test 21 
:- test arithmetic_comparision_test21(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '<'/2: expected(error) bug(fail)".

arithmetic_comparision_test21(X) :- '<'(X, 5).

%% REVIEW:DONE
%test 22 
:- test arithmetic_comparision_test22(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '>'/2: expected(error) bug(fail)".

arithmetic_comparision_test22(X) :- '>'(X, 5).

%% REVIEW:DONE
%test 23 
:- test arithmetic_comparision_test23(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '>='/2: expected(error) bug(fail)".

arithmetic_comparision_test23(X) :- '>='(X, 5).

%% REVIEW:DONE
%test 24 
:- test arithmetic_comparision_test24(X)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] '=<'/2: expected(error) bug(fail)".

arithmetic_comparision_test24(X) :- '=<'(X, 5).


% ===========================================================================
%% 8.8.1.4 These tests are specified in page 77 of the ISO standard %%%%

:- dynamic(cat/0).
cat.

:- dynamic(dog/0).
dog :- true.

elk(X) :- moose(X).

:- dynamic(legs/2).
legs(A, 6) :- insect(A).
legs(A, 7) :- A, call(A).

:- dynamic (insect/1).
insect(ant).
insect(bee).

% ---------------------------------------------------------------------------

%% REVIEW:PENDING                                           **Label_4**
%test 1 
:- test clause_test1
# "[ISO] clause/2: expected(succeed) bug(fail)".

clause_test1 :- clause(cat, true).

%% REVIEW:PENDING                                    **Label_4**
%test 2 
:- test clause_test2
# "[ISO] clause/2: expected(succeed) bug(fail)".

clause_test2:- clause(dog, true).

%% REVIEW:PENDING                                   ** Wrong_vs_iso**
%%   [gprolog]: it is correct
%%   [ciao]: returns a different result
%test 3 
:- test clause_test3(I, Body) => (Body=insect(I))
# "[ISO] clause/2: expected(succeed) bug(fail)".

clause_test3(I, Body) :- clause(legs(I, 6), Body).

%% REVIEW:PENDING                                   ** Wrong_vs_iso**
%%   [gprolog]: it is correct
%%   [ciao]: returns a different result
%test 4 
:- test clause_test4(C, Body) => (Body=(call(C), call(C)))
# "[ISO] clause/2: expected(succeed) bug(fail)".

clause_test4(C, Body) :- clause(legs(C, 7), Body).

%% REVIEW:PENDING                                 ** Wrong_vs_iso**
%%   [gprolog]: it is correct
%%   [ciao]: returns a different result
%test 5 
:- test clause_test5(Result) => (Result=[[ant, true], [bee, true]])
# "[ISO] clause/2: expected(succeed) bug(fail)".

clause_test5(Result) :- findall([I, T], clause(insect(I), T), Result).

%% REVIEW:PENDING                                    **Label_4**
%test 6                
:- test clause_test6(Body) + fails
# "[ISO] clause/2: expected(fail)".

clause_test6(Body) :- clause(x, Body).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantation_error, _))
%%   [ciao]: no throws
%test 7 
:- test clause_test7(B) + exception(error(instantation_error, Imp_dep))
# "[ISO] clause/2: expected(error) bug(fail)".

clause_test7(B) :- clause(_, B).

%% REVIEW:PENDING                                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 4), _))
%%   [ciao]: no throws
%test 8 
:- test clause_test8(X) + exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] clause/2: expected(error) bug(fail)".

clause_test8(X) :- clause(4, X).

%% REVIEW:PENDING                                                 **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(access, private_procedure, elk/1),_))
%%   [ciao]: throws exception(error(permission_error(modify,static_procedure,'iso_tests:elk'/1),clause/2))
%test 9
:- test clause_test9(N, Body)
	+ exception(error(permission_error(access, private_procedure, elk/1),
		Imp_dep))
# "[ISO] clause/2: expected(error) bug(wrong_error)".

clause_test9(N, Body) :- clause(elk(N), Body).

%% REVIEW:PENDING                                                 **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(permission_error(access, private_procedure, atom/1),_))
%%   [ciao]: throws exception(error(permission_error(modify,static_procedure,'term_typing:atom'/1),clause/2))
%test 10
:- test clause_test10(Body)
	+ exception(error(permission_error(access, private_procedure, atom/1),
		Imp_dep))
# "[ISO] clause/2: expected(error) bug(wrong_error)".

clause_test10(Body) :- clause(atom(_), Body).

%test 11
:- test clause_test11 + fails
# "[ISO] clause/2: expected(fail)".

clause_test11 :- clause(legs(A, 6), insect(f(A))).



%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 5), _))
%%   [ciao]: throws exception(error(permission_error(modify,static_procedure,'iso_tests:f'/1),clause/2))
%test 12 
:- test clause_test12
	+ exception(error(type_error(callable, 5), Imp_dep))
# "[Non-ISO] clause/2: expected(error) bug(fail)".

clause_test12 :- clause(f(_), 5).


% ===========================================================================
%% 8.8.2.4 These tests are specified in page 78 of the ISO standard %%%%


%test 1
:- test currentpredicate_test1
# "[ISO] current_predicate/2: expected(succeed)".

currentpredicate_test1 :- current_predicate(dog/0).


%test 2
:- test currentpredicate_test2 + fails
# "[ISO] current_predicate/2: expected(fail)".

currentpredicate_test2 :- current_predicate(current_predicate/0).


%test 3
:- test currentpredicate_test3(Arity) => (Arity=1)
# "[ISO] current_predicate/2: expected(succeed)".

currentpredicate_test3(Arity) :- current_predicate(elk/Arity).

%% REVIEW:PENDING                                                    **Label_5**
%%   [gprolog]: nondet
%%   [ciao]: succeed
%test 4
:- test currentpredicate_test4(A) + fails
# "[ISO] current_predicate/2: expected(fail)".

currentpredicate_test4(A) :- current_predicate(foo_undefined/A).

%test 5
:- test currentpredicate_test5(Result)
	=> (find_on_list([elk], Result), find_on_list([insect], Result))
# "[ISO] current_predicate/2: expected(succeed)".

currentpredicate_test5(Result) :-
	findall(Name, current_predicate(Name/1), Result).

%% REVIEW:PENDING                                                      **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(predicate_indicator, 4),_))
%%   [ciao]: no throws 
%test 6 
:- test currentpredicate_test6
	+ exception(error(type_error(predicate_indicator, 4), Imp_dep))
# "[ISO] current_predicate/2: expected(error) bug(fail)".

currentpredicate_test6 :- current_predicate(4).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throw exception(error(type_error(predicat_indicator, 0/dog), _))
%%   [ciao]: no throws 
%test 7 
:- test currentpredicate_test7(X) : (X=dog)
	+ exception(error(type_error(predicat_indicator, 0/dog), Imp_dep))
# "[Non-ISO] current_predicate/2: expected(error) bug(fail)".

currentpredicate_test7(X) :- current_predicate(X).

%% REVIEW:PENDING                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception: error(type_error(atom,0),current_predicate/1)
%%   [ciao]: no throws 
%test 8
:- test currentpredicate_test8(X) : (X=0/dog)
	+ exception(error(type_error(predicat_indicator, 0/dog), Imp_dep))
# "[Non-ISO] current_predicate/2: expected(error) bug(fail)".

currentpredicate_test8(X) :- current_predicate(X).

%test 9 
:- test currentpredicate_test9(X, Result)
	=> (find_on_list([cat/0, dog/0, elk/1, insect/1, legs/2], Result))
# "[Non-ISO] current_predicate/2: expected(succeed)".

currentpredicate_test9(X, Result) :- findall(X, current_predicate(X), Result).



% ===========================================================================
%% 8.9.1.4 These tests are specified in page 79 of the ISO standard %%%%


%test 1
:- test asserta_test1
# "[ISO] asserta/2: expected(succeed)".

asserta_test1 :- asserta(legs(octopus, 8)).

%test 2
:- test asserta_test2
# "[ISO] asserta/2: expected(succeed)".

asserta_test2 :- asserta((legs(A, 4) :- animal(A))).

%test 3
:- test asserta_test3
# "[ISO] asserta/2: expected(succeed)".

asserta_test3 :- asserta((foo(A) :- A, call(A))).

%% REVIEW:PENDING                                                         **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error,_))
%%   [ciao]: throws exception(error(type_error(clause,_),asserta/1-1)) 
%test 4
:- test asserta_test4 + exception(error(instantiation_error, Imp_dep))
# "[ISO] asserta/2: expected(error) bug(wrong_error)".

asserta_test4 :- asserta(_).

%% REVIEW:PENDING                                                        **Diffthrow_vs_iso**
%%   [gprolog]: exception(error(type_error(callable, 4), _))
%%   [ciao]: throws exception(error(type_error(clause,4),asserta/1-1))
%test 5
:- test asserta_test5 + exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] asserta/2: expected(error) bug(wrong_error)".

asserta_test5 :- asserta(4).

%% REVIEW:PENDING                                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 4), _))
%%   [ciao]: throws exception(error(type_error(clause,('iso_tests:foo':-4)),asserta/1-1))
%test 6 
:- test asserta_test6 + exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] asserta/2: expected(error) bug(wrong_error)".

asserta_test6 :- asserta((foo :- 4)).

%% REVIEW:PENDING                                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(modify, static_procedure, atom/1), _))
%%   [ciao]: throws exception(error(permission_error(modify,static_procedure,'term_typing:atom'/1),asserta/1))
%test 7 
:- test asserta_test7
	+ exception(error(permission_error(modify, static_procedure, atom/1),
		Imp_dep))
# "[ISO] asserta/2: expected(error) bug(wrong_error)".

asserta_test7 :- asserta((atom(_) :- true)).


% ===========================================================================
%% 8.9.2.4 These tests are specified in page 80 of the ISO standard %%%%


%test 1
:- test assertz_test1
# "[ISO] assertz/2: expected(succeed)".

assertz_test1 :- assertz(legs(spider, 8)).


%test 2
:- test assertz_test2
# "[ISO] assertz/2: expected(succeed)".

assertz_test2 :- assertz((legs(B, 2) :- bird(B))).


%test 3
:- test assertz_test3
# "[ISO] assertz/2: expected(succeed)".

assertz_test3 :- assertz((foo(X) :- X -> call(X))).

%% REVIEW:PENDING                                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error,_))
%%   [ciao]: throws exception(error(type_error(clause,_),assertz/1-1))
%test 4 
:- test assertz_test4 + exception(error(instantiation_error, Imp_dep))
# "[ISO] assertz/2: expected(error) bug(wrong_error)".

assertz_test4 :- assertz(_).

%% REVIEW:PENDING                                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 4), _))
%%   [ciao]: throws exception(error(type_error(clause,4),assertz/1-1))
%test 5 
:- test assertz_test5 + exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] assertz/2: expected(error) bug(wrong_error)".

assertz_test5 :- assertz(4).

%% REVIEW:PENDING                                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 4), _))
%%   [ciao]: throws exception(error(type_error(clause,('iso_tests:foo':-4)),assertz/1-1))
%test 6 
:- test assertz_test6 + exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] assertz/2: expected(error) bug(wrong_error)".

assertz_test6 :- assertz((foo :- 4)).


%% REVIEW:PENDING                                                  **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(permission_error(modify, static_procedure, atom/1),_))
%%   [ciao]: throws  exception(error(permission_error(modify,static_procedure,'term_typing:atom'/1),assertz/1))
%test 7 
:- test assertz_test7
	+ exception(error(permission_error(modify, static_procedure, atom/1),
		Imp_dep))
# "[ISO] assertz/2: expected(error) bug(wrong_error)".

assertz_test7 :- assertz((atom(_) :- true)).


% ===========================================================================
%% 8.9.3.4 These tests are specified in page 81 of the ISO standard %%%%

%test 1
:- test retract_test1
# "[ISO] retract/1: expected(succeed)".

retract_test1 :- retract(legs(octopus, 8)).

%test 2
:- test retract_test2 + fails
# "[ISO] retract/1: expected(fail)".

retract_test2 :- retract(legs(spider, 6)).


%% REVIEW:PENDING                                                          **Label_4**
%test 3
:- test retract_test3(X, T) => (T=bird(X))
# "[ISO] retract/1: expected(succeed) bug(fail)".

retract_test3(X, T) :- retract((legs(X, 2) :-T)).


%% REVIEW:PENDING                                                ** Wrong_vs_iso**
%%   [gprolog]: does not return what was expected
%%   [ciao]: does not return what was expected
%test 4 
:- test retract_test4(Result)
	=> (Result=[[_, 4, animal(A)], [_, 6, insect(A)], [spider, 8, true]])
# "[ISO] retract/1: expected(succeed) bug(fail)".

retract_test4(Result) :-
	findall([X, Y, Z], retract((legs(X, Y) :- Z)), Result).

%test 5 
:- test retract_test5(X, Y, Z) + fails
# "[ISO] retract/1: expected(fail)".

retract_test5(X, Y, Z) :- retract((legs(X, Y) :- Z)).

%test 6 
:- test retract_test6(Result) => (Result=[ant])
	+ user_output("antbee")
# "[ISO] retract/1: expected(succeed)".

retract_test6(Result) :-
	findall(I, (retract(insect(I)), write(I), retract(insect(bee))),
	    Result).

%% REVIEW:PENDING                                               **Label_4**
% %test 7 UNDEFINED but is a bit strange, sometimes succeeds and sometimes fails
% %       Added times(50) to increase the chance the test fails
% :- test retract_test7(A) + times(50).
:- test retract_test7(A). % TODO: fix setup/cleanup in these tests
retract_test7(A) :- retract((foo(A) :- A, call(A))).

%% REVIEW:PENDING                                                  **Label_4**
%test 8
:- test retract_test8(A, B, C) => (A=call(C), B=call(C))
# "[ISO] retract/1: expected(succeed) bug(fail)".

retract_test8(A, B, C) :- retract((foo(C) :- A -> B)).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 9 
:- test retract_test9(X, Y) + exception(error(instantiation_error, Imp_dep))
# "[ISO] retract/1: expected(error) bug(fail)".

retract_test9(X, Y) :- retract((X :- in_eec(Y))).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(callable, 4), _))
%%   [ciao]: no throws
%test 10 
:- test retract_test10(X)
	+ exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] retract/1: expected(error) bug(fail)".

retract_test10(X) :- retract((4 :- X)).

%% REVIEW:PENDING                                             **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(modify, static_procedure, atom/1),_))
%%   [ciao]:  throws exception(error(permission_error(modify,static_procedure,'term_typing:atom'/1),retract/1))
%test 11 
:- test retract_test11(X)
	+ exception(error(permission_error(modify, static_procedure, atom/1),
		Imp_dep))
# "[ISO] retract/2: expected(error) bug(wrong_error)".

retract_test11(X) :- retract((atom(X) :- X == '[]')).

% ===========================================================================
%% 8.9.4.4 These tests are specified in page 82 of the ISO standard %%%%

%test 1                                                 
:- test abolish_test1
# "[ISO] abolish/1: expected(succeed)".

abolish_test1 :- abolish(foo/2).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 2 
:- test abolish_test2
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] abolish/1: expected(error) bug(fail)".

abolish_test2 :- abolish(foo/_).

%% REVIEW:PENDING                                                   **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(predicate_indicator, foo),_))
%%   [ciao]: no throws
%test 3 
:- test abolish_test3
	+ exception(error(type_error(predicate_indicator, foo), Imp_dep))
# "[ISO] abolish/1: expected(error) bug(fail)".

abolish_test3 :- abolish(foo).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(predicate_indicator, foo(_)),_))
%%   [ciao]: no throws
%test 4 
:- test abolish_test4
	+ exception(error(type_error(predicate_indicator, foo(_)), Imp_dep))
# "[ISO] abolish/1: expected(error) bug(fail)".

abolish_test4 :- abolish(foo(_)).

% %test 5
% :- test abolish_test5(X) : 
%        (X=abolish/1) 
% 	+ exception(error(permission_error(modify,static_procedure,abolish/1),Imp_dep))
% # "[ISO] abolish/1: expected(error) bug(succeed)".
%
% abolish_test5(X) :- abolish(X).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%% THESE PREDICATES ARE NECESARIES FOR THE NEXT TESTS %%%%%%%%%%%%%%%%
:- dynamic(foo/1).

% ---------------------------------------------------------------------------

%test 6
:- test abolish_test6
# "[Non-ISO] abolish/1: expected(succeed)".

abolish_test6 :- abolish(foo/1).

%test 7
:- test abolish_test7(Result)
	=> (Result=[ant, bee])
# "[Non-ISO] abolish/1: expected(succeed)".

abolish_test7(Result) :-
	asserta(insect(bee)), asserta(insect(ant)),
	findall(X, (insect(X), abolish(insect/1)), Result).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 8
:- test abolish_test8 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test8 :- abolish(foo/_).

%% REVIEW:PENDING                                             **Nothrow_vs_iso**
%%   [gprolog]: no throws
%%   [ciao]: no throws
%test 9 
:- test abolish_test9
	+ exception(error(permission_error(modify, static_procedure, bar/1),
		Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(succeed)".

abolish_test9 :- abolish(bar/1).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, a), _))
%%   [ciao]: no throws
%test 10  
:- test abolish_test10
	+ exception(error(type_error(integer, a), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test10 :- abolish(foo/a).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(not_less_than_zero, -1),_))
%%   [ciao]: no throws
%test 11 
:- test abolish_test11
	+ exception(error(domain_error(not_less_than_zero, -1), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test11 :- abolish(foo /(-1)).

%% REVIEW:PENDING                                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(representation_error(max_arity), _))
%%   [ciao]: no throws
%test 12 
:- test abolish_test12(X)
	: (current_prolog_flag(max_arity, M), X is M+1)
	+ exception(error(representation_error(max_arity), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test12(X) :- abolish(foo/X).

%% REVIEW:PENDING                                                   **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 5), _))
%%   [ciao]: no throws
%test 13 
:- test abolish_test13 + exception(error(type_error(atom, 5), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test13 :- abolish(5/a).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(predicate_indicator, insect), _))
%%   [ciao]: no throws
%test 14  
:- test abolish_test14            
	+ exception(error(type_error(predicate_indicator, insect), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(fail)".

abolish_test14 :- abolish(insect).

% ===========================================================================
%% 8.10.1.4 These tests are specified in page 83 of the ISO standard %%%

%test 1
:- test findall_test1(Result) => (Result=[1, 2])
# "[ISO] findall/3: expected(succeed)".

findall_test1(Result) :- findall(X, (X=1;X=2), Result).


%test 2
:- test findall_test2(Result, Y) => (Result=[1+_])
# "[ISO] findall/3: expected(succeed)".

findall_test2(Result, Y) :- findall(X+Y, (X=1), Result).


%test 3
:- test findall_test3(Result, X) => (Result=[])
# "[ISO] findall/3: expected(succeed)".

findall_test3(Result, X) :- findall(X, fail, Result).


%test 4
:- test findall_test4(Result) => (Result=[1, 1])
# "[ISO] findall/3: expected(succeed)".

findall_test4(Result) :- findall(X, (X=1;X=1), Result).


%test 5
:- test findall_test5 + fails
# "[ISO] findall/3: expected(fail)".

findall_test5 :- findall(X, (X=2;X=1), [1, 2]).

%test 6
:- test findall_test6(X, Y) => (X=1, Y=2)
# "[ISO] findall/3: expected(succeed)".

findall_test6(X, Y) :- findall(X, (X=1;X=2), [X, Y]).

%test 7
:- test findall_test7(X, Goal, Result)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] findall/3: expected(error)".

findall_test7(X, Goal, Result) :- findall(X, Goal, Result).

%test 8
:- test findall_test8(X, Result)
	+ exception(error(type_error(callable, 4), Imp_dep))
# "[ISO] findall/3: expected(error)".

findall_test8(X, Result) :- findall(X, 4, Result).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                                   **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, [A|1]), _))
%%   [ciao]: no throws
%test 9 
:- test findall_test9
	+ exception(error(type_error(list, [A|1]), Imp_dep))
# "[Non-ISO] findall/3: expected(error) bug(fail)".

findall_test9 :- findall(X, (X=1), [_|1]).



% ===========================================================================
%% 8.10.2.4 These tests are specified in page 84 of the ISO standard %%%

%%%%%%%% THE FOLLOWING PREDICATES WILL BE USED IN THE FOLLOWING TESTS %%%%%%%%
:- dynamic(a/2).
a(1, f(_)).
a(2, f(_)).


:- dynamic(b/2).
b(1, 1).
b(1, 1).
b(1, 2).
b(2, 1).
b(2, 2).
b(2, 2).

% ---------------------------------------------------------------------------

%test 1
:- test bagof_test1(Result) => (Result=[1, 2])
# "[ISO] bagof/3: expected(succeed)".

bagof_test1(Result) :- bagof(X, (X=1;X=2), Result).

%test 2
:- test bagof_test2(X) => (X=[1, 2])
# "[ISO] bagof/3: expected(succeed)".

bagof_test2(X) :- bagof(X, (X=1;X=2), X).

%test 3
:- test bagof_test3(Result, Y, Z) => (Result=[Y, Z])
# "[ISO] bagof/3: expected(succeed)".

bagof_test3(Result, Y, Z) :- bagof(X, (X=Y;X=Z), Result).

%test 4
:- test bagof_test4(Result, X) + fails
# "[ISO] bagof/3: expected(fail)".

bagof_test4(Result, X) :- bagof(X, fail, Result).

%test 5
:- test bagof_test5(Result) => (Result=[[[1], 1], [[1], 2]])
# "[ISO] bagof/3: expected(succeed)".

bagof_test5(Result) :- findall([L, Y], bagof(1, (Y=1;Y=2), L), Result).

%test 6
:- test bagof_test6(Result) => (Result=[f(a, _), f(_, b)])
# "[ISO] bagof/3: expected(succeed)".

bagof_test6(Result) :- bagof(f(X, Y), (X=a;Y=b), Result).

%test 7
:- test bagof_test7(Result) => (Result=[1, 2])
# "[ISO] bagof/3: expected(succeed)".

bagof_test7(Result) :- bagof(X, Y^((X=1, Y=1);(X=2, Y=2)), Result).

%test 8
:- test bagof_test8(Result)
	=> (Result=[1, _, 2])
# "[ISO] bagof/3: expected(succeed)".

bagof_test8(Result) :- bagof(X, Y^((X=1;Y=1);(X=2, Y=2)), Result).

%test 9 
:- test bagof_test9(Result)
	=> (Result=[1, _, 3])
# "[ISO] bagof/3: expected(succeed)".

bagof_test9(Result) :- bagof(X, (Y^(X=1;Y=2) ;X=3), Result).

%% REVIEW:DONE
%test10
% Note: results of this test are represented as list of sol/? terms,
%   capturing both the solution and relevant bindings, so that we can
%   check the results consistently (due to variable renamings)
:- test bagof_test10(Sols) =>
    ( Result=[sol(1,_,[_]), sol(Y2,Z2,[Y2,Z2])]
    ; Result=[sol(Y1,Z1,[Y1,Z1]), sol(1,_,[_])]
    ) # "[ISO] bagof/3: expected(succeed)".

bagof_test10(Sols) :-
    findall(sol(Y,Z,L), bagof_test10_(Y,Z,L), Sols).

bagof_test10_(Y,Z,L) :-
    bagof(X, (X=Y;X=Z;Y=1), L).

%test 11
:- test bagof_test11(Result, Y) => (Result=[1, 2], Y=f(_))
# "[ISO] bagof/3: expected(succeed)".

bagof_test11(Result, Y) :- bagof(X, a(X, Y), Result).

%test 12 
:- test bagof_test12(Result, Y) => (Result=[[[1, 1, 2], 1], [[1, 2, 2], 2]])
# "[ISO] bagof/3: expected(succeed)".

bagof_test12(Result, Y) :- findall([L, Y], bagof(X, b(X, Y), L), Result).

%test 13
:- test bagof_test13(Result, X, Y, Z)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] bagof/3: expected(error)".

bagof_test13(Result, X, Y, Z) :- bagof(X, Y^Z, Result).

%test 14
:- test bagof_test14(Result, X)
	+ exception(error(type_error(callable, 1), Imp_dep))
# "[ISO] bagof/3: expected(error)".

bagof_test14(Result, X) :- bagof(X, 1, Result).



% ===========================================================================
%% 8.10.3.4 These tests are specified in page 85 of the ISO standard %%%


%%%%%%%% THE FOLLOWING PREDICATES WILL BE USED IN THE FOLLOWING TESTS %%%%%%%%

% Note: member whas renamed to member_ to avoid clashes with member/2
% in basic_props -- EMM

:-dynamic (member_/2).
member_(X, [X|_]).
member_(X, [_|L]) :- member_(X, L).


:- dynamic(d/3).
d(1, 1).
d(1, 2).
d(1, 1).
d(2, 2).
d(2, 1).
d(2, 2).

% ---------------------------------------------------------------------------

%test 1
:- test setof_test1(Result) => (Result=[1, 2])
# "[ISO] setof/3: expected(succeed)".

setof_test1(Result) :- setof(X, (X=1;X=2), Result).

%test 2
:- test setof_test2(X) => (X=[1, 2])
# "[ISO] setof/3: expected(succeed)".

setof_test2(X) :- setof(X, (X=1;X=2), X).

%test 3
:- test setof_test3(Result) => (Result=[1, 2])
# "[ISO] setof/3: expected(succeed)".

setof_test3(Result) :- setof(X, (X=2;X=1), Result).

%test 4
:- test setof_test4(Result) => (Result=[2])
# "[ISO] setof/3: expected(succeed)".

setof_test4(Result) :- setof(X, (X=2;X=2), Result).

%test 5
:- test setof_test5(Result, Y, Z) => (Result=[Y, Z] ;S=[Z, Y])
# "[ISO] setof/3: expected(impldep)".

setof_test5(Result, Y, Z) :- setof(X, (X=Y;X=Z), Result).

%test 6
:- test setof_test6(Result, X) + fails
# "[ISO] setof/3: expected(fail)".

setof_test6(Result, X) :- setof(X, fail, Result).

%test 7
:- test setof_test7(Result) => (Result=[[[1], 1], [[1], 2]])
# "[ISO] setof/3: expected(succeed)".

setof_test7(Result) :- findall([L, Y], setof(1, (Y=2;Y=1), L), Result).

%test 8
:- test setof_test8(Result) => (Result=[f(_, b), f(a, _)])
# "[ISO] setof/3: expected(succeed)".

setof_test8(Result) :- setof(f(X, Y), (X=a;Y=b), Result).

%% REVIEW:PENDING                                     ** Wrong_vs_iso**
%%   [gprolog]: throws exception: error(existence_error(procedure,(^)/2),setof/3)
%%   [ciao]:   _1=[1]
%test 9 
:- test setof_test9(Result) => (Result=[1, 2])
# "[ISO] setof/3: expected(succeed)".

setof_test9(Result) :- setof(X, (Y^(X=1, Y=1);(X=2, Y=2)), Result).

%test 10 
:- test setof_test10(Result) => (Result=[_, 1, 2])
# "[ISO] setof/3: expected(succeed)".

setof_test10(Result) :- setof(X, Y^((X=1;Y=1);(X=2, Y=2)), Result).

%test 11 
:- test setof_test11(Result, Y) => (Result=[_, 1, 3])
# "[ISO] setof/3: expected(succeed)".

setof_test11(Result, Y) :- setof(X, (Y^(X=1;Y=2) ;X=3), Result).

%% REVIEW:DONE                   
%test 12 
% Note: results of this test are represented as list of sol/? terms,
%   capturing both the solution and relevant bindings, so that we can
%   check the results consistently (due to variable renamings)
:- test setof_test12(Sols) =>
   ( Result = [sol(1,_,[_]),sol(Y2,Z2,[Y2,Z2])]
   ; Result = [sol(Y1,Z1,[Y1,Z1]),sol(1,_,[_])]
   ) # "[ISO] setof/3: expected(succeed)".

setof_test12(Sols) :-
    findall(sol(Y,Z,S), setof_test12_(Y,Z,S), Sols).

setof_test12_(Y, Z, S) :-
    setof(X, (X=Y;X=Z;Y=1), S).

%test 13
:- test setof_test13(Result, Y) => (Result=[1, 2], Y=f(_))
# "[ISO] setof/3: expected(succeed)".

setof_test13(Result, Y) :- setof(X, a(X, Y), Result).

%test 14 
:- test setof_test14(Y, Z, Result)
	=> (Result=[f(Y, b), f(Z, c)] ;L=[f(Z, c), f(Y, b)])
# "[ISO] setof/3: expected(impldep)".

setof_test14(Y, Z, Result) :- setof(X, member_(X, [f(Y, b), f(Z, c)]), Result).

%test 15 
:- test setof_test15(Y, Z) + fails
# "[ISO] setof/3: expected(fail)".

setof_test15(Y, Z) :- setof(X, member_(X, [f(Y, b), f(Z, c)]),
	    [f(a, c), f(a, b)]).

%% REVIEW:PENDING                                                ** Wrong_vs_iso**
%%   [gprolog]:  _1=Y
%%   [ciao]:  _1=Y
%test 16
:- test setof_test16(Result, Y, Z) => (Y=a, Z=a)
# "[ISO] setof/3: expected(succeed)".

setof_test16(Result, Y, Z) :- setof(X, member_(X, [f(b, Y), f(c, Z), [f(b, a),
			f(c, a)]]), Result).

%test 17
:- test setof_test17(Y, Z, Result)
	=> (Result=[Y, Z, f(Y), f(Z)] ;Result=[Z, Y, f(Z), f(Y)])
# "[ISO] setof/3: expected(succeed)".

setof_test17(Y, Z, Result) :- setof(X, member_(X, [Z, Y, f(Y), f(Z)]), Result).

%test 18
:- test setof_test18(Y, Z) => ((Y=a, Z=b);(Y=b, Z=a))
# "[ISO] setof/3: expected(succeed)".

setof_test18(Y, Z) :-
	setof(X, member_(X, [Z, Y, f(Y), f(Z)]), [a, b, f(a), f(b)]).

%test 19
:- test setof_test19(Y, Z) + fails
# "[ISO] setof/3: expected(fail)".

setof_test19(Y, Z) :-
	setof(X, member_(X, [Z, Y, f(Y), f(Z)]), [a, b, f(b), f(a)]).

%test 20
:- test setof_test20(Y, Z)
# "[ISO] setof/3: expected(succeed)".

setof_test20(Y, Z) :-
	setof(X, (exists(Y, Z) ^member_(X, [Z, Y, f(Y), f(Z)])),
	    [a, b, f(b), f(a)]).

%test 21 
:- test setof_test21(Y, Result)
	=> (Result=[[[1, 2], 1], [[1, 2], 2]])
# "[ISO] setof/3: expected(succeed)".

setof_test21(Y, Result) :- findall([L, Y], setof(X, b(X, Y), L), Result).

%test 22
:- test setof_test22(Y, Result) => (Result=[1-[1, 2], 2-[1, 2]])
# "[ISO] setof/3: expected(succeed)".

setof_test22(Y, Result) :- setof(X-Z, Y^setof(Y, b(X, Y), Z), Result).

%test 23
:- test setof_test23(Y, Result) => (Result=[1-[1, 2], 2-[1, 2]], Y=_)
# "[ISO] setof/3: expected(succeed)".

setof_test23(Y, Result) :- setof(X-Z, setof(Y, b(X, Y), Z), Result).

%test 24
:- test setof_test24(Y, Result) => (Result=[1-[1, 2, 1], 2-[2, 1, 2]], Y=_)
# "[ISO] setof/3: expected(succeed)".

setof_test24(Y, Result) :- setof(X-Z, bagof(Y, d(X, Y), Z), Result).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 25
:- test setof_test25(Result) : (Result=[f(g(Z), Z)])
# "[Non-ISO] setof/3: expected(succeed)".

setof_test25(Result) :- setof(f(X, Y), X=Y, Result).

%test 26
:- test setof_test26(Result)
	+ exception(error(type_error(callable, 4), Imp_dep))
# "[Non-ISO] setof/3: expected(error)".

setof_test26(Result) :- setof(X, X^(true;4), Result).

%test 27
:- test setof_test27(Result)
	+ exception(error(type_error(callable, 1), Imp_dep))
# "[Non-ISO] setof/3: expected(error)".

setof_test27(Result) :- setof(_X, Y^Y^1, Result).

%test 28
:- test setof_test28(A) => (A=[])
# "[Non-ISO] setof/3: expected(succeed)".

setof_test28(A) :- setof(X, X=1, [1|A]).

%% REVIEW:PENDING                      **It's correct in GNU**                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, [A|1]), _))
%%   [ciao]: no throws
%test 29 
:- test setof_test29
	+ exception(error(type_error(list, [A|1]), Imp_dep))
# "[Non-ISO] setof/3: expected(error) bug(fail)".

setof_test29 :- setof(X, X=1, [_|1]).



%% 8.11.1 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 86 of the ISO standard.                                           %%


%test1
:- test currentinput_test1(S)
# "[Non-ISO] current_input/1: expected(succeed)".

currentinput_test1(S) :- current_input(S).

%% REVIEW:PENDING                                                             **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(stream, foo), _))
%%   [ciao]:  throws exception(error(domain_error(stream_or_alias,foo),'stream_basic:current_output'/1-1))
%test2 
:- test currentinput_test2
	+ exception(error(domain_error(stream, foo), Imp_dep))
# "[Non-ISO] current_input/1: expected(error) bug(wrong_error)".

currentinput_test2 :- current_input(foo).

%test3
:- test currentinput_test3(S) : (current_output(S)) + fails
# "[Non-ISO] current_input/1: expected(fail)".

currentinput_test3(S) :- current_input(S).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: no throws
%%   [ciao]: no throws
%test 4 
:- test currentinput_test4(S2)
	: ( open('/tmp/foo', write, S, [type(text)]),
	    close(S),
	    open('/tmp/foo', read, S2, []),
	    close(S2) )
	+ exception(error(domain_error(stream, S2), Imp_dep))
# "[Non-ISO] current_input/1: expected(error) bug(fail)".

currentinput_test4(S2) :- current_input(S2).

%test5
:- test currentinput_test5(S) : (current_input(S))
# "[Non-ISO] current_input/1: expected(succeed)".

currentinput_test5(S) :- current_input(S).


%% 8.11.2 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 86 of the ISO standard.                                           %%


%test1
:- test currentoutput_test1(S)
# "[Non-ISO] current_output/1: expected(succeed)".

currentoutput_test1(S) :- current_output(S).

%% REVIEW:PENDING                                                  **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(domain_error(stream, foo), _))
%%   [ciao]: no throws
%test2 
:- test currentoutput_test2
	+ exception(error(domain_error(stream, foo), Imp_dep))
# "[Non-ISO] current_output/1: expected(error) bug(wrong_error)".

currentoutput_test2 :- current_output(foo).

%test3
:- test currentoutput_test3(S) : (current_input(S)) + fails
# "[Non-ISO] current_output/1: expected(fail)".

currentoutput_test3(S) :- current_output(S).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: no throws
%%   [ciao]: no throws
%test4 
:- test currentoutput_test4(S)
	: (open('/tmp/foo', write, S, [type(text)]), close(S))
	+ exception(error(domain_error(stream, S), Imp_dep))
# "[Non-ISO] current_output/1: expected(error) bug(fail)".

currentoutput_test4(S) :- current_output(S).


%test5 
:- test currentoutput_test5(S) : (current_output(S))
# "[Non-ISO] current_output/1: expected(succeed) bug(fail)".

currentoutput_test5(S) :- current_output(S).



%% 8.11.3 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 87 of the ISO standard.                                           %%

%test1
:- test setinput_test1(S) : (current_input(S))
# "[Non-ISO] set_input/1: expected(succeed)".

setinput_test1(S) :- set_input(S).

%test2 
:- test setinput_test2 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] set_input/1: expected(error)".

setinput_test2 :- set_input(_).

%test3 
:- test setinput_test3
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] set_input/1: expected(error)".

setinput_test3 :- set_input(foo).

%test 4 
:- test setinput_test4(S1) :
	( open('/tmp/foo', write, S, []),
	    close(S),
	    open('/tmp/foo', read, S1, []),
	    close(S1) )
	+ exception(error(existence_error(stream, S1), Imp_dep))
# "[Non-ISO] abolish/1: expected(error) bug(succeed)".

setinput_test4(S1) :- set_input(S1).

%% REVIEW:PENDING                                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(permission_error(input, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(access,stream,user_output),'stream_basic:set_input'/1-1))
%test5 
:- test setinput_test5(S) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] set_input/1: expected(error) bug(wrong_error)".

setinput_test5(S) :- set_input(S).



% ===========================================================================
%% 8.11.4 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 87 of the ISO standard.                                           %%

%test 1 
:- test setoutput_test1(S) : (current_output(S)).
setoutput_test1(S) :- set_output(S).


%test2 
:- test setoutput_test2 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] set_output/1: expected(error)".

setoutput_test2 :- set_output(_).


%test3 
:- test setoutput_test3
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] set_output/1: expected(error)".

setoutput_test3 :- set_output(foo).

%test4
:- test setoutput_test4(S) :
	(open('/tmp/foo', write, S, []), close(S), current_output(Sc))
	=> (close_outstreams(Sc, S))
	+ exception(error(existence_error(stream, S_or_a), Imp_dep))
# "[Non-ISO] set_output/1: expected(error) bug(wrong_error)".

setoutput_test4(S) :- set_output(S).

%% REVIEW:PENDING                                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(permission_error(output, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(modify,stream,user_input),'stream_basic:set_output'/1-1))
%test5 
:- test setoutput_test5(S) : (current_input(S))
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] set_output/1: expected(error) bug(wrong_error)".

setoutput_test5(S) :- set_output(S).


%% 8.11.5.4 These tests are specified in page 88 of the ISO standard. %%

%% REVIEW:PENDING                                          **Label_6**
%test1 
:- test open_test1(Stream) :
	(open('/tmp/roger data', write, S, [type(binary)]), close(S))
	=> (current_input(Sc), set_input(Stream), close_instreams(Sc, Stream))
# "[ISO] open/4: expected(succeed)".

open_test1(Stream) :- open('/tmp/roger data', read, Stream, [type(binary)]).

%% REVIEW:PENDING                                         **Label_6**
%test 2 
:- test open_test2(S)
	=> (current_output(Sc), set_output(S), close_outstreams(Sc, S))
# "[ISO] open/4: expected(succeed)".

open_test2(S) :- open('/tmp/scowen', write, S, [alias(editor)]).

%% REVIEW:PENDING                                     **Label_6**
%test3
:- test open_test3(Stream) :
	(open('/tmp/data', write, S, []), close(S))
	=> (current_input(Sc), set_input(Stream), close_instreams(Sc, Stream))
# "[ISO] open/4: expected(succeed)".

open_test3(Stream) :- open('/tmp/data', read, Stream, []).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 4 
:- test open_test4 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test4 :- open(_, read, _).


%test 5 
:- test open_test5
	+ exception(error(domain_error(source_sink, Source_sink), Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test5 :- open('/tmp/f', _, _).

%% REVIEW:PENDING                                                      **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 6 
:- test open_test6 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] open/4: expected(error)".

open_test6 :- open('/tmp/f', write, _, _).

%% REVIEW:PENDING                                                      **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(error(instantiation_error,_))
%%   [ciao]: no throws
%test 7 .
:- test open_test7 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] opoen/4: expected(error) bug(succeed)".

open_test7 :- open('/tmp/f', write, _, [type(text)|_]).

%% REVIEW:PENDING                                                       **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: throws exception(error(type_error(atom,_),'stream_basic:$open'/4-4))
%test 8
:- test open_test8 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] open/4: expected(error) bug(wrong_error)".

open_test8 :- open('/tmp/f', write, _, [type(text), _]).

%test 9 
:- test open_test9
	+ exception(error(domain_error(source_sink, Source_sink), Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test9 :- open('/tmp/f', 1, _).

%% REVIEW:PENDING                                                         **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, type(text)),_))
%%   [ciao]: no throws
%test 10 
:- test open_test10 + exception(error(type_error(list, type(text)), Im_dep))
# "[Non-ISO] open/4: expected(error) bug(wrong_error)".

open_test10 :- open('/tmp/f', write, _, type(text)).

%test 11
:- test open_test11 + exception(error(uninstantiation_error(bar), Imp_dep))
# "[Non-ISO] open/3: expected(error) bug(wrong_error)".

open_test11 :- open('/tmp/f', write, bar).

%test 12 
:- test open_test12
	+ exception(error(domain_error(source_sink, foo(1, 2)), Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test12 :- open(foo(1, 2), write, _).

%test 13
:- test open_test13
	+ exception(error(domain_error(source_sink, Source_sink), Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test13 :- open('/tmp/foo', red, _).

%% REVIEW:PENDING                                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(stream_option, bar),_))
%%   [ciao]: throws exception(error(domain_error(open_option_list,[bar]),open/4-4)
%test 14 
:- test open_test14
	+ exception(error(domain_error(stream_option, bar), Imp_dep))
# "[Non-ISO] open/4: expected(error) bug(succeed)".

open_test14 :- open('/tmp/foo', write, _, [bar]).

%test 15
:- test open_test15
	+ exception(error(existence_error(source_sink, Source_sink), Imp_dep))
# "[Non-ISO] open/3: expected(error)".

open_test15 :- open('nonexistent', read, _).

%test 16 
:- test open_test16 : (open('/tmp/foo', write, _, [alias(a)]))
	+ exception(error(permission_error(open, source_sink, alias(a)),
		Imp_dep))
# "[Non-ISO] open/4: expected(error) bug(succeed)".

open_test16 :- open('/tmp/bar', write, _, [alias(a)]).

%% REVIEW:PENDING                                                           **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(open, source_sink, reposition(true)), _))
%%   [ciao]: throws exception(error(domain_error(open_option_list,[reposition(true)]),open/4-4))
%test 17
:- test open_test17
	+ exception(error(permission_error(open, source_sink, reposition(true)
		), Imp_dep))
# "[Non-ISO] open/4: expected(error) bug(succeed)".

open_test17 :- open('/dev/tty', read, _, [reposition(true)]).
% TODO: we will not implement reposition(true) in open/4


% ===========================================================================
%% 8.11.6 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 88 of the ISO standard.                                           %%

%test 1
:- test close_test1(S) : (open('/tmp/foo', write, S))
# "[Non-ISO] close/1: expected(succeed)".

close_test1(S) :- close(S).

%% REVIEW:PENDING                                                           **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: throws exception(error(domain_error(stream_or_alias,_),'stream_basic:close'/1-1))
%test 2 
:- test close_test2 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] close/1: expected(error) bug(wrong_error)".

close_test2 :- close(_).

%% REVIEW:PENDING                                                         **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error,_))
%%   [ciao]: no throws
%test 3 
:- test close_test3(Sc) : (current_input(Sc))
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] close/2: expected(error) bug(succeed)".

close_test3(Sc) :- close(Sc, _).

%% REVIEW:PENDING                                                       **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 4 
:- test close_test4(Sc) : (current_input(Sc))
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] close/2: expected(error) bug(succeed)".

close_test4(Sc) :- close(Sc, [force(true)|_]).

%% REVIEW:PENDING                                                      **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 5 
:- test close_test5(Sc) : (current_input(Sc))
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] close/2: expected(error) bug(succeed)".

close_test5(Sc) :- close(Sc, [force(true), _]).

%% REVIEW:PENDING                                                          **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, foo), _))
%%   [ciao]: no throws
%test 6
:- test close_test6(Sc) : (current_input(Sc))
	+ exception(error(type_error(list, foo), Imp_dep))
# "[Non-ISO] close/2: expected(error) bug(succeed)".

close_test6(Sc) :- close(Sc, foo).

%% REVIEW:PENDING                                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(close_option, foo),_))
%%   [ciao]: no throws
%test 7 
:- test close_test7(Sc) : (current_input(Sc))
	+ exception(error(domain_error(close_option, foo), Imp_dep))
# "[Non-ISO] close/2: expected(error) bug(succeed)".

close_test7(Sc) :- close(Sc, [foo]).

%test 8 
:- test close_test8
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] close/1: expected(error)".

close_test8 :- close(foo).

%% REVIEW:PENDING                                                         **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(existence_error(stream, S), _))
%%   [ciao]: throws  exception(error(domain_error(stream_or_alias,'$stream'(int,int)),'stream_basic:close'/1-1))
%test 9 
:- test close_test9(S) : (open('/tmp/foo', write, S, []), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] close/1: expected(error)".

close_test9(S) :- close(S).



% ===========================================================================
%% 8.11.7 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 89 of the ISO standard.                                           %%

%% REVIEW:PENDING                                              **Label_6**
%test 1
:- test flush_output_test1(S)
	: (open_and_write('/tmp/foo', write, S, [], text, foo))
	=> (close(S), open('/tmp/foo', read, S1, []), read_no_term(S1, "foo"))
# "[Non-ISO] flush_output/1: expected(succeed)".

flush_output_test1(S) :- flush_output(S).

%test 2
:- test flush_output_test2
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] flush_output/1: expected(error)".

flush_output_test2 :- flush_output(foo).

%test 3
:- test flush_output_test3 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] flush_output/1: expected(error)".

flush_output_test3 :- flush_output(_).

%test 4
:- test flush_output_test4(S) :
	(open('/tmp/foo', write, S, []), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] flush_output/1: expected(error) bug(wrong_error)".

flush_output_test4(S) :- flush_output(S).

%% REVIEW:PENDING                                                            **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, stream, S),_))
%%   [ciao]: throws  exception(error(permission_error(modify,stream,'$stream'(int,int)),'stream_basic:flush_output'/1-1))
%test 5 
:- test flush_output_test5(S1) :
	( open('/tmp/foo', write, S, [type(text)]),
	    close(S),
	    open('/tmp/foo', read, S1) )
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] flush_output/1: expected(error) bug(wrong_error)".

flush_output_test5(S1) :- flush_output(S1).

%% REVIEW:PENDING                                                    **Diffthrow_vs_iso**
%%   [gprolog]: throws exception: error(permission_error(open,source_sink,alias(st_o)),open/4)
%%   [ciao]: throws exception(error(domain_error(stream_or_alias,st_o),'stream_basic:flush_output'/1-1))
%test 6 
:- test flush_output_test6 :
	(Alias=st_o, open('/tmp/foo', write, S, [type(text), alias(st_o)]))
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] flush_output/1: expected(error) bug(wrong_error)".

flush_output_test6 :- flush_output(st_o).



% ===========================================================================
%% 8.11.8.4 These tests are specified in page 90 of the ISO standard. %%%


%test 1 
:- test stream_property_test1(L) :
	( open('/tmp/file1.pl', write, SS, []),
	    close(SS),
	    open('/tmp/file1.pl', read, S1, []), open('/tmp/file2.pl', write, S2, []) )
	=> (
	    absolute_file_name('/tmp/file1.pl', File1),
	    absolute_file_name('/tmp/file2.pl', File2),
	    find_path(L, File1),
	    find_path(L, File2))
# "[ISO] stream_property/2: expected(succeed)".

stream_property_test1(L) :- findall(F, stream_property(_, file_name(F)), L).

%% REVIEW:PENDING                                                        **Label_6**
%test 2 
:- test stream_property_test2(L) :
	(open('/tmp/file1', write, S1, []), current_output(Cout))
	=> (find_on_list([S1, Cout], L), close(S1))
# "[ISO] stream_property/2: expected(succeed) bug(fail)".
% TODO: stream_property(_,output) is not implemented

stream_property_test2(L) :- findall(S, stream_property(S, output), L).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                                            **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(stream, foo), _))
%%   [ciao]: no throws
%test 3 
:- test stream_property_test3
	+ exception(error(domain_error(stream, foo), Imp_dep))
# "[Non-ISO] stream_property/2: expected(error) bug(fail)".

stream_property_test3 :- stream_property(foo, _Property).

%% REVIEW:PENDING                                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(stream_property, foo), _))
%%   [ciao]: no throws
%test 4 
:- test stream_property_test4
	+ exception(error(domain_error(stream_property, foo), Imp_dep))
# "[Non-ISO] stream_property/2: expected(error) bug(fail)".

stream_property_test4 :- stream_property(_S, foo).

%% REVIEW:PENDING                                                      **Label_4**
%test 5 
:- test stream_property_test5(S, Property) :
	(current_input(S))
	=> ( find_on_list([input, alias(user_input), eof_action(reset),
		    mode(read), reposition(true), type(text)], Property) )
# "[Non-ISO] stream_property/2: expected(succeed) bug(fail)".
% TODO: we will not implement reposition(true) in open/4

stream_property_test5(S, Property) :- stream_property(S, Property).

%% REVIEW:PENDING                                                     **Label_4**
%test 6 
:- test stream_property_test6(S, Property) :
	(current_output(S))
	=> ( find_on_list([output, alias(user_output), eof_action(reset),
		    mode(append), reposition(false), type(text)], Property) )
# "[Non-ISO] stream_property/2: expected(succeed) bug(fail)".
% TODO: we will not implement reposition(true) in open/4

stream_property_test6(S, Property) :- stream_property(S, Property).

%% REVIEW:DONE                     
%test 7 
:- test stream_property_test7 + fails
# "[Non-ISO] stream_property/2: expected(fail)".

stream_property_test7 :- stream_property(_S, type(binary)).

% ===========================================================================

%% REVIEW:PENDING                                              **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(error(instantiation_error,_))
%%   [ciao]: no throws
%test 1
:- test at_end_of_stream_test1
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] at_end_of_stream/1: expected(error) bug(wrong_error)".

at_end_of_stream_test1 :- at_end_of_stream(_S).

%% REVIEW:PENDING                                         **Nothrow_vs_iso**
%%   [gprolog]: throws error(existence_error(stream,foo),at_end_of_stream/1)
%%   [ciao]: no throws
%test 2 
:- test at_end_of_stream_test2
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] at_end_of_stream/1: expected(error) bug(wrong_error)".

at_end_of_stream_test2 :- at_end_of_stream(foo).

%% REVIEW:PENDING                                            **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(existence_error(stream, S), _))
%%   [ciao]: no throws
%test 3 
:- test at_end_of_stream_test3(S) :
	(open('/tmp/foo', write, S, []), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] at_end_of_stream/1: expected(error) bug(wrong_error)".

at_end_of_stream_test3(S) :- at_end_of_stream(S).

%% REVIEW:PENDING                                                       **Label_6**
%test 4 
:- test at_end_of_stream_test4 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open('/tmp/tmp.in', read, S1,
		[type(text), eof_action(error), alias(st_i)]) )
# "[Non-ISO] at_end_of_stream/1: expected(succeed) bug(error)".

at_end_of_stream_test4 :- at_end_of_stream(st_i).

%% REVIEW:PENDING                                                   **Label_6**
%test 5 
:- test at_end_of_stream_test5 :
	( open('/tmp/tmp.in', write, S, [type(text)]), write_contents(text, a, S),
	    close(S),
	    open('/tmp/tmp.in', read, S1,
		[type(text), eof_action(error), alias(st_i)]) )
	=> (read_no_term(S1, "a")) + fails
# "[Non-ISO] at_end_of_stream/1: expected(fail) bug(error)".

at_end_of_stream_test5 :- at_end_of_stream(st_i).

%% REVIEW:PENDING                                                  **Label_6**
%test 6 
:- test at_end_of_stream_test6 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open('/tmp/tmp.in', read, S1,
		[type(binary), eof_action(error), alias(st_i)]) )
# "[Non-ISO] at_end_of_stream/1: expected(succeed) bug(error)".

at_end_of_stream_test6 :- at_end_of_stream(st_i).

%% REVIEW:PENDING                                             **Label_6**
%test 7 
:- test at_end_of_stream_test7 :
	( open_and_write('/tmp/tmp.in', write, S, [type(binary)], binary, "a"),
	    close(S),
	    open('/tmp/tmp.in', read, S1, [type(binary), eof_action(error),
		    alias(Alias)]) )
	=> (read_no_term(S1, "a")) + fails
# "[Non-ISO] at_end_of_stream/1: expected(fail) bug(error)".

at_end_of_stream_test7 :- at_end_of_stream(st_i).


%% 8.11.9 (FROM SICTUS AND EDDBALI) These tests are specified in the         %%
%% page 90 of the ISO standard.                                           %%

%% REVIEW:PENDING                                                  **Label_6**
%test1
:- test set_stream_position_test1(S, Pos) :
	( open('/tmp/bar', write, S, [reposition(true)]),
	    stream_property(S, position(Pos)) )
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".
% TODO: position(Pos) in stream_property/2 not implemented
% TODO: we will not implement reposition(true) in open/4

set_stream_position_test1(S, Pos) :- stream_property(S, position(Pos)),
	set_stream_position(_, Pos).

%% REVIEW:PENDING                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception: error(permission_error(reposition,stream,'$stream'(0)),set_stream_position/2)
%%   [ciao]: no throws
%test2 
:- test set_stream_position_test2(S, _Pos) : (current_input(S))
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".

set_stream_position_test2(S, _Pos) :- set_stream_position(S, _Pos).

%% REVIEW:PENDING                                              **Label_6**
%test3
:- test set_stream_position_test3(Pos) :
	( open('/tmp/bar', write, S, [reposition(true)]),
	    stream_property(S, position(Pos)) )
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".
% TODO: we will not implement reposition(true) in open/4

set_stream_position_test3(Pos) :- set_stream_position(foo, Pos).

%% REVIEW:PENDING                                              **Label_6**
%test4 
:- test set_stream_position_test4(S, Pos) :
	( open('/tmp/bar', write, S, [reposition(true)]),
	    stream_property(S, position(Pos)),
	    close(S) )
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".
% TODO: we will not implement reposition(true) in open/4

set_stream_position_test4(S, Pos) :- set_stream_position(S, Pos).

%% REVIEW:PENDING                           **Nothrow_vs_iso**
%%   [gprolog]: throwsexception: error(permission_error(reposition,stream,'$stream'(0)),set_stream_position/2)
%%   [ciao]: no throws
%test5 
:- test set_stream_position_test5(S) :
	(current_input(S))
	+ exception(error(domain_error(stream_position, foo), Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".

set_stream_position_test5(S) :- set_stream_position(S, foo).

%% REVIEW:PENDING                                            **Label_4**
%test6 
:- test set_stream_position_test6(S, Pos) :
	( open('/tmp/foo', write, S),
	    stream_property(S, position(Pos)),
	    current_input(S) )
	+ exception(error(permission_error(reposition, stream, S), Imp_dep))
# "[Non-ISO] set_stream_position/2: expected(error) bug(not_implemented)".

set_stream_position_test6(S, Pos) :- set_stream_position(S, Pos).

% ===========================================================================
%% 8.12.1.4 These tests are specified in page 91 of the ISO standard. %%%

%% REVIEW:PENDING                           **Label_6**
%test 1
:- test getchar_test1(Char) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text)], text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text)]) )
	=> (read(X), Char='q', X='werty', close_instreams(Sc, S2))
# "[ISO] get_char/1: expected(succeed)".

getchar_test1(Char) :- get_char(Char).

%% REVIEW:PENDING                       **Label_6**
%test 2
:- test getcode_test2(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text)], text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text)]) )
	=> (read(X), Code=0'q, X='werty', close_instreams(Sc, S2))
# "[ISO] get_code/1: expected(succeed)".

getcode_test2(Code) :- get_code(Code).

%% REVIEW:PENDING                  **Label_6**
%test 3 
:- test getchar_test3(Char)
	: ( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read(X), Char='q', X='werty', close(S2))
# "[ISO] get_char/2: expected(succeed) bug(error)".

getchar_test3(Char) :- get_char(st_i, Char).

%% REVIEW:PENDING                    **Label_6**
%test 4
:- test getcode_test4(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read(X), Code=0'q, X='werty', close(S2))
# "[ISO] get_code/2: expected(succeed) bug(error)".

getcode_test4(Code) :- get_code(st_i, Code).

%% REVIEW:PENDING                               **Label_6**
%test 5 
:- test getchar_test5(Char) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, "'qwerty'"),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read_no_term(S2, "qwerty'"), Char='''')
# "[ISO] get_char/2: expected(succeed) bug(error)".

getchar_test5(Char) :- get_char(st_i, Char).

%% REVIEW:PENDING                       **Label_6**
%test 6 
:- test getcode_test6(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, "'qwerty'"),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read_no_term(S2, "qwerty'"), Code=0''')
# "[ISO] get_code/2: expected(succeed) bug(error)".

getcode_test6(Code) :- get_code(st_i, Code).

%% REVIEW:PENDING                     **Label_6**
%test 7 
:- test getchar_test7 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read(X), close(S2), X=werty) + fails
# "[ISO] get_char/2: expected(fail) bug(error)".

getchar_test7 :- get_char(st_i, p).

%% REVIEW:PENDING                        **Label_6**
%test 8 
:- test getcode_test8 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(binary), alias(st_i)]) )
	=> (read(X), close(S2), X=werty) + fails
# "[ISO] get_code/2: expected(fail) bug(error)".

getcode_test8 :- get_code(st_i, 0'p).

%% REVIEW:PENDING       **Label_6**
%test 9 
:- test getchar_test9(Char) :
	( open('/tmp/tmp.in', write, S1, [type(text), alias(st_i)]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i),
		    eof_action(error)]) )
	=> ( Char=(end_of_file), stream_property(st_i, end_of_stream(past)),
	    close(S2) )
# "[ISO] get_char/2: expected(succeed) bug(error)".

getchar_test9(Char) :- get_char(st_i, Char).

%% REVIEW:PENDING        **Label_6**
%test 10 
:- test getcode_test10(Code) :
	( open('/tmp/tmp.in', write, S1, [type(text), alias(st_i)]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2,
		[type(text), alias(st_i), eof_action(error)]) )
	=> (Code=(-1), stream_property(Alias, end_of_stream(past)), close(S2))
# "[ISO] get_code/2: expected(succeed) bug(error)".

getcode_test10(Code) :- get_code(st_i, Code).

%% REVIEW:PENDING                                                **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_ouput), _))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:get_code'/2-1))
%test 11 
:- test getchar_test11
	+ exception(error(permission_error(input, stream, user_ouput),
		Imp_dep))
# "[ISO] get_char/1: expected(error) bug(wrong_error)".

getchar_test11 :- get_char(user_output, _X).

%% REVIEW:PENDING                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_ouput), _))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:get_code'/2-1))
%test 12 
:- test getcode_test12
	+ exception(error(permission_error(input, stream, user_ouput),
		Imp_dep))
# "[ISO] get_code/1: expected(error) bug(wrong_error)".

getcode_test12 :- get_code(user_output, _X).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 13
:- test getchar_test13 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] get_char/2: expected(error)".

getchar_test13 :- get_char(_, _).

%% REVIEW:PENDING                                                  **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(in_character, 1), _))
%%   [ciao]: throws exception(error(permission_error(access,past_end_of_stream,[]),'io_basic:get_code'/1))
%test 14 
:- test getchar_test14 + exception(error(type_error(in_character, 1), Imp_dep))
# "[Non-ISO] get_char/1: expected(error) bug(wrong_error)".

getchar_test14 :- get_char(1).

%% REVIEW:PENDING                                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(in_character, 1), _))
%%   [ciao]: no throws 
%test 15 
:- test getchar_test15 + exception(error(type_error(in_character, 1), Imp_dep))
# "[Non-ISO] get_char/2: expected(error) bug(wrong_error)".

getchar_test15 :- get_char(user_input, 1).

%test 16
:- test getchar_test16
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] get_char/2: expected(error)".

getchar_test16 :- get_char(foo, _).

% %test 17
:- test getchar_test17(S) :
 	(open('/tmp/foo', write, S, []), close(S))
 	+ exception(error(existence_error(stream, S), Imp_dep)).
 getchar_test17(S) :- get_char(S, _).

 %% REVIEW:PENDING                                           **Diffthrow_vs_iso**
 %%   [gprolog]: throws exception(error(permission_error(input, stream, S), _))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:get_code'/2-1))
%test 18 
:- test getchar_test18(S, _) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] get_char/1: expected(error) bug(wrong_error)".

getchar_test18(S, _) :- get_char(S, _).

%% REVIEW:PENDING                           **Label_6**
%test 19 
:- test getchar_test19 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] get_char/1: expected(error) bug(wrong_error)".

getchar_test19 :- get_char(_).

%% REVIEW:PENDING                            **Label_6**
%test 20
:- test getchar_test20 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1),
	    get_char(X) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, past_end_of_stream, S1),
		Imp_dep))
# "[Non-ISO] get_char/1: expected(error) bug(wrong_error)".

getchar_test20 :- get_char(_).

%% REVIEW:PENDING                               **Label_6**
%test 21
:- test getchar_test21(S1, Char1, Char2) :
	( open_and_write('/tmp/t', write, S, [type(text)], text, ''),
	    close(S),
	    open('/tmp/t', read, S1, [eof_action(eof_code)]) )
	=>(Char1=end_of_file, Char2=end_of_file)
# "[Non-ISO] get_char/2: expected(succeed) bug(error)".

getchar_test21(S1, Char1, Char2) :- get_char(S1, Char1), get_char(S1, Char2).

%% REVIEW:PENDING                                       **Nothrow_vs_iso**
%%   [gprolog]: throws exception: error(existence_error(procedure,open_and_write/6),getchar_test22/0)
%%   [ciao]: no throws
%test 22
:- test getchar_test22(S1) :
	( open_and_write('/tmp/t', write, S, [type(binary)], binary, [0]),
	    close(S),
	    open('/tmp/t', read, S1) )
	+ exception(error(representation_error(character), Imp_dep))
# "[Non-ISO] get_char/2: expected(error) bug(wrong_error)".

getchar_test22(S1) :- get_char(S1, _).

%test 23
:- test getcode_test23 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] get_code/2: expected(error)".

getcode_test23 :- get_code(_, _).

%% REVIEW:PENDING                                            **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, p), _))
%%   [ciao]: throws exception(error(permission_error(access,past_end_of_stream,[]),'io_basic:get_code'/1))
%test 24  
:- test getcode_test24 + exception(error(type_error(integer, p), Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(wrong_error)".

getcode_test24 :- get_code(p).

%% REVIEW:PENDING                                         **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, p), _))
%%   [ciao]: throws exception(error(permission_error(access,past_end_of_stream,user_input),'io_basic:get_code'/2-1))
%test 25 
:- test getcode_test25 + exception(error(type_error(integer, p), Imp_dep))
# "[Non-ISO] get_code/2: expected(error) bug(wrong_error)".

getcode_test25 :- get_code(user_input, p).

%% REVIEW:PENDING                                          **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(representation_error(in_character_code), _))
%%   [ciao]: throws exception(error(permission_error(access,past_end_of_stream,[]),'io_basic:get_code'/1))
%test 26 
:- test getcode_test26
	+ exception(error(representation_error(in_character_code), Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(wrong_error)".

getcode_test26 :- get_code(-2).

%test 27 
:- test getcode_test27
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] get_code/2: expected(error)".

getcode_test27 :- get_code(foo, _).

%test 28 
:- test getcode_test28(S1) :
	( open('/tmp/foo', write, S, []),
	    close(S),
	    open('/tmp/foo', read, S1, []),
	    close(S1) )
	+ exception(error(existence_error(stream, S1), Imp_dep)).

getcode_test28(S1) :- get_code(S1, _).

%% REVIEW:PENDING                                              **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(access,stream,user_output),'io_basic:get_code'/2-1))
%test 29 
:- test getcode_test29(S) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(wrong_error)".

getcode_test29(S) :- get_code(S, _).

%% REVIEW:PENDING                                **Label_6**
%test 30 
:- test getcode_test30 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) ) => (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(succeed)".

getcode_test30 :- get_code(_).

%% REVIEW:PENDING                                     **Label_6**
%test 31
:- test getcode_test31 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1),
	    get_code(X) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, past_end_of_stream, S1),
		Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(wrong_error)".

getcode_test31 :- get_code(_).

%% REVIEW:PENDING                                   **Label_6**
%test 32 
:- test getcode_test32(S1, Code1, Code2) :
	( open_and_write('/tmp/t', write, S, [type(text)], text, ''),
	    close(S),
	    open('/tmp/t', read, S1, [eof_action(eof_code)]) )
	=>(Code1=(-1), Code2=(-1), close(S1))
# "[Non-ISO] get_code/2: expected(succeed) bug(error)".

getcode_test32(S1, Code1, Code2) :- get_code(S1, Code1), get_code(S1, Code2).

%% REVIEW:PENDING                              **Nothrow_vs_iso**
%%   [gprolog]: throws exception: error(existence_error(procedure,open_and_write/6),getcode_test33/0)
%%   [ciao]: no throws
%test 33
:- test getcode_test33(S1) :
	( open_and_write('/tmp/t', write, S, [type(binary)], binary, [0]),
	    close(S),
	    open('/tmp/t', read, S1) )
	+ exception(error(representation_error(character), Imp_dep))
# "[Non-ISO] get_code/2: expected(error) bug(succeed)".

getcode_test33(S1) :- get_code(S1, _).



% ===========================================================================
%% 8.12.2.4 These tests are specified in page 93 of the ISO standard. %%%

%% REVIEW:PENDING                             **Label_6**
%test 1
:- test peekchar_test1(Char) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text)], text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text)]) )
	=> (read(X), Char='q', X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_char/1: expected(succeed)".

peekchar_test1(Char) :- peek_char(Char).

%% REVIEW:PENDING                                **Label_6**
%test 2
:- test peekcode_test2(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text)], text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text)]) )
	=> (read(X), Code=0'q, X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_code/1: expected(succeed)".

peekcode_test2(Code) :- peek_code(Code).

%% REVIEW:PENDING                               **Label_6**
%test 3 
:- test peekchar_test3(Char) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text), alias(st_i)]) )
	=> (read(X), Char='q', X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_char/2: expected(succeed) bug(error)".

peekchar_test3(Char) :- peek_char(st_i, Char).

%% REVIEW:PENDING                            **Label_6**
%test 4 
:- test peekcode_test4(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text), alias(st_i)]) )
	=> (read(X), Code=0'q, X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_code/2: expected(succeed) bug(error)".

peekcode_test4(Code) :- peek_code(st_i, Code).

%% REVIEW:PENDING                         **Label_6**
%test 5 
:- test peekchar_test5(Char) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary), alias(st_i)],
		binary, "'qwerty'."),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(binary), alias(st_i)]) )
	=> (Char='''', read(X), X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_char/2: expected(succeed) bug(error)".

peekchar_test5(Char) :- peek_char(st_i, Char).

%% REVIEW:PENDING                            **Label_6**
%test 6 
:- test peekcode_test6(Code) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary), alias(st_i)],
		binary, "'qwerty'."),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(binary), alias(st_i)]) )
	=> (Code=0''', read(X), X='qwerty', close_instreams(Sc, S2))
# "[ISO] peek_code/2: expected(succeed) bug(error)".

peekcode_test6(Code) :- peek_code(st_i, Code).

%% REVIEW:PENDING                            **Label_6**
%test 7  
:- test peekchar_test7 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(text), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text), alias(st_i)]) )
	=> (read(X), close_instreams(Sc, S2), X=qwerty) + fails
# "[ISO] peek_char/2: expected(fail) bug(error)".

peekchar_test7 :- peek_char(st_i, p).

%% REVIEW:PENDING                              **Label_6**
%test 8 
:- test peekcode_test8 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary), alias(st_i)],
		text, 'qwerty.'),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(binary), alias(st_i)]) )
	=> (read(X), close_instreams(Sc, S2), X=qwerty) + fails
# "[ISO] peek_code/2: expected(fail) bug(error)".

peekcode_test8 :- peek_code(st_i, 0'p).

%% REVIEW:PENDING                                  **Label_6**
%test 9 
:- test peekchar_test9(Char) :
	( open('/tmp/tmp.in', write, S1, [type(text), alias(st_i)]),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text), alias(st_i),
		    eof_action(error)]) )
	=> ( Char=(end_of_file), stream_property(st_i, end_of_stream(at)),
	    close_instreams(Sc, S2) )
# "[ISO] peek_char/2: expected(succeed) bug(error)".

peekchar_test9(Char) :- peek_char(st_i, Char).

%% REVIEW:PENDING                                **Label_6**
%test 10 
:- test peekcode_test10(Code) :
	( open('/tmp/tmp.in', write, S1, [type(text), alias(st_i)]),
	    close(S1),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(text), alias(st_i),
		    eof_action(error)]) )
	=> ( Code=(-1), stream_property(st_i, end_of_stream(at)),
	    close_instreams(Sc, S2) )
# "[ISO] peek_code/2: expected(succeed) bug(error)".

peekcode_test10(Code) :- peek_code(st_i, Code).

%% REVIEW:PENDING                                   **Label_6**
%test 11 
:- test peekchar_test11 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open('/tmp/tmp.in', read, S2, [type(text), eof_action(error),
		    alias(s)]), get_code(s, P) )
	+ exception(error(permission_error(input, past_end_of_stream, S),
		Imp_dep))
# "[ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test11 :- peek_char(s, _).

%% REVIEW:PENDING                                             **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_ouput),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_code'/2-1))
%test 12
:- test peekchar_test12
	+ exception(error(permission_error(input, stream, user_ouput),
		Imp_dep))
# "[ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test12 :- peek_char(user_output, _).

%% REVIEW:PENDING                                              **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_ouput),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_code'/2-1))
%test 13 
:- test peekcode_test13
	+ exception(error(permission_error(input, stream, user_ouput),
		Imp_dep))
# "[ISO] peek_char/2: expected(error) bug(wrong_error)".

peekcode_test13 :- peek_code(user_output, _).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 14
:- test peekchar_test14 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] peek_char/2: expected(error)".

peekchar_test14 :- peek_char(_, _).

%% REVIEW:PENDING                                          **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(in_character, 1),_))
%%   [ciao]: no throws
%test 15 
:- test peekchar_test15
	+ exception(error(type_error(in_character, 1), Imp_dep))
# "[Non-ISO] peek_char/1: expected(error) bug(wrong_error)".

peekchar_test15 :- peek_char(1).

%% REVIEW:PENDING                                              **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(in_character, 1), _))
%%   [ciao]: throws  exception(error(permission_error(access,past_end_of_stream,user_input),'io_basic:peek_code'/2-1))
%test 16 
:- test peekchar_test16
	+ exception(error(type_error(in_character, 1), Imp_dep))
# "[Non-ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test16 :- peek_char(user_input, 1).

%test 17
:- test peekchar_test17
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] peek_char/2: expected(error)".

peekchar_test17 :- peek_char(foo, _).

% %test 18 
:- test peekchar_test18(S1) : ( open('/tmp/foo', write, S),
 	    close(S),
 	    open('/tmp/foo', read, S1),
 	    close(S1) )
 	+ exception(error(existence_error(stream, S1), Imp_dep)).
peekchar_test18(S1) :- peek_char(S1, _).

%% REVIEW:PENDING                                             **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, S), _))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_code'/2-1))
%test 19 
:- test peekchar_test19(S) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test19(S) :- peek_char(S, _).

%% REVIEW:PENDING                                                    **Label_6**
%test 20 
:- test peekchar_test20 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open('/tmp/tmp.in', read, S1, [type(binary), eof_action(error),
		    alias(s)]) )
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test20 :- peek_char(s, _).

%test 21 
:- test peekchar_test21(S1, Char1, Char2)
	: ( open('/tmp/t', write, S, [type(text)]),
	    close(S),
	    open('/tmp/t', read, S1) )
	=> (Char1=end_of_file, Char2=end_of_file)
# "[Non-ISO] peek_char/2: expected(succeed) bug(error)".

peekchar_test21(S1, Char1, Char2) :- peek_char(S1, Char1), peek_char(S1, Char1
	), get_char(S1, Char2).

%% REVIEW:PENDING                               **Nothrow_vs_iso**
%%   [gprolog]: throws exception(existence_error(procedure,open_and_write/6))
%%   [ciao]: no throws
%test 22 
:- test peekchar_test22(S1) :
	( open_and_write('/tmp/t', write, S, [type(binary)], binary, [0]),
	    close(S),
	    open('/tmp/t', read, S1) )
	+ exception(error(representation_error(character), Imp_dep))
# "[Non-ISO] peek_char/2: expected(error) bug(wrong_error)".

peekchar_test22(S1) :- peek_char(S1, _).

%test 23
:- test peekcode_test23 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] peek_code/2: expected(error)".

peekcode_test23 :- peek_code(_, _).

%% REVIEW:PENDING                                             **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, p), _))
%%   [ciao]: no throws
%test 24
:- test peekcode_test24 + exception(error(type_error(integer, p), Imp_dep))
# "[Non-ISO] peek_code/1: expected(error) bug(fail)".

peekcode_test24 :- peek_code(p).

%% REVIEW:PENDING                                                **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, p), _))
%%   [ciao]: throws  exception(error(permission_error(access,past_end_of_stream,user_input),'io_basic:peek_code'/2-1))
%test 25 
:- test peekcode_test25 + exception(error(type_error(integer, p), Imp_dep))
# "[Non-ISO] peek_code/2: expected(error) bug(fail)".

peekcode_test25 :- peek_code(user_input, p).

%% REVIEW:PENDING                                                  **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(representation_error(in_character_code), _))
%%   [ciao]: no throws
%test 26 
:- test peekcode_test26
	+ exception(error(representation_error(in_character_code), Imp_dep))
# "[Non-ISO] peek_code/1: expected(error) bug(fail)".

peekcode_test26 :- peek_code(-2).

%test 27 
:- test peekcode_test27
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] peek_code/2: expected(error)".

peekcode_test27 :- peek_code(foo, _).

% %test 28 
:- test peekcode_test28(S1) : ( open('/tmp/foo', write, S, []),
 	    close(S),
 	    open('/tmp/foo', read, S1, []),
 	    close(S1) )
 	+ exception(error(existence_error(stream, S1), Imp_dep)).

peekcode_test28(S1) :- peek_code(S1, _).

%% REVIEW:PENDING                                                  **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, S), Imp_dep))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_code'/2-1))
%test 29
:- test peekcode_test29(S) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] peek_code/2: expected(error) bug(wrong_error)".

peekcode_test29(S) :- peek_code(S, _).

%% REVIEW:PENDING                                   **Label_6**
%test 30 
:- test peekcode_test30(S1) :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] peek_code/2: expected(error) bug(succeed)".

peekcode_test30(S1) :- peek_code(S1, _).

%% REVIEW:PENDING                                      **Label_6**
%test 31  
:- test peekcode_test31 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1),
	    get_code(X) )
	=> (close_instreams(Sc, S1)) + exception(error(permission_error(input,
		    past_end_of_stream, S1), Imp_dep))
# "[Non-ISO] peek_code/1: expected(error) bug(wrong_error)".

peekcode_test31 :- peek_code(_).

%% REVIEW:PENDING                             **Label_6**
%test 32 
:- test peekcode_test32(Code1, Code2) :
	( open('/tmp/t', write, S, [type(text)]),
	    close(S),
	    open_to_read(t, read, Sc,
		S1, [type(text), eof_action(error)]) )
	=> (close_instreams(Sc, S1), Code1=(-1), Code2=(-1))
# "[Non-ISO] peek_code/1: expected(succeed)".

peekcode_test32(Code1, Code2) :- peek_code(Code1), get_code(Code2).

%% REVIEW:PENDING                                       **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(existence_error(procedure,open_to_read/5))
%%   [ciao]: no throws
%test 33 
:- test peekcode_test33(S1) :
	( open_and_write('/tmp/t', write, S, [type(binary)], binary, [0]),
	    close(S),
	    open('/tmp/t', read, S1) )
	+ exception(error(representation_error(character), Imp_dep))
# "[Non-ISO] peek_code/2: expected(error) bug(succeed)".

peekcode_test33(S1) :- peek_code(S1, _).



% ===========================================================================
%% 8.12.3.4 These tests are specified in page 94 of the ISO standard. %%%

%% REVIEW:PENDING                                   **Label_6**
%test 1
:- test putchar_test1 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text)], text, 'qwer'),
	    current_output(Sc), set_output(S) )
	=>
	( write_contents(text, '.', S),
	    close_outstreams(Sc, S),
	    open_to_read('/tmp/tmp.out', read, Sc1, S1, [type(text)]),
	    read(L),
	    close_instreams(Sc1, S1), L='qwert' )
# "[ISO] put_char/1: expected(succeed) bug(error)".

putchar_test1 :- put_char(t).

%% REVIEW:PENDING                               **Label_6**
%test 2 
:- test putchar_test2 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text), alias(st_o)],
		text, 'qwer') )
	=>
	( write_contents(text, '.', S),
	    close(S),
	    open_to_read('/tmp/tmp.out', read, Sc, S1, [type(text)]),
	    read(L),
	    close_instreams(Sc, S1),
	    L='qwerA' )
# "[ISO] put_char/2: expected(succeed) bug(error)".

putchar_test2 :- put_char(st_o, 'A').

%% REVIEW:PENDING                             **Label_6**
%test 3
:- test putcode_test3 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text)], text, 'qwer'),
	    current_output(Sc),
	    set_output(S) )
	=>
	( write_contents(text, '.', S),
	    close_outstreams(Sc, S),
	    open_to_read('/tmp/tmp.out', read, Sc1, S1, [type(text)]),
	    read(L),
	    close_instreams(Sc1, S1), L='qwert' )
# "[ISO] put_code/1: expected(succeed) bug(error)".

putcode_test3 :- put_code(0't).

%% REVIEW:PENDING                                 **Label_6**
%test 4 
:- test putcode_test4 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text), alias(st_o)],
		text, 'qwer') )
	=> ( write_contents(text, '.', S),
	    close(S),
	    open_to_read('/tmp/tmp.out', read, Sc, S1, [type(text)]),
	    read(L),
	    close_instreams(Sc, S1),
	    L='qwert' )
# "[ISO] put_code/2: expected(succeed) bug(error)".

putcode_test4 :- put_code(st_o, 0't).

%% REVIEW:PENDING                              **Label_6**
%test 5 
:- test putchar_test5 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text)], text, 'qwer'),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "qwer\na") )
# "[ISO] put_char/1: expected(succeed) bug(error)".

putchar_test5 :- nl, put_char(a).

%% REVIEW:PENDING                               **Label_6**
%test 6
:- test putchar_test6 :
	( open_and_write('/tmp/tmp.out', write, S, [type(text), alias(st_o)],
		text, 'qwer') )
	=> ( close(S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "qwer\na") )
# "[ISO] put_char/2: expected(succeed) bug(error)".

putchar_test6 :- nl(st_o), put_char(st_o, a).

%test 7
:- test putchar_test7 + exception(error(instantiation_error, Imp_dep))
# "[ISO] put_char/2: expected(error)".

putchar_test7 :- put_char(my_file, _).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(character, ty), _))
%%   [ciao]: no throws
%test 8
:- test putchar_test8 + exception(error(type_error(character, ty), Imp_dep))
# "[ISO] put_char/2: expected(error) bug(fail)".

putchar_test8 :- put_char(st_o, 'ty').

%test 9 
:- test putcode_test9
	+ exception(error(domain_error(stream_or_alias, S_or_a), Imp_dep))
# "[ISO] put_code/2: expected(error)".

putcode_test9 :- put_code(my_file, _).

%% REVIEW:PENDING                                            **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer,ty),'io_basic:put_code'/2-2))
%%   [ciao]: throws  exception(error(type_error(integer,ty),'io_basic:put_code'/2-2))
%test 10
:- test putcode_test10
	+ exception(error(domain_error(stream_or_alias, S_or_a), Imp_dep))
# "[ISO] put_code/2: expected(error)".

putcode_test10 :- put_code(st_o, 'ty').

%test 11 
:- test nl_test11 + exception(error(instantiation_error, Imp_dep))
# "[ISO] nl/1: expected(error) bug(succeed)".

nl_test11 :- nl(_).

%% REVIEW:PENDING                                                         **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, stream, user_input), _))
%%   [ciao]: throws exception(error(permission_error(modify,stream,user_input),'io_basic:nl'/1-1))
%test 12 
:- test nl_test12
	+ exception(error(permission_error(output, stream, user_input),
		Imp_dep))
# "[ISO] nl/1: expected(error) bug(wrong_error)".

nl_test12 :- nl(user_input).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 13
:- test putchar_test13 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_char/2: expected(error)".

putchar_test13 :- put_char(_, t).


%test 14
:- test putchar_test14 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_char/2: expected(error)".

putchar_test14 :- put_char(_).

%test 15 
:- test putchar_test15(S) : (open('/tmp/foo', write, S), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] put_char/2: expected(error) bug(wrong_error)".

putchar_test15(S) :- put_char(S, a).

%% REVIEW:PENDING                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws  exception(error(permission_error(output, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(modify,stream,'$stream'(int,int)),'io_basic:put_code'/2-1))
%test 16 
:- test putchar_test16(S) : (current_input(S))
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] put_char/2: expected(error) bug(wrong_error)".

putchar_test16(S) :- put_char(S, a).

%% REVIEW:PENDING                                       **Nothrow_vs_iso**
%%   [gprolog]: throws exception(existence_error(procedure,open_and_write/6))
%%   [ciao]: no throws
%test 17 
:- test putchar_test17 :
	( open_and_write('/tmp/tmp.out', write, S, [type(binary)], binary, []),
	    current_output(Sc),
	    set_output(S),
	    current_output(S) )
	+ exception(error(permission_error(output, binary_stream, S), Imp_dep))
# "[Non-ISO] put_char/1: expected(error) bug(succeed)".

putchar_test17 :- put_char(a).

%test 18 
:- test putcode_test18
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_code/2: expected(error)".

putcode_test18 :- put_code(_, 0't).

%test 19
:- test putcode_test19 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_code/2: expected(error)".

putcode_test19 :- put_code(_).

%test 20 
:- test putcode_test20(S) : (open('/tmp/foo', write, S), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] put_code/2: expected(error) bug(wrong_error)".

putcode_test20(S) :- put_code(S, 0'a).

%% REVIEW:PENDING                                       **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(modify,stream,'$stream'(int,int)),'io_basic:put_code'/2-1))
%test 21 
:- test putcode_test21(S) : (current_input(S))
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] put_code/2: expected(error) bug(wrong_error)".

putcode_test21(S) :- put_code(S, 0'a).

%% REVIEW:PENDING                                          **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, binary_stream, S),_))
%%   [ciao]: no throws
%test 22 
:- test putcode_test22(S) : (open('/tmp/t', write, S, [type(binary)]))
	+ exception(error(permission_error(output, binary_stream, S), Imp_dep))
# "[Non-ISO] put_code/2: expected(error) bug(succeed)".

putcode_test22(S) :- put_code(S, 0'a).

%test 23 .
:- test putcode_test23
	+ exception(error(representation_error(character_code), Imp_dep))
# "[Non-ISO] put_code/1: expected(error) bug(wrong_error)".

putcode_test23 :- put_code(-1).

%test 24
:- test putcode_test24
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] put_code/2: expected(error)".

putcode_test24 :- put_code(foo, -1).



% ===========================================================================
%% 8.13.1.4 These tests are specified in page 96 of the ISO standard. %%%

%% REVIEW:PENDING                             **Label_6**
%test 1 
:- test getbyte_test1(Byte) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)], binary, [113, 119,
		    101, 114]), close(S1), open('/tmp/tmp.in', read, S2, [type(
			binary)]) )
	=> (read_no_term(S2, [119, 101, 114]), Byte=113)
# "[ISO] get_byte/1: expected(succeed)".

getbyte_test1(Byte) :- get_byte(Byte).

%% REVIEW:PENDING                               **Label_6**
%test 2 
:- test getbyte_test2(Byte) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)],
		binary, [113, 119, 101, 114]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(text), alias(st_i)]) )
	=> (read_no_term(S2, [119, 101, 114]), Byte=113)
# "[ISO] get_byte/2: expected(succeed) bug(error)".

getbyte_test2(Byte) :- get_byte(st_i, Byte).

%% REVIEW:PENDING                                **Label_6**
%test 3
:- test getbyte_test3 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)],
		binary, [113, 119, 101, 114, 116, 121]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(binary), alias(st_i)]) )
	=> (read_no_term(S2, [113, 119, 101, 114, 116, 121])) + fails
# "[ISO] get_byte/2: expected(fail) bug(error)".

getbyte_test3 :- get_byte(st_i, 114).

%% REVIEW:PENDING                                **Label_6**
%test 4 
:- test getbyte_test4(Byte)
	: ( open('/tmp/tmp.in', write, S1, [type(binary)]),
	    open('/tmp/tmp.in', read, S2, [type(binary), alias(st_i)]) )
	=> (Byte=(-1), stream_property(S2, end_of_stream(past)))
# "[ISO] get_byte/2: expected(succeed) bug(error)".

getbyte_test4(Byte) :- get_byte(st_i, Byte).

%% REVIEW:PENDING                                                   **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_output),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:get_byte'/2-1))
%test 5 
:- test getbyte_test5
	+ exception(error(permission_error(input, stream, user_output),
		Imp_dep))
# "[ISO] get_byte/2: expected(error) bug(wrong_error)".

getbyte_test5 :- get_byte(user_output, _).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 6
:- test getbyte_test6
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] get_byte/2: expected(error)".

getbyte_test6 :- get_byte(_, _).

%% REVIEW:PENDING                                  **Label_6**
%test 7 
:- test getbyte_test7 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]) )
	=> (close_instreams(Sc, S1)) + exception(error(type_error(in_byte, p),
		Imp_dep))
# "[Non-ISO] get_byte/1: expected(error) bug(fail)".

getbyte_test7 :- get_byte(p).

%% REVIEW:PENDING                                 **Label_6**
%test 8 
:- test getbyte_test8 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]) )
	=> (close_instreams(Sc, S1)) + exception(error(type_error(in_byte, -2),
		Imp_dep))
# "[Non-ISO] get_code/1: expected(error) bug(fail)".

getbyte_test8 :- get_byte(-2).

%test 9
:- test getbyte_test9
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] get_byte/2: expected(error)".

getbyte_test9 :- get_byte(foo, _).

% test 10 
:- test getbyte_test10(S1) : ( open('/tmp/foo', write, S, [type(text)]),
	    close(S),
	    open('/tmp/foo', read, S1, [type(binary)]), close(S1) )
	+ exception(error(existence_error(stream, S1), Imp_dep)).

getbyte_test10(S1) :- get_byte(S1, _).

%% REVIEW:PENDING                                               **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(access,stream,user_output),'io_basic:get_byte'/2-1))
%test 11 
:- test getbyte_test11(S) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] get_byte/2: expected(error) bug(wrong_error)".

getbyte_test11(S) :- get_byte(S, _).

%% REVIEW:PENDING                                        **Label_6**
%test 12 
:- test getbyte_test12 :
	( open('/tmp/tmp.in', write, S, [type(text)]), close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, text_stream, S1), Imp_dep))
# "[Non-ISO] get_byte/2: expected(error) bug(succeed)".

getbyte_test12 :- get_byte(_).

%% REVIEW:PENDING                                        **Label_6**
%test 13 .
:- test getbyte_test13 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(bnary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1)) + exception(error(permission_error(input,
		    past_end_of_stream, S1), Imp_dep))
# "[Non-ISO] get_byte1: expected(error) bug(wrong_error)".

getbyte_test13 :- get_byte(_), get_byte(_).


% ===========================================================================
%% 8.13.2.4 These tests are specified in page 97 of the ISO standard. %%%

%% REVIEW:PENDING                                            **Label_4**
%test 1 
:- test peekbyte_test1(Byte) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)],
		binary, [113, 119, 101, 114]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(binary)]) )
	=> (read_no_term(S2, [113, 119, 101, 114]), Byte=113)
# "[ISO] peek_byte/1: expected(succeed) bug(error)".

peekbyte_test1(Byte) :- peek_byte(Byte).

%% REVIEW:PENDING                                           **Label_6**
%test 2
:- test peekbyte_test2(Byte) :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)], binary,
		[113, 119, 101, 114]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(binary), alias(st_i)]) )
	=> (read_no_term(S2, [113, 119, 101, 114]), Byte=113)
# "[ISO] peek_byte/2: expected(succeed) bug(error)".

peekbyte_test2(Byte) :- peek_byte(st_i, Byte).

%% REVIEW:PENDING                                     **Label_6**
%test 3 
:- test peekbyte_test3 :
	( open_and_write('/tmp/tmp.in', write, S1, [type(binary)], binary,
		[113, 119, 101, 114, 116, 121]),
	    close(S1),
	    open('/tmp/tmp.in', read, S2, [type(binary), alias(st_i)]) )
	=> (read_no_term(S2, [113, 119, 101, 114, 116, 121])) + fails
# "[ISO] peek_byte/2: expected(succeed) bug(error)".

peekbyte_test3 :- peek_byte(st_i, 114).

%% REVIEW:PENDING                                      **Label_6**
%test 4 
:- test peekbyte_test4 :
	( open('/tmp/tmp.in', write, S1, [type(binary)]),
	    open_to_read('/tmp/tmp.in', read, Sc, S2, [type(binary), alias(st_i)]) )
	=> ( Byte=(-1), stream_property(S2, end_of_stream(past)),
	    close_instreams(Sc, S2) )
# "[ISO] peek_byte/2: expected(succeed) bug(error)".

peekbyte_test4 :- peek_byte(st_i, _).

%% REVIEW:PENDING                                                     **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, user_output),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_byte'/2-1))
%test 5 
:- test peekbyte_test5
	+ exception(error(permission_error(input, stream, user_output),
		Imp_dep))
# "[ISO] peek_byte/2: expected(error) bug(not_implemented)".

peekbyte_test5 :- peek_byte(user_output, _).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 6
:- test peekbyte_test6 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] peek_byte/2: expected(error)".

peekbyte_test6 :- peek_byte(_, _).

%% REVIEW:PENDING                                            **Label_6**
%test 7 
:- test peekbyte_test7 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]) )
	=> (close_instreams(Sc, S1))
	+ exception(error(type_error(in_byte, p), Imp_dep))
# "[Non-ISO] peek_byte/1: expected(error) bug(fail)".

peekbyte_test7 :- peek_byte(p).

%% REVIEW:PENDING                                   **Label_6**
%test 8 
:- test peekbyte_test8 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]) )
	=> (close_instreams(Sc, S1))
	+ exception(error(type_error(in_byte, -2), Imp_dep))
# "[Non-ISO] peek_byte/1: expected(error) bug(fail)".

peekbyte_test8 :- peek_byte(-2).

%test 9
:- test peekbyte_test9
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] peek_byte/2: expected(error)".

peekbyte_test9 :- peek_byte(foo, _).

%test 10 
:- test peekbyte_test10(S1) :
	( open('/tmp/foo', write, S, [type(text)]),
	    close(S),
	    open('/tmp/foo', read, S1, [type(binary)]),
	    close(S1) )
	+ exception(error(existence_error(stream, S1), Imp_dep)).

peekbyte_test10(S1) :- peek_byte(S1, _).

%% REVIEW:PENDING                                            **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(input, stream, S),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),'io_basic:peek_byte'/2-1))
%test 11
:- test peekbyte_test11(S, _) : (current_output(S))
	+ exception(error(permission_error(input, stream, S), Imp_dep))
# "[Non-ISO] peek_byte/2: expected(error) bug(wrong_error)".

peekbyte_test11(S, _) :- peek_byte(S, _).

%% REVIEW:PENDING                                  **Label_6**
%test 12 
:- test peekbyte_test12 :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, text_stream, S1), Imp_dep))
# "[Non-ISO] peek_byte/1: expected(error) bug(succeed)".

peekbyte_test12 :- peek_byte(_).

%% REVIEW:PENDING                                       **Label_6**
%test 13
:- test peekbyte_test13 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(bnary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, past_end_of_stream, S1),
		Imp_dep))
# "[Non-ISO] peek_byte/1: expected(error) bug(wrong_error)".

peekbyte_test13 :- get_byte(_), peek_byte(_).


% ===========================================================================
%% 8.13.2.4 These tests are specified in page 98 of the ISO standard. %%%

%% REVIEW:PENDING                                     **Label_6**
%test 1 
:- test putbyte_test1 :
	( open_and_write('/tmp/tmp.out', write, S, [type(binary)], binary,
		[113, 119, 101, 114]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(binary)]),
	    read_no_term(S1, [113, 119, 101, 114, 84]) )
# "[ISO] put_byte/1: expected(succeed) bug(error)".

putbyte_test1 :- put_byte(84).

%% REVIEW:PENDING                                       **Label_6**
%test 2
:- test putbyte_test2 :
	( open_and_write('/tmp/tmp.out', write, S, [type(binary), alias(st_i)],
		binary, [113, 119, 101, 114]) )
	=> ( close(S),
	    open('/tmp/tmp.out', read, S1, [type(binary)]),
	    read_no_term(S1, [113, 119, 101, 114, 84]) )
# "[ISO] put_byte/2: expected(succeed) bug(error)".

putbyte_test2 :- put_byte(st_i, 84).

%% REVIEW:PENDING                                          **Diffthrow_vs_iso**
%%   [gprolog]: throws existence_error(stream,my_file),put_byte/2)
%%   [ciao]: throws exception(error(domain_error(stream_or_alias,my_file),'io_basic:put_byte'/2-1))
%test 3 
:- test putbyte_test3 + exception(error(instantiation_error, Imp_dep))
# "[ISO] put_byte/2: expected(error) bug(wrong_error)".

putbyte_test3 :- put_byte(my_file, _).

%test 4 
:- test putbyte_test4 + exception(error(type_error(byte, ty), Imp_dep))
# "[ISO] put_byte/2: expected(error)".

putbyte_test4 :- put_byte(user_output, 'ty').

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 5
:- test putbyte_test5 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test5 :- put_byte(_, 118).

%% REVIEW:PENDING                                  **Label_6**
%test 6
:- test putbyte_test6 :
	( open('/tmp/tmp.out', write, S, [tye(binary)]),
	    current_output(Sc),
	    set_output(S) )
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test6 :- put_byte(_).

%test 7 
:- test putbyte_test7(S) : (open('/tmp/foo', write, S), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] catch: expected(error) bug(wrong_error)".

putbyte_test7(S) :- put_byte(S, 77).

%% REVIEW:PENDING                                      **Label_6**
%test 8 
:- test putbyte_test8(S1) :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(output, stream, S1), Imp_dep))
# "[Non-ISO] put_byte/2: expected(error) bug(wrong_error)".

putbyte_test8(S1) :- put_byte(S1, 99).

%% REVIEW:PENDING                                                   **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, text_stream, S), _))
%%   [ciao]: no throws
%test 9 
:- test putbyte_test9 : (current_output(S))
	+ exception(error(permission_error(output, text_stream, S), Imp_dep))
# "[Non-ISO] put_byte/1: expected(error) bug(succeed)".

putbyte_test9 :- put_byte(99).

%test 10 
:- test putbyte_test10 : ( open('/tmp/tmp.out', write, S, [type(binary)]),
	    set_output(S) )
	+ exception(error(type_error(byte, -1), Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test10 :- put_byte(-1).

%test 11
:- test putbyte_test11 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test11 :- put_byte(_, 1).

%test 12
:- test putbyte_test12
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test12 :- put_byte(foo, 1).

%test 13
:- test putbyte_test13 + exception(error(type_error(byte, ty), Imp_dep))
# "[Non-ISO] put_byte/2: expected(error)".

putbyte_test13 :- put_byte(user_output, 'ty').



% ===========================================================================
%% 8.14.1.4 These tests are specified in page 99 of the ISO standard. %%X

%% REVIEW:PENDING                                      **Label_6**
%test 1 
:- test read_test1(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)],
		text, 'term1. term2.'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1, [type(text)]) )
	=> (X='term1', read(Y), Y='term2', close_instreams(Sc, S1))
# "[ISO] read/1: expected(succeed)".

read_test1(X) :- read(X).

%% REVIEW:PENDING                                         **Label_6**
%test 2
:- test read_test2(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)],
		text, 'term1. term2.'),
	    close(S),
	    open('/tmp/tmp.in', read, S1, [type(text), alias(st_o)]) )
	=> (X='term1', read(Y), Y='term2')
# "[ISO] read/2: expected(succeed) bug(error)".

read_test2(X) :- read(st_o, X).

%% REVIEW:PENDING                                             **Label_6**
%test 3
:- test read_test3(T, VL, VN, VS) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text,
		'foo(A+Roger,A+_). term2.'),
	    close(S),
	    open('/tmp/tmp.in', read, S1, [type(text), alias(st_o)]) )
	=> ( T=foo(X1+X2, X1+X3), VL=[X1, X2, X3], VN=['A'=X1, 'Roger'=X2],
	    VS=['Roger'=X2], read(Y), Y='term2' )
# "[ISO] read_term/2: expected(succeed) bug(error)".

read_test3(T, VL, VN, VS) :-
	read_term(st_o, T, [variables(VL), variable_names(VN),
		singletons(VS)]).

%% REVIEW FAILURE EXPECTED
%test 4 
:- test read_test4 :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, '3.1. term2.'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1, [type(text)]) )
	=> (read(Y), close_instreams(Sc, S1), Y='term2') + fails
# "[ISO] read/1: expected(fail)".

read_test4 :- read(4.1).

%% REVIEW:PENDING                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws existence_error(procedure,open_and_write/6)
%%   [ciao]: throws exception(error(syntax_error([1,1,['operator expected after expression'],['',foo,'\n','** here **','\n','',123,' ','.']]),read/1))
%test 5 
:- test read_test5(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)],
		text, 'foo 123. term2.'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1, [type(text)]) )
	=> (read(Y), close_instreams(Sc, S1), Y='term2')
	+ exception(error(syntax_error(Imp_dep), Imp_dep))
# "[ISO] read/1: expected(error) bug(wrong_error)".

read_test5(X) :- read(X).

%% REVIEW:PENDING                                          **Diffthrow_vs_iso**
%%   [gprolog]: throws existence_error(procedure,open_and_write/6)
%%   [ciao]: throws  exception(error(syntax_error([1,1,['operator expected after expression'],['',3.1,'\n','** here **','\n']]),read/1))
%test 6 
:- test read_test6(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, '3.1'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1, [type(text)]) )
	=>(stream_property(S, end_of_stream(past)), close_instreams(Sc, S1))
	+ exception(error(syntax_error(Imp_dep), Imp_dep))
# "[ISO] read/1: expected(error) bug(wrong_error)".

read_test6(X) :- read(X).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                             **Label_6**
%test 7
:- test read_test7(T, L) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, 'foo(bar).'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (T=foo(bar), L=[], close_instreams(Sc, S1))
# "[Non-ISO] read_term/2: expected(succeed)".

read_test7(T, L) :- read_term(T, [singletons(L)]).

%test 8
:- test read_test8 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] read/2: expected(error)".

read_test8 :- read(_, _).

%test 9
:- test read_test9 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] read_term/3: expected(error)".

read_test9 :- read_term(user_input, _, _).

%test 10
:- test read_test10 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] read_term/3: expected(error)".

read_test10 :- read_term(user_input, _, [variables(_)|_]).

%test 11
:- test read_test11 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] read_term/3: expected(error)".

read_test11 :- read_term(user_input, _, [variables(_), _]).

%test 12
:- test read_test12
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] read/2: expected(error)".

read_test12 :- read(foo, _).

%test 13
:- test read_test13
	+ exception(error(type_error(list, bar), Imp_dep))
# "[Non-ISO] read_term/3: expected(error)".

read_test13 :- read_term(user_input, _, bar).

%test 14
:- test read_test14
	+ exception(error(domain_error(read_option, bar), Imp_dep))
# "[Non-ISO] read_term/3: expected(error)".

read_test14 :- read_term(user_input, _, [bar]).

%% REVIEW:PENDING                                      **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permissioin_error(input, stream, user_output),_))
%%   [ciao]: throws exception(error(permission_error(access,stream,user_output),read_term/3))
%test 15 
:- test read_test15
	+ exception(error(permissioin_error(input, stream, user_output),
		Imp_dep))
# "[Non-ISO] read_term/3: expected(error) bug(wrong_error)".

read_test15 :- read_term(user_output, _, []).

%% REVIEW:PENDING                                            **Label_6**
%test 16
:- test read_test16(T) :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (T=end_of_file, close_instreams(Sc, S1))
# "[Non-ISO] read/1: expected(succeed)".

read_test16(T) :- read(T).

%test 17  
:- test read_test17(S1) : ( open('/tmp/foo', write, S, [type(text)]),
	    close(S),
	    open('/tmp/foo', read, S1, [type(text)]),
	    close(S1) )
	+ exception(error(existence_error(stream, S1), Imp_dep)).

read_test17(S1) :- read_term(S1, _, []).

%% REVIEW:PENDING                                         **Label_6**
%test 18
:- test read_test18 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] read_term/2: expected(error) bug(succeed)".

read_test18 :- read_term(_, []).

%% REVIEW:PENDING                                         **Label_6**
%test 19 
:- test read_test19 :
	( open('/tmp/tmp.in', write, S, [type(binary)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(binary), eof_action(error)]),
	    current_input(S1) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, binary_stream, S1), Imp_dep))
# "[Non-ISO] read/1: expected(error) bug(succeed)".

read_test19 :- read(_).

%% REVIEW:PENDING                                        **Label_6**
%test 20 
:- test read_test20(S1) :
	( open('/tmp/tmp.in', write, S, [type(text)]),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    current_input(S1),
	    get_code(_) )
	=> (close_instreams(Sc, S1))
	+ exception(error(permission_error(input, past_end_of_stream, S1),
		Imp_dep))
# "[Non-ISO] read_term/3: expected(error) bug(wrong_error)".

read_test20(S1) :- read_term(S1, _, []).

% Reformatted to avoid new lines in atoms. --MH
aux_read_test21('foo(\n 	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n 	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1).').

%% REVIEW:PENDING                                            **Label_6**
%test 21
:- test read_test21(Ops) :
	( Ops=[],
	    open('/tmp/tmp.in', write, S, [type(text)]),
	    aux_read_test21(T),
	    write_contents(text, T, S),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	+ exception(error(representation_error(max_arity), Imp_dep))
# "[Non-ISO] read_term/2: expected(error) bug(wrong_error)".

read_test21(Ops) :- read_term(_, Ops).

%% REVIEW:PENDING                                         **Label_6**
%test 22
:- test read_test22 :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "'a."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (close_instreams(Sc, S1))
	+ exception(error(syntax_error, Imp_dep))
# "[Non-ISO] read_term/2: expected(error) bug(wrong_error)".

read_test22 :- read_term(_, []).

%% REVIEW:PENDING                                              **Label_6**
%test 23
:- test read_test23(T) :
	( (current_prolog_flag(max_integer, M) ->true;M=0),
	    number_codes(M, L),
	    atom_codes(Atm, L),
	    open_and_write('/tmp/tmp.in', write, S, [ype(text)], text, Atm),
	    write_contents(text, '.', S),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (T=M, close_instreams(Sc, S1))
# "[Non-ISO] read/1: expected(succeed)".

read_test23(T) :- read(T).

%% REVIEW:PENDING                                          **Label_6**
%test 24
:- test read_test24(T) :
	( (current_prolog_flag(min_integer, M) ->true;M=0),
	    number_codes(M, L),
	    atom_codes(Atm, L),
	    open_and_write('/tmp/tmp.in', write, S, [type(text)], text, Atm),
	    write_contents(text, '.', S),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (T=M, close_instreams(Sc, S1))
# "[Non-ISO] read/1: expected(succeed)".

read_test24(T) :- read(T).



% ===========================================================================
%% 8.14.2.4 These tests are specified in page 100 of the ISO standard. %%

%% REVIEW:PENDING                                                  **Label_6**
%test 1 
:- test write_test1(S) :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( write_contents(text, '.', S),
	    close_outstreams(Sc, S),
	    open_to_read('/tmp/tmp.out', read, Sc1, S1,
		[type(text)]), read(X), X=[1, 2, 3],
	    close_instreams(Sc1, S1) )
# "[ISO] write_term/3: expected(succeed)".

write_test1(S) :- write_term(S, [1, 2, 3], []).

%% REVIEW:PENDING                                        **Label_6**
%test 2 
:- test write_test2 :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "'.'(1,'.'(2,'.'(3,[])))") )
# "[ISO] write_canonical/1: expected(succeed) bug(error)".

write_test2 :- write_canonical([1, 2, 3]).

%% REVIEW:PENDING                                      **Label_6**
%test 3
:- test write_test3(S) :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "1<2") )
# "[ISO] write_term/3: expected(succeed)".

write_test3(S) :- write_term(S, '1<2', []).

%% REVIEW:PENDING                                          **Label_6**
%test 4
:- test write_test4(S) :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S), open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "'1<2'") )
# "[ISO] writeq/2: expected(succeed)".

write_test4(S) :- writeq(S, '1<2').

%% REVIEW:PENDING                                                **Label_6**
%test 5 
:- test write_test5 :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "A") )
# "[ISO] writeq/1: expected(succeed) bug(error)".

write_test5 :- writeq('$VAR'(0)).

%% REVIEW:PENDING                                                    **Label_6**
%test 6 
:- test write_test6(S) :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "$VAR(1)") )
# "[ISO] write_term/3: expected(succeed)".

write_test6(S) :- write_term(S, '$VAR'(1), [numbervars(false)]).

%% REVIEW:PENDING                                                **Label_6**
%test 7
:- test write_test7(S) :
	( open('/tmp/tmp.out', write, S, [type(text)]),
	    current_output(Sc),
	    set_output(S) )
	=> ( close_outstreams(Sc, S),
	    open('/tmp/tmp.out', read, S1, [type(text)]),
	    read_no_term(S1, "Z1") )
# "[ISO] write_term/3: expected(succeed)".

write_test7(S) :- write_term(S, '$VAR'(51), [numbervars(true)]).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 8
:- test write_test8 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] write/2: expected(error)".

write_test8 :- write(_, foo).

%test 9 
:- test write_test9 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test9 :- write_term(foo, _).

%test 10 
:- test write_test10 + exception(error(instantiation_error,Imp_dep)).
write_test10 :- write_term(user_output,foo,_).

%test 11
:- test write_test11
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test11 :- write_term(foo, [quoted(true)|_]).

%test 12 
:- test write_test12 + exception(error(instantiation_error,Imp_dep)).
write_test12 :- write_term(user_output,foo,[quoted(true)|_]).


%test 13
:- test write_test13
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test13 :- write_term(foo, [quoted(true), _]).

%test 14 
:- test write_test14 + exception(error(instantiation_error,Imp_dep)).
write_test14 :- write_term(user_output,foo,[quoted(true),_]).


%test 15 
:- test write_test15 + exception(error(type_error(list,2),Imp_dep)).
write_test15 :- write_term(user_output,1,2).

%% REVIEW:PENDING                                                       **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, [quoted(true)|foo]), _))
%%   [ciao]: throws exception(error(type_error(list,foo),write_term/2-2))
%test 16 
:- test write_test16
	+ exception(error(type_error(list, [quoted(true)|foo]), Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test16 :- write_term(1, [quoted(true)|foo]).

%test 17
:- test write_test17
	+ exception(error(domain_error(stream_or_alias, foo), Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test17 :- write(foo, 1).

%test 18
:- test write_test18
	+ exception(error(domain_error(write_option, foo), Imp_dep))
# "[Non-ISO] write_term/2: expected(error)".

write_test18 :- write_term(1, [quoted(true), foo]).

%test 19 
:- test write_test19(S) : (open('/tmp/foo', write, S), close(S))
	+ exception(error(existence_error(stream, S), Imp_dep))
# "[Non-ISO] write/2: expected(error) bug(wrong_error)".

write_test19(S) :- write(S, a).

%% REVIEW:PENDING                                                **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, stream, S), _))
%%   [ciao]: throws  exception(error(permission_error(modify,stream,'$stream'(int,int)),write/2-1))
%test 20 
:- test write_test20(S) : (current_input(S))
	+ exception(error(permission_error(output, stream, S), Imp_dep))
# "[Non-ISO] write/2: expected(error) bug(wrong_error)".

write_test20(S) :- write(S, a).

%% REVIEW:PENDING                                              **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(output, binary_stream, S), _))
%%   [ciao]: no throws
%test 21 
:- test write_test21 :
	( open('/tmp/tmp.out', write, S, [type(binary)]),
	    current_output(Sc),
	    set_output(S),
	    current_output(S) )
	+ exception(error(permission_error(output, binary_stream, S), Imp_dep))
# "[Non-ISO] write/1: expected(error) bug(succeed)".

write_test21 :- write(a).


% ===========================================================================
%% 8.14.3.4 These tests are specified in page 102 of the ISO standard. %%

:- prop op_test1_poscond/1.

% Kludge: Added a dummy extra argument because the property without
% arguments is expanded as havin an extra argument -- EMM

op_test1_poscond(_) :- (current_op(30, xfy, ++), op(0, xfy, ++)).

%test 1 
:- test op_test1/1 => op_test1_poscond
# "[ISO] op/3: expected(succeed)".


op_test1(_) :- op(30, xfy, ++).

%test 2 
:- test op_test2 => (\+current_op(_, yfx, ++))
# "[ISO] op/3: expected(succeed)".

op_test2 :- op(0, yfx, ++).

%% REVIEW:PENDING                                     **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, max), _))
%%   [ciao]: throws  exception(error(domain_error(operator_priority,max),op/3-1))
%test 3 
:- test op_test3 + exception(error(type_error(integer, max), Imp_dep))
# "[ISO] op/3: expected(error) bug(wrong_error)".

op_test3 :- op(max, xfy, ++).

%test 4 
:- test op_test4
	+ exception(error(domain_error(operator_priority, -30), Imp_dep))
# "[ISO] op/3: expected(error)".

op_test4 :- op(-30, xfy, ++).

%test 5
:- test op_test5
	+ exception(error(domain_error(operator_priority, 1201), Imp_dep))
# "[ISO] op/3: expected(error)".

op_test5 :- op(1201, xfy, ++).

%test 6
:- test op_test6 + exception(error(instantiation_error, Imp_dep))
# "[ISO] op/3: expected(error)".

op_test6 :- op(30, _Xfy, ++).

%test 7
:- test op_test7
	+ exception(error(domain_error(operator_specifier, yfy), Imp_dep))
# "[ISO] op/3: expected(error)".

op_test7 :- op(30, yfy, ++).

%test 8
:- test op_test8 + exception(error(type_error(list, 0), Imp_dep))
# "[ISO] op/3: expected(error)".

op_test8 :- op(30, xfy, 0).


%test 9
:- prop op_test9_poscond/1.

op_test9_poscond(_) :- (current_op(40, xfx, ++), op(0, xfx, ++)).

:- test op_test9/1 => op_test9_poscond
# "[ISO] op/3: expected(succeed)".

op_test9(_) :- op(30, xfy, ++), op(40, xfx, ++).

%% REVIEW:PENDING                                             **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(create, operator, ++), _))
%%   [ciao]: no throws
%test 10 
:- test op_test10
	+ exception(error(permission_error(create, operator, ++), Imp_dep))
# "[ISO] op/3: expected(error) bug(succeed)".

op_test10 :- op(30, xfy, ++), op(50, yf, ++).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 11
:- test op_test11 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] op/3: expected(error)".

op_test11 :- op(_, xfx, ++).

%% REVIEW:PENDING                                   **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error,_))
%%   [ciao]: throws exception(error(permission_error(modify,operator,','),op/3))
%test 12
:- test op_test12 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] op/3: expected(error) bug(succeed)".

op_test12 :- op(100, xfx, _).

%% REVIEW:PENDING                                              **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error,_))
%%   [ciao]: no throws
%test 13 
:- test op_test13 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] op/3: expected(error) bug(succeed)".

op_test13 :- op(100, xfx, [a|_]).

%test 14
:- test op_test14 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] op/3: expected(error)".

op_test14 :- op(100, xfx, [a, _]).

%test 15 
:- test op_test15
	+ exception(error(domain_error(operator_specifier, Op_specifier),
		Imp_dep))
# "[Non-ISO] op/3: expected(error)".

op_test15 :- op(100, 200, [a]).

%test 16 
:- test op_test16
	+ exception(error(domain_error(operator_specifier, Op_specifier),
		Imp_dep))
# "[Non-ISO] op/3: expected(error)".

op_test16 :- op(100, f(1), [a]).

%test 17
:- test op_test17 + exception(error(type_error(atom, a+b), Imp_dep))
# "[Non-ISO] op/3: expected(error)".

op_test17 :- op(100, xfx, [a, a+b]).

%test 18
:- test op_test18
	+ exception(error(permission_error(modify, operator, ','), Imp_dep))
# "[Non-ISO] op/3: expected(error) bug(succeed)".

op_test18 :- op(100, xfx, ',').

%% REVIEW:PENDING                                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(modify, operator, ','), _))
%%   [ciao]: no throws
%test 19
:- test op_test19
	+ exception(error(permission_error(modify, operator, ','), Imp_dep))
# "[Non-ISO] op/3: expected(error) bug(succeed)".

op_test19 :- op(100, xfx, [a, ',']).



% ===========================================================================
%% 8.14.4.4 These tests are specified in page 103 of the ISO standard. %%


%test 1                                               ** Wrong_vs_iso**
%%   [gprolog]: Result = [[1050,*->],[740,#==>],[1000,','],[600,:],[1100,;],[200,^],[1105,'|'],[740,#\==>],[730,##],[1050,->],[750,#\<=>],[750,#<=>]]
%%   [ciao]: Result = [[1100,;],[1050,->],[200,^],[30,++]]
:- test current_op_test1(Result)
	=> ( find_on_list([[1100, ';'], [1050, '->'], [1000, ','], [200, '^']],
		Result) )
# "[ISO] current_op/3: expected(succeed) bug(fail)".

current_op_test1(Result) :- findall([P, OP], current_op(P, xfy, OP), Result).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(operator_priority, 1201),_))
%%   [ciao]: no throws
%test 2 
:- test current_op_test2
	+ exception(error(domain_error(operator_priority, 1201), Imp_dep))
# "[Non-ISO] current_op/3: expected(error) bug(fail)".

current_op_test2 :- current_op(1201, _, _).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(operator_specifier, yfy), Imp_dep))
%%   [ciao]: no throws
%test 3
:- test current_op_test3
	+ exception(error(domain_error(operator_specifier, yfy), Imp_dep))
# "[Non-ISO] current_op/3: expected(error) bug(fail)".

current_op_test3 :- current_op(_, yfy, _).

%% REVIEW:PENDING                                           **Nothrow_vs_iso**
%%   [gprolog]: throws error(domain_error(operator_specifier,0),current_op/3)
%%   [ciao]: no throws
%test 4 
:- test current_op_test4 + exception(error(type_error(atom, 0), Imp_dep))
# "[Non-ISO] current_op/3: expected(error) bug(fail)".

current_op_test4 :- current_op(_, 0, _).

%% REVIEW:PENDING                                                             **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 5), _))
%%   [ciao]: no throws
%test 5 
:- test current_op_test5 + exception(error(type_error(atom, 5), Imp_dep))
# "[Non-ISO] current_op/3: expected(error) bug(fail)".

current_op_test5 :- current_op(_, _, 5).



% ===========================================================================
%% 8.14.5.4 These tests are specified in page 103 of the ISO standard. %%

%% REVIEW:PENDING                               **Label_6**      
%test 1 
:- test char_conversion_test1
	: ( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, 'a&b. &'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (read('a,b'), get_char(' '), get_char('&'), close_instreams(Sc, S1))
# "[ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test1 :- char_conversion('&', ',').

%% REVIEW:PENDING                                    **Label_6**  
%test 2 
:- test char_conversion_test2
	: ( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, '^b+c^'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (read('b+c'), get_char(' '), get_char('^'), close_instreams(Sc, S1))
# "[ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test2 :- char_conversion('^', '''').

%% REVIEW:PENDING                                  **Label_6**  
%test 3 
:- test char_conversion_test3 :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "'A+c'+A."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]) )
	=> (read('A+c'+a), close_instreams(Sc, S1))
# "[ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test3 :- char_conversion('A', 'a').

%% REVIEW:PENDING                                      **Label_6**  
%test 4 
:- test char_conversion_test4(X, Y, Z) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text,
		"A&A. 'AAA'. ^A&A^."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read,
		Sc, S1, [type(text), eof_action(error)]),
	    char_conversion('&', ','),
	    char_conversion('^', ''''),
	    char_conversion('A', 'a') )
	=>(close_instreams(Sc, S1), X=(a, a), Y='AAA', Z='a,a')
# "[ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test4(X, Y, Z) :- read(X), read(Y), read(Z).

%% REVIEW:PENDING                                  **Label_6**          
%test 5  
:- test char_conversion_test5 :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "& ."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('&', ',') )
	=>(read('&'), close_instreams(Sc, S1), \+current_char_conversion(_, _))
# "[ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test5 :- char_conversion('&', '&').


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                              **Label_6**  
%test 6 
:- test char_conversion_test6(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "0'%%1."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(close_instreams(Sc, S1), X=(0'%) +1)
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test6(X) :- read(X).

%% REVIEW:PENDING                                               **Label_6**  
%test 7 
:- test char_conversion_test7(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "'%'%1."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(close_instreams(Sc, S1), X=('%' +1))
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test7(X) :- read(X).

%% REVIEW:PENDING                                                  **Label_6**  
%test 8  
:- test char_conversion_test8(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, '"%"%1.'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(X=(close_instreams(Sc, S1), "%" +1))
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test8(X) :- read(X).

%% REVIEW:PENDING                                               **Label_6**  
%test 9 
:- test char_conversion_test9(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, '1.#.'),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    op(100, xfx, '.'),
	    char_conversion('#', '!') )
	=>(close_instreams(Sc, S1), X='.'(1, !), op(0, xfx, '.'))
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test9(X) :- read(X).

%% REVIEW:PENDING                                                 **Label_6**  
%test 10  
:- test char_conversion_test10(X) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "^aa'+'bb^'."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(close_instreams(Sc, S1), X=('aa'+'bb^'))
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test10(X) :- read(X).

%% REVIEW:PENDING                                                **Label_6**  
%test 11 
:- test char_conversion_test11(X, Y) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "+ .% ."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(close_instreams(Sc, S1), X=(+), Y=(+))
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test11(X, Y) :- set_prolog_flag(char_conversion, off), read(X),
	set_prolog_flag(char_conversion, on), read(Y).

%% REVIEW:PENDING                                          **Label_6**  
%test 12 
:- test char_conversion_test12(X, Y) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "- .% ."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    char_conversion('%', '+'),
	    char_conversion('^', '\'') )
	=>(close_instreams(Sc, S1), X=('-'('.+')), Y=end_of_file)
# "[Non-ISO] char_conversion/2: expected(succeed) bug(error)".

char_conversion_test12(X, Y) :- read(X), read(Y).

%% 8.14.6.4 These tests are specified in page 104 of the ISO standard. %%

%% REVIEW:PENDING                               **Label_6**  
%test 1  
:- test current_char_conversion_test1(Result) :
	( open_and_write('/tmp/tmp.in', write, S, [type(text)], text, "'\\341\\'."),
	    close(S),
	    open_to_read('/tmp/tmp.in', read, Sc, S1,
		[type(text), eof_action(error)]),
	    read(Aacute),
	    char_conversion('A', 'a'),
	    char_conversion(Aacute, 'a') )
	=>(close_instreams(Sc, S1), Result=['A', Aacute])
# "[ISO] current_char_conversion/2: expected(succeed) bug(error)".

current_char_conversion_test1(Result) :-
	findall(C, current_char_conversion(C, a), Result).



%% 8.15.1.4 These tests are specified in page 105 of the ISO standard. %%
%test1
:- test not_test1 + fails
# "[ISO] '\\+': expected(fail)".

not_test1 :- '\\+'(true).

%test2 
:- test not_test2(X) : (X= !) + fails
# "[ISO] '\\+': expected(fail)".

not_test2(X) :- '\\+'(X).

%test3 
:- test not_test3(X) : (X= !)
# "[ISO] '\\+'/2: expected(succeed)".

not_test3(X) :- '\\+'((X, fail)).

%test4
:-test not_test4(Result) => (Result=[1, 2])
# "[ISO] '\\+'/2: expected(succeed)".

not_test4(Result) :- findall(X, ((X=1;X=2), '\\+'((!, fail))), Result).

%test5
:- test not_test5
# "[ISO] '\\+'/2: expected(succeed)".

not_test5 :- '\\+'(4=5).

%test6
:- test not_test6(X) : (X=3)
	+ exception(error(type_error(callable, 3), Imp_def))
# "[ISO] '\\+'/2: expected(error)".

not_test6(X) :- '\\+'(X).


%test7 
:- test not_test7 + exception(error(instantiation_error, Imp_def))
# "[ISO] '\\+'/2: expected(error)".

not_test7 :- '\\+'(_X).

%test8 
:- test not_test8 + fails
# "[ISO] '\\+'/2: expected(undefined)".

not_test8 :- '\\+'(X=f(X)).


%% 8.15.2.4 These tests are specified in page 105 of the ISO standard. %%

%test1
:- test once_test1
# "[ISO] once/1: expected(succeed)".

once_test1 :- once(!).

%test 2
:- test once_test2(Result) => (Result=[1, 2])
# "[ISO] once/1: expected(succeed)".

once_test2(Result) :- findall(X, (once(!), (X=1;X=2)), Result).

%test3
:- test once_test3
# "[ISO] once/1: expected(succeed)".

once_test3 :- once(repeat).

%test4
:- test once_test4 + fails
# "[ISO] once/1: expected(fail)".

once_test4 :- once(fail).

%test5 
:- test once_test5
# "[ISO] once/1: expected(undefined)".

once_test5 :- once(X=f(X)).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test6 
:- test once_test6 + exception(error(type_error(callable, 3), Imp_dep))
# "[Non-ISO] once/1: expected(error)".

once_test6 :- once(3).

%test 7
:- test once_test7 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] once/1: expected(error)".

once_test7 :- once(_).



% ===========================================================================
%% 8.15.3.4 These tests are specified in page 105 of the ISO standard. %%
%test 1
%:- test repeat_test1 + current_output("hello").
%repeat_test1 :- repeat,write(hello),fails.


%test2 
:- test repeat_test2 + fails
# "[ISO] repeat/0: expected(fail)".

repeat_test2 :- repeat, !, fail.



%% 8.16.1.4 These tests are specified in page 106 of the ISO standard. %%

%test1
:- test atomlength_test1(N) => (N=17)
# "[ISO] atom_length/2: expected(succeed)".

atomlength_test1(N) :- atom_length('enchanted evening', N).

%test2
:- test atomlength_test2(N) => (N=17)
# "[ISO] atom_length/2: expected(succeed)".

atomlength_test2(N) :- atom_length('enchanted\
 evening', N).

%test3
:- test atomlength_test3(N) => (N=0)
# "[ISO] atom_length/2: expected(succeed)".

atomlength_test3(N) :- atom_length('', N).

%test4
:- test atomlength_test4(N) : (N=5) + fails
# "[ISO] atom_length/2: expected(fail)".

atomlength_test4(N) :- atom_length('scarlet', N).

%test5 
:- test atomlength_test5 + exception(error(instantiation_error, Imp_def))
# "[ISO] atomlength/2: expected(error)".

atomlength_test5 :- atom_length(_Atom, 4).

%test6 
:- test atomlength_test6 + exception(error(type_error(atom, 1.23), Imp_def))
# "[ISO] atomlength/2: expected(error)".

atomlength_test6 :- atom_length(1.23, 4).

%test7 
:- test atomlength_test7 + exception(error(type_error(integer, '4'), Imp_def))
# "[ISO] atomlength/2: expected(error)".

atomlength_test7 :- atom_length(atom, '4').

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(not_less_than_zero, -4), Imp_def))
%%   [ciao]: no throws
%test8 
:- test atomlength_test8
	+ exception(error(domain_error(not_less_than_zero, -4), Imp_def))
# "[Non-ISO] atom_length/2: expected(error) bug(fail)".

atomlength_test8 :- atom_length(atom, -4).

%% REVIEW:PENDING                              ** Wrong_vs_iso**
%%   [gprolog]: L = 13
%%   [ciao]: L = 13
%test9
:- test atomlength_test9(L) => (L=11)
# "[Non-ISO] atom_length/2: expected(succeed)".

atomlength_test9(L) :- atom_length('Bartók Béla', L).


%% 8.16.2.4 These tests are specified in page 107 of the ISO standard. %%

%test1
:- test atomconcat_test1(S3) => (S3='hello world')
# "[ISO] atom_concat/2: expected(succeed)".

atomconcat_test1(S3) :- atom_concat('hello', ' world', S3).

%test2
:- test atomconcat_test2(T) => (T='small')
# "[ISO] atom_concat/2: expected(succeed)".

atomconcat_test2(T) :- atom_concat(T, ' world', 'small world').

%test3
:- test atomconcat_test3 + fails
# "[ISO] atom_concat/3: expected(fail)".

atomconcat_test3 :- atom_concat('hello', ' world', 'small world').

%test4
:- test atomconcat_test4(Result)
	=> ( S=[['', 'hello'], ['h', 'ello'], ['he', 'llo'], ['hel', 'lo'],
		['hell', 'o'], ['hello', '']] )
# "[ISO] atom_concat/2: expected(succeed)".

atomconcat_test4(Result) :- findall([T1, T2], atom_concat(T1, T2, 'hello'),
	    Result).

%test5
:- test atomconcat_test5 + exception(error(instantiation_error, Imp_def))
# "[ISO] atom_concat/2: expected(error)".

atomconcat_test5 :- atom_concat(small, _V2, _V4).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test6
:- test atomconcat_test6 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] atom_concat/2: expected(error)".

atomconcat_test6 :- atom_concat(_T1, 'iso', _S).

%test7
:- test atomconcat_test7 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] atom_concat/2: expected(error)".

atomconcat_test7 :- atom_concat('iso', _T2, _S).

%test8
:- test atomconcat_test8(X, Y, S) : (X=f(a), Y='iso')
	+ exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] atom_concat/2: expected(error)".

atomconcat_test8(X, Y, S) :- atom_concat(X, Y, S).

%test9
:- test atomconcat_test9 + exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] atom_concat/2: expected(error)".

atomconcat_test9 :- atom_concat('iso', f(a), _S).

%test10
:- test atomconcat_test10 + exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] atom_concat/2: expected(error)".

atomconcat_test10 :- atom_concat(_T1, _T2, f(a)).

%test11
:- test atomconcat_test11(S) => (S='Bartók Béla')
# "[Non-ISO] atom_concat/2: expected(succeed)".

atomconcat_test11(S) :- atom_concat('Bartók ', 'Béla', S).

%test12
:- test atomconcat_test12(T1) => (T1='Bartók ')
# "[Non-ISO] atom_concat/2: expected(succeed)".

atomconcat_test12(T1) :- atom_concat(T1, 'Béla', 'Bartók Béla').

%test13
:- test atomconcat_test13(T2) => (T2='Béla')
# "[Non-ISO] atom_concat/2: expected(succeed)".

atomconcat_test13(T2) :- atom_concat('Bartók ', T2, 'Bartók Béla').

:- if(defined(fixed_utf8)).
%test14 
:- test atomconcat_test14(Result)
	=> ( Result=[['', 'Pécs'], ['P', 'écs'], ['Pé', 'cs'], ['Péc', 's'],
		['Pécs', '']] )
# "[Non-ISO] atom_concat/2: expected(succeed)".

atomconcat_test14(Result) :-
	findall([T1, T2], atom_concat(T1, T2, 'Pécs'), Result).
:- endif.

% ===========================================================================
%% 8.16.3.4 These tests are specified in page 108 of the ISO standard. %%

%test 1
:- test subatom_test1(S) => (S='abrac')
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test1(S) :- sub_atom(abracadabra, 0, 5, _, S).

%% REVIEW:DONE                   
%test 2
:- test subatom_test2(S) => (S='dabra')
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test2(S) :- sub_atom(abracadabra, _, 5, 0, S).

%test 3
:- test subatom_test3(L, S) => (Y=5, S='acada')
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test3(L, S) :- sub_atom(abracadabra, 3, L, 3, S).

%test 4
:- test subatom_test4(Result) => (Result=[[0, 9], [7, 2]])
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test4(Result) :-
	findall([B, A], sub_atom(abracadabra, B, 2, A, ab), Result).

%test 5
:- test subatom_test5(S) => (S='an')
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test5(S) :- sub_atom(banana, 3, 2, _, S).

%test 6
:- test subatom_test6(Result) => (Result=['cha', 'har', 'ari', 'rit', 'ity'])
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test6(Result) :-
	findall(S, sub_atom(charity, _, 3, _, S), Result).

%test 7
:- test subatom_test7(Result)
	=> ( Result=[[0, 0, ''], [0, 1, 'a'], [0, 2, 'ab'], [1, 0, ''],
		[1, 1, 'b'], [2, 0, '']] )
# "[ISO] sub_atom/5: expected(succeed)".

subatom_test7(Result) :-
	findall([Start, Length, S], sub_atom(ab, Start, Length, _, S), Result).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 8
:- test subatom_test8 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error)".

subatom_test8 :- sub_atom(_W, 3, 2, _Z, _S).

%test 9
:- test subatom_test9 + exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error)".

subatom_test9 :- sub_atom(f(a), 2, 2, _Z, _S).

%% REVIEW:PENDING
%test 10                                             **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 2), _))
%%   [ciao]: no throws
:- test subatom_test10 + exception(error(type_error(atom, 2), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test10 :- sub_atom('Banana', 4, 2, _Z, 2).

%% REVIEW:PENDING                                          **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, a), _))
%%   [ciao]: no throws
%test 11 
:- test subatom_test11 + exception(error(type_error(integer, a), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test11 :- sub_atom('Banana', a, 2, _Z, _S).

%% REVIEW:PENDING                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, n), _))
%%   [ciao]: no throws
%test 12
:- test subatom_test12 + exception(error(type_error(integer, n), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test12 :- sub_atom('Banana', 4, n, _Z, _S).

%% REVIEW:PENDING                                           **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer, m), _))
%%   [ciao]: no throws
%test 13 
:- test subatom_test13 + exception(error(type_error(integer, m), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test13 :- sub_atom('Banana', 4, _Y, m, _S).

%% REVIEW:PENDING                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(not_less_than_zero, -2), _))
%%   [ciao]: no throws
%test 14 
:- test subatom_test14
	+ exception(error(domain_error(not_less_than_zero, -2), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test14 :- sub_atom('Banana', -2, 3, 4, _S).

%% REVIEW:PENDING                                          **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(error(domain_error(not_less_than_zero, -3),_))
%%   [ciao]: no throws
%test 15 
:- test subatom_test15
	+ exception(error(domain_error(not_less_than_zero, -3), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test15 :- sub_atom('Banana', 2, -3, 4, _S).

%% REVIEW:PENDING                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(not_less_than_zero, -4),_))
%%   [ciao]: no throws
%test 16.
:- test subatom_test16
	+ exception(error(domain_error(not_less_than_zero, -4), Imp_dep))
# "[Non-ISO] sub_atom/5: expected(error) bug(fail)".

subatom_test16 :- sub_atom('Banana', 2, 3, -4, _S).

%test 17
:- test subatom_test17(Z) => (Z=1)
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test17(Z) :- sub_atom('Banana', 2, 3, Z, 'nan').

%test 18 
:- test subatom_test18(X) => (X=2)
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test18(X) :- sub_atom('Banana', X, 3, 1, 'nan').

%test 19 
:- test subatom_test19(Y) => (Y=3)
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test19(Y) :- sub_atom('Banana', 2, Y, 1, 'nan').

%test 20 
:- test subatom_test20(Y, Z) => (Y=3, Z=1)
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test20(Y, Z) :- sub_atom('Banana', 2, Y, Z, 'nan').

%test 21 
:- test subatom_test21(X, Y) => (X=2, Y=3)
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test21(X, Y) :- sub_atom('Banana', X, Y, 1, 'nan').

%test 22 
:- test subatom_test22 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test22 :- sub_atom('Banana', 2, 3, 1, 'ana').

%test 23
:- test subatom_test23 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test23 :- sub_atom('Banana', 2, 3, 2, 'nan').

%test 24
:- test subatom_test24 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test24 :- sub_atom('Banana', 2, 3, 2, _S).

%test 25
:- test subatom_test25 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test25 :- sub_atom('Banana', 2, 3, 1, 'anan').

%test 26
:- test subatom_test26 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test26 :- sub_atom('Banana', 0, 7, 0, _S).

%test 27
:- test subatom_test27 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test27 :- sub_atom('Banana', 7, 0, 0, _S).

%test 28
:- test subatom_test28 + fails
# "[Non-ISO] sub_atom/5: expected(fail)".

subatom_test28 :- sub_atom('Banana', 0, 0, 7, _S).

%% REVIEW:PENDING                   **Failure due to accent marks**                               ** Wrong_vs_iso**
%%   [gprolog]: Y = 7
%%   [ciao]: Y = 7
%test 31
:- test subatom_test31(Z, S) => (Z=5, S='ók')
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test31(Z, S) :- sub_atom('Bartók Béla', 4, 2, Z, S).

%% REVIEW:PENDING                   **Failure due to accent marks**                                ** Wrong_vs_iso**
%%   [gprolog]: Y = 4
%%   [ciao]: Y = 4
%test 32 
:- test subatom_test32(Y, S) => (Y=2, S='ók')
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test32(Y, S) :- sub_atom('Bartók Béla', 4, Y, 5, S).

%% REVIEW:PENDING                   **Failure due to accent marks**                                ** Wrong_vs_iso**
%%   [gprolog]: Y = 6
%%   [ciao]: Y = 6
%test 33 
:- test subatom_test33(X, S) => (X=4, S='ók')
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test33(X, S) :- sub_atom('Bartók Béla', X, 2, 5, S).

:- if(defined(fixed_utf8)).
%test 34 
:- test subatom_test34(Result)
	=> (Result=[[0, 2, 'Pé'], [1, 1, 'éc'], [2, 0, 'cs']])
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test34(Result) :- findall([X, Z, S], sub_atom('Pécs', X, 2, Z, S),
	    Result).
:- endif.

%test 35
:- test subatom_test35(Result) => (Result=[[0, 4, 7], [7, 4, 0]])
# "[Non-ISO] sub_atom/5: expected(succeed)".

subatom_test35(Result) :-
	findall([X, Y, Z], sub_atom('abracadabra', X, Y, Z, abra), Result).


% ===========================================================================
%% 8.16.4.4 These tests are specified in page 108 of the ISO standard. %%

%test 1
:- test atomchars_test1(L) => (L=[])
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test1(L) :- atom_chars('', L).

%test 2
:- test atomchars_test2(L) => (L=['[', ']'])
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test2(L) :- atom_chars([], L).

%test 3
:- test atomchars_test3(L) => (L=[''''])
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test3(L) :- atom_chars('''', L).

%test 4
:- test atomchars_test4(L) => (L=['a', 'n', 't'])
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test4(L) :- atom_chars('ant', L).

%test 5
:- test atomchars_test5(Str) => (Str='sop')
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test5(Str) :- atom_chars(Str, ['s', 'o', 'p']).

%test 6
:- test atomchars_test6(X) => (X=['o', 'r', 't', 'h'])
# "[ISO] atom_chars/2: expected(succeed)".

atomchars_test6(X) :- atom_chars('North', ['N'|X]).

%test 7
:- test atomchars_test7 + fails
# "[ISO] atom_chars/2: expected(fail)".

atomchars_test7 :- atom_chars('soap', ['s', 'o', 'p']).

%% REVIEW:PENDING                                           **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 8 
:- test atomchars_test8
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] atom_chars/2: expected(error) bug(succeed)".

atomchars_test8 :- atom_chars(_X, _Y).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 9
:- test atomchars_test9 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] atom_chars/2: expected(error)".

atomchars_test9 :- atom_chars(_A, [a, _E, c]).

%% REVIEW:PENDING                                       **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, Imp_dep))
%%   [ciao]: no throws
%test 10
:- test atomchars_test10 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] atom_chars/2: expected(error)".

atomchars_test10 :- atom_chars(_A, [a, b|_L]).

%test 11
:- test atomchars_test11 + exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] atom_chars/2: expected(error)".

atomchars_test11 :- atom_chars(f(a), _L).

%% REVIEW:PENDING                                           **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, iso), Imp_dep))
%%   [ciao]: no throws
%test 12 
:- test atomchars_test12 + exception(error(type_error(list, iso), Imp_dep))
# "[Non-ISO] atom_chars/2: expected(error) bug(fail)".

atomchars_test12 :- atom_chars(_A, iso).

%% REVIEW:PENDING                                                  **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(character, f(b)), _))
%%   [ciao]: throws exception(error(type_error(atom,f(b)),'atomic_basic:$constant_codes'/3-1))
%test 13 
:- test atomchars_test13
	+ exception(error(type_error(character, f(b)), Imp_dep))
# "[Non-ISO] atom_chars/2: expected(error) bug(wrong_error)".

atomchars_test13 :- atom_chars(_A, [a, f(b)]).

:- if(defined(fixed_utf8)).
%test 14 
:- test atomchars_test14(L) => (L=['P', 'é', 'c', 's'])
# "[Non-ISO] atom_chars/2: expected(succeed) bug(error)".

atomchars_test14(L) :- atom_chars('Pécs', L).
:- endif.

:- if(defined(fixed_utf8)).
%test 15 
:- test atomchars_test15(A) => (A='Pécs')
# "[Non-ISO] atom_chars/2: expected(succeed) bug(fail)".

atomchars_test15(A) :- atom_chars(A, ['P', 'é', 'c', 's']).
:- endif.



% ===========================================================================
%% 8.16.5.4 These tests are specified in page 109 of the ISO standard. %%

%test 1
:- test atomcodes_test1(L) => (L=[])
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test1(L) :- atom_codes('', L).

%test 2
:- test atomcodes_test2(L) => (L=[0'[, 0']])
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test2(L) :- atom_codes([], L).

%test 3
:- test atomcodes_test3(L) => (L=[0'''])
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test3(L) :- atom_codes('''', L).

%test 4
:- test atomcodes_test4(L) => (L=[0'a, 0'n, 0't])
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test4(L) :- atom_codes('ant', L).

%test 5
:- test atomcodes_test5(Str) => (Str='sop')
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test5(Str) :- atom_codes(Str, [0's, 0'o, 0'p]).

%test 6
:- test atomcodes_test6(X) => (X=[0'o, 0'r, 0't, 0'h])
# "[ISO] atom_codes/2: expected(succeed)".

atomcodes_test6(X) :- atom_codes('North', [0'N|X]).

%test 7
:- test atomcodes_test7 + fails
# "[ISO] atom_codes/2: expected(fail)".

atomcodes_test7 :- atom_codes('soap', [0's, 0'o, 0'p]).

%test 8 
:- test atomcodes_test8 + exception(error(instantiation_error, Imp_dep))
# "[ISO] atom_codes/2: expected(error)".

atomcodes_test8 :- atom_codes(_X, _Y).

%%% Errors of atom_codes are corrected in both
%%% * ISO/IEC 13211-1:1995/Cor.1:2007(E) (page 4)
%%% * ISO/IEC 13211-1:1995/Cor.2:2012(E) (page 18)

:- test atomcodes_extra_errortest_1
	+ exception(error(instantiation_error, _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_1 :- atom_codes(_, [1|_]).

:- test atomcodes_extra_errortest_2
	+ exception(error(type_error(list, a), _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_2 :- atom_codes(_, a).

:- test atomcodes_extra_errortest_3
	+ exception(error(instantiation_error, _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_3 :- atom_codes(_, [1,_]).

:- test atomcodes_extra_errortest_4
	+ exception(error(type_error(integer, a), _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_4 :- atom_codes(_, [1,a]).

:- test atomcodes_extra_errortest_5
	+ exception(error(representation_error(character_code), _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_5 :- atom_codes(_, [-1]).

:- test atomcodes_extra_errortest_6
	+ exception(error(type_error(atom, 1), _ImpDep))
# "[ISO] atom_code/2: Extra test for exception.".

atomcodes_extra_errortest_6 :- atom_codes(1, [0'1]).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 9
:- test atomcodes_test9 + exception(error(type_error(atom, f(a)), Imp_dep))
# "[Non-ISO] atom_codes/2: expected(error)".

atomcodes_test9 :- atom_codes(f(a), _L).

%test 10 
:- test atomcodes_test10 + exception(error(type_error(list, 0'x), Imp_dep))
# "[Non-ISO] atom_codes/2: expected(error) bug(wrong_error)".

atomcodes_test10 :- atom_codes(_, 0'x).

%test 11
:- test atomcodes_test11
	+ exception(error(representation_error(character_code), Imp_dep))
# "[Non-ISO] atom_codes/2: expected(error) bug(wrong_error)".

atomcodes_test11 :- atom_codes(_X, [0'i, 0's, -1]).

%test 12 
%:- test atomcodes_test12(L) => (L=[0'P,0'é,0'c,0's]).  
%atomcodes_test12(L) :- atom_codes('Pécs',L).

%test 13 
%:- test atomcodes_test13(A) => (A='Pécs').
%atomcodes_test13(A) :- atom_codes(A,[0'P,0'é,0'c,0's]).

%% REVIEW:PENDING                                                     **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(integer,a),'atomic_basic:$constant_codes'/3-2))
%%   [ciao]: throws exception(error(type_error(integer,a),'atomic_basic:$constant_codes'/3-2))
%test 16 
:- test atomcodes_test16
	+ exception(error(representation_error(character_code), Imp_dep))
# "[Non-ISO] atom_codes/2: expected(error) bug(wrong_error)".

atomcodes_test16 :- atom_codes(_A, [a, b, c]).



% ===========================================================================
%% 8.16.6.4 These tests are specified in page 110 of the ISO standard. %%

%test 1
:- test charcode_test1(Code) => (Code=0'a)
# "[ISO] char_code/2: expected(succeed)".

charcode_test1(Code) :- char_code('a', Code).

%test 2 
:- test charcode_test2(Str) => (Str=c)
# "[ISO] char_code/2: expected(succeed)".

charcode_test2(Str) :- char_code(Str, 99).

%test 3
:- test charcode_test3(Str) => (Str=c)
# "[ISO] char_code/2: expected(succeed)".

charcode_test3(Str) :- char_code(Str, 0'c).

%test 4 
:- test charcode_test4(X)
# "[ISO] char_code/2: expected(succeed)".

charcode_test4(X) :- char_code(X, 163).

%test 5
:- test charcode_test5
# "[ISO] char_code/2: expected(succeed)".

charcode_test5 :- char_code('b', 0'b).

%% REVIEW:PENDING                                                        **Nothrow_vs_iso**
%%   [gprolog]: throws  exception(error(type_error(character, ab), _))
%%   [ciao]: no throws
%test 6 
:- test charcode_test6 + exception(error(type_error(character, ab), Imp_dep))
# "[ISO] char_code/2: expected(error) bug(fail)".

charcode_test6 :- char_code('ab', _Int).


%test 7 
:- test charcode_test7 + exception(error(instantiation_error, Imp_dep))
# "[ISO] char_code/2: expected(error)".

charcode_test7 :- char_code(_C, _I).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 8
:- test charcode_test8 + exception(error(type_error(integer, x), Imp_dep))
# "[Non-ISO] char_code/2: expected(error) bug(fail)".

charcode_test8 :- char_code(a, x).

%test 9
:- test charcode_test9
	+ exception(error(representation_error(character_code), Imp_dep))
# "[Non-ISO] char_codes/2: expected(error) bug(wrong_error)".

charcode_test9 :- char_code(_Str, -2).


%% 8.16.7.4 These tests are specified in page 111 of the ISO standard. %%

%test1
:- test numberchars_test1(L) => (L=['3', '3'])
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test1(L) :- number_chars(33, L).

%test2
:- test numberchars_test2
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test2 :- number_chars(33, ['3', '3']).

%test3 
:- test numberchars_test3(N) => (N=33.0)
# "[ISO] number_chars/2: expected(impldep)".

numberchars_test3(N) :- number_chars(33.0, Y), number_chars(N, Y).

%test4 
:- test numberchars_test4(X) => (near(X, 3.3, 0.02))
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test4(X) :- number_chars(X, ['3', '.', '3', 'E', +, '0']).

%test5 
:- test numberchars_test5 + fails
# "[ISO] number_chars/2: expected(impldep)".

numberchars_test5 :- number_chars(3.3, ['3', '.', '3', 'E', +, '0']).

%test6
:- test numberchars_test6(A) => (A=(-25))
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test6(A) :- number_chars(A, [-, '2', '5']).

%% REVIEW:PENDING                                           **Label_4**
%test7 
:- test numberchars_test7(A) => (A=3)
# "[ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test7(A) :- number_chars(A, ['\n', '', '3']).

%% REVIEW:PENDING                                                **Nothrow_vs_iso**
%%   [gprolog]: throws type_error(character,'')  
%%   [ciao]: no throws
%test8 
:- test numberchars_test8
	+ exception(error(syntax_error(imp_dep_atom), Imp_dep))
# "[ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test8 :- number_chars(_A, ['3', '']).

%% REVIEW:PENDING                                            **Label_4**
%test9 
:- test numberchars_test9(A) => (A=15)
# "[ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test9(A) :- number_chars(A, ['0', x, f]).

%% REVIEW:PENDING                                  **Label_4**
%test10 
:- test numberchars_test10(A) => (A=0'a)
# "[ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test10(A) :- number_chars(A, ['0', '''', a]).

%test11
:- test numberchars_test11(A) => (A=4.2)
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test11(A) :- number_chars(A, ['4', '.', '2']).

%test12
:- test numberchars_test12(A) => (A=4.2)
# "[ISO] number_chars/2: expected(succeed)".

numberchars_test12(A) :- number_chars(A, ['4', '2', '.', '0', 'e', '-', '1']).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 13
:- test numberchars_test13 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_chars/2: expected(error)".

numberchars_test13 :- number_chars(_X, _Y).

%test 14
:- test numberchars_test14 + exception(error(type_error(number, a), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error)".

numberchars_test14 :- number_chars(a, _Y).

%% REVIEW:PENDING                                                   **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(list, 4), _))
%%   [ciao]: no throws
%test 15 
:- test numberchars_test15 + exception(error(type_error(list, 4), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test15 :- number_chars(_, 4).

%% REVIEW:PENDING                                                **Diffthrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(character, 2), _))
%%   [ciao]: throws exception(error(type_error(atom,2),'atomic_basic:$constant_codes'/3-1))
%test 16
:- test numberchars_test16
	+ exception(error(type_error(character, 2), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(wrong_error)".

numberchars_test16 :- number_chars(_A, ['4', 2]).

%test 17
:- test numberchars_test17 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_chars/2: expected(error)".

numberchars_test17 :- number_chars(_A, [a|_]).

%test 18
:- test numberchars_test18
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_chars/2: expected(error)".

numberchars_test18 :- number_chars(_A, [a, _]).

%% REVIEW:PENDING                                              **Label_4**
%test 19 
:- test numberchars_test19(A) => (A=9)
# "[Non-ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test19(A) :- number_chars(A, [' ', '0', 'o', '1', '1']).

%% REVIEW:PENDING                                           **Label_4**
%test 20
:- test numberchars_test20(A) => (A=17)
# "[Non-ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test20(A) :- number_chars(A, [' ', '0', 'x', '1', '1']).               

%% REVIEW:PENDING                                       **Label_4**
%test 21 
:- test numberchars_test21(A) => (A=3)
# "[Non-ISO] number_chars/2: expected(succeed) bug(fail)".

numberchars_test21(A) :- number_chars(A, [' ', '0', 'b', '1', '1']).

%% REVIEW:PENDING                                        **Nothrow_vs_iso**
%%   [gprolog]: throws error(syntax_error('constant term stream:1 (char:2) non numeric character'),number_chars/2)
%%   [ciao]: no throws
%test 22 
:- test numberchars_test22
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test22 :- number_chars(_A, ['0', 'o', '8']).

%% REVIEW:PENDING                                             **Nothrow_vs_iso**
%%   [gprolog]: exception(error(syntax_error(_), _)) 
%%   [ciao]: no throws
%test 23 
:- test numberchars_test23
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test23 :- number_chars(_A, [' ', 'b', '2']).

%% REVIEW:PENDING                                             **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(syntax_error(_), _))
%%   [ciao]: no throws
%test 24 
:- test numberchars_test24
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test24 :- number_chars(_A, [' ', 'x', 'g']).

%% REVIEW:PENDING                                          **Nothrow_vs_iso**
%%   [gprolog]: throws  error(type_error(character,'\xc3\\xa1\'),number_chars/2)
%%   [ciao]: no throws
%test 25 
:- test numberchars_test25
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test25 :- number_chars(_A, ['á']).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(syntax_error(_), _))
%%   [ciao]: no throws
%test 26 
:- test numberchars_test26
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test26 :- number_chars(_A, ['a']).

%% REVIEW:PENDING                                                                **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(syntax_error(_), _))
%%   [ciao]: no throws
%test 27 
:- test numberchars_test27
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_chars/2: expected(error) bug(fail)".

numberchars_test27 :- number_chars(_A, ['0', 'x', '0', '.', '0']).


% ===========================================================================
%% 8.16.8.4 These tests are specified in page 112 of the ISO standard. %%

%test 1
:- test numbercodes_test1(L) => (L=[0'3, 0'3])
# "[ISO] number_codes/2: expected(succeed)".

numbercodes_test1(L) :- number_codes(33, L).

%test 2
:- test numbercodes_test2
# "[ISO] number_codes/2: expected(succeed)".

numbercodes_test2 :- number_codes(33, [0'3, 0'3]).

%test 3 
:- test numbercodes_test3(Y) => (number_codes(N, Y), N=33.0)
# "[ISO] number_codes/2: expected(impldep)".

numbercodes_test3(Y) :- number_codes(33.0, Y).

%test 4 
:- test numbercodes_test4
# "[ISO] number_codes/2: expected(impldep)".

numbercodes_test4 :- number_codes(33.0, [0'3|_L]).

%test 5
:- test numbercodes_test5(A) => (A=(-25))
# "[ISO] number_codes/2: expected(succeed)".

numbercodes_test5(A) :- number_codes(A, [0'-, 0'2, 0'5]).

%% REVIEW:PENDING                                                        **Label_4**
%test 6 
:- test numbercodes_test6(A) => (A=3)
# "[ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test6(A) :- number_codes(A, [0' , 0'3]).

%% REVIEW:PENDING                                         **Label_4**
%test 7 
:- test numbercodes_test7(A) => (A=15)
# "[ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test7(A) :- number_codes(A, [0'0, 0'x, 0'f]).

%% REVIEW:PENDING                                       **Label_4**
%test 8 
:- test numbercodes_test8(A) => (A=0'a)
# "[ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test8(A) :- number_codes(A, [0'0, 0''', 0'a]).

%test 9
:- test numbercodes_test9(A) => (A=4.2)
# "[ISO] number_codes/2: expected(succeed)".

numbercodes_test9(A) :- number_codes(A, [0'4, 0'., 0'2]).

%test 10
:- test numbercodes_test10(A) => (A=4.2)
# "[ISO] number_codes/2: expected(succeed)".

numbercodes_test10(A) :- number_codes(A, [0'4, 0'2, 0'., 0'0, 0'e, 0'-, 0'1]).


:- test numbercodes_extra_errortest_1
	+ exception(error(instantiation_error, _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_1 :- number_codes(_, [1|_]).

:- test numbercodes_extra_errortest_2
	+ exception(error(type_error(list, a), _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_2 :- number_codes(_, a).

:- test numbercodes_extra_errortest_3
	+ exception(error(instantiation_error, _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_3 :- number_codes(_, [1,_]).

:- test numbercodes_extra_errortest_4
	+ exception(error(type_error(integer, a), _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_4 :- number_codes(_, [1,a]).

:- test numbercodes_extra_errortest_5
	+ exception(error(representation_error(character_code), _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_5 :- number_codes(_, [-1]).

:- test numbercodes_extra_errortest_6
	+ exception(error(type_error(number, '1'), _ImpDep))
# "[ISO] number_codes/2: Extra test for exception.".

numbercodes_extra_errortest_6 :- number_codes('1', [0'1]).



%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 11
:- test numbercodes_test11 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_codes/2: expected(error)".

numbercodes_test11 :- number_codes(_, _).

%test 12
:- test numbercodes_test12 + exception(error(type_error(number, a), Imp_dep))
# "[Non-ISO] number_codes/2: expected(error)".

numbercodes_test12 :- number_codes(a, _Y).

%test 13 
:- test numbercodes_test13 + exception(error(type_error(list, 4), Imp_dep))
# "[Non-ISO] number_codes/2: expected(error) bug(wrong_error)".

numbercodes_test13 :- number_codes(_X, 4).


%test 14
:- test numbercodes_test14
	+ exception(error(representation_error(character_code), Imp_dep))
# "[Non-ISO] number_codes/2: expected(error) bug(wrong_error)".

numbercodes_test14 :- number_codes(_X, [0'4, -1]).

%test 15 
:- test numbercodes_test15 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_codes/2: expected(error)".

numbercodes_test15 :- number_codes(_X, [0'a|_]).

%test 16 
:- test numbercodes_test16 + exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] number_codes/2: expected(error)".

numbercodes_test16 :- number_codes(_X, [0'a, _]).

%% REVIEW:PENDING                                                  **Label_4**
%test 17 
:- test numbercodes_test17(A, S) => (A=273, S=[50, 55, 51])
# "[Non-ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test17(A, S) :-
	number_chars(A, [' ', '0', 'x', '1', '1', '1']),
	number_codes(A, S).

%% REVIEW:PENDING                                        **Label_4**
%test 18 
:- test numbercodes_test18(A, S) => (A=73, S=[55, 51])
# "[Non-ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test18(A, S) :-
	number_chars(A, [' ', '0', 'o', '1', '1', '1']),
	number_codes(A, S).

%% REVIEW:PENDING                                                         **Label_4**
%test 19  
:- test numbercodes_test19(A, S) => (A=7, S=[55])
# "[Non-ISO] number_codes/2: expected(succeed) bug(fail)".

numbercodes_test19(A, S) :-
	number_chars(A, [' ', '0', 'b', '1', '1', '1']),
	number_codes(A, S).

%% REVIEW:PENDING                          **It's correct in GNU**                             **Nothrow_vs_iso**
%%   [gprolog]: throws FOO
%%   [ciao]: no throws
%test 20 
:- test numbercodes_test20
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_codes/2: expected(error) bug(succeed)".

numbercodes_test20 :- number_codes(_X, "ä").

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(syntax_error(_), _))
%%   [ciao]: no throws
%test 21 
:- test numbercodes_test21
	+ exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[Non-ISO] number_codes/2: expected(error) bug(fail)".

numbercodes_test21 :- number_codes(_A, [0'0, 0'x, 0'0, 0'., 0'0]).


% ===========================================================================
%% 8.17.1.4 These tests are specified in page 112 of the ISO standard. %%

%test 1
:- test setflag_test1
# "[ISO] set_prolog_flag/2: expected(succeed)".

setflag_test1 :- set_prolog_flag(unknown, fail).

%% REVIEW:PENDING                                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(instantiation_error, _))
%%   [ciao]: no throws
%test 2 
:- test setflag_test2 + exception(error(instantiation_error, Imp_dep))
# "[ISO] set_flag/2: expected(error) bug(fail)".

setflag_test2 :- set_prolog_flag(_X, off).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 5), _))
%%   [ciao]: no throws
%test 3 
:- test setflag_test3 + exception(error(type_error(atom, 5), Imp_dep))
# "[ISO] set_flag/2: expected(error) bug(fail)".

setflag_test3 :- set_prolog_flag(5, decimals).

%% REVIEW:PENDING                                                    **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(flag, date), _))
%%   [ciao]: no throws
%test 4 
:- test setflag_test4 + exception(error(domain_error(flag, date), Imp_dep))
# "[ISO] set_flag/2: expected(error) bug(fail)".

setflag_test4 :- set_prolog_flag(date, 'July 1988').

%% REVIEW:PENDING                                                       **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(flag_value, debug+trace), _))
%%   [ciao]: no throws
%test 5 
:- test setflag_test5
	+ exception(error(domain_error(flag_value, debug+trace), Imp_dep))
# "[ISO] set_flag/2: expected(error) bug(fail)".

setflag_test5 :- set_prolog_flag(debug, trace).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%% REVIEW:PENDING                                                        **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(permission_error(modify, flag, max_arity), _))
%%   [ciao]: no throws
%test 6 
:- test setflag_test6
	+ exception(error(permission_error(modify, flag, max_arity), Imp_dep))
# "[Non-ISO] set_flag/2: expected(error) bug(fail)".

setflag_test6 :- set_prolog_flag(max_arity, 40).



% ===========================================================================
%% 8.17.2.4 These tests are specified in page 113 of the ISO standard. %%

%% REVIEW:PENDING                                       **Label_4**
%test 1 
:- test currentflag_test1 : (X=debug, Y=off, set_prolog_flag(X, Y))
# "[ISO] current_prolog_flag/2: expected(succeed) bug(fail)".

currentflag_test1 :- current_prolog_flag(debug, off).

%test 2 
:- test currentflag_test2(Result) => (Result\=[])
# "[ISO] current_prolog_flag/2: expected(succeed)".

currentflag_test2(Result) :-
	findall([X, Y], current_prolog_flag(X, Y), Result).

%% REVIEW:PENDING                                                      **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 5), _))
%%   [ciao]: no throws
%test 3 
:- test currentflag_test3 + exception(error(type_error(atom, 5), Imp_dep))
# "[ISO] current_prolog_flag/2: expected(error) bug(fail)".

currentflag_test3 :- current_prolog_flag(5, _Y).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%


%test 4
:- test currentflag_test4 : (X=unknown, Y=warning, set_prolog_flag(X, Y))
# "[Non-ISO] current_prolog_flag/2: expected(succeed)".

currentflag_test4 :- current_prolog_flag(unknown, warning).

%test 5
:- test currentflag_test5 : (X=unknown, Y=warning, set_prolog_flag(X, Y))
	+ fails
# "[Non-ISO] current_prolog_flag/2: expected(fail)".

currentflag_test5 :- current_prolog_flag(unknown, error).

%% REVIEW:PENDING                                               **Label_4**
%test 6 
:- test currentflag_test6
# "[Non-ISO] current_prolog_flag/2: expected(succeed) bug(fail)".

currentflag_test6 :- current_prolog_flag(debug, off).

%% REVIEW:PENDING                                                 **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(domain_error(prolog_flag, warning), _))
%%   [ciao]: no throws
%test 7 
:- test currentflag_test7
	+ exception(error(domain_error(prolog_flag, warning), Imp_dep))
# "[Non-ISO] current_prolog_flag/2: expected(error) bug(fail)".

currentflag_test7 :- current_prolog_flag(warning, _Y).

%% REVIEW:PENDING                                                     **Nothrow_vs_iso**
%%   [gprolog]: throws exception(error(type_error(atom, 1 + 2), _))
%%   [ciao]: no throws
%test 8 
:- test currentflag_test8
	+ exception(error(type_error(atom, 1 + 2), Imp_dep))
# "[Non-ISO] current_prolog_flag/2: expected(error) bug(fail)".

currentflag_test8 :- current_prolog_flag(1 + 2, flag).



% ===========================================================================
%% 8.17.3.4 and 8.17.4.4 These tests are specified in page 113 from      %%
%% the ISO standard.                                                        %%

% TODO: Let us trust that halt/0 and halt/1 effectively stops the process.
%   Testing those predicates require new comp properties. (JF)
:- if(defined(testing_halt)).
%test 1 
:- test halt_test1
# "[ISO] halt/0: stops the process.".

halt_test1 :- halt.

%test 2 
:- test halt_test2
# "[ISO] halt/1: stops the process with error code 1.".

halt_test2 :- halt(1).
:- endif.

%test 3 
:- test halt_test3
	+ exception(error(type_error(integer, a), Imp_dep))
# "[ISO] halt/1: expected(error)".

halt_test3 :- halt(a).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 4
:- test halt_test4
	+ exception(error(instantiation_error, Imp_dep))
# "[Non-ISO] halt/1: expected(error)".

halt_test4 :- halt(_).








