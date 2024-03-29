:- module(iso_tests_arithmetic, _, [assertions, nativeprops, unittestdecls, iso_strict]).

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


% ===========================================================================
%% 9.1.7 These tests are specified in page 117 of the ISO standard. %%%%%
%test 1
:- test eval_test1(S) => (S=42)
# "[ISO] '+'/2: expected(succeed)".

eval_test1(S) :- S is '+'(7, 35).

%test 2
:- test eval_test2(S) => (S=14)
# "[ISO] '+'/2: expected(succeed)".

eval_test2(S) :- S is '+'(0, 3 +11).

%test 3
:- test eval_test3(S) => (near(S, 14.2000, 0.0001))
# "[ISO] '+'/2: expected(succeed)".

eval_test3(S) :- S is '+'(0, 3.2 +11).


%test 4 
:- test eval_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '+'/2: expected(error) bug(fail)".

eval_test4(S) :- S is '+'(77, _N).

%% REVIEW:PENDING                                                      **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test eval_test5(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '+'/2: expected(error) bug(fail)".

eval_test5(S) :- S is '+'(foo, 77).

%test 6
:- test eval_test6(S) => (S=(-7))
# "[ISO] '-'/2: expected(succeed)".

eval_test6(S) :- S is '-'(7).

%test 7
:- test eval_test7(S) => (S=(8))
# "[ISO] '-'/2: expected(succeed)".

eval_test7(S) :- S is '-'(3 -11).

%test 8
:- test eval_test8(S) => (near(S, 7.8000, 0.0001))
# "[ISO] '-'/2: expected(succeed)".

eval_test8(S) :- S is '-'(3.2 -11).

%test 9 
:- test eval_test9(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '-'/2: expected(error) bug(fail)".

eval_test9(S) :- S is '-'(_N).

%% REVIEW:PENDING                                                           **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 10 
:- test eval_test10(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '-'/2: expected(error) bug(fail)".

eval_test10(S) :- S is '-'(foo).

%test 11
:- test eval_test11(S) => (S=(-28))
# "[ISO] '-'/2: expected(succeed)".

eval_test11(S) :- S is '-'(7, 35).

%test 12
:- test eval_test12(S) => (S=6)
# "[ISO] '-'/2: expected(succeed)".

eval_test12(S) :- S is '-'(20, 3 +11).


%test 13
:- test eval_test13(S) => (near(S, -14.2000, 0.0001))
# "[ISO] '-'/2: expected(succeed)".

eval_test13(S) :- S is '-'(0, 3.2 +11).

%test 14
:- test eval_test14(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '-'/2: expected(error) bug(fail)".

eval_test14(S) :- S is '-'(77, _N).

%% REVIEW:PENDING                                                  **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 15 
:- test eval_test15(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '-'/2: expected(error) bug(fail)".

eval_test15(S) :- S is '-'(foo, 77).

%test 16
:- test eval_test16(S) => (S=245)
# "[ISO] '*'/2: expected(succeed)".

eval_test16(S) :- S is '*'(7, 35).

%test 17
:- test eval_test17(S) : (X=0, Y=(3 +11)) => (S=0)
# "[ISO] '*'/2: expected(succeed)".

eval_test17(S) :- S is '*'(0, 3 +11).

%test 18 
:- test eval_test18(S) => (near(S, 21.3, 0.0001))
# "[ISO] '*'/2: expected(succeed)".

eval_test18(S) :- S is '*'(1.5, 3.2 +11).


%test 19
:- test eval_test19(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '*'/2: expected(error) bug(fail)".

eval_test19(S) :- S is '*'(77, _N).

%% REVIEW:PENDING                                                      **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 20 
:- test eval_test20(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '*'/2: expected(error) bug(fail)".

eval_test20(S) :- S is '*'(foo, 77).

%test 21
:- test eval_test21(S) => (S=0)
# "[ISO] '//'/2: expected(succeed)".

eval_test21(S) :- S is '//'(7, 35).

%test 22
:- test eval_test22(S) => (near(S, 0.2000, 0.0001))
# "[ISO] '//'/2: expected(succeed)".

eval_test22(S) :- S is '/'(7.0, 35).

%test 23
:- test eval_test23(S) => (S=10)
# "[ISO] '//'/2: expected(succeed)".

eval_test23(S) :- S is '//'(140, 3 +11).

%test 24
:- test eval_test24(S) => (near(S, 1.42, 0.0001))
# "[ISO] '/'/2: expected(succeed)".

eval_test24(S) :- S is '/'(20.164, 3.2 +11).

%test 25 
:- test eval_test25(S)
# "[ISO] '//'/2: expected(impldep)".

eval_test25(S) :- S is '//'(7, -3).

%test 26 
:- test eval_test26(S)
# "[ISO] '//'/2: expected(impldep)".

eval_test26(S) :- S is '//'(-7, 3).

%% REVIEW:DONE                             
%test 27 
:- test eval_test27(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '/'/2: expected(error) bug(fail)".

eval_test27(S) :- S is '/'(77, _N).

%% REVIEW:PENDING                                                              **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 28 
:- test eval_test28(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '/'/2: expected(error) bug(fail)".

eval_test28(S) :- S is '/'(foo, 77).

%% REVIEW:DONE                             
%test 29 
:- test eval_test29(S) + exception(error(evaluation_error(zero_divisor),
		Imp_dep))
# "[Non-ISO] '/'/2: expected(error) bug(succeed)".

eval_test29(S) :- S is '//'(3, 0).

%test 30
:- test eval_test30(S) => (S=1)
# "[ISO] mod/2: expected(succeed)".

eval_test30(S) :- S is mod(7, 3).

%test 31
:- test eval_test31(S) => (S=0)
# "[ISO] mod/2: expected(succeed)".

eval_test31(S) :- S is mod(0, 3 +11).

%test 32
:- test eval_test32(S) => (S=(-1))
# "[ISO] mod/2: expected(succeed)".

eval_test32(S) :- S is mod(7, -2).

%test 33 
:- test eval_test33(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] 'mod'/2: expected(error) bug(fail)".

eval_test33(S) :- S is mod(77, _N).

%% REVIEW:PENDING                                                      **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 34 
:- test eval_test34(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] 'mod'/2: expected(error) bug(fail)".

eval_test34(S) :- S is mod(foo, 77).

%test 35 
:- test eval_test35(S) + exception(error(type_error(integer, 7.5), Imp_dep))
# "[ISO] mod/2: expected(error) bug(succeed)".

eval_test35(S) :- S is mod(7.5, 2).

%test 36 
:- test eval_test36(S)
	+ exception(error(evaluation_error(zero_divisor), Imp_dep))
# "[ISO] mod/2: expected(error)".

eval_test36(S) :- S is mod(7, 0).

%test 37
:- test eval_test37(S) => (S=7)
# "[ISO] floor/1: expected(succeed)".

eval_test37(S) :- S is floor(7.4).

%test 38
:- test eval_test38(S) => (S=(-1))
# "[ISO] floor/1: expected(succeed)".

eval_test38(S) :- S is floor(-0.4).

%test 39
:- test eval_test39(S) => (S=8)
# "[ISO] round/1: expected(succeed)".

eval_test39(S) :- S is round(7.5).

%test 40
:- test eval_test40(S) => (S=8)
# "[ISO] round/1: expected(succeed)".

eval_test40(S) :- S is round(7.6).

%test 41
:- test eval_test41(S) => (S=(-1))
# "[ISO] round/1: expected(succeed)".

eval_test41(S) :- S is round(-0.6).

%test 42
:- test eval_test42(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] round/2: expected(error) bug(fail)".

eval_test42(S) :- S is round(_X).

%test 43
:- test eval_test43(S) => (S=0)
# "[ISO] ceiling/1: expected(succeed)".

eval_test43(S) :- S is ceiling(-0.5).

%test 44
:- test eval_test44(S) => (S=0)
# "[ISO] ceiling/1: expected(succeed)".

eval_test44(S) :- S is truncate(-0.5).

%% REVIEW:PENDING                                                        **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws  exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 45
:- test eval_test45(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] truncate/1: expected(error) bug(fail)".

eval_test45(S) :- S is truncate(foo).

%test 46
:- test eval_test46(S) => (S=7.0)
# "[ISO] float/1: expected(succeed)".

eval_test46(S) :- S is float(7).

%test 47
:- test eval_test47(S) => (near(S, 7.3, 0.0001))
# "[ISO] float/1: expected(succeed)".

eval_test47(S) :- S is float(7.3).

%test 48 
:- test eval_test48(S) => (S=1.0)
# "[ISO] float/1: expected(succeed)".

eval_test48(S) :- S is float(5//3).

%test 49 
:- test eval_test49(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] float/1: expected(error) bug(fail)".

eval_test49(S) :- S is float(_X).

%% REVIEW:PENDING                                                            **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 50  
:- test eval_test50(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] float/1: expected(error) bug(fail)".

eval_test50(S) :- S is float(foo).

%test 51
:- test eval_test51(S) => (S=7)
# "[ISO] abs/1: expected(succeed)".

eval_test51(S) :- S is abs(7).

%test 52
:- test eval_test52(S) => (S=8)
# "[ISO] abs/1: expected(succeed)".

eval_test52(S) :- S is abs(3 -11).

%test 53
:- test eval_test53(S) => (near(S, 7.8000, 0.0001))
# "[ISO] abs/1: expected(succeed)".

eval_test53(S) :- S is abs(3.2 -11.0).

%test 54  
:- test eval_test54(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] abs/1: expected(error) bug(fail)".

eval_test54(S) :- S is abs(_N).

%% REVIEW:PENDING                                                       **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws  exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 55  
:- test eval_test55(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] abs/1: expected(error) bug(fail)".

eval_test55(S) :- S is abs(foo).

%test 56 
:- test eval_test56(S) => (S=(5.0))
# "[ISO] '/'/2: expected(succeed)".

eval_test56(S) :- S is '/'(10,2).

%test 57
:- test eval_test57(S) => (S=(0.0))
# "[ISO] '/'/2: expected(succeed)".

eval_test57(S) :- S is '/'(0,3+11).

%test 58
:- test eval_test58(S) => (S=(-2.5))
# "[ISO] '/'/2: expected(succeed)".

eval_test58(S) :- S is '/'(-5,2).

%test 59
:- test eval_test59(S) => (S=(-0.1))
# "[ISO] '/'/2: expected(succeed)".

eval_test59(S) :- S is '/'(1,-10).

%test 60 
:- test eval_test60(S) => (S=(0))
# "[ISO] '//'/2: expected(succeed)".

eval_test60(S) :- S is '//'(0,3+11).

%test 61 
:- test eval_test61(S) => (S=(-1))
# "[ISO] '//'/2: expected(succeed)".

eval_test61(S) :- S is '//'(-5,3).

%test 62
:- test eval_test62(S) => (S=(0))
# "[ISO] '//'/2: expected(succeed)".

eval_test62(S) :- S is '//'(1,-12).

%test 63                                                              **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: S = 3
%%   [ciao]: throws exception(error(type_error(evaluable,max(2,3)),'arithmetic:is'/2-2))
:- test eval_test63(S) => (S=(3)) + no_exception
# "[ISO] max/2: expected(succeed) bug(fail)".

eval_test63(S) :- S is max(2, 3).

%test 64                                                                **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: throws exception: error(instantiation_error,(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,max(_,3)),'arithmetic:is'/2-2))
:- test eval_test64(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] max/2: expected(succeed) bug(fail)".

eval_test64(S) :- S is max(_N,3).

%test 65                                                              **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws  exception(error(type_error(evaluable,max(3,foo)),'arithmetic:is'/2-2))
:- test eval_test65(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] max/2: expected(succeed) bug(fail)".

eval_test65(S) :- S is max(3,foo).

%test 66                                                                 **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: S = 2
%%   [ciao]: throws exception(error(type_error(evaluable,min(2,3)),'arithmetic:is'/2-2))
:- test eval_test66(S) => (S=(2)) + no_exception
# "[ISO] min/2: expected(succeed) bug(fail)".

eval_test66(S) :- S is min(2, 3).

%test 67                                                                  **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: throws exception: error(instantiation_error,(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,min(_,3)),'arithmetic:is'/2-2))
:- test eval_test67(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] min/2: expected(succeed) bug(fail)".

eval_test67(S) :- S is min(_N,3).

%test 68                                                                 **Label_3**
%% REVIEW:PENDING
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,min(3,foo)),'arithmetic:is'/2-2))
:- test eval_test68(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] min/2: expected(succeed) bug(fail)".

eval_test68(S) :- S is min(3,foo).
% ===========================================================================
%% 9.3.1.4 These tests are specified in page 120 of the ISO standard. %%%

%test 1
:- test power_test1(S) => (S=125.0000)
# "[ISO] '**'/2: expected(succeed)".

power_test1(S) :- S is '**'(5, 3).

%test 2
:- test power_test2(S) => (S=(-125.0000))
# "[ISO] '**'/2: expected(succeed)".

power_test2(S) :- S is '**'(-5.0, 3).

%test 3
:- test power_test3(S) => (S=0.2000)
# "[ISO] '**'/2: expected(succeed)".

power_test3(S) :- S is '**'(5, -1).

%test 4 
:- test power_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '**'/2: expected(error) bug(fail)".

power_test4(S) :- S is '**'(77, _N).

%% REVIEW:PENDING                                                          **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test power_test5(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] '**'/2: expected(error) bug(fail)".

power_test5(S) :- S is '**'(foo, 2).

%test 6
:- test power_test6(S) => (S=125.0000)
# "[ISO] '**'/2: expected(succeed)".

power_test6(S) :- S is '**'(5, 3.0).

%test 7
:- test power_test7(S) => (S=1.0)
# "[ISO] '**'/2: expected(succeed)".

power_test7(S) :- S is '**'(0.0, 0).


% ===========================================================================
%% 9.3.2.4 These tests are specified in page 120 of the ISO standard. %%%

%test 1
:- test sin_test1(S) => (S=0.0)
# "[ISO] sin/1: expected(succeed)".

sin_test1(S) :- S is sin(0.0).

%test 2 
:- test sin_test2(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] sin/1: expected(error) bug(fail)".

sin_test2(S) :- S is sin(_N).

%test 3
:- test sin_test3(S) => (S=0.0)
# "[ISO] sin/1: expected(succeed)".

sin_test3(S) :- S is sin(0).

%% REVIEW:PENDING                                                            **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 4 
:- test sin_test4(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] sin/1: expected(error) bug(fail)".

sin_test4(S) :- S is sin(foo).

%test 5  
:- test sin_test5(PI, S) :
	(PI is atan(1.0) *4)
	=> (near(S, 1.0000, 0.0001), near(PI, 3.14159, 0.0001))
# "[ISO] sin/1: expected(succeed)".

sin_test5(PI, S) :- S is sin(PI/2.0).


% ===========================================================================
%% 9.3.3.4 These tests are specified in page 120 of the ISO standard. %%%

%test 1
:- test cos_test1(S) => (S=1.0)
# "[ISO] cos/1: expected(succeed)".

cos_test1(S) :- S is cos(0.0).

%test 2 
:- test cos_test2(S)
	+ exception(error(instantiation_error, Imp_dep))
# "[ISO] cos/1: expected(error) bug(fail)".

cos_test2(S) :- S is cos(_N).

%test 3
:- test cos_test3(S) => (S=1.0)
# "[ISO] cos/1: expected(succeed)".

cos_test3(S) :- S is cos(0).

%% REVIEW:PENDING                                                           **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 4 
:- test cos_test4(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] cos/1: expected(error) bug(fail)".

cos_test4(S) :- S is cos(foo).

%test 5  
:- test cos_test5(PI, S)
	: (PI is atan(1.0) *4)
	=> (near(S, 0.0000, 0.02), near(PI, 3.14159, 0.02))
# "[ISO] cos/1: expected(succeed)".

cos_test5(PI, S) :- S is cos(PI/2.0).

% ===========================================================================
%% 9.3.3.4 These tests are specified in page 121 of the ISO standard. %%%

%test 1
:- test atan_test1(S) => (S=0.0)
# "[ISO] atan/1: expected(succeed)".

atan_test1(S) :- S is atan(0.0).

%test2 
:- test atan_test2(PI) => (near(PI, 3.14159, 0.02))
# "[ISO] atan/1: expected(succeed)".

atan_test2(PI) :- PI is atan(1.0) *4.

%test 3 
:- test atan_test3(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] atan/1: expected(error) bug(fail)".

atan_test3(S) :- S is atan(_N).

%test 4
:- test atan_test4(S) => (S=0.0)
# "[ISO] atan/1: expected(succeed)".

atan_test4(S) :- S is atan(0.0).

%% REVIEW:PENDING                                                     **Label_3**
%%   [gprolog]: throws error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test atan_test5(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] atan/1: expected(error) bug(fail)".

atan_test5(S) :- S is atan(foo).


% ===========================================================================
%% 9.3.5.4 These tests are specified in page 121 of the ISO standard. %%%

%test 1
:- test exp_test1(S) => (S=1.0)
# "[ISO] exp/1: expected(succeed)".

exp_test1(S) :- S is exp(0.0).

%test 2 
:- test exp_test2(S) => (near(S, 2.7818, 0.1))
# "[ISO] exp/1: expected(succeed)".

exp_test2(S) :- S is exp(1.0).


%test 3 
:- test exp_test3(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] exp/1: expected(error) bug(fail)".

exp_test3(S) :- S is exp(_N).

%test 4
:- test exp_test4(S) => (S=1.0)
# "[ISO] exp/1: expected(succeed)".

exp_test4(S) :- S is exp(0).
%%REVIEW:PENDING                                      **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test exp_test5(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] exp/1: expected(error) bug(fail)".

exp_test5(S) :- S is exp(foo).


% ===========================================================================
%% 9.3.6.4 These tests are specified in page 121 of the ISO standard. %%%

%test 1
:- test log_test1(S) => (S=0.0)
# "[ISO] log/1: expected(succeed)".

log_test1(S) :- S is log(1.0).

%test 2 
:- test log_test2(S) => (near(S, 1.0000, 0.02))
# "[ISO] log/1: expected(succeed)".

log_test2(S) :- S is log(2.71828).

%test 3 
:- test log_test3(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] log/1: expected(error) bug(fail)".

log_test3(S) :- S is log(_N).

%% REVIEW:PENDING                                                    **Label_2**
%%   [gprolog]: S = -inf
%%   [ciao]: no throws
%test 4 
:- test log_test4(S) + exception(error(evaluation_error(undefined), Imp_dep))
# "[ISO] log/2: expected(error) bug(succeed)".

log_test4(S) :- S is log(0).

%% REVIEW:PENDING                                                  **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test log_test5(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] log/1: expected(error) bug(fail)".

log_test5(S) :- S is log(foo).

%% REVIEW:PENDING                                         **Label_2**
%%   [gprolog]: S = -inf
%%   [ciao]: no throws
%test 6 
:- test log_test6(S) + exception(error(evaluation_error(undfined), Imp_dep))
# "[ISO] log/2: expected(error) bug(succeed)".

log_test6(S) :- S is log(0.0).


% ===========================================================================
%% 9.3.7.4 These tests are specified in page 122 of the ISO standard. %%%

%test 1
:- test sqrt_test1(S) => (S=0.0)
# "[ISO] sqrt/1: expected(succeed)".

sqrt_test1(S) :- S is sqrt(0.0).

%test 2
:- test sqrt_test2(S) => (S=1.0)
# "[ISO] sqrt/1: expected(succeed)".

sqrt_test2(S) :- S is sqrt(1).

%test 3 
:- test sqrt_test3(X, S) : (X=1.21) => (near(S, 1.1000, 0.02))
# "[ISO] sqrt/1: expected(succeed)".

sqrt_test3(X, S) :- S is sqrt(X).

%test 4 
:- test sqrt_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] sqrt/1: expected(error) bug(fail)".

sqrt_test4(S) :- S is sqrt(_N).

%% REVIEW:PENDING                                             **Label_2**
%%   [gprolog]: S = -nan
%%   [ciao]: no throws
%test 5 
:- test sqrt_test5(S) + exception(error(evaluation_error(undefined), Imp_dep))
# "[ISO] sqrt/1: expected(error) bug(succeed)".

sqrt_test5(S) :- S is sqrt(-1.0).

%% REVIEW:PENDING                                                **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: no throws
%test 6
:- test sqrt_test6(S) + exception(error(type_error(number, foo), Imp_dep))
# "[ISO] sqrt/1: expected(error) bug(fail)".

sqrt_test6(S) :- S is sqrt(foo).

% ===========================================================================
%% 9.4.1.4 These tests are specified in page 122 of the ISO standard. %%%

%test 1
:- test bit_rl_test1(S) => (S=4)
# "[ISO] '>>'/2: expected(succeed)".

bit_rl_test1(S) :- S is '>>'(16, 2).

%test 2
:- test bit_rl_test2(S) => (S=4)
# "[ISO] '>>'/2: expected(succeed)".

bit_rl_test2(S) :- S is '>>'(19, 2).

%test 3 
:- test bit_rl_test3(S) => (S=(-4))
# "[ISO] '>>'/2: expected(impldep)".

bit_rl_test3(S) :- S is '>>'(-16, 2).

%test 4 
:- test bit_rl_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '>>'/2: expected(error) bug(fail)".

bit_rl_test4(S) :- S is '>>'(77, _N).

%% REVIEW:PENDING                                                      **Label_3**
%%   [gprolog]: throws  exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws  exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test bit_rl_test5(S) + exception(error(type_error(integer, foo), Imp_dep))
# "[ISO] '>>'/2: expected(error) bug(fail)".

bit_rl_test5(S) :- S is '>>'(foo, 2).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 6 
:- test bit_rl_test6(S) + exception(error(type_error(integer, 1.0), Imp_dep))
# "[Non-ISO] '>>'/2: expected(error) bug(succeed)".

bit_rl_test6(S) :- S is '>>'(1.0, 2).


% ===========================================================================
%% 9.4.2.4 These tests are specified in page 123 of the ISO standard. %%%

%test 1
:- test bit_lr_test1(S) => (S=64)
# "[ISO] '<<'/2: expected(succeed)".

bit_lr_test1(S) :- S is '<<'(16, 2).

%test 2
:- test bit_lr_test2(S) => (S=76)
# "[ISO] '<<'/2: expected(succeed)".

bit_lr_test2(S) :- S is '<<'(19, 2).

%test 3 
:- test bit_lr_test3(S) => (S=(-64))
# "[ISO] '<<'/2: expected(impldep)".

bit_lr_test3(S) :- S is '<<'(-16, 2).

%test 4 
:- test bit_lr_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '<<'/2: expected(error) bug(fail)".

bit_lr_test4(S) :- S is '<<'(77, _N).

%% REVIEW:PENDING                                                                 **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 5 
:- test bit_lr_test5(S) + exception(error(type_error(integer, foo), Imp_dep))
# "[ISO] '<<'/2: expected(error) bug(fail)".

bit_lr_test5(S) :- S is '<<'(foo, 2).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 6 
:- test bit_lr_test6(S) + exception(error(type_error(integer, 1.0), Imp_dep))
# "[Non-ISO] '<<'/2: expected(error) bug(succeed)".

bit_lr_test6(S) :- S is '<<'(1.0, 2).


% ===========================================================================
%% 9.4.3.4 These tests are specified in page 123 of the ISO standard. %%%

%test 1
:- test bit_and_test1(S) => (S=8)
# "[ISO] '/\\'/2: expected(succeed)".

bit_and_test1(S) :- S is '/\\'(10, 12).

%test 2
:- test bit_and_test2(S) => (S=8)
# "[ISO] '/\'/2: expected(succeed)".

bit_and_test2(S) :- S is /\(10, 12).

%test 3 
:- test bit_and_test3(S) => (S=125)
# "[ISO] '/\\'/2: expected(impldep)".

bit_and_test3(S) :- S is '/\\'(17*256 +125, 255).

%test 4
:- test bit_and_test4(S) => (S=4)
# "[ISO] '/\'/2: expected(impldep)".

bit_and_test4(S) :- S is /\(-10, 12).

%test 5 
:- test bit_and_test5(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '/\\'/2: expected(error) bug(fail)".

bit_and_test5(S) :- S is '/\\'(77, _N).

%% REVIEW:PENDING                                                            **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 6 
:- test bit_and_test6(S) + exception(error(type_error(integer, foo), Imp_dep))
# "[ISO] '/\\'/2: expected(error) bug(fail)".

bit_and_test6(S) :- S is '/\\'(foo, 2).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 7 
:- test bit_and_test7(S) + exception(error(type_error(integer, 1.0), Imp_dep))
# "[Non-ISO] '/\\'/2: expected(error) bug(succeed)".

bit_and_test7(S) :- S is '/\\'(1.0, 2).

% ===========================================================================
%% 9.4.4.4 These tests are specified in page 124 of the ISO standard. %%%

%test 1
:- test bit_or_test1(S) => (S=14)
# "[ISO] '\\/'/2: expected(succeed)".

bit_or_test1(S) :- S is '\\/'(10, 12).

%test 2
:- test bit_or_test2(S) => (S=14)
# "[ISO] '\/'/2: expected(succeed)".

bit_or_test2(S) :- S is \/(10, 12).

%test 3 
:- test bit_or_test3(S) => (S=255)
# "[ISO] '\\/'/2: expected(succeed)".

bit_or_test3(S) :- S is '\\/'(125, 255).

%test 4 
:- test bit_or_test4(S) => (S=(-2))
# "[ISO] '\/'/2: expected(impldep)".

bit_or_test4(S) :- S is \/(-10, 12).

%test 5
:- test bit_or_test5(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '\\/'/2: expected(error) bug(fail)".

bit_or_test5(S) :- S is '\\/'(77, _N).

%% REVIEW:PENDING                                                      **Label_3**
%%   [gprolog]: throws exception: error(type_error(evaluable,foo/0),(is)/2)
%%   [ciao]: throws exception(error(type_error(evaluable,foo),'arithmetic:is'/2-2))
%test 6
:- test bit_or_test6(S) + exception(error(type_error(integer, foo), Imp_dep))
# "[ISO] '\\/'/2: expected(error) bug(fail)".

bit_or_test6(S) :- S is '\\/'(foo, 2).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 7 
:- test bit_or_test7(S) + exception(error(type_error(integer, 1.0), Imp_dep))
# "[Non-ISO] '\\/'/2: expected(error) bug(succeed)".

bit_or_test7(S) :- S is '\\/'(1.0, 2).


% ===========================================================================
%% 9.4.5.4 These tests are specified in page 124 of the ISO standard. %%%

%test 1
:- test bit_not_test1(S) => (S=10)
# "[ISO] '\\'/1: expected(succeed)".

bit_not_test1(S) :- S is '\\'('\\'(10)).

%test 2
:- test bit_not_test2(S) => (S=10)
# "[ISO] '\\'/1: expected(succeed)".

bit_not_test2(S) :- S is \(\(10)).

%test 3 
:- test bit_not_test3(S)
	=> (S=(-11))
# "[ISO] '\'/1: expected(impldep)".

bit_not_test3(S) :- S is \(10).

%test 4
:- test bit_not_test4(S) + exception(error(instantiation_error, Imp_dep))
# "[ISO] '\\'/2: expected(error) bug(fail)".

bit_not_test4(S) :- S is '\\'(_N).

%test 5 
:- test bit_not_test5(S) + exception(error(type_error(integer, 2.5), Imp_dep))
# "[ISO] '\\'/2: expected(error) bug(succeed)".

bit_not_test5(S) :- S is '\\'(2.5).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 6 
:- test bit_not_test6(S) + exception(error(type_error(integer, 2.5), Imp_dep))
# "[Non-ISO] '\\'/2: expected(error) bug(succeed)".

bit_not_test6(S) :- S is '\\'(2.5).


% ===========================================================================
%% These tests verifying the operation of unbounded based on logtalk tests.

%test 1
:- test unbounded_test1(N) => (N=( 123456789012345678901234567890))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test1(N) :- N is '-'( 123456789012345678901234567891, 1).

%test 2
:- test unbounded_test2(N) => (N=(-1.3419876543210988e+34))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test2(N) :- N is '-'( 123456789012345678901234567890, 13.42e+33).

%test 3
:- test unbounded_test3(N) => (N=(123456789012345678901234567890))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test3(N) :- N is '-'( 246913578024691357802469135780,123456789012345678901234567890).

%test 4
:- test unbounded_test4(N) => (N=(-123456789012345678901234567890))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test4(N):- N is '-'(1,123456789012345678901234567891).

%test 5
:- test unbounded_test5(N) => (N=(123456789012345678901234567891))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test5(N):- N is '+'(1,123456789012345678901234567890).

%test 6
:- test unbounded_test6(N) => (N=(246913578024691357802469135780))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test6(N):- N is '+'(123456789012345678901234567890,123456789012345678901234567890).

%test 7
:- test unbounded_test7(N) => (N=(1.3420123456789013e+34))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test7(N):- N is '+'(123456789012345678901234567890,13.42e+33).

%test 8
:- test unbounded_test8(N) => (N=(370370367037037036703703703670))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test8(N):- N is '*'(123456789012345678901234567890,3).

%test 9
:- test unbounded_test9(N) => (N=(15241578753238836750495351562536198787501905199875019052100))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test9(N):- N is '*'(123456789012345678901234567890,123456789012345678901234567890).

%test 10
:- test unbounded_test10(N) => (N=( 1.656790108545679e+63))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test10(N):- N is '*'(123456789012345678901234567890,13.42e+33).

%test 11
:- test unbounded_test11(N) => (N=(41152263004115226300411522630))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test11(N):- N is '//'(123456789012345678901234567890,3).

%test 12
:- test unbounded_test12(N) => (N=(0))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test12(N):- N is '//'(3,123456789012345678901234567890).

%test 13
:- test unbounded_test13(N) => (N=( 41152263004115226300411522630))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test13(N):- N is '//'(15241578753238836750495351562536198787501905199875019052100, 370370367037037036703703703670).

%test 14
:- test unbounded_test14(N) => (N=(4.115226300411523e+28))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test14(N):- N is '/'(123456789012345678901234567890,3).

%test 15
:- test unbounded_test15(N) => (N=( 2.4300000218700003e-29))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test15(N):- N is '/'(3,123456789012345678901234567890).

%test 16
:- test unbounded_test16(N) => (N=( 3.0000000000000004))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test16(N):- N is '/'(370370367037037036703703703670,123456789012345678901234567890).

%test 17
:- test unbounded_test17(N) => (N=( 2.7598388005740465e-05))
# "[ISO] '-'/2: expected(succeed)".

unbounded_test17(N):- N is '/'(370370367037037036703703703670,13.42e+33).


