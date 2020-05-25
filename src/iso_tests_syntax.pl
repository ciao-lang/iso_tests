:- module(iso_tests_syntax, _, [assertions, nativeprops, unittestdecls, iso]).

:- doc(title, "ISO tests for syntax").
:- doc(author, "Lorea Galech").
:- doc(author, "R@'{e}my Haemmerl@'{e}").

:- doc(module, "ISO standard tests for Ciao for syntax (see `iso_tests.pl`).").

:- use_module(iso_tests(iso_tests_common), []).

:- reexport(iso_tests(iso_tests_common)).
:- reexport(library(read)).
:- reexport(library(streams), [open/3, close/1]).
:- reexport(engine(runtime_control)).

% ===========================================================================
%% 6.3.3.1 These tests are specified in page 17 of the ISO standard. %%%%

%test 1
:- test term_test1 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, 'f(x,y).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] arguments: expected(succeed)".

term_test1 :- read(_).

%test 2
:- test term_test2 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text,
            'f(:-, ;, [:-, :-|:-]).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] arguments: expected(succeed)".

term_test2 :- read(_).

%test3 
:- test term_test3 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, 'f(,,a).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] arguments: expected(error) bug(wrong_error)".

term_test3 :- read(_).

%test4 
:- test term_test4 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, '[a,,|v].'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] arguments: expected(error) bug(wrong_error)".

term_test4 :- read(_).

%test5 
:- test term_test5 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, '[a,b|,]'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] arguments: expected(error) bug(wrong_error)".

term_test5 :- read(_).

%test6
:- test term_test6 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, "f(',',a)."),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] arguments: expected(succeed)".

term_test6 :- read(_).

%test7
:- test term_test7 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, "[a,','|v]."),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] arguments: expected(succeed)".

term_test7 :- read(_).

%test8
:- test term_test8 :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, "[a,b|',']."),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] arguments: expected(succeed)".

term_test8 :- read(_).




%% 6.3.4 These tests are specified in page 17 of the ISO standard. %%%%%%

operators :-
    op(100, fx,  fx),
    op(100, fy,  fy),
    op(100, xfx, xfx),
    op(100, xfy, xfy),
    op(100, yfx, yfx),
    op(100, xf,  xf),
    op(100, yf,  yf).


%test1 
:- test opnotation_test1 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            'fx fx 1.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] operands: expected(error) bug(wrong_error)".

opnotation_test1 :- read(_).

%test2
:- test opnotation_test2 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            'fx (fx 1).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test2 :- read(_).


%test3 
:- test opnotation_test3 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xf xf.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] operands: expected(error) bug(wrong_error)".

opnotation_test3 :- read(_).

%test4
:- test opnotation_test4 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '(1 xf) xf.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test4 :- read(_).

%test5 
:- test opnotation_test5 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xfx 2 xfx 3.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] operands: expected(error) bug(wrong_error)".

opnotation_test5 :- read(_).

%test6
:- test opnotation_test6 :
    ( operators, open('/tmp/tmp.in', write, Stream), write_contents(text,
            '(1 xfx 2) xfx 3.', Stream),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test6 :- read(_).

%test7 
:- test opnotation_test7 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xfx 2 xfx 3.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
    + exception(error(syntax_error(Imp_dep_atom), Imp_dep))
# "[ISO] operands: expected(error) bug(wrong_error)".

opnotation_test7 :- read(_).


%test8
:- test opnotation_test8 :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xfx (2 xfx 3).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test8 :- read(_).

%test9
:- test opnotation_test9(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            'fy fy 1. fy (fy 1).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test9(T, T1) :- read(T), read(T1).

%test10
:- test opnotation_test10(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xfy 2 xfy 3. 1 xfy (2 xfy 3).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test10(T, T1) :- read(T), read(T1).


%test11
:- test opnotation_test11(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 xfy 2 yfx 3. 1 xfy (2 yfx 3).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test11(T, T1) :- read(T), read(T1).


%test12
:- test opnotation_test12(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            'fy 2 yf. fy (2 yf).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test12(T, T1) :- read(T), read(T1).


%test13
:- test opnotation_test13(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 yf yf. (1 yf) yf.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn))
# "[ISO] operands: expected(succeed)".

opnotation_test13(T, T1) :- read(T), read(T1).

%test14
:- test opnotation_test14(T, T1) :
    ( operators, open_and_write('/tmp/tmp.in', write, Stream, [], text,
            '1 yfx 2 yfx 3. (1 yfx 2) yfx 3.'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=T1, close_instreams(Sc, Sn), no_operators)
# "[ISO] operands: expected(succeed)".

opnotation_test14(T, T1) :- read(T), read(T1).

no_operators :-
    op(0,   fx,  fx),
    op(0,   fy,  fy),
    op(0,   xfx, xfx),
    op(0,   xfy, xfy),
    op(0,   yfx, yfx),
    op(0,   xf,  xf),
    op(100, yf,  yf).


% ===========================================================================
%% 6.3.5.1 These tests are specified in page 19 of the ISO standard. %%%%

%test 1
:- test list_test1(T) :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, '.(a,[]).'),
        close(Stream), open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=[a], close_instreams(Sc, Sn))
# "[ISO] list notation: expected(succeed)".

list_test1(T) :- read(T).

%test 2
:- test list_test2(T) :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, '.(a, .(b,[])).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=[a, b], close_instreams(Sc, Sn))
# "[ISO] list notation: expected(succeed)".

list_test2(T) :- read(T).

%test 3
:- test list_test3(T) :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, '.(a,b).'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T=[a|b], close_instreams(Sc, Sn))
# "[ISO] list notation: expected(succeed)".

list_test3(T) :- read(T).



% ===========================================================================
%% 6.3.6.1 These tests are specified in page 20 of the ISO standard. %%%%

%test 1
:- test curly_test1(T) :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, "'{}'(a)."),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T={a}, close_instreams(Sc, Sn))
# "[ISO] {}/1 notation: expected(succeed)".

curly_test1(T) :- read(T).


%test 2
:- test curly_test2(T) :
    ( open_and_write('/tmp/tmp.in', write, Stream, [], text, "'{}'(','(a,b))."),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []) )
    => (T={a, b}, close_instreams(Sc, Sn))
# "[ISO] {}/1 notation: expected(succeed)".

curly_test2(T) :- read(T).



% ===========================================================================
%% 6.3.7.1 These tests are specified in page 20 of the ISO standard. %%%%

%test 1 
:- test doublequoted_test1(X, Y) : (X='jim', Y= "jim") + not_fails
# "[ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".
% TODO: rewrite in several tests

doublequoted_test1(X, Y) :-
    ( current_prolog_flag(double_quotes, chars),
        atom_chars(X, Y) ;
        current_prolog_flag(double_quotes, codes), atom_codes(X, Y) ;
        current_prolog_flag(double_quotes, atom), X==Y ).

%test 2 
:- test doublequoted_test2(X, Y, Z) : (X=[], Y= "", Z='') + not_fails
# "[ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".
% TODO: rewrite in several tests

doublequoted_test2(X, Y, Z) :-
    ( current_prolog_flag(double_quotes, chars), X==Y;
        current_prolog_flag(double_quotes, codes), X==Y;
        current_prolog_flag(double_quotes, atom), Z==Y ).


%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

%test 3 
:- test doublequoted_test3(X) :
    ( current_prolog_flag(double_quotes, chars),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text,
            '"jim".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test3(X) :- atom_chars('jim', X).


%test 4 
:- test doublequoted_test4(X) :
    ( current_prolog_flag(double_quotes, codes),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text,
            '"jim".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test4(X) :- atom_codes('jim', X).


%test 5 
:- test doublequoted_test5(X) :
    ( current_prolog_flag(double_quotes, atom),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text,
            '"jim".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test5(X) :- 'jim'= X.

%test 6 
:- test doublequoted_test6(X) :
    ( current_prolog_flag(double_quotes, chars),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text, '"".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test6(X) :- X=[].

%test 7 
:- test doublequoted_test7(X) :
    ( current_prolog_flag(double_quotes, codes),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text, '"".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test7(X) :- X=[].

%test 8 
:- test doublequoted_test8(X) :
    ( current_prolog_flag(double_quotes, atom),
        open_and_write('/tmp/tmp.in', write, Stream, [type(text)], text, '"".'),
        close(Stream),
        open_to_read('/tmp/tmp.in', read, Sc, Sn, []), read(X) )
    => (close_instreams(Sc, Sn))
# "[Non-ISO] (depending on double_quotes flag) a double quoted list is either an atom or a list.".

doublequoted_test8(X) :- X=''.
