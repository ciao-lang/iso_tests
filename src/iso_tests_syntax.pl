:- module(iso_tests_syntax, _, [assertions, nativeprops, unittestdecls, iso_strict]).

:- doc(title, "ISO tests for syntax").
:- doc(author, "Lorea Galech").
:- doc(author, "R@'{e}my Haemmerl@'{e}").
:- doc(author, "Jose F. Morales").

:- doc(module, "ISO standard tests for Ciao for syntax (see `iso_tests.pl`).").

:- use_module(iso_tests(iso_tests_common), []).

:- reexport(iso_tests(iso_tests_common)).
:- reexport(library(streams), [open/3]).
:- reexport(library(iso_incomplete)).
:- reexport(engine(runtime_control)).

% ===========================================================================
%! # 6.3 Term syntax

setup_tmp_in(Text) :-
    open_and_write('/tmp/tmp.in', write, Stream, [], text, Text),
    iso_incomplete:close(Stream).

setup_read_test(Ops, Text, prev(Ops, Sc, Sn)) :-
    ( Ops = yes -> set_operators
    ; true
    ),
    setup_tmp_in(Text),
    open_to_read('/tmp/tmp.in', read, Sc, Sn, []).

cleanup_read_test(prev(Ops, Sc, Sn)) :-
    ( Ops = yes -> unset_operators
    ; true
    ),
    close_instreams(Sc, Sn).

% TODO:[JF] split fxops and fyops

set_operators :-
    op(100, fx,  fx),
    op(100, fy,  fy),
    op(100, xfx, xfx),
    op(100, xfy, xfy),
    op(100, yfx, yfx),
    op(100, xf,  xf),
    op(100, yf,  yf).

unset_operators :-
    op(0, fx,  fx),
    op(0, fy,  fy),
    op(0, xfx, xfx),
    op(0, xfy, xfy),
    op(0, yfx, yfx),
    op(0, xf,  xf),
    op(0, yf,  yf).

% ---------------------------------------------------------------------------
%! ## 6.3.3 canonical notation ISOcore#p17

% NOTE: The standard calls this functional notation, which has nothing
%   to do with fsyntax package in Ciao Prolog (JF)

:- test term_test1
   + (not_fails,
      setup(setup_read_test(no, 'f(x,y).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: arguments".

term_test1 :- read(_).

:- test term_test2
   + (not_fails,
      setup(setup_read_test(no, 'f(:-, ;, [:-, :-|:-]).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: arguments".

term_test2 :- read(_).

:- test term_test3
   + (setup(setup_read_test(no, 'f(,,a).', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: arguments".

term_test3 :- read(_).

:- test term_test4
   + (setup(setup_read_test(no, '[a,,|v].', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: arguments".

term_test4 :- read(_).

:- test term_test5
   + (setup(setup_read_test(no, '[a,b|,]', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: arguments".

term_test5 :- read(_).

:- test term_test6
   + (not_fails,
      setup(setup_read_test(no, "f(',',a).", Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: arguments".

term_test6 :- read(_).

:- test term_test7
   + (not_fails,
      setup(setup_read_test(no, "[a,','|v].", Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: arguments".

term_test7 :- read(_).

:- test term_test8
   + (not_fails,
      setup(setup_read_test(no, "[a,b|','].", Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: arguments".

term_test8 :- read(_).

% ---------------------------------------------------------------------------
%! ## 6.3.4 operator notation ISOcore#p17

:- test opnotation_test1
   + (setup(setup_read_test(yes, 'fx fx 1.', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: operators".

opnotation_test1 :- read(_).

:- test opnotation_test2
   + (not_fails,
      setup(setup_read_test(yes, 'fx (fx 1).', Prev)),
      cleanup(cleanup_read_test(Prev)))
# "[ISO] syntax: operators".

opnotation_test2 :- read(_).

:- test opnotation_test3
   + (setup(setup_read_test(yes, '1 xf xf.', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: operators".

opnotation_test3 :- read(_).

:- test opnotation_test4
   + (not_fails,
      setup(setup_read_test(yes, '(1 xf) xf.', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test4 :- read(_).

:- test opnotation_test5
   + (setup(setup_read_test(yes, '1 xfx 2 xfx 3.', Prev)),
      cleanup(cleanup_read_test(Prev)),
      exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: operators".

opnotation_test5 :- read(_).

:- test opnotation_test6
   + (not_fails,
      setup(setup_read_test(yes, '(1 xfx 2) xfx 3.', Prev)),
      cleanup(cleanup_read_test(Prev)))
# "[ISO] syntax: operators".

opnotation_test6 :- read(_).

:- test opnotation_test7
    + (setup(setup_read_test(yes, '1 xfx 2 xfx 3.', Prev)),
       cleanup(cleanup_read_test(Prev)),
       exception(error(syntax_error(ImplDepAtom), ImplDep)))
   # "[ISO] syntax: operators".

opnotation_test7 :- read(_).

:- test opnotation_test8
   + (not_fails,
      setup(setup_read_test(yes, '1 xfx (2 xfx 3).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test8 :- read(_).

:- test opnotation_test9(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, 'fy fy 1. fy (fy 1).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test9(T, T1) :- read(T), read(T1).

:- test opnotation_test10(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, '1 xfy 2 xfy 3. 1 xfy (2 xfy 3).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test10(T, T1) :- read(T), read(T1).

:- test opnotation_test11(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, '1 xfy 2 yfx 3. 1 xfy (2 yfx 3).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test11(T, T1) :- read(T), read(T1).

:- test opnotation_test12(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, 'fy 2 yf. fy (2 yf).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test12(T, T1) :- read(T), read(T1).

:- test opnotation_test13(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, '1 yf yf. (1 yf) yf.', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test13(T, T1) :- read(T), read(T1).

:- test opnotation_test14(T, T1) : true => (T=T1)
   + (not_fails,
      setup(setup_read_test(yes, '1 yfx 2 yfx 3. (1 yfx 2) yfx 3.', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: operators".

opnotation_test14(T, T1) :- read(T), read(T1).

% ---------------------------------------------------------------------------
%! ## 6.3.5 list notation ISOcore#p19

:- test list_test1(T) : true => (T=[a])
   + (not_fails, setup(setup_read_test(no, '.(a,[]).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: list notation".

list_test1(T) :- read(T).

:- test list_test2(T) : true => (T=[a, b])
   + (not_fails,
      setup(setup_read_test(no, '.(a, .(b,[])).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: list notation".

list_test2(T) :- read(T).

:- test list_test3(T) : true => (T=[a|b])
   + (not_fails,
      setup(setup_read_test(no, '.(a,b).', Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: list notation".

list_test3(T) :- read(T).

% ---------------------------------------------------------------------------
%! ## 6.3.6 curly bracketed term ISOcore#p20

:- test curly_test1(T) : true => (T={a})
   + (not_fails,
      setup(setup_read_test(no, "'{}'(a).", Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: @{@}/1 notation".

curly_test1(T) :- read(T).

:- test curly_test2(T) : true => (T={a, b})
   + (not_fails,
      setup(setup_read_test(no, "'{}'(','(a,b)).", Prev)),
      cleanup(cleanup_read_test(Prev)))
   # "[ISO] syntax: @{@}/1 notation".

curly_test2(T) :- read(T).

% ---------------------------------------------------------------------------
%! ## 6.3.7 double quoted list notation ISOcore#p20

% TODO: Current issues in Ciao
%
%  - Do not trust the output of those tests until the double_quotes
%    flag is implemented.

text_def(dq_ex_1, [
'( current_prolog_flag(double_quotes, chars), atom_chars(\'jim\', "jim")',
'; current_prolog_flag(double_quotes, codes), atom_codes(\'jim\', "jim")',
'; current_prolog_flag(double_quotes, atom), \'jim\' == "jim"',
').']).
text_def(dq_ex_2, [
'( current_prolog_flag(double_quotes, chars), [] == ""',
'; current_prolog_flag(double_quotes, codes), [] == ""',
'; current_prolog_flag(double_quotes, atom), \'\' == ""',
').']).

setup_doublequoted_ex(What, DQ, prev(PrevDQ, Sc, Sn)) :-
    ( nonvar(What), What = def(What0), text_def(What0, Text0) -> Text = Text0
    ; Text = What
    ),
    current_prolog_flag(double_quotes, PrevDQ),
    setup_tmp_in(Text),
    set_prolog_flag(double_quotes, DQ),
    open_to_read('/tmp/tmp.in', read, Sc, Sn, []).

cleanup_doublequoted_ex(prev(PrevDQ, Sc, Sn)) :-
    set_prolog_flag(double_quotes, PrevDQ),
    close_instreams(Sc, Sn).

% TODO:[JF] atom_chars(X, [108]) should report error(type_error(character,108),atom_chars/2).
:- test doublequoted_test1 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_1), chars, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test1 :-
    read(Goal), call(Goal).

:- test doublequoted_test2 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_1), codes, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test2 :-
    read(Goal), call(Goal).

:- test doublequoted_test3 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_1), atom, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test3 :-
    read(Goal), call(Goal).

:- test doublequoted_test4 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_2), chars, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test4 :-
    read(Goal), call(Goal).

:- test doublequoted_test5 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_2), codes, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test5 :-
    read(Goal), call(Goal).

:- test doublequoted_test6 +
   ( not_fails,
     setup(setup_doublequoted_ex(def(dq_ex_2), atom, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test6 :-
    read(Goal), call(Goal).

%%%%%%%%%%%%%%%%%%%%%%%% TEST FROM SICTUS AND EDDBALI %%%%%%%%%%%%%%%%%%%%%%%%

:- test doublequoted_test7 +
   ( not_fails,
     setup(setup_doublequoted_ex('"jim".', chars, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test7 :- read(X), atom_chars('jim', X).

:- test doublequoted_test8 +
   ( not_fails,
     setup(setup_doublequoted_ex('"jim".', codes, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test8 :- read(X), atom_codes('jim', X).

:- test doublequoted_test9 +
   ( not_fails,
     setup(setup_doublequoted_ex('"jim".', atom, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test9 :- read(X), 'jim' == X.

:- test doublequoted_test10 +
   ( not_fails,
     setup(setup_doublequoted_ex('"".', chars, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test10 :- read(X), atom_chars('', X).

:- test doublequoted_test11 +
   ( not_fails,
     setup(setup_doublequoted_ex('"".', codes, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test11 :- read(X), atom_codes('', X).

:- test doublequoted_test12 +
   ( not_fails,
     setup(setup_doublequoted_ex('"".', atom, Prev)),
     cleanup(cleanup_doublequoted_ex(Prev)) )
   # "[Non-ISO] syntax: double quotes: bug()".

doublequoted_test12 :- read(X), '' == X.

