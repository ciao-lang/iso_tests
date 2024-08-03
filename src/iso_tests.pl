:- module(iso_tests, _, [assertions, nativeprops, unittestdecls, iso_strict]).

:- doc(title, "ISO Prolog tests for Ciao").
:- doc(author, "The Ciao Development Team").
:- doc(author, "Lorea Galech (first port)").
:- doc(author, "R@'{e}my Haemmerl@'{e}").
:- doc(author, "Jos@'{e} Luis Bueno").
:- doc(author, "Jose F. Morales (fixes, rewrite)").

:- doc(module, "This module contains a collection of test assertions
for checking compliance of Ciao with the ISO Prolog standard using the
@lib{iso_strict} package. The description of each test annotates:

 - the source of the test:
   - `[ISO]` tests based on ISO Prolog standard document ISO+IEC+13211
   - `[ISO-cor1]` tests based or modified according to Corrigenda 1
   - `[ISO-cor2]` tests based or modified according to Corrigenda 2
   - `[ISO-cor3]` tests based or modified according to Corrigenda 3
   - `[ISO-sics]` other tests based Péter Szabó (SICStus) tests
   - `[ISO-eddbali]` other tests based on A Ed-Dbali's tests
   - `[ISO-ciao]` other ISO tests unique to this test suite
   - `[ISO-lg]` tests based on Logtalk test suite
 - the predicate or feature to be tested (e.g., a predicate, syntax, etc.)
 - and the current status in Ciao:
   - nothing else: works as expected
   - `bug()`: The test fails but fixing it is feasible in Ciao.
   - `bug(wontfix)`: The test fails but we are not considering fixing it
     (without breaking some useful Ciao feature).

The tests follow (when possible) the order specified in the ISO/IEC
13211-1 document. Additionally, it contain references to the documents
as follows:

 - `ISOcore#pNNN` means *ISO/IEC 13211-1:1995. Part 1: General Core* page NNN
 - `ISOcor1#pNNN` means *ISO/IEC 13211-1:1995 TECHNICAL CORRIGENDUM 1* page NNN
 - `ISOcor2#pNNN` means *ISO/IEC 13211-1:1995 TECHNICAL CORRIGENDUM 2* page NNN
 - `ISOcor3#pNNN` means *ISO/IEC 13211-1:1995 TECHNICAL CORRIGENDUM 3* page NNN
").

% TODO:[JF] wrong utf8 support sends corrupted data, which breaks unit
%   tests runnersending, uncomment the following line when fixed:

% :- compilation_fact(fixed_utf8).

% ---------------------------------------------------------------------------
%! # Auxiliary predicates (mostly for IO)

% TODO: copy of lists:sublist/2
% @var{List2} contains all the elements of @var{List1}
%:- export(sublist/2).
sublist([], _).
sublist([Element|Residue], List) :-
    member(Element, List),
    sublist(Residue, List).

% NOTE: default is type(text), eof_action(error)

:- discontiguous text_def/2.

write_data(txt(What), S) :-
    ( nonvar(What), What = def(What0), text_def(What0, Text0) -> Text = Text0
    ; Text = What
    ),
    ( atom(Text) -> write(S, Text)
    ; write_list(Text, S)
    ).
write_data(bin(Bytes), S) :-
    put_byte_list(Bytes, S).

write_list([],          _) :- !.
write_list([Head|Tail], S) :- !,
    write_list(Head, S), write_list(Tail, S).
write_list(Atom, S) :-
    atom(Atom), !,
    write(S, Atom).
write_list(Code, S) :-
    put_code(S, Code).

put_byte_list([],     _).
put_byte_list([B|Bs], S) :-
    put_byte(S, B),
    put_byte_list(Bs, S).

% This predicate sets the stream Sc as input and closes the stream Sn
close_instreams(Sc, Sn) :-
    set_input(Sc),
    close(Sn).

% This predicate sets the stream Sc as output and closes the stream Sn
close_outstreams(Sc, Sn) :-
    set_output(Sc),
    close(Sn).

% Current output stream
curr_out(S) :- current_output(S).

% Obtain a closed output stream (for tests)
closed_outstream(S) :-
    open('/tmp/tmp.out', write, S, []), close(S).

% Current input stream
curr_in(S) :- current_input(S).

% Obtain a closed input stream (for tests)
closed_instream(S) :-
    F = '/tmp/tmp.in',
    wr_f(F, txt('')), % make sure the file exists
    open(F, read, S, []), close(S).

w_type(txt(_), text).
w_type(bin(_), binary).

wr_f_s(F, What, Opts, S) :-
    w_type(What, Type),
    open(F, write, S, [type(Type)|Opts]),
    write_data(What, S).

wr_f(F, What) :-
    wr_f_s(F, What, [], S),
    close(S).

chk_out(F, What) :-
    w_type(What, Type),
    open(F, read, S, [type(Type)]),
    ( What = txt(Data) -> read_string_to_end(S, Data0)
    ; What = bin(Data) -> read_bytes_to_end(S, Data0)
    ; fail
    ),
    close(S),
    Data = Data0.

wr_and_open(F,What,Opts,S) :-
    ( What = txtbin(Bin) -> % write text specified as a binary, read as text
        wr_f(F, bin(Bin)),
        Type = text
    ; wr_f(F, What),
      w_type(What, Type)
    ),
    open(F, read, S, [type(Type)|Opts]).

w_in(What,prev(Sc,S)) :-
    wr_and_open('/tmp/tmp.in',What,[],S),
    current_input(Sc),
    set_input(S).

w_in_s(What,S,prev(S)) :-
    wr_and_open('/tmp/tmp.in',What,[],S).

w_in_s_e(What,S,prev(S)) :-
    wr_and_open('/tmp/tmp.in',What,[eof_action(eof_code)],S).

w_in_a(What,prev(S)) :-
    wr_and_open('/tmp/tmp.in',What,[alias(st_i)],S).

txt_out_s(S, prev(S)) :-
    open('/tmp/tmp.out', write, S).

txt_out_a(prev(S1)) :-
    open('/tmp/tmp.out', write, S1, [alias(st_o)]).

% Undo (close streams, etc)
und(prev(S2)) :- close(S2).
und(prev(Sc, Sn)) :- close_instreams(Sc, Sn).

:- meta_predicate with_def_ops(goal).
with_def_ops(Goal) :-
    % TODO: refine, not all operators are needed in all tests
    % TODO:[JF] split fxops and fyops
    Ops = [op(100, fx,  fx),
           op(100, fy,  fy),
           op(100, xfx, xfx),
           op(100, xfy, xfy),
           op(100, yfx, yfx),
           op(100, xf,  xf),
           op(100, yf,  yf)],
    with_ops(Ops, Goal).

% ---------------------------------------------------------------------------
% TODO: duplicated stream_utils:read_string_to_end/2; remove once stream aliases are integrated

%:- export(read_string_to_end/2).
read_string_to_end(S, L) :-
    get_code(S, C),
    ( C = -1 -> L = []
    ; L = [C|L0],
      read_string_to_end(S, L0)
    ).

read_bytes_to_end_ci(X) :-
    current_input(S),
    read_bytes_to_end(S, X).

%:- export(read_bytes_to_end/2).
read_bytes_to_end(S, L) :-
    get_byte(S, C),
    ( C = -1 -> L = []
    ; L = [C|L0],
      read_bytes_to_end(S, L0)
    ).

% ---------------------------------------------------------------------------

:- use_module(library(port_reify)).

:- meta_predicate with_pflag(?, ?, goal).
with_pflag(Flag, Value, G) :-
    current_prolog_flag(Flag, Value0),
    set_prolog_flag(Flag, Value),
    once_port_reify(G, Port),
    set_prolog_flag(Flag, Value0),
    port_call(Port).

:- meta_predicate with_ops(?, goal).
with_ops(Ops, G) :-
    set_ops(Ops),
    once_port_reify(G, Port),
    unset_ops(Ops),
    port_call(Port).

set_ops([]).
set_ops([op(P,F,Op)|Ops]) :- op(P, F, Op), set_ops(Ops).

unset_ops([]).
unset_ops([op(_,F,Op)|ABs]) :- op(0, F, Op), unset_ops(ABs).

% NOTE: char conversion may break message passing in the unittest framework, enclose here
:- meta_predicate with_chcvs(?, goal).
with_chcvs(ChCvs, G) :-
    set_char_conversions(ChCvs),
    set_prolog_flag(char_conversion, on),
    once_port_reify(G, Port),
    set_prolog_flag(char_conversion, off),
    unset_char_conversions(ChCvs),
    port_call(Port).

set_char_conversions([]).
set_char_conversions([A-B|ABs]) :- char_conversion(A,B), set_char_conversions(ABs).

unset_char_conversions([]).
unset_char_conversions([A-_|ABs]) :- char_conversion(A,A), unset_char_conversions(ABs).

% TODO:[JF] factorize
:- meta_predicate with_out_s(?, ?, goal, ?).
with_out_s(What, S, G, OutWhat) :-
    wr_f_s('/tmp/tmp.out', What, [], S),
    once_port_reify(G, Port),
    close(S),
    port_call(Port),
    chk_out('/tmp/tmp.out', OutWhat).

:- meta_predicate with_out(?, goal, ?).
with_out(What, G, OutWhat) :-
    wr_f_s('/tmp/tmp.out', What, [], S),
    current_output(Sc),
    set_output(S),
    once_port_reify(G, Port),
    close_outstreams(Sc, S),
    port_call(Port),
    chk_out('/tmp/tmp.out', OutWhat).

:- meta_predicate with_out_a(?, goal, ?).
with_out_a(What, G, OutWhat) :-
    wr_f_s('/tmp/tmp.out', What, [alias(st_o)], S),
    once_port_reify(G, Port),
    close(S),
    port_call(Port),
    chk_out('/tmp/tmp.out', OutWhat).

% ===========================================================================
%! # 6.3 Term syntax

% ---------------------------------------------------------------------------
%! ## 6.3.3 canonical notation ISOcore#p17

% NOTE: The standard calls this functional notation, which has nothing
%   to do with fsyntax package in Ciao Prolog (JF)

:- test term_test1
   + (not_fails,
      setup(w_in(txt('f(x,y).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: arguments".

term_test1 :- read(_).

:- test term_test2
   + (not_fails,
      setup(w_in(txt('f(:-, ;, [:-, :-|:-]).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: arguments".

term_test2 :- read(_).

:- test term_test3
   + (setup(w_in(txt('f(,,a).'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: arguments".

term_test3 :- read(_).

:- test term_test4
   + (setup(w_in(txt('[a,,|v].'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: arguments".

term_test4 :- read(_).

:- test term_test5
   + (setup(w_in(txt('[a,b|,]'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: arguments".

term_test5 :- read(_).

:- test term_test6
   + (not_fails,
      setup(w_in(txt("f(',',a)."), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: arguments".

term_test6 :- read(_).

:- test term_test7
   + (not_fails,
      setup(w_in(txt("[a,','|v]."), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: arguments".

term_test7 :- read(_).

:- test term_test8
   + (not_fails,
      setup(w_in(txt("[a,b|',']."), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: arguments".

term_test8 :- read(_).

% ---------------------------------------------------------------------------
%! ## 6.3.4 operator notation ISOcore#p17

:- test opnotation_test1
   + (setup(w_in(txt('fx fx 1.'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: operators".

opnotation_test1 :- with_def_ops(read(_)).

:- test opnotation_test2
   + (not_fails,
      setup(w_in(txt('fx (fx 1).'), Prev)), cleanup(und(Prev)))
# "[ISO] syntax: operators".

opnotation_test2 :- with_def_ops(read(_)).

:- test opnotation_test3
   + (setup(w_in(txt('1 xf xf.'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: operators".

opnotation_test3 :- with_def_ops(read(_)).

:- test opnotation_test4
   + (not_fails,
      setup(w_in(txt('(1 xf) xf.'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test4 :- with_def_ops(read(_)).

:- test opnotation_test5
   + (setup(w_in(txt('1 xfx 2 xfx 3.'), Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: operators".

opnotation_test5 :- with_def_ops(read(_)).

:- test opnotation_test6
   + (not_fails,
      setup(w_in(txt('(1 xfx 2) xfx 3.'), Prev)), cleanup(und(Prev)))
# "[ISO] syntax: operators".

opnotation_test6 :- with_def_ops(read(_)).

:- test opnotation_test7
    + (setup(w_in(txt('1 xfx 2 xfx 3.'), Prev)), cleanup(und(Prev)),
       exception(error(syntax_error(ImplDepAtom), _)))
   # "[ISO] syntax: operators".

opnotation_test7 :- with_def_ops(read(_)).

:- test opnotation_test8
   + (not_fails,
      setup(w_in(txt('1 xfx (2 xfx 3).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test8 :- with_def_ops(read(_)).

:- test opnotation_test9(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('fy fy 1. fy (fy 1).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test9(T, T1) :- with_def_ops((read(T), read(T1))).

:- test opnotation_test10(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('1 xfy 2 xfy 3. 1 xfy (2 xfy 3).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test10(T, T1) :- with_def_ops((read(T), read(T1))).

:- test opnotation_test11(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('1 xfy 2 yfx 3. 1 xfy (2 yfx 3).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test11(T, T1) :- with_def_ops((read(T), read(T1))).

:- test opnotation_test12(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('fy 2 yf. fy (2 yf).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test12(T, T1) :- with_def_ops((read(T), read(T1))).

:- test opnotation_test13(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('1 yf yf. (1 yf) yf.'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test13(T, T1) :- with_def_ops((read(T), read(T1))).

:- test opnotation_test14(T, T1) => (T=T1)
   + (not_fails,
      setup(w_in(txt('1 yfx 2 yfx 3. (1 yfx 2) yfx 3.'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: operators".

opnotation_test14(T, T1) :- with_def_ops((read(T), read(T1))).

% ---------------------------------------------------------------------------
%! ## 6.3.5 list notation ISOcore#p19

:- test list_test1(T) => (T=[a])
   + (not_fails,
      setup(w_in(txt('.(a,[]).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: list notation".

list_test1(T) :- read(T).

:- test list_test2(T) => (T=[a, b])
   + (not_fails,
      setup(w_in(txt('.(a, .(b,[])).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: list notation".

list_test2(T) :- read(T).

:- test list_test3(T) => (T=[a|b])
   + (not_fails,
      setup(w_in(txt('.(a,b).'), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: list notation".

list_test3(T) :- read(T).

% ---------------------------------------------------------------------------
%! ## 6.3.6 curly bracketed term ISOcore#p20

:- test curly_test1(T) => (T={a})
   + (not_fails,
      setup(w_in(txt("'{}'(a)."), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: @{@}/1 notation".

curly_test1(T) :- read(T).

:- test curly_test2(T) => (T={a, b})
   + (not_fails,
      setup(w_in(txt("'{}'(','(a,b))."), Prev)), cleanup(und(Prev)))
   # "[ISO] syntax: @{@}/1 notation".

curly_test2(T) :- read(T).

% ---------------------------------------------------------------------------
%! ## 6.3.7 double quoted list notation ISOcore#p20

% NOTE: Current issues in Ciao:
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

% TODO:[JF] atom_chars(X, [108]) should report error(type_error(character,108),atom_chars/2).
:- test doublequoted_test1 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_1)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test1 :-
    with_pflag(double_quotes, chars, (read(Goal), call(Goal))).

:- test doublequoted_test2 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_1)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test2 :-
    with_pflag(double_quotes, codes, (read(Goal), call(Goal))).

:- test doublequoted_test3 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_1)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test3 :-
    with_pflag(double_quotes, atom, (read(Goal), call(Goal))).

:- test doublequoted_test4 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_2)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test4 :-
    with_pflag(double_quotes, chars, (read(Goal), call(Goal))).

:- test doublequoted_test5 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_2)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test5 :-
    with_pflag(double_quotes, codes, (read(Goal), call(Goal))).

:- test doublequoted_test6 +
   ( not_fails,
     setup(w_in(txt(def(dq_ex_2)), Prev)), cleanup(und(Prev)) )
   # "[ISO] syntax: double quotes: bug()".

doublequoted_test6 :-
    with_pflag(double_quotes, atom, (read(Goal), call(Goal))).

:- test doublequoted_test7 +
   ( not_fails,
     setup(w_in(txt('"jim".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test7 :-
    with_pflag(double_quotes, chars, (read(X), atom_chars('jim', X))).

:- test doublequoted_test8 +
   ( not_fails,
     setup(w_in(txt('"jim".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test8 :-
    with_pflag(double_quotes, codes, (read(X), atom_codes('jim', X))).

:- test doublequoted_test9 +
   ( not_fails,
     setup(w_in(txt('"jim".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test9 :-
    with_pflag(double_quotes, atom, (read(X), 'jim' == X)).

:- test doublequoted_test10 +
   ( not_fails,
     setup(w_in(txt('"".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test10 :-
    with_pflag(double_quotes, chars, (read(X), atom_chars('', X))).

:- test doublequoted_test11 +
   ( not_fails,
     setup(w_in(txt('"".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test11 :-
    with_pflag(double_quotes, codes, (read(X), atom_codes('', X))).

:- test doublequoted_test12 +
   ( not_fails,
     setup(w_in(txt('"".'), Prev)), cleanup(und(Prev)) )
   # "[ISO-sics] syntax: double quotes: bug()".

doublequoted_test12 :-
    with_pflag(double_quotes, atom, (read(X), '' == X)).

% ===========================================================================
%! # 7.8 Control constructs

% NOTE: Current issues in Ciao:
%
%  - cut (`!/0`) is illegal in `\+` or if-parts of `->`
%  - The term to goal translation in `call/1` should set the right
%    scope of cut (!).
%  - The term to goal translation in `call/1` should complain when
%    finding a non-callable and report the whole term.
%
% NOTE: Incompatibilities in Ciao:
%
%  - catch_test4 seems to be wrong

%! ## 7.8.1 true/0 ISOcore#p43

:- test true + not_fails # "[ISO] true/0".

% ---------------------------------------------------------------------------
%! ## 7.8.2 fail/0 ISOcore#p44

:- test fail/0 + fails # "[ISO] fail/0".

% ---------------------------------------------------------------------------
%! ## 7.8.3 call/1 ISOcore#p45

:- test call_test1 # "[ISO] call/1".
call_test1 :- call(!).
 
:- test call_test2 + fails # "[ISO] call/1".
call_test2 :- call(fail).

:- test call_test3(X) + fails # "[ISO] call/1".
call_test3(X) :- call((fail, X)).

:- test call_test4 + fails # "[ISO] call/1".
call_test4 :- call((fail, call(1))).

:- test call_test5 + exception(error(instantiation_error, _)) # "[ISO] call/1".
call_test5 :- call(bb(_)).

bb(X) :-
    Y=(write(X), X),
    call(Y).

:- test call_test6
   + ( user_output("3"),
       exception(error(type_error(callable, 3), _)) )
   # "[ISO] call/1".

call_test6 :- call(bb(3)).

% TODO:[JF] set the scope of cut when the term is translated to a goal
:- test call_test7(Result) => (Result=[[1, !]])
   # "[ISO] call/1: bug()".

call_test7(Result) :- findall([X, Z], (Z= !, call((Z= !, aa(X), Z))), Result).

aa(1).

aa(2).

% NOTE: It works because `call(!)` is equivalent to `true`
:- test call_test8(Result) => (Result=[[1, !], [2, !]])
   # "[ISO] call/1".

call_test8(Result) :- findall([X, Z], (call((Z= !, aa(X), Z))), Result).

:- test call_test9(X)
   + (user_output("3"), exception(error(instantiation_error, _)))
   # "[ISO] call/1".

call_test9(X) :- call((write(3), X)).

:- test call_test10
   + (user_output("3"),
      exception(error(type_error(callable, 1), _)))
   # "[ISO] call/1".

call_test10 :- call((write(3), call(1))).

:- test call_test11 + exception(error(instantiation_error, _))
   # "[ISO] call/1".

call_test11 :- call(_).

:- test call_test12 + exception(error(type_error(callable, 1), _))
   # "[ISO] call/1".

call_test12 :- call(1).

% TODO:[JF] complain about non-callable when the term is translated to a goal
:- test call_test13
   + exception(error(type_error(callable, (fail, 1)), _))
   # "[ISO] call/1: bug()".

call_test13 :- call((fail, 1)).

% TODO:[JF] complain about non-callable when the term is translated to a goal,
%   do not write anything to output!
:- test call_test14
   + exception(error(type_error(callable, (write(3), 1)), _))
   # "[ISO] call/1: bug()".

call_test14 :- call((write(3), 1)).

% TODO:[JF] it should complain about non-callable when the term is translated to a goal,
%   and report the whole goal
:- test call_test15 + exception(error(type_error(callable, (1;true)), _))
# "[ISO] call/1: bug()".

call_test15 :- call((1;true)).

% TODO:[JF] it should complain about non-callable when the term is translated to a goal,
%   instead it executes the first branch
:- test call_test16 + exception(error(type_error(callable, (true;1)), _))
   # "[ISO-ciao] call/1: bug()".

call_test16 :- call((true;1)).

% ---------------------------------------------------------------------------
%! ## 7.8.4 !/0 ISOcore#p46

:- test cut_test1
   # "[ISO] cut".

cut_test1 :- !.

:- test cut_test2/0 + fails
   # "[ISO] cut".

cut_test2 :- !, fail;true.

:- test cut_test3/0
   # "[ISO] cut".

cut_test3 :- call(!), fail;true.

:- test cut_test4/0 + (user_output("C Forwards "), fails)
   # "[ISO] cut".

cut_test4 :- twice(_), !, write('Forwards '), fail.

:- test cut_test5 + (user_output("Cut disjunction"), fails)
   # "[ISO] cut".

cut_test5 :- (! ; write('No ')), write('Cut disjunction'), fail.

:- test cut_test6 + (user_output("C No Cut Cut "), fails)
   # "[ISO] cut".

cut_test6 :- twice(_), (write('No ') ; !), write('Cut '), fail.

:- test cut_test7 + (user_output("C "), fails)
   # "[ISO] cut".

cut_test7 :- twice(_), (!, fail, write('No ')).

:- test cut_test8 + (user_output("C Forwards Moss Forwards "), fails)
   # "[ISO] cut".

cut_test8 :- twice(X), call(X), write('Forwards '), fail.

:- test cut_test9 + (user_output("C Forwards Three Forwards "), fails)
   # "[ISO] cut".

cut_test9 :- goal(X), call(X), write('Forwards '), fail.

% TODO:[JF] ! is illegal in \+ or if-parts of ->; uncomment when fixed
:- test cut_test10 
   + (user_output("C Forwards Moss Forwards "),fails)
   # "[ISO] cut: bug()".
% cut_test10 :- twice(_), (\+(\+(!))), write('Forwards '), fail.
cut_test10 :- throw(bug).

:- test cut_test11 + (user_output("C Forwards Moss Forwards "), fails)
   # "[ISO] cut".

cut_test11 :- twice(_), once(!), write('Forwards '), fail.

:- test cut_test12 + (user_output("C Forwards Moss Forwards "), fails)
   # "[ISO] cut".

cut_test12 :- twice(_), call(!), write('Forwards '), fail.

% TODO:[JF] ! illegal in -> part ; reimplement without findall/3 when fixed
:- test cut_test13 + not_fails
   # "[ISO-ciao] cut: bug()".
cut_test13 :-
    findall(Y, ( member(X,[1,2]), !, X=2 -> Y=a ; Y=b ), Ys),
    Ys = [b].

% ---------------------------------------------------------------------------
% (these predicates are used in the tests above)

twice(!) :- write('C ').
twice(true) :- write('Moss ').

goal((twice(_), !)).
goal(write('Three ')).

% ---------------------------------------------------------------------------
%! ## 7.8.5 (,)/2 ISOcore#p47

:- test and_test1 + fails
   # "[ISO] ','".

and_test1 :- ','(X=1, var(X)).

:-test and_test2(X) => (X=1)
  # "[ISO] ','".

and_test2(X) :- ','(var(X), X=1).

:- test and_test3(X) => (X=true)
   # "[ISO] ','".

and_test3(X) :- ','(X=true, call(X)).

% ---------------------------------------------------------------------------
%! ## 7.8.6 (;)/2 ISOcore#p48

:- test or_test1
   # "[ISO] ';'".

or_test1 :- ';'(true, fail).

:- test or_test2 + fails
   # "[ISO] ';'".

or_test2 :- ';'((!, fail), true).

:- test or_test3
   # "[ISO] ';'".

or_test3 :- ';'(!, call(3)).

:- test or_test4(X) => (X=1)
   # "[ISO] ';'".

or_test4(X) :- ';'((X=1, !), X=2).

:- test or_test5(Result) => (Result=[1, 1])
   # "[ISO] ';'".

or_test5(Result) :- findall(X, call((;(X=1, X=2), ;(true, !))), Result).

% ---------------------------------------------------------------------------
%! ## 7.8.7 (->)/2 if-then ISOcore#p49

:- test ifthen_test1
   # "[ISO] '->'".

ifthen_test1 :- '->'(true, true).

:- test ifthen_test2 + fails
   # "[ISO] '->'".

ifthen_test2:- '->'(true, fail).

:- test ifthen_test3 + fails
   # "[ISO] '->'".

ifthen_test3 :- '->'(fail, true).

:- test ifthen_test4(Result) => (Result=[1])
   # "[ISO] '->'".

ifthen_test4(Result) :- findall(X, '->'(true, X=1), Result).

:- test ifthen_test5(Result) => (Result=[1])
   # "[ISO] '->'".

ifthen_test5(Result) :- findall(X, '->'(';'(X=1, X=2), true), Result).

:- test ifthen_test6(Result) => (Result=[1, 2])
   # "[ISO] '->'".

ifthen_test6(Result) :- findall(X, '->'(true, ';'(X=1, X=2)), Result).

% ===========================================================================
%! ## 7.8.8 (;)/2 if-then-else ISOcore#p51

:- test ifthenelse_test1
   # "[ISO] if-then-else".

ifthenelse_test1 :- ';'('->'(true, true), fail).

:- test ifthenelse_test2
   # "[ISO] if-then-else".

ifthenelse_test2 :- ';'('->'(fail, true), true).

:- test ifthenelse_test3 + fails
   # "[ISO] if-then-else".

ifthenelse_test3 :- ';'('->'(true, fail), fail).

:- test ifthenelse_test4 + fails
   # "[ISO] if-then-else".

ifthenelse_test4 :- ';'('->'(fail, true), fail).

:- test ifthenelse_test5(X) => (X=1)
   # "[ISO] if-then-else".

ifthenelse_test5(X) :- ';'('->'(true, X=1), X=2).

:- test ifthenelse_test6(X) => (X=2)
   # "[ISO] if-then-else".

ifthenelse_test6(X) :- ';'('->'(fail, X=1), X=2).

:- test ifthenelse_test7(Result) => (Result=[1, 2])
   # "[ISO] if-then-else".

ifthenelse_test7(Result) :-
    findall(X, ';'('->'(true, ';'(X=1, X=2)), true), Result).

:- test ifthenelse_test8(X) => (X=1)
   # "[ISO] if-then-else".

ifthenelse_test8(X) :- ';'('->'(';'(X=1, X=2), true), true).

% TODO:[JF] ! is illegal in \+ or if-parts of ->; uncomment when fixed
:- test ifthenelse_test9
   + not_fails
   # "[ISO] if-then-else".

% ifthenelse_test9 :- ';'('->'(','(!, fail), true), true).
ifthenelse_test9 :- throw(bug).

% ---------------------------------------------------------------------------
%! ## 7.8.9 catch/3 ISOcore#p52

:- test catch_test1(Y) => (Y=10)
   # "[ISO] catch/3".

catch_test1(Y) :- catch(p_catch__foo(5), test(Y), true).

p_catch__foo(X) :- Y is X*2, throw(test(Y)).

:- test catch_test2(Z) : (Z=3)
   # "[ISO] catch/3".

catch_test2(Z) :- catch(p_catch__bar(3), Z, true).

p_catch__bar(X) :- X = Y, throw(Y).

:- test catch_test3
   # "[ISO] catch/3".

catch_test3 :- catch(true, _, 3).

% TODO:[JF] this ISO tests seems to be wrong (according to all Prolog systems and Logtalk)
% :- test catch_test4 + exception(error(system_error, _))
%    # "[ISO] catch/3".
% 
% catch_test4 :- catch(true, _C, write(demoen)), throw(bla).

:- test catch_test5(Y) => (Y=1)
   # "[ISO] catch/3".

catch_test5(Y) :- catch(p_catch__car(_X), Y, true).

p_catch__car(X) :- X=1, throw(X).

:- test catch_test6 + fails
   # "[ISO] catch/3".

catch_test6 :-
    catch(number_chars(_X, ['1', 'a', '0']), error(syntax_error(_), _), fail).

:- test catch_test7(Result) => (Result=[c]) + (user_output("h1"))
   # "[ISO] catch/3".

catch_test7(Result) :- findall(C, catch(p_catch__g, C, write(h1)), Result).

p_catch__g :- catch(p_catch__p, _B, write(h2)), p_catch__coo(c).

p_catch__p.
p_catch__p :- throw(b).

p_catch__coo(X) :- throw(X).

:- test catch_test8(Y) => (Y=error(instantiation_error, Imp_def))
   # "[ISO] catch/3".

catch_test8(Y) :- catch(p_catch__coo8(_X), Y, true).

p_catch__coo8(X) :- throw(X).

% ---------------------------------------------------------------------------
%! ## 7.8.10 throw/1 ISOcore#p53

% (see 7.8.9 catch/3)

% ===========================================================================
%! # 8.2 Term unification
%! ## 8.2.1 (=)/2 ISOcore#p65

:- test unify_test1 + not_fails
   # "[ISO] =/2".

unify_test1:- '='(1, 1).

:- test unify_test2(X) => (X=1)
   # "[ISO] =/2".

unify_test2(X) :- '='(X, 1).

:- test unify_test3(X, Y) => (X=Y)
   # "[ISO] =/2".

unify_test3(X, Y) :- '='(X, Y).

:- test unify_test4 + not_fails
   # "[ISO] =/2".

unify_test4 :- '='(_, _).

:- test unify_test5(X, Y) => (X='abc', Y='abc')
   # "[ISO] =/2".

unify_test5(X, Y) :- '='(X, Y), '='(X, abc).

:- test unify_test6(X, Y) => (X='def', Y='def')
   # "[ISO] =/2".

unify_test6(X, Y) :- '='(X, def), '='(def, Y).

:- test unify_test7 + fails
   # "[ISO] =/2".

unify_test7 :- '='(1, 2).

:- test unify_test8 + fails
   # "[ISO] =/2".

unify_test8 :- '='(1, 1.0).

:- test unify_test9 + fails
   # "[ISO] =/2".

unify_test9 :- '='(g(X), f(f(X))).

:- test unify_test10 + fails
   # "[ISO] =/2".

unify_test10 :- '='(f(X, 1), f(a(X))).

:- test unify_test11 + fails
   # "[ISO] =/2".

unify_test11 :- '='(f(X, Y, X), f(a(X), a(Y), Y, 2)).

:- test unify_test12
   # "[ISO] =/2". % NOTE: Ciao supports rational terms

unify_test12 :- '='(X, a(X)).

:- test unify_test13
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] =/2".

unify_test13 :- '='(f(X, 1), f(a(X), 2)).

:- test unify_test14
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] =/2".

unify_test14 :- '='(f(1, X, 1), f(2, a(X), 2)).

:- test unify_test15
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] =/2".

unify_test15 :- '='(f(1, X), f(2, a(X))).

:- test unify_test16
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] =/2".

unify_test16 :- '='(f(X, Y, X, 1), f(a(X), a(Y), Y, 2)).

% ---------------------------------------------------------------------------
%! ## 8.2.2 unify_occurs_check/2 ISOcore#p66

:- test unify_occurs_test1 + not_fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test1 :- unify_with_occurs_check(1, 1).

:- test unify_occurs_test2(X) => (X=1)
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test2(X) :- unify_with_occurs_check(X, 1).

:- test unify_occurs_test3(X, Y) => (X=Y)
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test3(X, Y) :- unify_with_occurs_check(X, Y).

:- test unify_occurs_test4 + not_fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test4 :- unify_with_occurs_check(_, _).

:- test unify_occurs_test5(X, Y) => (X=abc, Y=abc)
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test5(X, Y) :-
    unify_with_occurs_check(X, Y),
    unify_with_occurs_check(X, abc).

:- test unify_occurs_test6(X, Y) => (X=def, Y=def)
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test6(X, Y) :- unify_with_occurs_check(f(X, def), f(def, Y)).

:- test unify_occurs_test7 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test7 :- unify_with_occurs_check(1, 2).

:- test unify_occurs_test8 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test8 :- unify_with_occurs_check(1, 1.0).

:- test unify_occurs_test9 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test9 :- unify_with_occurs_check(g(X), f(X)).

:- test unify_occurs_test10 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test10 :- unify_with_occurs_check(f(X, 1), f(a(X))).

:- test unify_occurs_test11 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test11 :-
    unify_with_occurs_check(f(X, Y, X), f(a(X), a(Y), Y, 2)).

:- test unify_occurs_test12 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test12 :- unify_with_occurs_check(X, a(X)).

:- test unify_occurs_test13 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test13 :-
    unify_with_occurs_check(f(X, 1), f(a(X), 2)).

:- test unify_occurs_test14 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test14 :- unify_with_occurs_check(f(1, X, 1), f(2, a(X), 2)).

:- test unify_occurs_test15 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test15 :- unify_with_occurs_check(f(1, X), f(2, a(X))).

:- test unify_occurs_test16 + fails
   # "[ISO] unify_with_occurs_check/2".

unify_occurs_test16 :-
    unify_with_occurs_check(f(X, Y, X, 1), f(a(X), a(Y), Y, 2)).

% ---------------------------------------------------------------------------
%! ## 8.2.3 (\=)/2 ISOcore#p67

:- test not_uni_test1 + fails
   # "[ISO] '\\='/2".

not_uni_test1 :- '\\='(1, 1).

:- test not_uni_test2(X) + fails
   # "[ISO] '\\='/2".

not_uni_test2(X) :- \=(X, 1).

:- test not_uni_test3(X, Y) + fails
   # "[ISO] '\\='/2".

not_uni_test3(X, Y) :- '\\='(X, Y).

:- test not_uni_test4 + fails
   # "[ISO] '\\='/2".

not_uni_test4 :- \=(_, _).

:- test not_uni_test5(X, Y) + fails
   # "[ISO] '\\='/2".

not_uni_test5(X, Y) :- \=(f(X, def), f(def, Y)).

:- test not_uni_test6 + not_fails
   # "[ISO] '\\='/2".

not_uni_test6 :- '\\='(1, 2).

:- test not_uni_test7 + not_fails
   # "[ISO] '\\='/2".

not_uni_test7:- \=(1, 1.0).

:- test not_uni_test8(X) + not_fails
   # "[ISO] '\\='/2".

not_uni_test8(X) :- '\\='(g(X), f(f(X))).

:- test not_uni_test9(X) + not_fails
   # "[ISO] '\\='/2".

not_uni_test9(X) :- \=(f(X, 1), f(a(X))).

:- test not_uni_test10(X, Y) + not_fails
   # "[ISO] '\\='/2".

not_uni_test10(X, Y) :- '\\='(f(X, Y, X), f(a(X), a(Y), Y, 2)).

:- test not_uni_test11(X) 
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] '\\='/2".

not_uni_test11(X) :- \=(X, a(X)).

:- test not_uni_test12(X) 
   # "[ISO] '\\='/2". % NOTE: Ciao supports rational terms

not_uni_test12(X) :- '\\='(f(X, 1), f(a(X), 2)).

:- test not_uni_test13(X)
   # "[ISO] '\\='/2". % NOTE: Ciao supports rational terms

not_uni_test13(X) :- '\\='(f(1, X, 1), f(2, a(X), 2)).

:- test not_uni_test14(X) 
   + fails % NOTE: Ciao supports rational terms
   # "[ISO] '\\='/2".

not_uni_test14(X) :- \=(f(2, X), f(2, a(X))).

:- test not_uni_test15(X, Y)
   # "[ISO] '\\='/2". % NOTE: Ciao supports rational terms

not_uni_test15(X, Y) :- '\\='(f(X, Y, X, 1), f(a(X), a(Y), Y, 2)).

% ===========================================================================
%! # 8.3 Type testing
%! ## 8.3.1 var/1 ISOcore#p67

:- test var_test1 + fails # "[ISO] var/1".
var_test1 :- var(foo).

:- test var_test2(Foo) + not_fails # "[ISO] var/1".
var_test2(Foo) :- var(Foo).

:- test var_test3 + fails # "[ISO] var/1".
var_test3 :- foo=Foo, var(Foo).

:- test var_test4 + not_fails # "[ISO] var/1".
var_test4 :- var(_).

% ---------------------------------------------------------------------------
%! ## 8.3.2 atom/1 ISOcore#p68

:- test atom_test1 + not_fails # "[ISO] atom/1".
atom_test1 :- atom(atom).

:- test atom_test2 + not_fails # "[ISO] atom/1".
atom_test2 :- atom('string').

:- test atom_test3 + fails # "[ISO] atom/1".
atom_test3 :- atom(a(b)).

:- test atom_test4 + fails # "[ISO] atom/1".
atom_test4 :- atom(_Var).

:- test atom_test5 + not_fails # "[ISO] atom/1".
atom_test5 :- atom([]).

:- test atom_test6 + fails # "[ISO] atom/1".
atom_test6 :- atom(6).

:- test atom_test7 + fails # "[ISO] atom/1".
atom_test7 :- atom(3.3).

% ---------------------------------------------------------------------------
%! ## 8.3.3 integer/1 ISOcore#p68

:- test integer_test1 + not_fails # "[ISO] integer/1".
integer_test1 :- integer(3).

:- test integer_test2 + not_fails # "[ISO] integer/1".
integer_test2 :- integer(-3).

:- test integer_test3 + fails # "[ISO] integer/1".
integer_test3 :- integer(3.3).

:- test integer_test4(X) + fails # "[ISO] integer/1".
integer_test4(X) :- integer(X).

:- test integer_test5 + fails # "[ISO] integer/1".
integer_test5 :- integer(atom).

% ---------------------------------------------------------------------------
%! ## 8.3.4 float/1 ISOcore#p68

:- test float_test1 + not_fails # "[ISO] float/1".
float_test1 :- float(3.3).

:- test float_test2 + not_fails # "[ISO] float/1".
float_test2 :- float(-3.3).

:- test float_test3 + fails # "[ISO] float/1".
float_test3 :- float(3).

:- test float_test4 + fails # "[ISO] float/1".
float_test4 :- float(atom).

:- test float_test5(X) + fails # "[ISO] float/1".
float_test5(X) :- float(X).

% ---------------------------------------------------------------------------
%! ## 8.3.5 ISOcore#p69

:- test atomic_test1 + not_fails # "[ISO] atomic/1".
atomic_test1 :- atomic(atom).

:- test atomic_test2 + fails # "[ISO] atomic/1".
atomic_test2 :- atomic(a(b)).

:- test atomic_test3(Var) + fails # "[ISO] atomic/1".
atomic_test3(Var) :- atomic(Var).

:- test atomic_test4 + not_fails # "[ISO] atomic/1".
atomic_test4 :- atomic(6).

:- test atomic_test5 + not_fails # "[ISO] atomic/1".
atomic_test5 :- atomic(3.3).

% ---------------------------------------------------------------------------
%! ## 8.3.6 compound/1 ISOcore#p69

:- test compound_test1 + fails # "[ISO] compound/1".
compound_test1 :- compound(33.3).

:- test compound_test2 + fails # "[ISO] compound/1".
compound_test2 :- compound(-33.3).

:- test compound_test3 + not_fails # "[ISO] compound/1".
compound_test3 :- compound(-a).

:- test compound_test4 + fails # "[ISO] compound/1".
compound_test4 :- compound(_).

:- test compound_test5 + fails # "[ISO] compound/1".
compound_test5 :- compound(a).

:- test compound_test6 # "[ISO] compound/1".
compound_test6 :- compound(a(b)).

:- test compound_test7 + fails # "[ISO] compound/1".
compound_test7 :- compound([]).

:- test compound_test8 + not_fails # "[ISO] compound/1".
compound_test8 :- compound([a]).

% ---------------------------------------------------------------------------
%! ## 8.3.7 nonvar/1 ISOcore#p69

:- test nonvar_test1 + not_fails # "[ISO] nonvar/1".
nonvar_test1 :- nonvar(33.3).

:- test nonvar_test2 + not_fails # "[ISO] nonvar/1".
nonvar_test2 :- nonvar(foo).

:- test nonvar_test3(Foo) + fails # "[ISO] nonvar/1".
nonvar_test3(Foo) :- nonvar(Foo).

:- test nonvar_test4(Foo) + not_fails # "[ISO] nonvar/1".
nonvar_test4(Foo) :- foo=Foo, nonvar(Foo).

:- test nonvar_test5 + fails # "[ISO] nonvar/1".
nonvar_test5 :- nonvar(_).

:- test nonvar_test6 + not_fails # "[ISO] nonvar/1".
nonvar_test6 :- nonvar(a(b)).

% ---------------------------------------------------------------------------
%! ## 8.3.8 number/1 ISOcore#p70

:- test number_test1 + not_fails # "[ISO] number/1".
number_test1 :- number(3).

:- test number_test2 + not_fails # "[ISO] number/1".
number_test2 :- number(3.3).

:- test number_test3 + not_fails # "[ISO] number/1".
number_test3 :- number(-3).

:- test number_test4 + fails # "[ISO] number/1".
number_test4 :- number(a).

:- test number_test5(X) + fails # "[ISO] number/1".
number_test5(X) :- number(X).

% ===========================================================================
%! # 8.4 Term comparison
%! ## 8.4.1 (==)/2, (\==)/2, (@=<)/2, (@<)/2, (@>=)/2, (@>)/2 ISOcore#p70

:- test termcmp_test1 + not_fails # "[ISO] '@=<'/2".
termcmp_test1:- '@=<'(1.0, 1).

:- test termcmp_test2 + not_fails # "[ISO] '@<'/2".
termcmp_test2 :- '@<'(1.0, 1).

:- test termcmp_test3 + fails # "[ISO] '\\=='/2".
termcmp_test3 :- '\\=='(1, 1).

:- test termcmp_test4 + not_fails # "[ISO] '@=<'/2".
termcmp_test4 :- '@=<'(aardvark, zebra).

:- test termcmp_test5 + not_fails # "[ISO] '@=<'/2".
termcmp_test5 :- '@=<'(short, short).

:- test termcmp_test6 + not_fails # "[ISO] '@=<'/2".
termcmp_test6 :- '@=<'(short, shorter).

:- test termcmp_test7 + fails # "[ISO] '@>='/2".
termcmp_test7 :- '@>='(short, shorter).

:- test termcmp_test8 + fails # "[ISO] '@>'/2".
termcmp_test8 :- '@<'(foo(a, b), north(a)).

:- test termcmp_test9 + not_fails # "[ISO] '@>'/2".
termcmp_test9 :- '@>'(foo(b), foo(a)).

:- test termcmp_test10(X, Y) + not_fails # "[ISO] '@<'/2".
termcmp_test10(X, Y) :- '@<'(foo(a, X), foo(b, Y)).

:- test termcmp_test11(X, Y) # "[ISO] '@<'/2".
termcmp_test11(X, Y) :- '@<'(foo(X, a), foo(Y, b)).

:- test termcmp_test12(X, X) + not_fails # "[ISO] '@=<'/2".
termcmp_test12(X, X) :- '@=<'(X, X).

:- test termcmp_test13(X, X) + not_fails # "[ISO] '=='/2".
termcmp_test13(X, X) :- '=='(X, X).

:- test termcmp_test14(X, Y) # "[ISO] '@=<'/2".
termcmp_test14(X, Y) :- '@=<'(X, Y).

:- test termcmp_test15(X, Y) + fails # "[ISO] '=='/2".
termcmp_test15(X, Y) :- '=='(X, Y).

:- test termcmp_test16 + not_fails # "[ISO] '\=='/2".
termcmp_test16 :- \==(_, _).

:- test termcmp_test17 + fails # "[ISO] '=='/2".
termcmp_test17 :- '=='(_, _).

:- test termcmp_test18 # "[ISO] '@=<'/2".
termcmp_test18 :- '@=<'(_, _). % (order of vars by compiler)

:- test termcmp_test19(X, Y) # "[ISO] '@=<'/2".
termcmp_test19(X, Y) :- '@=<'(foo(X, a), foo(Y, b)).

% ===========================================================================
%! # 8.5 Term creation and decomposition
%! ## 8.5.1 functor/3 ISOcore#p71

:- test functor_test1 + not_fails # "[ISO] functor/3".
functor_test1 :- functor(foo(a, b, c), foo, 3).

:- test functor_test2(X, Y) => (X=foo, Y=3) # "[ISO] functor/3".
functor_test2(X, Y) :- functor(foo(a, b, c), X, Y).

:- test functor_test3(X) => (X=foo(_, _, _)) # "[ISO] functor/3".
functor_test3(X) :- functor(X, foo, 3).

:- test functor_test4(X) => (X=foo) # "[ISO] functor/3".
functor_test4(X) :- functor(X, foo, 0).

:- test functor_test5(A, B) => (A=mats, B=2) # "[ISO] functor/3".
functor_test5(A, B) :- functor(mats(A, B), A, B).

:- test functor_test6 + fails # "[ISO] functor/3".
functor_test6 :- functor(foo(a), foo, 2).

:- test functor_test7 + fails # "[ISO] functor/3".
functor_test7 :- functor(foo(a), fo, 1).

:- test functor_test8(X, Y) => (X=1, Y=0) # "[ISO] functor/3".
functor_test8(X, Y) :- functor(1, X, Y).

:- test functor_test9(X) => (X=1.1) # "[ISO] functor/3".
functor_test9(X) :- functor(X, 1.1, 0).

:- test functor_test10 + not_fails # "[ISO] functor/3".
functor_test10 :- functor([_|_], '.', 2).

:- test functor_test11 + not_fails # "[ISO] functor/3".
functor_test11 :- functor([], [], 0).

:- test functor_test12(X, Y)
    + exception(error(instantiation_error, _))
   # "[ISO] functor/3: bug()".

functor_test12(X, Y) :- functor(X, Y, 3).

:- test functor_test13(X, N)
    + exception(error(instantiation_error, _))
   # "[ISO] functor/3: bug()".

functor_test13(X, N) :- functor(X, foo, N).

:- test functor_test14(X)
    + exception(error(type_error(integer, a), _))
   # "[ISO] functor/3: bug()".

functor_test14(X) :- functor(X, foo, a).

:- test functor_test15(X)
    + exception(error(type_error(atom, 1.5), _))
   # "[ISO] functor/3: bug()".

functor_test15(X) :- functor(X, 1.5, 1).

:- test functor_test16(X)
    + exception(error(type_error(atomic, foo(a)), _))
   # "[ISO] functor/3: bug()".

functor_test16(X) :- functor(X, foo(a), 1).

:- test functor_test17(T)
   + exception(error(representation_error(max_arity), _))
   # "[ISO] functor/3: bug()".

functor_test17(T) :-
    current_prolog_flag(max_arity, A), A1 is A + 1,
    functor(T, foo, A1).

:- test functor_test18(F)
   + exception(error(domain_error(not_less_than_zero, -1), _))
   # "[ISO] functor/3: bug()".

functor_test18(T) :- functor(T, foo, -1).

% ---------------------------------------------------------------------------
%! ## 8.5.2 arg/3 ISOcore#p72

:- test arg_test1 + not_fails # "[ISO] arg/3".
arg_test1 :- arg(1, foo(a, b), a).

:- test arg_test2(X) => (X=a) # "[ISO] arg/3".
arg_test2(X) :- arg(1, foo(a, b), X).

:- test arg_test3(X) => (X=a) # "[ISO] arg/3".
arg_test3(X) :- arg(1, foo(X, b), a).

:- test arg_test4(X, Y) : (X=Y) # "[ISO] arg/3".
arg_test4(X, Y) :- arg(1, foo(X, b), Y).

:- test arg_test5 + fails # "[ISO] arg/3".
arg_test5 :- arg(1, foo(a, b), b).

:- test arg_test6 + fails # "[ISO] arg/3".
arg_test6 :- arg(0, foo(a, b), foo).

:- test arg_test7(N) + fails # "[ISO] arg/3".
arg_test7(N) :- arg(3, foo(3, 4), N).

:- test arg_test8(X) + exception(error(instantiation_error, _))
   # "[ISO] arg/3: bug()".

arg_test8(X) :- arg(X, foo(a, b), a).

:- test arg_test9(X) + exception(error(instantiation_error, _))
   # "[ISO] arg/3: bug()".

arg_test9(X) :- arg(1, X, a).

:- test arg_test10(A)
    + exception(error(type_error(compound, atom), _))
   # "[ISO] arg/3: bug()".

arg_test10(A) :- arg(0, atom, A).

:- test arg_test11(A) + exception(error(type_error(compound, 3), _))
   # "[ISO] arg/3: bug()".

arg_test11(A) :- arg(0, 3, A).

:- test arg_test12(X) # "[ISO] arg/3". % NOTE: Ciao supports rational terms

arg_test12(X) :- arg(1, foo(X), u(X)).

:- test arg_test13
   + exception(error(domain_error(not_less_than_zero, -3), _))
   # "[ISO-eddbali] arg/3: bug()".

arg_test13 :- arg(-3, foo(a, b), _).

:- test arg_test14(X)
    + exception(error(type_error(integer, a), _))
   # "[ISO-eddbali] arg/3: bug()".

arg_test14(X) :- arg(a, foo(a, b), X).

:- test arg_test15(X, Y) => (X=a, Y=b)
   # "[ISO-eddbali] arg/3".

arg_test15(X, Y) :- arg(2, foo(a, f(X, b), c), f(a, Y)).

:- test arg_test16 + exception(error(type_error(compound, 3), _))
   # "[ISO-sics] arg/3: bug()".

arg_test16 :- arg(1, 3, _).

% ---------------------------------------------------------------------------
%! ## 8.5.3 =../2 ISOcore#p73

:- test univ_test1 + not_fails
   # "[ISO] '=..'/2".

univ_test1 :- '=..'(foo(a, b), [foo, a, b]).

:- test univ_test2(X) => (X=foo(a, b))
   # "[ISO] '=..'/2".

univ_test2(X) :- '=..'(X, [foo, a, b]).

:- test univ_test3(L) => (L=[foo, a, b])
   # "[ISO] '=..'/2".

univ_test3(L) :- '=..'(foo(a, b), L).

:- test univ_test4(X, Y) => (X=a, Y=b)
   # "[ISO] '=..'/2".

univ_test4(X, Y) :- '=..'(foo(X, b), [foo, a, Y]).

:- test univ_test5 + not_fails
   # "[ISO] '=..'/2".

univ_test5 :- '=..'(1, [1]).

:- test univ_test6 + fails
   # "[ISO] '=..'/2".

univ_test6 :- '=..'(foo(a, b), [foo, b, a]).

:- test univ_test7(X, Y) + exception(error(instantiation_error, _))
   # "[ISO] '=..'/2".

univ_test7(X, Y) :- '=..'(X, Y).

:- test univ_test8(X, Y) + exception(error(instantiation_error, _))
   # "[ISO] '=..'/2".

univ_test8(X, Y) :- '=..'(X, [foo, a|Y]).

:- test univ_test9(X) + exception(error(type_error(list, [foo|bar]), _))
   # "[ISO] '=..'/2".

univ_test9(X) :- '=..'(X, [foo|bar]).

:- test univ_test10(X, Foo) + exception(error(instantiation_error, _))
   # "[ISO] '=..'/2".

univ_test10(X, Foo) :- '=..'(X, [Foo, bar]).

:- test univ_test11(X) + exception(error(type_error(atom, 3), _))
   # "[ISO] '=..'/2".

univ_test11(X) :- '=..'(X, [3, 1]).

:- test univ_test12(X) + exception(error(type_error(atom, 1.1), _))
   # "[ISO] '=..'/2".

univ_test12(X) :- '=..'(X, [1.1, foo]).

:- test univ_test13(X) + exception(error(type_error(atom, a(b)), _))
   # "[ISO] '=..'/2".

univ_test13(X) :- '=..'(X, [a(b), 1]).

:- test univ_test14(X) + exception(error(type_error(list, 4), _))
   # "[ISO] '=..'/2".

univ_test14(X) :- '=..'(X, 4).

:- test univ_test15(X)
   # "[ISO] '=..'/2". % NOTE: Ciao supports rational terms

univ_test15(X) :- '=..'(f(X), [f, u(X)]).

:- test univ_test16(X) + exception(error(type_error(atomic, f(a)), _))
   # "[ISO-sics] '=..'/2".

univ_test16(X) :- '=..'(X, [f(a)]).

:- test univ_test17(X)
    + exception(error(domain_error(non_empty_list, []), _))
   # "[ISO-sics] '=..'/2".

univ_test17(X) :- '=..'(X, []).

:- test univ_test18(X)
   + exception(error(representation_error(max_arity), _))
   # "[ISO-sics] '=..'/2".

univ_test18(X) :-
    current_prolog_flag(max_arity, A), A1 is A + 1,
    my_list_of(A1, 1, L),
    X =.. [f|L].

my_list_of(0, _, []).
my_list_of(N, A, [A|L]) :-
    N > 0,
    N1 is N-1,
    my_list_of(N1, A, L).

% ---------------------------------------------------------------------------
%! ## 8.5.4 copy_term/2 ISOcore#p74

:- test copyterm_test1(X, Y) + not_fails
   # "[ISO] copy_term/2".

copyterm_test1(X, Y) :- copy_term(X, Y).

:- test copyterm_test2(X) + not_fails
   # "[ISO] copy_term/2".

copyterm_test2(X) :- copy_term(X, 3).

:- test copyterm_test3 + not_fails
   # "[ISO] copy_term/2".

copyterm_test3 :- copy_term(_, a).

:- test copyterm_test4(X) => (X=a)
   # "[ISO] copy_term/2".

copyterm_test4(X) :- copy_term(a+X, X+b).

:- test copyterm_test5 + not_fails
   # "[ISO] copy_term/2".

copyterm_test5 :- copy_term(_, _).

:- test copyterm_test6(X, Y, A, B) => (A=B)
   # "[ISO] copy_term/2".

copyterm_test6(X, Y, A, B) :- copy_term(X+X+Y, A+B+B).

:- test copyterm_test7 + fails
   # "[ISO] copy_term/2".

copyterm_test7 :- copy_term(a, b).

:- test copyterm_test8(X) + fails
   # "[ISO] copy_term/2".

copyterm_test8(X) :- copy_term(a+X, X+b), copy_term(a+X, X+b).

:- test copyterm_test9(X, Y)
   # "[ISO] copy_term/2". % NOTE: Ciao supports rational terms

copyterm_test9(X, Y) :- copy_term(demoen(X, X), demoen(Y, f(Y))).

% ===========================================================================
%! # 8.6 Arithmetic evaluation
%! ## 8.6.1 is/2 ISOcore#p74

:- test is_test1(Result) => (Result=14.0)
   # "[ISO] arith is/2".

is_test1(Result) :- Result is 3 + 11.0.

:- test is_test2(X, Y) => (X=(1 +2), Y=9)
   # "[ISO] arith is/2".

is_test2(X, Y) :- X = 1 + 2, Y is X*3.

:- test is_test3
   # "[ISO] arith is/2".

is_test3 :- 3 is 3.

:- test is_test4 + fails
   # "[ISO] arith is/2".

is_test4 :- 3 is 3.0.

:- test is_test5 + fails
   # "[ISO] arith is/2".

is_test5 :- foo is 77.

:- test is_test6(N) + exception(error(instantiation_error, _))
   # "[ISO] arith is/2".

is_test6(N) :- 77 is N.

% ===========================================================================
%! # 8.7 Arithmetic comparison
%! ## 8.7.1 arithmetic comparison predicates ISOcore#p76

:- test arithcomp_test1 + fails
   # "[ISO] arith '=:='/2".

arithcomp_test1 :- '=:='(0, 1).

:- test arithcomp_test2
   # "[ISO] arith '=\\='/2".

arithcomp_test2 :- '=\\='(0, 1).

:- test arithcomp_test3
   # "[ISO] arith '<'/2".

arithcomp_test3 :- '<'(0, 1).

:- test arithcomp_test4 + fails
   # "[ISO] arith '>'/2".

arithcomp_test4 :- '>'(0, 1).

:- test arithcomp_test5 + fails
   # "[ISO] arith '>='/2".

arithcomp_test5 :- '>='(0, 1).

:- test arithcomp_test6
   # "[ISO] arith '=<'/2".

arithcomp_test6 :- '=<'(0, 1).

:- test arithcomp_test7
   # "[ISO] arith '=:='/2".

arithcomp_test7 :- '=:='(1.0, 1).

:- test arithcomp_test8 + fails
   # "[ISO] arith '=\='/2".

arithcomp_test8 :- '=\='(1.0, 1).

:- test arithcomp_test9 + fails
   # "[ISO] arith '<'/2".

arithcomp_test9 :- '<'(1.0, 1).

:- test arithcomp_test10 + fails
   # "[ISO] arith '>'/2".

arithcomp_test10 :- '>'(1.0, 1).

:- test arithcomp_test11
   # "[ISO] arith '>='/2".

arithcomp_test11 :- '>='(1.0, 1).

:- test arithcomp_test12
   # "[ISO] arith '=<'/2".

arithcomp_test12 :- '=<'(1.0, 1).

:- test arithcomp_test13
   # "[ISO] arith '=:='/2".

arithcomp_test13 :- '=:='(3*2, 7 -1).

:- test arithcomp_test14 + fails
   # "[ISO] arith '=\\='/2".

arithcomp_test14 :- '=\\='(3*2, 7 -1).

:- test arithcomp_test15 + fails
   # "[ISO] arith '<'/2".

arithcomp_test15 :- '<'(3*2, 7 -1).

:- test arithcomp_test16 + fails
   # "[ISO] arith '>'/2".

arithcomp_test16 :- '>'(3*2, 7 -1).

:- test arithcomp_test17
   # "[ISO] arith '>='/2".

arithcomp_test17 :- '>='(3*2, 7 -1).

:- test arithcomp_test18
   # "[ISO] arith '=<'/2".

arithcomp_test18 :- '=<'(3*2, 7 -1).

:- test arithcomp_test19(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '=:='/2".

arithcomp_test19(X) :- '=:='(X, 5).

:- test arithcomp_test20(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith =\\=/2".

arithcomp_test20(X) :- X =\= 5.

:- test arithcomp_test21(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '<'/2".

arithcomp_test21(X) :- '<'(X, 5).

:- test arithcomp_test22(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '>'/2".

arithcomp_test22(X) :- '>'(X, 5).

:- test arithcomp_test23(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '>='/2".

arithcomp_test23(X) :- '>='(X, 5).

:- test arithcomp_test24(X)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '=<'/2".

arithcomp_test24(X) :- '=<'(X, 5).

% ===========================================================================
%! # 8.8 Clause retrieval and information
%! ## 8.8.1 clause/2 ISOcore#p77

% (clauses for clause tests and current_predicate)

:- dynamic(p_clause__cat/0).
p_clause__cat.

:- dynamic(p_clause__dog/0).
p_clause__dog :- true.

p_clause__elk(X) :- moose(X).

moose(_) :- fail.

:- dynamic(p_clause__legs/2).
p_clause__legs(A, 6) :- p_clause__insect(A).
p_clause__legs(A, 7) :- A, call(A).

:- dynamic(p_clause__insect/1).
p_clause__insect(ant).
p_clause__insect(bee).

:- test clause_test1
   + not_fails
   # "[ISO] clause/2".
clause_test1 :- clause(p_clause__cat, true).

:- test clause_test2
   + not_fails
   # "[ISO] clause/2".
clause_test2 :- clause(p_clause__dog, true).

:- test clause_test3(I, Body) => (Body=p_clause__insect(I))
   # "[ISO] clause/2".
clause_test3(I, Body) :- clause(p_clause__legs(I, 6), Body).

:- test clause_test4(C, Body) => (Body=(call(C), call(C)))
   # "[ISO] clause/2".
clause_test4(C, Body) :- clause(p_clause__legs(C, 7), Body).

:- test clause_test5(Result) => (Result=[[ant, true], [bee, true]])
   # "[ISO] clause/2".
clause_test5(Result) :- findall([I, T], clause(p_clause__insect(I), T), Result).

:- test clause_test6(Body)
   + (fails,
      no_exception)
   # "[ISO] clause/2".
clause_test6(Body) :- clause(x, Body). % TODO:[JF] note that 'x' is not defined

% TODO:[JF] fix, clause/2 should throw exception
:- test clause_test7(B) + exception(error(instantation_error, _))
   # "[ISO] clause/2: bug()".
clause_test7(B) :- clause(_, B).

% TODO:[JF] fix, clause/2 should throw exception
:- test clause_test8(X) + exception(error(type_error(callable, 4), _))
   # "[ISO] clause/2: bug()".
clause_test8(X) :- clause(4, X).

% TODO:[JF] fix, clause/2 should throw exception
:- test clause_test9(N, Body)
   + exception(error(permission_error(access, private_procedure, p_clause__elk/1), _))
   # "[ISO] clause/2: bug()".
clause_test9(N, Body) :- clause(p_clause__elk(N), Body).

% TODO:[JF] fix, clause/2 should throw exception
:- test clause_test10(Body)
   + exception(error(permission_error(access, private_procedure, atom/1), _))
   # "[ISO] clause/2: bug()".
clause_test10(Body) :- clause(atom(_), Body).

% TODO:[JF] creates cyclic term; missing check
:- test clause_test11 + not_fails
   # "[ISO] clause/2".
clause_test11 :- clause(p_clause__legs(A, 6), p_clause__insect(f(A))).

% TODO:[JF] fix, clause/2 should throw exception
:- test clause_test12
   + exception(error(type_error(callable, 5), _))
   # "[ISO-eddbali] clause/2: bug()".
clause_test12 :- clause(f(_), 5).

% f(_) :- fail. % TODO:[JF] it should not be needed (for this error)

% ---------------------------------------------------------------------------
%! ## 8.8.2 current_predicate/1 ISOcore#p78

:- test currentpredicate_test1
   # "[ISO] current_predicate/1".
currentpredicate_test1 :- current_predicate(p_clause__dog/0).

:- test currentpredicate_test2 + fails
   # "[ISO] current_predicate/1".
currentpredicate_test2 :- current_predicate(current_predicate/0).

:- test currentpredicate_test3(Arity) => (Arity=1)
   # "[ISO] current_predicate/1".
currentpredicate_test3(Arity) :- current_predicate(p_clause__elk/Arity).

:- test currentpredicate_test4(A) + fails
   # "[ISO] current_predicate/1".
currentpredicate_test4(A) :- current_predicate(p_current__foo/A).

% (this predicate must be missing for this test)
% p_current__foo.

:- test currentpredicate_test5(Result)
   => (sublist([p_clause__elk], Result), sublist([p_clause__insect], Result))
   # "[ISO] current_predicate/1".
currentpredicate_test5(Result) :-
    findall(Name, current_predicate(Name/1), Result).

% TODO:[JF] throw exception
:- test currentpredicate_test6
   + exception(error(type_error(predicate_indicator, 4), _))
   # "[ISO] current_predicate/1: bug()".
currentpredicate_test6 :- current_predicate(4).

% TODO:[JF] throw exception
:- test currentpredicate_test7(X) : (X=p_clause__dog)
   + exception(error(type_error(predicate_indicator, p_clause__dog), _))
   # "[ISO-eddbali] current_predicate/1: bug()".
currentpredicate_test7(X) :- current_predicate(X).

% TODO:[JF] throw exception
:- test currentpredicate_test8(X) : (X=0/p_clause__dog)
   + exception(error(type_error(predicate_indicator, 0/p_clause__dog), _))
   # "[ISO-eddbali] current_predicate/1: bug()".
currentpredicate_test8(X) :- current_predicate(X).

:- test currentpredicate_test9(X, Result)
   => (sublist([p_clause__cat/0, p_clause__dog/0, p_clause__elk/1, p_clause__insect/1, p_clause__legs/2], Result))
   # "[ISO-eddbali] current_predicate/1".
currentpredicate_test9(X, Result) :- findall(X, current_predicate(X), Result).

% ===========================================================================
%! # 8.9 Clause creation and destruction

%! ## 8.9.1 asserta/1 ISOcore#p79

% TODO:[JF] Ciao will complain when asserting clauses with animal/1 or
%   bird/1 in its body, if those predicates are not defined. Is this
%   behaviour compatible with ISO?
animal(_) :- fail.
bird(_) :- fail.

:- dynamic(p_asserta1__legs/2).
p_asserta1__legs(A, 6) :- p_asserta__insect(A).

:- dynamic(p_asserta2__legs/2).
p_asserta2__legs(A, 6) :- p_asserta__insect(A).

:- dynamic(p_asserta__insect/1).
p_asserta__insect(ant).
p_asserta__insect(bee).

% TODO:[JF] missing check that predicate is modified
:- test asserta_test1
   # "[ISO] asserta/1".
asserta_test1 :- asserta(p_asserta1__legs(octopus, 8)).

% TODO:[JF] missing check that predicate is modified
:- test asserta_test2
   # "[ISO] asserta/1".
asserta_test2 :- asserta((p_asserta2__legs(A, 4) :- animal(A))).

% TODO:[JF] since predicate does not exist, it is made dynamic
:- test asserta_test3
   # "[ISO] asserta/1: bug()".
asserta_test3 :- C = (p_asserta3__foo(A) :- A, call(A)), asserta(C). % TODO:[JF] tmp var to avoid static error

:- test asserta_test4 + exception(error(instantiation_error, _))
   # "[ISO] asserta/1".
asserta_test4 :- asserta(_).

:- test asserta_test5 + exception(error(type_error(callable, 4), _))
   # "[ISO] asserta/1".
asserta_test5 :- asserta(4).

:- test asserta_test6 + exception(error(type_error(callable, 4), _))
   # "[ISO] asserta/1: bug()".
asserta_test6 :- C = (p_asserta6__foo(_) :- 4), asserta(C). % TODO:[JF] tmp var to avoid static error

:- test asserta_test7
   + exception(error(permission_error(modify, static_procedure, _), _))
   # "[ISO] asserta/1".
asserta_test7 :- asserta((atom(_) :- true)).

% TODO:[JF] missing asserta_test8

% ---------------------------------------------------------------------------
%! ## 8.9.2 assertz/1 ISOcore#p80

:- dynamic(p_assertz1__legs/2).
p_assertz1__legs(A, 4) :- animal(A).
p_assertz1__legs(octopus, 8).
p_assertz1__legs(A, 6) :- p_assertz__insect(A).

:- dynamic(p_assertz2__legs/2).
p_assertz2__legs(A, 4) :- animal(A).
p_assertz2__legs(octopus, 8).
p_assertz2__legs(A, 6) :- p_assertz__insect(A).

:- dynamic(p_assertz__insect/1).
p_assertz__insect(ant).
p_assertz__insect(bee).

% TODO:[JF] missing check that predicate is modified
:- test assertz_test1
   # "[ISO] assertz/1".
assertz_test1 :- assertz(p_assertz1__legs(spider, 8)).

% TODO:[JF] missing check that predicate is modified
:- test assertz_test2
   # "[ISO] assertz/1".
assertz_test2 :- assertz((p_assertz2__legs(B, 2) :- bird(B))).

% TODO:[JF] missing check that predicate is modified
:- test assertz_test3
   # "[ISO] assertz/1: bug()".
assertz_test3 :- C = (p_assertz3__foo(X) :- X -> call(X)), assertz(C). % TODO:[JF] tmp var to avoid static error

:- test assertz_test4 + exception(error(instantiation_error, _))
   # "[ISO] assertz/1".
assertz_test4 :- assertz(_).

:- test assertz_test5 + exception(error(type_error(callable, 4), _))
   # "[ISO] assertz/1".
assertz_test5 :- assertz(4).

:- test assertz_test6 + exception(error(type_error(callable, 4), _))
   # "[ISO] assertz/1: bug()".
assertz_test6 :- C = (p_assertz6__foo(_) :- 4), assertz(C). % TODO:[JF] tmp var to avoid static error

:- test assertz_test7
   + exception(error(permission_error(modify, static_procedure, _), _))
   # "[ISO] assertz/1".
assertz_test7 :- assertz((atom(_) :- true)).

% ---------------------------------------------------------------------------
%! ## 8.9.3 retract/1 ISOcore#p81

:- dynamic(p_retract1__legs/2).
p_retract1__legs(A, 4) :- animal(A).
p_retract1__legs(octopus, 8).
p_retract1__legs(A, 6) :- p_retract__insect(A).
p_retract1__legs(spider, 8).
p_retract1__legs(B, 2) :- bird(B).

:- dynamic(p_retract2__legs/2).
p_retract2__legs(A, 4) :- animal(A).
p_retract2__legs(A, 6) :- p_retract__insect(A).
p_retract2__legs(spider, 8).
p_retract2__legs(B, 2) :- bird(B).

:- dynamic(p_retract3__legs/2).
p_retract3__legs(A, 4) :- animal(A).
p_retract3__legs(A, 6) :- p_retract__insect(A).
p_retract3__legs(spider, 8).
p_retract3__legs(B, 2) :- bird(B).

:- dynamic(p_retract4__legs/2).
p_retract4__legs(A, 4) :- animal(A).
p_retract4__legs(A, 6) :- p_retract__insect(A).
p_retract4__legs(spider, 8).

:- dynamic(p_retract5__legs/2).
% p_retract5__legs(_, _) :- fail.

:- dynamic(p_retract__insect/1).
p_retract__insect(ant).
p_retract__insect(bee).

:- dynamic(p_retract6__insect/1).
p_retract6__insect(ant).
p_retract6__insect(bee).

:- dynamic(p_retract7__foo/1).
p_retract7__foo(X) :- call(X), call(X).
p_retract7__foo(X) :- call(X) -> call(X).

:- dynamic(p_retract8__foo/1).
p_retract8__foo(X) :- call(X), call(X).
p_retract8__foo(X) :- call(X) -> call(X).

% TODO:[JF] missing check that predicate is modified
:- test retract_test1
   # "[ISO] retract/1".
retract_test1 :- retract(p_retract1__legs(octopus, 8)).

:- test retract_test2 + fails
   # "[ISO] retract/1".
retract_test2 :- retract(p_retract2__legs(spider, 6)).

% TODO:[JF] missing check that predicate is modified
:- test retract_test3(X, T) => (T=bird(X))
   + not_fails
   # "[ISO] retract/1".
retract_test3(X, T) :- retract((p_retract3__legs(X, 2) :-T)).

% TODO:[JF] missing check that predicate is modified
:- test retract_test4(Result)
   => (Result=[[_, 4, animal(_)],
               [_, 6, p_retract__insect(_)],
               [spider, 8, true]])
   # "[ISO] retract/1".
retract_test4(Result) :-
    findall([X, Y, Z], retract((p_retract4__legs(X, Y) :- Z)), Result).

:- test retract_test5(X, Y, Z) + fails
   # "[ISO] retract/1".
retract_test5(X, Y, Z) :- retract((p_retract5__legs(X, Y) :- Z)).

% TODO:[JF] missing check that predicate is modified
% TODO:[JF] dynamic_clause has problems with "logical update view"
:- test retract_test6(Result) => (Result=[ant])
   + user_output("antbee")
   # "[ISO] retract/1: bug()".

retract_test6(Result) :-
    findall(I, (retract(p_retract6__insect(I)),
                write(I),
                retract(p_retract6__insect(bee))),
	    Result).

% TODO:[JF] missing check that predicate is modified
:- test retract_test7(A)
   # "[ISO] retract/1: bug()".
retract_test7(A) :- retract((p_retract7__foo(A) :- A, call(A))). % TODO:[JF] this creates a cyclic term! A=call(A)

% TODO:[JF] missing check that predicate is modified
:- test retract_test8(A, B, C) => (A=call(C), B=call(C))
   + not_fails
   # "[ISO] retract/1".
retract_test8(A, B, C) :- retract((p_retract8__foo(C) :- A -> B)).

% TODO:[JF] see "check_head(V, _, Spec, _) :- var(V), !," in dynamic_clauses_rt
:- test retract_test9(X, Y) + exception(error(instantiation_error, _))
   # "[ISO] retract/1: bug()".
retract_test9(X, Y) :- retract((X :- in_eec(Y))).

:- test retract_test10(X)
   + exception(error(type_error(callable, 4), _))
   # "[ISO] retract/1".
retract_test10(X) :- retract((4 :- X)).

:- test retract_test11(X)
   + exception(error(permission_error(modify, static_procedure, _), _))
   # "[ISO] retract/1".
retract_test11(X) :- retract((atom(X) :- X == '[]')).

% ---------------------------------------------------------------------------
%! ## 8.9.4 abolish/1 ISOcore#p82

% TODO:[JF] Tests marked with "dynamic program change" modify the
%   dynamic database as a side-effect. The result should be correct
%   fine as long as tests are executed only once per use_module.

% NOTE: using 'undef__' for predicates undefined on purpose

% TODO:[JF] make sure that it works (see '$meta_exp'(spec, undef__foo/2, X)).
:- test abolish_test1
   + not_fails
   # "[ISO] abolish/1: bug()".
abolish_test1 :- G=abolish(undef__foo1/2), call(G), throw(iso_requires_no_warning). % TODO:[JF] it should succeed, silently, even if the predicate do not exists

% TODO:[JF] fix
:- test abolish_test2
   + exception(error(instantiation_error, _))
   # "[ISO] abolish/1: bug()".
abolish_test2 :- abolish(undef__foo2/_).

% TODO:[JF] fix
:- test abolish_test3
   + exception(error(type_error(predicate_indicator, undef__foo3), _))
   # "[ISO] abolish/1: bug()".
abolish_test3 :- abolish(undef__foo3).

% TODO:[JF] fix
:- test abolish_test4
   + exception(error(type_error(predicate_indicator, undef__foo4(_)), _))
   # "[ISO] abolish/1: bug()".
abolish_test4 :- abolish(undef__foo4(_)).

% TODO:[JF] abolish_test5 is dangerous, the same is tested with abolish_test9
% :- test abolish_test5
%    + exception(error(permission_error(modify,static_procedure,abolish/1), _))
%    # "[ISO] abolish/1: bug()".
% abolish_test5 :- X=abolish/1, abolish(X).

% TODO:[JF] dynamic program change
:- test abolish_test6
   + not_fails
   # "[ISO-eddbali] abolish/1".
abolish_test6 :- abolish(p_abolish__foo/1).

:- dynamic(p_abolish__foo/1).
p_abolish__foo(X) :- call(X), call(X).
p_abolish__foo(X) :- call(X) -> call(X).

% TODO:[JF] dynamic program change
% (retrieve all solutions even if predicate is abolished)
:- test abolish_test7(Result)
   => (Result=[ant, bee])
   # "[ISO-eddbali] abolish/1".
abolish_test7(Result) :-
    findall(X, (p_abolish__insect(X), abolish(p_abolish__insect/1)), Result).

:- dynamic(p_abolish__insect/1).
p_abolish__insect(ant).
p_abolish__insect(bee).

% TODO:[JF] fix
:- test abolish_test8 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test8 :- abolish(p_abolish__foo/_).

% TODO:[JF] some systems allow abolishing static procedures and some
%   of our code need it. Add another mechanism if needed? Marked as
%   'wontfix' at this moment.
:- test abolish_test9
   + exception(error(permission_error(modify, static_procedure, p_abolish__bar/1), _))
   # "[ISO-eddbali] abolish/1: bug(wontfix)".

abolish_test9 :- abolish(p_abolish__bar/1).

% Some static pred
p_abolish__bar(_) :- true.

% TODO:[JF] fix
:- test abolish_test10
   + exception(error(type_error(integer, a), _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test10 :- abolish(p_abolish__foo/a).

% TODO:[JF] fix
:- test abolish_test11
   + exception(error(domain_error(not_less_than_zero, -1), _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test11 :- abolish(p_abolish__foo /(-1)).

% TODO:[JF] fix
:- test abolish_test12
   + exception(error(representation_error(max_arity), _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test12 :-
    current_prolog_flag(max_arity, A), A1 is A + 1,
    abolish(p_abolish__foo/A1).

% TODO:[JF] fix
:- test abolish_test13
   + exception(error(type_error(atom, 5), _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test13 :- abolish(5/a).

% TODO:[JF] fix
% (similar to abolish_test3, but functor name exists)
:- test abolish_test14            
   + exception(error(type_error(predicate_indicator, p_abolish__insect2), _))
   # "[ISO-eddbali] abolish/1: bug()".
abolish_test14 :- abolish(p_abolish__insect2).

:- dynamic(p_abolish__insect2/1).
p_abolish__insect2(ant).
p_abolish__insect2(bee).

% ===========================================================================
%! # 8.10 All solutions
%! ## 8.10.1 findall/3 ISOcore#p83

:- test findall_test1(Result) => (Result=[1, 2])
   # "[ISO] findall/3".
findall_test1(Result) :- findall(X, (X=1;X=2), Result).

:- test findall_test2(Result, Y) => (Result=[1+_])
   # "[ISO] findall/3".
findall_test2(Result, Y) :- findall(X+Y, (X=1), Result).

:- test findall_test3(Result, X) => (Result=[])
   # "[ISO] findall/3".
findall_test3(Result, X) :- findall(X, fail, Result).

:- test findall_test4(Result) => (Result=[1, 1])
   # "[ISO] findall/3".
findall_test4(Result) :- findall(X, (X=1;X=1), Result).

:- test findall_test5 + fails
   # "[ISO] findall/3".
findall_test5 :- findall(X, (X=2;X=1), [1, 2]).

:- test findall_test6(X, Y) => (X=1, Y=2)
   # "[ISO] findall/3".
findall_test6(X, Y) :- findall(X, (X=1;X=2), [X, Y]).

:- test findall_test7(X, Goal, Result)
   + exception(error(instantiation_error, _))
   # "[ISO] findall/3".
findall_test7(X, Goal, Result) :- findall(X, Goal, Result).

:- test findall_test8(X, Result)
   + exception(error(type_error(callable, 4), _))
   # "[ISO] findall/3".
findall_test8(X, Result) :- findall(X, 4, Result).

% TODO:[JF] typecheck list in findall/3 (only in iso compat)
:- test findall_test9
   + exception(error(type_error(list, [A|1]), _))
   # "[ISO-sics] findall/3: bug()".
findall_test9 :- findall(X, (X=1), [_|1]).

% ---------------------------------------------------------------------------
%! ## 8.10.2 bagof/3 ISOcore#p84

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

:- test bagof_test1(Result) => (Result=[1, 2])
   # "[ISO] bagof/3".
bagof_test1(Result) :- bagof(X, (X=1;X=2), Result).

:- test bagof_test2(X) => (X=[1, 2])
   # "[ISO] bagof/3".
bagof_test2(X) :- bagof(X, (X=1;X=2), X).

:- test bagof_test3(Result, Y, Z) => (Result=[Y, Z])
   # "[ISO] bagof/3".
bagof_test3(Result, Y, Z) :- bagof(X, (X=Y;X=Z), Result).

:- test bagof_test4(Result, X) + fails
   # "[ISO] bagof/3".
bagof_test4(Result, X) :- bagof(X, fail, Result).

:- test bagof_test5(Result) => (Result=[[[1], 1], [[1], 2]])
   # "[ISO] bagof/3".
bagof_test5(Result) :- findall([L, Y], bagof(1, (Y=1;Y=2), L), Result).

:- test bagof_test6(Result) => (Result=[f(a, _), f(_, b)])
   # "[ISO] bagof/3".
bagof_test6(Result) :- bagof(f(X, Y), (X=a;Y=b), Result).

:- test bagof_test7(Result) => (Result=[1, 2])
   # "[ISO] bagof/3".
bagof_test7(Result) :- bagof(X, Y^((X=1, Y=1);(X=2, Y=2)), Result).

:- test bagof_test8(Result)
   => (Result=[1, _, 2])
   # "[ISO] bagof/3".
bagof_test8(Result) :- bagof(X, Y^((X=1;Y=1);(X=2, Y=2)), Result).

:- test bagof_test9(Result)
   => (Result=[1, _, 3])
   # "[ISO] bagof/3".
bagof_test9(Result) :- bagof(X, (Y^(X=1;Y=2) ;X=3), Result).

% Note: results of this test are represented as list of sol/? terms,
%   capturing both the solution and relevant bindings, so that we can
%   check the results consistently (due to variable renamings)
:- test bagof_test10(Sols) =>
    ( Result=[sol(1,_,[_]), sol(Y2,Z2,[Y2,Z2])]
    ; Result=[sol(Y1,Z1,[Y1,Z1]), sol(1,_,[_])]
    ) # "[ISO] bagof/3".
bagof_test10(Sols) :-
    findall(sol(Y,Z,L), bagof_test10_(Y,Z,L), Sols).

bagof_test10_(Y,Z,L) :-
    bagof(X, (X=Y;X=Z;Y=1), L).

:- test bagof_test11(Result, Y) => (Result=[1, 2], Y=f(_))
   # "[ISO] bagof/3".
bagof_test11(Result, Y) :- bagof(X, a(X, Y), Result).

:- test bagof_test12(Result, Y) => (Result=[[[1, 1, 2], 1], [[1, 2, 2], 2]])
   # "[ISO] bagof/3".
bagof_test12(Result, Y) :- findall([L, Y], bagof(X, b(X, Y), L), Result).

:- test bagof_test13(Result, X, Y, Z)
   + exception(error(instantiation_error, _))
   # "[ISO] bagof/3".
bagof_test13(Result, X, Y, Z) :- bagof(X, Y^Z, Result).

:- test bagof_test14(Result, X)
   + exception(error(type_error(callable, 1), _))
   # "[ISO] bagof/3".
bagof_test14(Result, X) :- bagof(X, 1, Result).

% ---------------------------------------------------------------------------
%! ## 8.10.3 setof/3 ISOcore#p85

d(1, 1).
d(1, 2).
d(1, 1).
d(2, 2).
d(2, 1).
d(2, 2).

:- test setof_test1(Result) => (Result=[1, 2])
   # "[ISO] setof/3".
setof_test1(Result) :- setof(X, (X=1;X=2), Result).

:- test setof_test2(X) => (X=[1, 2])
   # "[ISO] setof/3".
setof_test2(X) :- setof(X, (X=1;X=2), X).

:- test setof_test3(Result) => (Result=[1, 2])
   # "[ISO] setof/3".
setof_test3(Result) :- setof(X, (X=2;X=1), Result).

:- test setof_test4(Result) => (Result=[2])
   # "[ISO] setof/3".
setof_test4(Result) :- setof(X, (X=2;X=2), Result).

:- test setof_test5(Result, Y, Z) => (Result=[Y, Z];Result=[Z, Y])
   # "[ISO] setof/3".
setof_test5(Result, Y, Z) :- setof(X, (X=Y;X=Z), Result).

:- test setof_test6(Result, X) + fails
   # "[ISO] setof/3".
setof_test6(Result, X) :- setof(X, fail, Result).

:- test setof_test7(Result) => (Result=[[[1], 1], [[1], 2]])
   # "[ISO] setof/3".
setof_test7(Result) :- findall([L, Y], setof(1, (Y=2;Y=1), L), Result).

:- test setof_test8(Result) => (Result=[f(_, b), f(a, _)])
   # "[ISO] setof/3".
setof_test8(Result) :- setof(f(X, Y), (X=a;Y=b), Result).

:- test setof_test9(Result) => (Result=[1, 2])
   # "[ISO] setof/3".
setof_test9(Result) :- setof(X, Y^((X=1, Y=1);(X=2, Y=2)), Result).

:- test setof_test10(Result) => (Result=[_, 1, 2])
   # "[ISO] setof/3".
setof_test10(Result) :- setof(X, Y^((X=1;Y=1);(X=2, Y=2)), Result).

:- test setof_test11(Result, Y) => (Result=[_, 1, 3])
   # "[ISO] setof/3".
setof_test11(Result, Y) :- setof(X, (Y^(X=1;Y=2) ;X=3), Result).

% Note: results of this test are represented as list of sol/? terms,
%   capturing both the solution and relevant bindings, so that we can
%   check the results consistently (due to variable renamings)
:- test setof_test12(Sols) =>
   ( Result = [sol(1,_,[_]),sol(Y2,Z2,[Y2,Z2])]
   ; Result = [sol(Y1,Z1,[Y1,Z1]),sol(1,_,[_])]
   ) # "[ISO] setof/3".
setof_test12(Sols) :-
    findall(sol(Y,Z,S), setof_test12_(Y,Z,S), Sols).

setof_test12_(Y, Z, S) :-
    setof(X, (X=Y;X=Z;Y=1), S).

:- test setof_test13(Result, Y) => (Result=[1, 2], Y=f(_))
   # "[ISO] setof/3".
setof_test13(Result, Y) :- setof(X, a(X, Y), Result).

:- test setof_test14(Y, Z, Result)
   => (Result=[f(Y, b), f(Z, c)];Result=[f(Z, c), f(Y, b)])
   # "[ISO] setof/3".
setof_test14(Y, Z, Result) :- setof(X, member(X, [f(Y, b), f(Z, c)]), Result).

:- test setof_test15(Y, Z) + fails
   # "[ISO] setof/3".
setof_test15(Y, Z) :-
    setof(X, member(X, [f(Y, b), f(Z, c)]), [f(a, c), f(a, b)]).

:- test setof_test16(Y, Z) => (Y=a, Z=a)
   # "[ISO] setof/3".
setof_test16(Y, Z) :-
    setof(X, member(X, [f(b, Y), f(c, Z)]), [f(b, a), f(c, a)]).

:- test setof_test17(Y, Z, Result)
   => (Result=[Y, Z, f(Y), f(Z)] ; Result=[Z, Y, f(Z), f(Y)])
   # "[ISO] setof/3".
setof_test17(Y, Z, Result) :- setof(X, member(X, [Z, Y, f(Y), f(Z)]), Result).

:- test setof_test18(Y, Z) => ((Y=a, Z=b);(Y=b, Z=a))
   # "[ISO] setof/3".
setof_test18(Y, Z) :-
    setof(X, member(X, [Z, Y, f(Y), f(Z)]), [a, b, f(a), f(b)]).

:- test setof_test19(Y, Z) + fails
   # "[ISO] setof/3".
setof_test19(Y, Z) :-
    setof(X, member(X, [Z, Y, f(Y), f(Z)]), [a, b, f(b), f(a)]).

:- test setof_test20(Y, Z)
   # "[ISO] setof/3".
setof_test20(Y, Z) :-
    setof(X, (exists(Y, Z) ^member(X, [Z, Y, f(Y), f(Z)])), [a, b, f(b), f(a)]).

:- test setof_test21(Y, Result)
   => (Result=[[[1, 2], 1], [[1, 2], 2]])
   # "[ISO] setof/3".
setof_test21(Y, Result) :- findall([L, Y], setof(X, b(X, Y), L), Result).

:- test setof_test22(Y, Result) => (Result=[1-[1, 2], 2-[1, 2]])
   # "[ISO] setof/3".
setof_test22(Y, Result) :- setof(X-Z, Y^setof(Y, b(X, Y), Z), Result).

:- test setof_test23(Y, Result) => (Result=[1-[1, 2], 2-[1, 2]], Y=_)
   # "[ISO] setof/3".
setof_test23(Y, Result) :- setof(X-Z, setof(Y, b(X, Y), Z), Result).

:- test setof_test24(Y, Result) => (Result=[1-[1, 2, 1], 2-[2, 1, 2]], Y=_)
   # "[ISO] setof/3".
setof_test24(Y, Result) :- setof(X-Z, bagof(Y, d(X, Y), Z), Result).

:- test setof_test25(Result) : (Result=[f(g(Z), Z)])
   # "[ISO-eddbali] setof/3".
setof_test25(Result) :- setof(f(X, Y), X=Y, Result).

:- test setof_test26(Result)
   + exception(error(type_error(callable, 4), _))
   # "[ISO-eddbali] setof/3".
setof_test26(Result) :- setof(X, X^(true;4), Result).

:- test setof_test27(Result)
   + exception(error(type_error(callable, 1), _))
   # "[ISO-sics] setof/3".
setof_test27(Result) :- setof(_X, Y^Y^1, Result).

:- test setof_test28(A) => (A=[])
   # "[ISO-sics] setof/3".
setof_test28(A) :- setof(X, X=1, [1|A]).

% TODO:[JF] typecheck list in setof/3 (only in iso compat)
:- test setof_test29
   + exception(error(type_error(list, [A|1]), _))
   # "[ISO-sics] setof/3: bug()".
setof_test29 :- setof(X, X=1, [_|1]).

%! # 8.11 Stream selection and control

% NOTE: Current issues in Ciao:
%
%  - current_input/1 and current_output/1 does not check that stream exists
%    ?- open('/tmp/foo', read, S), close(S), catch(current_input(S), E, true).

%! ## 8.11.1 current_input/1 ISOcore#p86

:- test currentinput_test1(S)
   # "[ISO-sics] current_input/1".
currentinput_test1(S) :- current_input(S).

:- test currentinput_test2
   + exception(error(domain_error(stream, foo), _))
   # "[ISO-sics] current_input/1".
currentinput_test2 :- current_input(foo).

:- test currentinput_test3(S) + 
   (setup(curr_out(S)),
    fails)
   # "[ISO-sics] current_input/1".
currentinput_test3(S) :- current_input(S).

% TODO:[JF] check behaviour of other Prologs (gprolog, ciao, scryer: no exception;
%   swipl: existence error, trealla: domain error)
:- test currentinput_test4(S2) 
   + (setup(closed_instream(S2)),
      exception(error(domain_error(stream, S2), _)))
   # "[ISO-sics] current_input/1: bug()".
currentinput_test4(S2) :- current_input(S2).

:- test currentinput_test5(S)
   + (not_fails,
      setup(curr_in(S)))
   # "[ISO-sics] current_input/1".
currentinput_test5(S) :- current_input(S).

%! ## 8.11.2 current_output/1 ISOcore#p86

:- test currentoutput_test1(S)
   # "[ISO-sics] current_output/1".
currentoutput_test1(S) :- current_output(S).

:- test currentoutput_test2
   + exception(error(domain_error(stream, foo), _))
   # "[ISO-sics] current_output/1".
currentoutput_test2 :- current_output(foo).

:- test currentoutput_test3(S)
   + (fails,
      setup(curr_in(S)))
   # "[ISO-sics] current_output/1".
currentoutput_test3(S) :- current_output(S).

% TODO:[JF] check behaviour of other Prologs (gprolog, ciao, scryer: no exception;
%   swipl: existence error, trealla: domain error)
:- test currentoutput_test4(S)
   + (setup(closed_outstream(S)),
      exception(error(domain_error(stream, S), _)))
   # "[ISO-sics] current_output/1: bug()".
currentoutput_test4(S) :- current_output(S).

:- test currentoutput_test5(S)
   + (not_fails,
      setup(curr_out(S)))
   # "[ISO-sics] current_output/1".
currentoutput_test5(S) :- current_output(S).

%! ## 8.11.3 set_input/1 ISOcore#p87

:- test setinput_test1(S)
   + (not_fails,
      setup(curr_in(S)))
   # "[ISO-sics] set_input/1".
setinput_test1(S) :- set_input(S).

:- test setinput_test2
   + exception(error(instantiation_error, _))
   # "[ISO-sics] set_input/1".
setinput_test2 :- set_input(_).

% TODO:[JF] both acceptable in ISO % TODO: unittest do not allow alternative here, fix
:- test setinput_test3
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] set_input/1".
setinput_test3 :- set_input(foo).

:- test setinput_test4(S1)
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] set_input/1".
setinput_test4(S1) :- set_input(S1).

:- test setinput_test5(S)
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] set_input/1".
setinput_test5(S) :- set_input(S).

% ---------------------------------------------------------------------------
%! ## 8.11.4 set_output/1 ISOcore#p87

% NOTE: Current issues in Ciao:
%
%  - reposition(true) is not supported in open/4

:- test setoutput_test1(S)
   + setup(curr_out(S))
   # "[ISO-sics] set_output/1".
setoutput_test1(S) :- set_output(S).

:- test setoutput_test2
   + exception(error(instantiation_error, _))
   # "[ISO-sics] set_output/1".
setoutput_test2 :- set_output(_).

% TODO:[JF] both acceptable in ISO % TODO: unittest do not allow alternative here, fix
:- test setoutput_test3
   + exception(error(existence_error(stream, foo), _))
   % + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] set_output/1".
setoutput_test3 :- set_output(foo).

:- test setoutput_test4(S)
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S_or_a), _)))
   # "[ISO-sics] set_output/1".
setoutput_test4(S) :- set_output(S).

:- test setoutput_test5(S)
   + (setup(curr_in(S)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] set_output/1".
setoutput_test5(S) :- set_output(S).

%! ## 8.11.5 open/3, open/4 ISOcore#p88

:- test open_test1
   + not_fails
   # "[ISO] open/4".

open_test1 :-
    wr_f('/tmp/roger_data', txt('')),
    open('/tmp/roger_data', read, Stream, [type(binary)]),
    ( at_end_of_stream(Stream) -> OK = yes ; OK = no ),
    close(Stream),
    OK = yes.

:- test open_test2
   + not_fails
   # "[ISO] open/4".

open_test2 :-
    open('/tmp/scowen', write, S, [alias(editor)]),
    ( stream_property(S, alias(editor)) -> OK = yes ; OK = no ),
    close(S),
    OK = yes.

:- test open_test3
   + not_fails
   # "[ISO] open/4".

open_test3 :-
    wr_f('/tmp/dave', txt('foo.')),
    open('/tmp/dave', read, Stream, [type(text)]),
    ( read(Stream, foo), at_end_of_stream(Stream) -> OK = yes ; OK = no ),
    close(Stream),
    OK = yes.

:- test open_test4 + exception(error(instantiation_error, _))
   # "[ISO-sics] open/3".

open_test4 :- open(_, read, _).

:- test open_test5
   + exception(error(instantiation_error, _))
   # "[ISO-sics] open/3".

open_test5 :- open('/tmp/f', _, _).

:- test open_test6
   + exception(error(instantiation_error, _))
   # "[ISO-sics] open/4".

open_test6 :- open('/tmp/f', write, _, _).

:- test open_test7
   + exception(error(instantiation_error, _))
   # "[ISO-sics] open/4".

open_test7 :- open('/tmp/f', write, _, [type(text)|_]).

:- test open_test8
   + exception(error(instantiation_error, _))
   # "[ISO-sics] open/4".

open_test8 :- open('/tmp/f', write, _, [type(text), _]).

:- test open_test9
   + exception(error(type_error(atom,1), _))
   # "[ISO-sics] open/3".

open_test9 :- open('/tmp/f', 1, _).

:- test open_test10
   + exception(error(type_error(list, type(text)), Im_dep))
   # "[ISO-sics] open/4".

open_test10 :- open('/tmp/f', write, _, type(text)).

:- test open_test11
   + exception(error(uninstantiation_error(bar), _))
   # "[ISO-sics] open/3".

open_test11 :- open('/tmp/f', write, bar).

:- test open_test12
   + exception(error(domain_error(source_sink, foo(1, 2)), _))
   # "[ISO-sics] open/3".

open_test12 :- open(foo(1, 2), write, _).

:- test open_test13
   + exception(error(domain_error(io_mode, red), _))
   # "[ISO-sics] open/3".

open_test13 :- open('/tmp/foo', red, _).

:- test open_test14
   + exception(error(domain_error(stream_option, bar), _))
   # "[ISO-sics] open/4".

open_test14 :- open('/tmp/foo', write, _, [bar]).

:- test open_test15
   + exception(error(existence_error(source_sink, Source_sink), _))
   # "[ISO-sics] open/3".

open_test15 :- open('nonexistent', read, _).

:- test open_test16
   + (setup(setup_open16(S)), cleanup(cleanup_open16(S)),
      exception(error(permission_error(open, source_sink, alias(a)), _)))
   # "[ISO-sics] open/4".

open_test16 :- open('/tmp/bar', write, _, [alias(a)]).

setup_open16(S) :- open('/tmp/foo', write, S, [alias(a)]).

cleanup_open16(S) :- close(S).

% TODO:[JF] We need to implement reposition(true) in open/4, but this
%   error is a bit different. Most Prolog system do not throw any
%   exception while opening this device.

:- test open_test17
   + exception(error(permission_error(open, source_sink, reposition(true)), _))
   # "[ISO-sics] open/4: bug()".

open_test17 :- open('/dev/tty', read, _, [reposition(true)]).

% ---------------------------------------------------------------------------
%! ## 8.11.6 close/1, close/2 ISOcore#p88

% NOTE: Current issues in Ciao:
%
%  - force(true) is not implemented in close/1

:- test close_test1(S)
   + not_fails
   # "[ISO-sics] close/1".

close_test1(S) :- open('/tmp/foo', write, S), close(S).

:- test close_test2
   + exception(error(instantiation_error, _))
   # "[ISO-sics] close/1".

close_test2 :- close(_).

:- test close_test3(Sc)
   + (setup(curr_in(Sc)),
      exception(error(instantiation_error, _)))
   # "[ISO-sics] close/2".

close_test3(Sc) :- close(Sc, _).

:- test close_test4(Sc)
   + (setup(curr_in(Sc)),
      exception(error(instantiation_error, _)))
   # "[ISO-sics] close/2".

close_test4(Sc) :- close(Sc, [force(true)|_]).

:- test close_test5(Sc)
   + (setup(curr_in(Sc)),
      exception(error(instantiation_error, _)))
   # "[ISO-sics] close/2".

close_test5(Sc) :- close(Sc, [force(true), _]).

:- test close_test6(Sc)
   + (setup(curr_in(Sc)),
      exception(error(type_error(list, foo), _)))
   # "[ISO-sics] close/2".

close_test6(Sc) :- close(Sc, foo).

:- test close_test7(Sc)
   + (setup(curr_in(Sc)),
      exception(error(domain_error(close_option, foo), _)))
   # "[ISO-sics] close/2".

close_test7(Sc) :- close(Sc, [foo]).

% TODO:[JF] both exceptions acceptable in ISO 
:- test close_test8
   + exception(error(existence_error(stream, foo), _))
   % + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] close/1".

close_test8 :- close(foo).

:- test close_test9(S)
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] close/1".

close_test9(S) :- close(S).

% TODO:[JF] force(true) option is not implemented
:- test close_test10(Sc)
   + (setup(curr_in(Sc)),
      not_fails)
   # "[ISO-ciao] close/2: bug()".

close_test10(Sc) :- close(Sc, [force(true)]).

% ---------------------------------------------------------------------------
%! ## 8.11.7 flush_output/1 ISOcore#p89

:- test flush_output_test1(S)
   + (setup(txt_out_s(S, Prev)), cleanup(und(Prev)))
   # "[ISO-sics] flush_output/1".

% NOTE: reads before closing the file
flush_output_test1(S) :-
    write(S, 'foo'),
    flush_output(S),
    chk_out('/tmp/tmp.out', txt("foo")).

% TODO:[JF] both acceptable in ISO 
:- test flush_output_test2
   + exception(error(existence_error(stream, foo), _))
   % + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] flush_output/1".

flush_output_test2 :- flush_output(foo).

:- test flush_output_test3
   + exception(error(instantiation_error, _))
   # "[ISO-sics] flush_output/1".

flush_output_test3 :- flush_output(_).

:- test flush_output_test4(S)
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] flush_output/1".

flush_output_test4(S) :- flush_output(S).

:- test flush_output_test5(S)
   + (setup(w_in_s(txt(''), S, Prev)), cleanup(und(Prev)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] flush_output/1".

flush_output_test5(S) :- flush_output(S).

% TODO:[JF] fixed, the orig test was different!
:- test flush_output_test6
   + (setup(txt_out_a(Prev)), cleanup(und(Prev)),
      not_fails)
   # "[ISO-sics] flush_output/1".

% TODO: should we check the output? (see orig test)
flush_output_test6 :- flush_output(st_o).

% ---------------------------------------------------------------------------
%! ## 8.11.8 stream_property/2, at_end_of_stream/0, at_end_of_stream/1 ISOcore#p90

:- use_module(library(idlists), [memberchk/2]).

:- test stream_property_test1
   + (not_fails, no_exception)
   # "[ISO] stream_property/2".

stream_property_test1 :-
    wr_f('/tmp/file1.pl', txt('')),
    open('/tmp/file1.pl', read, S1, []),
    open('/tmp/file2.pl', write, S2, []),
    findall(F, stream_property(_, file_name(F)), L),
    close(S1),
    close(S2),
    absolute_file_name('/tmp/file1.pl', File1),
    absolute_file_name('/tmp/file2.pl', File2),
    memberchk(File1, L),
    memberchk(File2, L).

:- test stream_property_test2
   + (not_fails, no_exception)
   # "[ISO] stream_property/2".

stream_property_test2 :-
    open('/tmp/file1', write, S1, []),
    current_output(Cout),
    findall(S, stream_property(S, output), L),
    close(S1),
    sublist([S1, Cout], L).

:- test stream_property_test3
   + exception(error(domain_error(stream, foo), _))
   # "[ISO-sics] stream_property/2".

stream_property_test3 :- stream_property(foo, _Property).

:- test stream_property_test4
   + exception(error(domain_error(stream_property, foo), _))
   # "[ISO-sics] stream_property/2".

stream_property_test4 :- stream_property(_S, foo).

:- test stream_property_test5 + not_fails
   # "[ISO-sics] stream_property/2".

stream_property_test5 :-
    current_input(S),
    findall(Property, stream_property(S, Property), Ps),
    sublist([input, alias(user_input), eof_action(reset),
                  mode(read), reposition(false), type(text)], Ps).

:- test stream_property_test6 + not_fails
   # "[ISO-sics] stream_property/2".

stream_property_test6 :-
    current_output(S),
    findall(Property, stream_property(S, Property), Ps),
    sublist([output, alias(user_output), eof_action(reset),
                  mode(append), reposition(false), type(text)], Ps).

% TODO:[JF] This test supposedly checks that there is no open binary
%   stream on startup, which is a bit weird. Disabling it.

% :- test stream_property_test7 + fails
%    # "[ISO-sics] stream_property/2".
% 
% stream_property_test7 :- stream_property(_S, type(binary)).

:- test at_end_of_stream_test1
   + exception(error(instantiation_error, _))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test1 :- at_end_of_stream(_S).

% TODO:[JF] both acceptable in ISO 
:- test at_end_of_stream_test2
%   + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test2 :- at_end_of_stream(foo).

:- test at_end_of_stream_test3(S)
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test3(S) :- at_end_of_stream(S).

:- test at_end_of_stream_test4
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test4 :- at_end_of_stream(st_i).

:- test at_end_of_stream_test5(S1) 
   + (setup(w_in_a(txt('a'), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test5(st_i) :-
    \+ at_end_of_stream(st_i),
    read_string_to_end(st_i, "a").

:- test at_end_of_stream_test6
   + (not_fails,
      setup(w_in_a(bin([]), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] at_end_of_stream/1".

at_end_of_stream_test6 :-
    at_end_of_stream(st_i).

:- test at_end_of_stream_test7
   + (not_fails,
      setup(w_in_a(bin([0]), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] at_end_of_stream/1".
                       
at_end_of_stream_test7 :-
    \+ at_end_of_stream(st_i),
    read_bytes_to_end(st_i, [0]).

%! ## 8.11.9 set_stream_position/2 ISOcore#p90

% NOTE: Current issues in Ciao:
%
%  - reposition(true) is not implemented in open/4
%  - position(Pos) property is not implemented in stream_property/2

% TODO:[JF] implement position/1 property in streams and reposition(true) in open/4
:- test set_stream_position_test1
   + exception(error(instantiation_error, _))
   # "[ISO-sics] set_stream_position/2: bug()".

set_stream_position_test1 :-
    open('/tmp/bar', write, S, [reposition(true)]),
    stream_property(S, position(Pos)),
    set_stream_position(_, Pos),
    close(S).

:- test set_stream_position_test2(S)
   + (setup(curr_in(S)),
      exception(error(instantiation_error, _)))
   # "[ISO-sics] set_stream_position/2".

set_stream_position_test2(S) :- set_stream_position(S, _Pos).

% TODO:[JF] implement position/1 property in streams and reposition(true) in open/4
% TODO:[JF] both errors acceptable in ISO 
:- test set_stream_position_test3
%   + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] set_stream_position/2: bug()".

set_stream_position_test3 :-
    open('/tmp/bar', write, S, [reposition(true)]),
    stream_property(S, position(Pos)),
    set_stream_position(foo, Pos),
    close(S).

% TODO:[JF] implement position/1 property in streams and reposition(true) in open/4
:- test set_stream_position_test4(S) 
   + exception(error(existence_error(stream, S), _))
   # "[ISO-sics] set_stream_position/2: bug()".

set_stream_position_test4(S) :-
    open('/tmp/bar', write, S, [reposition(true)]),
    stream_property(S, position(Pos)),
    close(S),
    set_stream_position(S, Pos).

:- test set_stream_position_test5(S)
   + (setup(curr_in(S)),
      exception(error(domain_error(stream_position, foo), _)))
   # "[ISO-sics] set_stream_position/2".

set_stream_position_test5(S) :- set_stream_position(S, foo).

% TODO:[JF] implement position/1 property in streams and reposition(true) in open/4
% TODO:[JF] implement set_stream_position/2
:- test set_stream_position_test6(S, Pos) 
   + exception(error(permission_error(reposition, stream, S), _))
   # "[ISO-sics] set_stream_position/2: bug()".

set_stream_position_test6(S, Pos) :-
    open('/tmp/foo', write, S),
    stream_property(S, position(Pos)),
    current_input(S),
    once_port_reify(set_stream_position(S, Pos), Port),
    close(S),
    port_call(Port).

% ===========================================================================
%! # 8.12 Character input/output
%! ## 8.12.1 get_char/1, get_char/2, get_code/1, get_code/2 ISOcore#p91

:- test getchar_test1(Char, X) => ( Char = 'q', X = 'werty' )
   + (setup(w_in(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_char/1".
getchar_test1(Char, X) :- get_char(Char), read(X).

:- test getcode_test2(Code, X) => ( Code = 0'q, X = 'werty' )
   + (setup(w_in(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_code/1".
getcode_test2(Code, X) :- get_code(Code), read(X).

:- test getchar_test3(Char, X) => ( Char = q, X = 'werty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_char/2".
getchar_test3(Char, X) :- get_char(st_i, Char), read(st_i, X).

:- test getcode_test4(Code, X) => ( Code = 0'q, X = 'werty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_code/2".
getcode_test4(Code, X) :- get_code(st_i, Code), read(st_i, X).

:- test getchar_test5(Char, X) => ( Char = '''', X = "qwerty'" )
   + (setup(w_in_a(txt("'qwerty'"), Prev)), cleanup(und(Prev)))
   # "[ISO] get_char/2".
getchar_test5(Char, X) :- get_char(st_i, Char), read_string_to_end(st_i, X).

:- test getcode_test6(Code, X) => ( Code= 0'', X = "qwerty'" )
   + (setup(w_in_a(txt("'qwerty'"), Prev)), cleanup(und(Prev)))
   # "[ISO] get_code/2".
getcode_test6(Code, X) :- get_code(st_i, Code), read_string_to_end(st_i, X).
    
:- test getchar_test7(X) => ( X='werty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_char/2".
getchar_test7(X) :- \+ get_char(st_i, p), read(st_i, X).

:- test getcode_test8(X) => ( X='werty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] get_code/2".
getcode_test8(X) :- \+ get_code(st_i, 0'p), read(st_i,X).

:- test getchar_test9(Char) => ( Char=end_of_file )
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO] get_char/2".
getchar_test9(Char) :- get_char(st_i, Char).
    %{past}
    %stream_property(st_w, end_of_stream(past)),
  
:- test getcode_test10(Code) => ( Code=(-1) )
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO] get_code/2".
getcode_test10(Code) :- get_code(st_i, Code).
    %{past}
    %stream_property(st_x, end_of_stream(past)),

:- test getchar_test11
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] get_char/1".
getchar_test11 :- get_char(user_output, _X).

:- test getcode_test12
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] get_code/1".
getcode_test12 :- get_code(user_output, _X).

:- test getchar_test13 + exception(error(instantiation_error, _))
   # "[ISO-sics] get_char/2".
getchar_test13 :- get_char(_, _).

:- test getchar_test14 + exception(error(type_error(in_character, 1), _))
   # "[ISO-sics] get_char/1".
getchar_test14 :- get_char(1).

:- test getchar_test15 + exception(error(type_error(in_character, 1), _))
   # "[ISO-sics] get_char/2".
getchar_test15 :- get_char(user_input, 1).

% TODO:[JF] both acceptable in ISO 
:- test getchar_test16
   + exception(error(existence_error(stream, foo), _))
%   + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] get_char/2".
getchar_test16 :- get_char(foo, _).

:- test getchar_test17(S) 
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] get_char/2".
getchar_test17(S) :- get_char(S, _).

:- test getchar_test18(S, _)
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] get_char/1".
getchar_test18(S, _) :- get_char(S, _).

:- test getchar_test19
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, _), _)))
   # "[ISO-sics] get_char/1".
getchar_test19 :- get_char(_).

:- test getchar_test20
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S1), _)))
   # "[ISO-sics] get_char/1".
getchar_test20 :-
    catch(get_char(_), _, fail), % no exception here
    get_char(_).

:- test getchar_test21(S, Char1, Char2) => ( Char1 = end_of_file, Char2 = end_of_file )
   + (setup(w_in_s_e(txt(''), S, Prev)), cleanup(und(Prev)))
   # "[ISO-sics] get_char/2".
getchar_test21(S1, Char1, Char2) :-
    get_char(S1, Char1),
    get_char(S1, Char2).

:- test getchar_test22(S) 
   + (setup(w_in_s(txtbin([0]), S, Prev)), cleanup(und(Prev)),
      exception(error(representation_error(character), _)))
   # "[ISO-sics] get_char/2".
getchar_test22(S) :- get_char(S, _).

:- test getcode_test23
   + exception(error(instantiation_error, _))
   # "[ISO-sics] get_code/2".
getcode_test23 :- get_code(_, _).

:- test getcode_test24
   + exception(error(type_error(integer, p), _))
   # "[ISO-sics] get_code/1".
getcode_test24 :- get_code(p).

:- test getcode_test25
   + exception(error(type_error(integer, p), _))
   # "[ISO-sics] get_code/2".
getcode_test25 :- get_code(user_input, p).

:- test getcode_test26
   + exception(error(representation_error(in_character_code), _))
   # "[ISO-sics] get_code/1".
getcode_test26 :- get_code(-2).

% TODO:[JF] both acceptable in ISO 
:- test getcode_test27
   + exception(error(existence_error(stream, foo), _))
%   + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] get_code/2".
getcode_test27 :- get_code(foo, _).

:- test getcode_test28(S1) 
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] get_code/2".
getcode_test28(S1) :- get_code(S1, _).

:- test getcode_test29(S) 
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] get_code/1".
getcode_test29(S) :- get_code(S, _).

:- test getcode_test30
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, S1), _)))
   # "[ISO-sics] get_code/1".
getcode_test30 :- get_code(_).

:- test getcode_test31
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S1), _)))
   # "[ISO-sics] get_code/1".
getcode_test31 :- catch(get_code(_), _, fail), get_code(_).

:- test getcode_test32(S, Code1, Code2) => (Code1=(-1), Code2=(-1))
   + (setup(w_in_s_e(txt(''), S, Prev)), cleanup(und(Prev)))
   # "[ISO-sics] get_code/2".
getcode_test32(S, Code1, Code2) :- get_code(S, Code1), get_code(S, Code2).

% TODO:[JF] note that other prologs seem to admit 0 in in_character_code
:- test getcode_test33(S) 
   + (setup(w_in_s(txtbin([0]), S, Prev)), cleanup(und(Prev)),
      exception(error(representation_error(character), _)))
   # "[ISO-sics] get_code/2".
getcode_test33(S) :- get_code(S, _).

% ---------------------------------------------------------------------------
%! ## 8.12.2 peek_char/1, peek_char/2, peek_code/1, peek_code/2 ISOcore#p93

:- test peekchar_test1(Char, X) => ( Char='q', X='qwerty' )
   + (setup(w_in(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_char/1".
peekchar_test1(Char, X) :- peek_char(Char), read(X).

:- test peekcode_test2(Code, X) => ( Code=0'q, X='qwerty' )
   + (setup(w_in(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_code/1".
peekcode_test2(Code, X) :- peek_code(Code), read(X).

:- test peekchar_test3(Char, X) => ( Char='q', X='qwerty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_char/2".
peekchar_test3(Char, X) :- peek_char(st_i, Char), read(st_i, X).

:- test peekcode_test4(Code, X) => ( Code=0'q, X='qwerty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_code/2".
peekcode_test4(Code, X) :- peek_code(st_i, Code), read(st_i, X).

:- test peekchar_test5(Char, X) => ( Char='''', X='qwerty' )
   + (setup(w_in_a(txt("'qwerty'."), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_char/2".
peekchar_test5(Char,X) :- peek_char(st_i, Char), read(st_i, X).

:- test peekcode_test6(Code, X) => ( Code=0'\', X='qwerty' )
   + (setup(w_in_a(txt("'qwerty'."), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_code/2".
peekcode_test6(Code, X) :- peek_code(st_i, Code), read(st_i, X).

:- test peekchar_test7(X) => ( X='qwerty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_char/2".
peekchar_test7(X) :- \+ peek_char(st_i, p), read(st_i, X).

:- test peekcode_test8(X) => ( X='qwerty' )
   + (setup(w_in_a(txt('qwerty.'), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_code/2".
peekcode_test8(X) :- \+ peek_code(st_i, 0'p), read(st_i, X).

:- test peekchar_test9(Char) => ( Char=(end_of_file) )
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_char/2".
peekchar_test9(Char) :- peek_char(st_i, Char).

:- test peekcode_test10(Code) => ( Code=(-1) )
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_code/2".
peekcode_test10(Code) :- peek_code(st_i, Code).

:- test peekchar_test11 
   + (setup(w_in_a(txt(''), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S), _)))
   # "[ISO] peek_char/2".
peekchar_test11 :-
    catch(get_code(st_i, _), _, fail), % (exception no relevant here)
    peek_char(st_i, _).

:- test peekchar_test12
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] peek_char/2".
peekchar_test12 :- peek_char(user_output, _).

:- test peekcode_test13
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] peek_char/2".
peekcode_test13 :- peek_code(user_output, _).

:- test peekchar_test14
   + exception(error(instantiation_error, _))
   # "[ISO-sics] peek_char/2".
peekchar_test14 :- peek_char(_, _).

:- test peekchar_test15
   + exception(error(type_error(in_character, 1), _))
   # "[ISO-sics] peek_char/1".
peekchar_test15 :- peek_char(1).

:- test peekchar_test16
   + exception(error(type_error(in_character, 1), _))
   # "[ISO-sics] peek_char/2".
peekchar_test16 :- peek_char(user_input, 1).

% TODO:[JF] both acceptable in ISO 
:- test peekchar_test17
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] peek_char/2".
peekchar_test17 :- peek_char(foo, _).

:- test peekchar_test18(S1) 
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] peek_char/2".
peekchar_test18(S1) :- peek_char(S1, _).

:- test peekchar_test19(S)
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] peek_char/2".
peekchar_test19(S) :- peek_char(S, _).

:- test peekchar_test20
   + (setup(w_in_a(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, S1), _)))
   # "[ISO-sics] peek_char/2".
peekchar_test20 :- peek_char(st_i, _).

:- test peekchar_test21(S, Char1, Char2) => (Char1=end_of_file, Char2=end_of_file)
   + (setup(w_in_s(txt(''), S, Prev)), cleanup(und(Prev)))
   # "[ISO-sics] peek_char/2".

peekchar_test21(S, Char1, Char2) :-
    peek_char(S, Char1),
    peek_char(S, Char1),
    get_char(S, Char2).

:- test peekchar_test22(S) 
   + (setup(w_in_s(txtbin([0]), S, Prev)), cleanup(und(Prev)),
      exception(error(representation_error(character), _)))
   # "[ISO-sics] peek_char/2".
peekchar_test22(S) :- peek_char(S, _).

:- test peekcode_test23
   + exception(error(instantiation_error, _))
   # "[ISO-sics] peek_code/2".
peekcode_test23 :- peek_code(_, _).

:- test peekcode_test24
   + exception(error(type_error(integer, p), _))
   # "[ISO-sics] peek_code/1".
peekcode_test24 :- peek_code(p).

:- test peekcode_test25
   + exception(error(type_error(integer, p), _))
   # "[ISO-sics] peek_code/2".
peekcode_test25 :- peek_code(user_input, p).

:- test peekcode_test26
   + exception(error(representation_error(in_character_code), _))
   # "[ISO-sics] peek_code/1".
peekcode_test26 :- peek_code(-2).

% TODO:[JF] both acceptable in ISO 
:- test peekcode_test27
   + exception(error(existence_error(stream, foo), _))
%   + exception(error(domain_error(stream_or_alias, foo), _))
   # "[ISO-sics] peek_code/2".
peekcode_test27 :- peek_code(foo, _).

:- test peekcode_test28(S1) 
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] peek_code/2".
peekcode_test28(S1) :- peek_code(S1, _).

:- test peekcode_test29(S) : true
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] peek_code/2".
peekcode_test29(S) :- peek_code(S, _).

:- test peekcode_test30(S) 
   + (setup(w_in_s(bin([]), S, Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, S), _)))
   # "[ISO-sics] peek_code/2".
peekcode_test30(S) :- peek_code(S, _).

:- test peekcode_test31
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S1), _)))
   # "[ISO-sics] peek_code/1".
peekcode_test31 :-
    catch(get_code(_X), _, fail), % ignore errors here
    peek_code(_).

:- test peekcode_test32(Code1, Code2) => ( Code1=(-1), Code2=(-1) )
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] peek_code/1".
peekcode_test32(Code1, Code2) :- peek_code(Code1), peek_code(Code2).

% TODO:[JF] note that other prologs seem to admit 0 in in_character_code
:- test peekcode_test33(S) 
   + (setup(w_in_s(txtbin([0]), S, Prev)), cleanup(und(Prev)),
      exception(error(representation_error(character), _)))
   # "[ISO-sics] peek_code/2".
peekcode_test33(S) :- peek_code(S, _).

% ---------------------------------------------------------------------------
%! ## 8.12.3 put_char/1, put_char/2, put_code/1, put_code/2 ISOcore#p94

:- test putchar_test1 + not_fails # "[ISO] put_char/1".
putchar_test1 :- with_out(txt('qwer'), put_char(t), txt("qwert")).

:- test putchar_test2 + not_fails # "[ISO] put_char/2".
putchar_test2 :- with_out_a(txt('qwer'), put_char(st_o, 'A'), txt("qwerA")).

:- test putcode_test3 + not_fails # "[ISO] put_code/1".
putcode_test3 :- with_out(txt('qwer'), put_code(0't), txt("qwert")).

:- test putcode_test4 + not_fails # "[ISO] put_code/2".
putcode_test4 :- with_out_a(txt('qwer'), put_code(st_o, 0't), txt("qwert")).

:- test putchar_test5 + not_fails # "[ISO] put_char/1".
putchar_test5 :- with_out(txt('qwer'), (nl, put_char(a)), txt("qwer\na")).

:- test putchar_test6 + not_fails # "[ISO] put_char/2".
putchar_test6 :- with_out_a(txt('qwer'), (nl(st_o), put_char(st_o, a)), txt("qwer\na")).

:- test putchar_test7
   + exception(error(instantiation_error, _))
   # "[ISO] put_char/2".
putchar_test7 :- with_out_a(txt(''), put_char(st_o, _), txt("")).

:- test putchar_test8
   + exception(error(type_error(character, ty), _))
   # "[ISO] put_char/2".
putchar_test8 :- with_out_a(txt(''), put_char(st_o, 'ty'), txt("")).

:- test putcode_test9
   + exception(error(instantiation_error, _))
   # "[ISO] put_code/2".
putcode_test9 :- with_out_a(txt(''), put_code(st_o, _), txt("")).

:- test putcode_test10
   + exception(error(type_error(integer, ty), _))
   # "[ISO] put_code/2".
putcode_test10 :- with_out_a(txt(''), put_code(st_o, 'ty'), txt("")).

:- test nl_test11 + exception(error(instantiation_error, _))
   # "[ISO] nl/1".
nl_test11 :- nl(_).

:- test nl_test12
   + exception(error(permission_error(output, stream, user_input), _))
   # "[ISO] nl/1".
nl_test12 :- nl(user_input).

:- test putchar_test13 + exception(error(instantiation_error, _))
   # "[ISO-sics] put_char/2".
putchar_test13 :- put_char(_, t).

:- test putchar_test14 + exception(error(instantiation_error, _))
   # "[ISO-sics] put_char/2".
putchar_test14 :- put_char(_).

:- test putchar_test15(S) 
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] put_char/2".
putchar_test15(S) :- put_char(S, a).

:- test putchar_test16(S) 
   + (setup(curr_in(S)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] put_char/2".
putchar_test16(S) :- put_char(S, a).

:- test putchar_test17 
   + exception(error(permission_error(output, binary_stream, S), _))
   # "[ISO-sics] put_char/1".
putchar_test17 :- with_out(bin([]), put_char(a), bin([])).

:- test putcode_test18
   + exception(error(instantiation_error, _))
   # "[ISO-sics] put_code/2".
putcode_test18 :- put_code(_, 0't).

:- test putcode_test19 + exception(error(instantiation_error, _))
   # "[ISO-sics] put_code/2".
putcode_test19 :- put_code(_).

:- test putcode_test20(S) 
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] put_code/2".
putcode_test20(S) :- put_code(S, 0'a).

:- test putcode_test21(S) 
   + (setup(curr_in(S)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] put_code/2".
putcode_test21(S) :- put_code(S, 0'a).

:- test putcode_test22
   + exception(error(permission_error(output, binary_stream, _), _))
   # "[ISO-sics] put_code/2".
putcode_test22 :- with_out_s(bin([]), S, put_code(S, 0'a), bin([])).

:- test putcode_test23
   + exception(error(representation_error(character_code), _))
   # "[ISO-sics] put_code/1".
putcode_test23 :- put_code(-1).

% TODO:[JF] both acceptable in ISO 
:- test putcode_test24
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] put_code/2".
putcode_test24 :- put_code(foo, -1).

% ===========================================================================
%! # 8.13 Byte input/output
%! ## 8.13.1 get_byte/1, get_byte/2 ISOcore#p96

:- test getbyte_test1(Byte, X) => ( Byte=113, X=[119, 101, 114] )
   + (setup(w_in(bin([113, 119, 101, 114]), Prev)), cleanup(und(Prev)))
   # "[ISO] get_byte/1".
getbyte_test1(Byte, X) :- get_byte(Byte), read_bytes_to_end_ci(X).

:- test getbyte_test2(Byte, X) => ( Byte=113, X=[119, 101, 114] )
   + (setup(w_in_a(bin([113, 119, 101, 114]), Prev)), cleanup(und(Prev)))
   # "[ISO] get_byte/1".
getbyte_test2(Byte, X) :- get_byte(st_i, Byte), read_bytes_to_end(st_i, X).

:- test getbyte_test3(X) => ( X=[119, 101, 114, 116, 121] )
   + (setup(w_in_a(bin([113, 119, 101, 114, 116, 121]), Prev)), cleanup(und(Prev)))
   # "[ISO] get_byte/2".
getbyte_test3(X) :- \+ get_byte(st_i, 114), read_bytes_to_end(st_i, X).

:- test getbyte_test4(Byte) => (Byte=(-1))
   + (setup(w_in_a(bin([]), Prev)), cleanup(und(Prev)))
   # "[ISO] get_byte/2".
getbyte_test4(Byte) :- get_byte(st_i, Byte).
    %{past}
    % stream_property(S2, end_of_stream(past)),

:- test getbyte_test5
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] get_byte/2".
getbyte_test5 :- get_byte(user_output, _).

:- test getbyte_test6
   + exception(error(instantiation_error, _))
   # "[ISO-sics] get_byte/2".
getbyte_test6 :- get_byte(_, _).

:- test getbyte_test7 
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(type_error(in_byte, p), _)))
   # "[ISO-sics] get_byte/1".
getbyte_test7 :- get_byte(p).

:- test getbyte_test8
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(type_error(in_byte, -2), _)))
   # "[ISO-sics] get_byte/1".
getbyte_test8 :- get_byte(-2).

% TODO:[JF] both acceptable in ISO 
:- test getbyte_test9
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] get_byte/2".
getbyte_test9 :- get_byte(foo, _).

:- test getbyte_test10(S) 
   + (setup(closed_instream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] get_byte/2".
getbyte_test10(S) :- get_byte(S, _).

:- test getbyte_test11(S) 
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] get_byte/2".

getbyte_test11(S) :- get_byte(S, _).

:- test getbyte_test12
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, text_stream, S1), _)))
   # "[ISO-sics] get_byte/1".

getbyte_test12 :- get_byte(_).

:- test getbyte_test13
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S1), _)))
   # "[ISO-sics] get_byte/1".

getbyte_test13 :- get_byte(_), get_byte(_).

% ---------------------------------------------------------------------------
%! ## 8.13.2 peek_byte/1, peek_byte/2 ISOcore#p97

:- test peekbyte_test1(Byte, X) => ( Byte=113, X=[113, 119, 101, 114] )
   + (setup(w_in(bin([113, 119, 101, 114]), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_byte/1".
peekbyte_test1(Byte, X) :- peek_byte(Byte), read_bytes_to_end_ci(X).

:- test peekbyte_test2(Byte, X) => ( Byte=113, X=[113, 119, 101, 114] )
   + (setup(w_in_a(bin([113, 119, 101, 114]), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_byte/2".
peekbyte_test2(Byte, X) :- peek_byte(st_i, Byte), read_bytes_to_end(st_i, X).

:- test peekbyte_test3(X) => ( X=[113, 119, 101, 114, 116, 121] )
   + (setup(w_in_a(bin([113, 119, 101, 114, 116, 121]), Prev)), cleanup(und(Prev)))
   # "[ISO] peek_byte/2".
peekbyte_test3(X) :- \+ peek_byte(st_i, 114), read_bytes_to_end(st_i, X).

:- test peekbyte_test4(Byte) => (Byte=(-1))
   + (setup(w_in_a(bin([]),Prev)), cleanup(und(Prev)))
   # "[ISO] peek_byte/2".
peekbyte_test4(Byte) :- peek_byte(st_i, Byte).

:- test peekbyte_test5
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO] peek_byte/2".
peekbyte_test5 :- peek_byte(user_output, _).

:- test peekbyte_test6
   + exception(error(instantiation_error, _))
   # "[ISO-sics] peek_byte/2".
peekbyte_test6 :- peek_byte(_, _).

:- test peekbyte_test7
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(type_error(in_byte, p), _)))
   # "[ISO-sics] peek_byte/1".
peekbyte_test7 :- peek_byte(p).

:- test peekbyte_test8
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(type_error(in_byte, -2), _)))
   # "[ISO-sics] peek_byte/1".
peekbyte_test8 :- peek_byte(-2).

% TODO:[JF] both acceptable in ISO 
:- test peekbyte_test9
%   + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] peek_byte/2".
peekbyte_test9 :- peek_byte(foo, _).

:- test peekbyte_test10(S1) 
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] peek_byte/2".
peekbyte_test10(S1) :- peek_byte(S1, _).

:- test peekbyte_test11(S, _) 
   + (setup(curr_out(S)),
      exception(error(permission_error(input, stream, S), _)))
   # "[ISO-sics] peek_byte/2".
peekbyte_test11(S, _) :- peek_byte(S, _).

:- test peekbyte_test12
   + (setup(w_in(txt(''),Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, text_stream, S), _)))
   # "[ISO-sics] peek_byte/1".
peekbyte_test12 :- peek_byte(_).

:- test peekbyte_test13
   + (setup(w_in(bin([]),Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S1), _)))
   # "[ISO-sics] peek_byte/1".
peekbyte_test13 :- get_byte(_), peek_byte(_).

% ---------------------------------------------------------------------------
%! ## 8.13.3 put_byte/1, put_byte/2 ISOcore#p98

:- test putbyte_test1 + not_fails # "[ISO] put_byte/1".
putbyte_test1 :- with_out(bin([113, 119, 101, 114]), put_byte(116), bin([113, 119, 101, 114, 116])).

:- test putbyte_test2 + not_fails # "[ISO] put_byte/1".
putbyte_test2 :- with_out_a(bin([113, 119, 101, 114]), put_byte(st_o, 84), bin([113, 119, 101, 114, 84])).

:- test putbyte_test3
   + exception(error(instantiation_error, _))
   # "[ISO] put_byte/2".
putbyte_test3 :- put_byte(my_file, _).

:- test putbyte_test4
   + exception(error(type_error(byte, ty), _))
   # "[ISO] put_byte/2".
putbyte_test4 :- put_byte(user_output, 'ty').

:- test putbyte_test5
   + exception(error(instantiation_error, _))
   # "[ISO-sics] put_byte/2".
putbyte_test5 :- put_byte(_, 118).

:- test putbyte_test6
   + exception(error(instantiation_error, _))
   # "[ISO-sics] put_byte/2".
putbyte_test6 :- with_out(bin([]), put_byte(_), bin([])).

:- test putbyte_test7(S) 
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] put_byte/2".
putbyte_test7(S) :- put_byte(S, 77).

:- test putbyte_test8(S) 
   + (setup(w_in_s(bin([]), S, Prev)), cleanup(und(Prev)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] put_byte/2".
putbyte_test8(S) :- put_byte(S, 99).

% TODO: this should be fixed when integrating into the engine (stream type = text in user_output)
:- test putbyte_test9 
   + (setup(curr_out(S)),
      exception(error(permission_error(output, text_stream, S), _)))
   # "[ISO-sics] put_byte/1".
putbyte_test9 :- put_byte(99).

:- test putbyte_test10 
   + exception(error(type_error(byte, -1), _))
   # "[ISO-sics] put_byte/2".
putbyte_test10 :- with_out(bin([]), put_byte(-1), bin([])).

:- test putbyte_test11
   + exception(error(instantiation_error, _))
   # "[ISO-sics] put_byte/2".
putbyte_test11 :- put_byte(_, 1).

% TODO:[JF] both acceptable in ISO 
:- test putbyte_test12
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
   # "[ISO-sics] put_byte/2".
putbyte_test12 :- put_byte(foo, 1).

:- test putbyte_test13
   + exception(error(type_error(byte, ty), _))
   # "[ISO-sics] put_byte/2".
putbyte_test13 :- put_byte(user_output, 'ty').

% ===========================================================================
%! # 8.14 Term input/output
%! ## 8.14.1 read/1, read/2, read_term/2, read_term/3 ISOcore#p99

text_def(max_int(M), [Atm, '.']) :-
    ( current_prolog_flag(max_integer, M) -> true ; M=0 ),
    number_codes(M, L),
    atom_codes(Atm, L).

text_def(min_int(M), [Atm, '.']) :-
    ( current_prolog_flag(min_integer, M) -> true ; M=0 ),
    number_codes(M, L),
    atom_codes(Atm, L).

:- test read_test1(X,Y) => (X='term1',Y='term2')
   + (setup(w_in(txt('term1. term2.'), Prev)), cleanup(und(Prev)))
   # "[ISO] read/1".
read_test1(X,Y) :- read(X), read(Y).

:- test read_test2(X,Y) => (X='term2')
   + (setup(w_in_a(txt('term1. term2.'), Prev)), cleanup(und(Prev)))
   # "[ISO] read/2".
read_test2(X,Y) :- read(st_i, Y), read(st_i, X).

:- test read_test3(T, VL, VN, VS, Y)
   : true =>
   ( T=foo(X1+X2, X1+X3),
     VL=[X1, X2, X3],
     VN=['A'=X1, 'Roger'=X2],
     VS=['Roger'=X2],
     Y='term2' )
   + (setup(w_in_a(txt('foo(A+Roger,A+_). term2.'), Prev)), cleanup(und(Prev)))
   # "[ISO] read_term/3".
read_test3(T, VL, VN, VS, Y) :-
   read_term(st_i, T, [variables(VL), variable_names(VN), singletons(VS)]),
   read(st_i,Y).

:- test read_test4(Y) => ( Y='term2' )
   + (setup(w_in(txt('3.1. term2.'),Prev)), cleanup(und(Prev)))
   # "[ISO] read/1".
read_test4(Y) :-
    ( read(4.1) -> fail ; true ),
    read(Y).

:- test read_test5(X, Y) => (Y='term2') +
   (setup(w_in(txt('foo 123. term2.'), Prev)), cleanup(und(Prev)),
    exception(error(syntax_error(S), _)))
   # "[ISO] read/1".
read_test5(X, Y) :- read(X), read(Y).

:- test read_test6(X) 
   + (setup(w_in(txt('3.1'),Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(S), _)))
   # "[ISO] read/1".
read_test6(X) :- read(X).
    %{past}
    %stream_property(S, end_of_stream(past)),

:- test read_test7(T, L) => (T=foo(bar), L=[])
   + (setup(w_in(txt('foo(bar).'),Prev)), cleanup(und(Prev)))
   # "[ISO-sics] read_term/2".
read_test7(T, L) :-
    read_term(T, [singletons(L)]).

:- test read_test8
   + exception(error(instantiation_error, _))
   # "[ISO-sics] read/2".
read_test8 :- read(_, _).

:- test read_test9
   + exception(error(instantiation_error, _))
   # "[ISO-sics] read_term/3".
read_test9 :- read_term(user_input, _, _).

:- test read_test10
   + exception(error(instantiation_error, _))
   # "[ISO-sics] read_term/3".
read_test10 :- read_term(user_input, _, [variables(_)|_]).

:- test read_test11
   + exception(error(instantiation_error, _))
   # "[ISO-sics] read_term/3".
read_test11 :- read_term(user_input, _, [variables(_), _]).

% TODO:[JF] both acceptable in ISO 
:- test read_test12
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
# "[ISO-sics] read/2".
read_test12 :- read(foo, _).

:- test read_test13
   + exception(error(type_error(list, bar), _))
   # "[ISO-sics] read_term/3".
read_test13 :- read_term(user_input, _, bar).

:- test read_test14
   + exception(error(domain_error(read_option, bar), _))
   # "[ISO-sics] read_term/3".
read_test14 :- read_term(user_input, _, [bar]).

:- test read_test15
   + exception(error(permission_error(input, stream, user_output), _))
   # "[ISO-sics] read_term/3".
read_test15 :- read_term(user_output, _, []).

:- test read_test16(T) => ( T=end_of_file )
   + (setup(w_in(txt(''), Prev)), cleanup(und(Prev)))
   # "[ISO-sics] read/1".
read_test16(T) :- read(T).

:- test read_test17(S1) 
   + (setup(closed_instream(S1)),
      exception(error(existence_error(stream, S1), _)))
   # "[ISO-sics] read_term/3".
read_test17(S1) :- read_term(S1, _, []).

:- test read_test18
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, _), _)))
   # "[ISO-sics] read_term/2".
read_test18 :- read_term(_, []).

:- test read_test19
   + (setup(w_in(bin([]), Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, binary_stream, _), _)))
   # "[ISO-sics] read/1".
read_test19 :- read(_).

% TODO:[JF] can current_input/1 return a stream alias like user_input?
%   it does in some prolog systems, not in gprolog
:- test read_test20(S) 
   + (setup(w_in_s(txt(''), S, Prev)), cleanup(und(Prev)),
      exception(error(permission_error(input, past_end_of_stream, S), _)))
   # "[ISO-sics] read_term/3".

read_test20(S) :-
    catch(get_code(S, _), _, fail), % (ignore errors here)
    read_term(S, _, []).

% NOTE: it exceeds max arity in Ciao
text_def(txt21, [
    'foo(\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,\n',
    '1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1).']).

:- test read_test21 
   + (setup(w_in(txt(def(txt21)),Prev)), cleanup(und(Prev)),
      exception(error(representation_error(max_arity), _)))
   # "[ISO-sics] read_term/2".
read_test21 :- read_term(_, []).

:- test read_test22
   + (setup(w_in(txt("'a."),Prev)), cleanup(und(Prev)),
      exception(error(syntax_error(S), _)))
   # "[ISO-sics] read_term/2".
read_test22 :- read_term(_, []).

:- test read_test23(T) => (T=M)
   + (setup(w_in(txt(def(max_int(M))),Prev)), cleanup(und(Prev)))
   # "[ISO-sics] read/1".
read_test23(T) :- read(T).

:- test read_test24(T) => (T=M)
   + (setup(w_in(txt(def(min_int(M))),Prev)), cleanup(und(Prev)))
   # "[ISO-sics] read/1".
read_test24(T) :- read(T).

% ---------------------------------------------------------------------------
%! ## 8.14.2 write/1, write/2, writeq/1, writeq/2, write_term/2, write_term/3 ISOcore#p100

:- test write_test1 + not_fails # "[ISO] write_term/3".
write_test1 :-
    with_out_s(txt(''), S, write_term(S, [1, 2, 3], []), txt("[1,2,3]")).

:- test write_test2 + not_fails # "[ISO] write_canonical/1".
write_test2 :-
    with_out(txt(''), write_canonical([1, 2, 3]), txt("'.'(1,'.'(2,'.'(3,[])))")).

:- test write_test3 + not_fails # "[ISO] write_term/3".
write_test3 :-
    with_out_s(txt(''), S, write_term(S, '1<2', []), txt("1<2")).

:- test write_test4 + not_fails # "[ISO] writeq/2".
write_test4 :-
    with_out_s(txt(''), S, writeq(S, '1<2'), txt("'1<2'")).

:- test write_test5 + not_fails # "[ISO] writeq/1".
write_test5 :-
    with_out(txt(''), writeq('$VAR'(0)), txt("A")).

:- test write_test6 + not_fails # "[ISO] write_term/3".
write_test6 :-
    with_out_s(txt(''), S, write_term(S, '$VAR'(1), [numbervars(false)]), txt("$VAR(1)")).

:- test write_test7 + not_fails # "[ISO] write_term/3".
write_test7 :-
    with_out_s(txt(''), S, write_term(S, '$VAR'(51), [numbervars(true)]), txt("Z1")).

:- test write_test8 + exception(error(instantiation_error, _))
   # "[ISO-sics] write/2".
write_test8 :- write(_, foo).

:- test write_test9 + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test9 :- write_term(foo, _).

:- test write_test10 + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test10 :- write_term(user_output,foo,_).

:- test write_test11
   + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test11 :- write_term(foo, [quoted(true)|_]).

:- test write_test12
   + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test12 :- write_term(user_output,foo,[quoted(true)|_]).

:- test write_test13
   + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test13 :- write_term(foo, [quoted(true), _]).

:- test write_test14
   + exception(error(instantiation_error, _))
   # "[ISO-sics] write_term/2".
write_test14 :- write_term(user_output,foo,[quoted(true),_]).

:- test write_test15
   + exception(error(type_error(list,2), _))
   # "[ISO-sics] write_term/2".
write_test15 :- write_term(user_output,1,2).

% TODO:[JF] type error list foo is common but not strictly conforming?
:- test write_test16
   + exception(error(type_error(list,foo), _))
   % + exception(error(type_error(list, [quoted(true)|foo]), _))
   # "[ISO-sics] write_term/2".
write_test16 :- write_term(1, [quoted(true)|foo]).

% TODO:[JF] both acceptable in ISO 
:- test write_test17
   % + exception(error(domain_error(stream_or_alias, foo), _))
   + exception(error(existence_error(stream, foo), _))
# "[ISO-sics] write_term/2".
write_test17 :- write(foo, 1).

:- test write_test18
   + exception(error(domain_error(write_option, foo), _))
   # "[ISO-sics] write_term/2".
write_test18 :- write_term(1, [quoted(true), foo]).

:- test write_test19(S) 
   + (setup(closed_outstream(S)),
      exception(error(existence_error(stream, S), _)))
   # "[ISO-sics] write/2".
write_test19(S) :- write(S, a).

:- test write_test20(S) 
   + (setup(curr_in(S)),
      exception(error(permission_error(output, stream, S), _)))
   # "[ISO-sics] write/2".
write_test20(S) :- write(S, a).

:- test write_test21
   + exception(error(permission_error(output, binary_stream, S), _))
   # "[ISO-sics] write/1".
write_test21 :- with_out(bin([]), write(a), bin([])).

% ---------------------------------------------------------------------------
%! ## 8.14.3 op/3 ISOcore#p102

:- test op_test1/1
   + not_fails
   # "[ISO] op/3".
op_test1(_) :- with_ops([op(30, xfy, ++)], op(30, xfy, ++)).

:- test op_test2
   + not_fails
   # "[ISO] op/3".
op_test2 :-
    with_ops([op(30, xfy, ++)], (op(0, xfy, ++), \+ current_op(_, xfy, ++))).

:- test op_test3
   + exception(error(type_error(integer, max), _))
   # "[ISO] op/3".
op_test3 :- op(max, xfy, ++).

:- test op_test4
   + exception(error(domain_error(operator_priority, -30), _))
   # "[ISO] op/3".
op_test4 :- op(-30, xfy, ++).

:- test op_test5
   + exception(error(domain_error(operator_priority, 1201), _))
   # "[ISO] op/3".
op_test5 :- op(1201, xfy, ++).

:- test op_test6
   + exception(error(instantiation_error, _))
   # "[ISO] op/3".
op_test6 :- op(30, _Xfy, ++).

:- test op_test7
   + exception(error(domain_error(operator_specifier, yfy), _))
   # "[ISO] op/3".
op_test7 :- op(30, yfy, ++).

:- test op_test8 + exception(error(type_error(list, 0), _))
   # "[ISO] op/3".
op_test8 :- op(30, xfy, 0).

:- test op_test9
   + not_fails
   # "[ISO] op/3".
op_test9 :-
    with_ops([op(30, xfy, ++)], (op(40, xfy, ++), current_op(40, xfy, ++))).

% NOTE: See op/3 documentation. Unlike in ISO-Prolog, it is allowed to
% define two operators with the same name, one infix and the other
% postfix.

% TODO:[JF] at least Ciao and SWI allow it
:- test op_test10
   + exception(error(permission_error(create, operator, ++), _))
   # "[ISO] op/3: bug(wontfix)".
op_test10 :-
    with_ops([op(30, xfy, ++)], with_ops([op(50, yf, ++)], true)).

:- test op_test11 + exception(error(instantiation_error, _))
   # "[ISO-sics] op/3".
op_test11 :- op(_, xfx, ++).

:- test op_test12 + exception(error(instantiation_error, _))
   # "[ISO-sics] op/3".
op_test12 :- op(100, xfx, _).

:- test op_test13 + exception(error(instantiation_error, _))
   # "[ISO-sics] op/3".
op_test13 :- op(100, xfx, [a|_]).

:- test op_test14 + exception(error(instantiation_error, _))
   # "[ISO-sics] op/3".
op_test14 :- op(100, xfx, [a, _]).

:- test op_test15
   + exception(error(type_error(atom, 200), _))
   # "[ISO-sics] op/3".
op_test15 :- op(100, 200, [a]).

:- test op_test16
   + exception(error(type_error(atom, f(1)), _))
   # "[ISO-sics] op/3".
op_test16 :- op(100, f(1), [a]).

:- test op_test17 + exception(error(type_error(atom, a+b), _))
   # "[ISO-sics] op/3".
op_test17 :- op(100, xfx, [a, a+b]).

:- test op_test18
   + exception(error(permission_error(modify, operator, ','), _))
   # "[ISO-sics] op/3".
op_test18 :- op(100, xfx, ',').

:- test op_test19
   + exception(error(permission_error(modify, operator, ','), _))
   # "[ISO-sics] op/3".
op_test19 :- op(100, xfx, [a, ',']).

% ---------------------------------------------------------------------------
%! ## 8.14.4 current_op/3 ISOcore#p103

:- test current_op_test1(Result)
   => ( sublist([[1100, ';'], [1050, '->'], [1000, ','], [200, '^']], Result) )
   # "[ISO] current_op/3".
current_op_test1(Result) :- findall([P, OP], current_op(P, xfy, OP), Result).

:- test current_op_test2
   + exception(error(domain_error(operator_priority, 1201), _))
   # "[ISO-sics] current_op/3".
current_op_test2 :- current_op(1201, _, _).

:- test current_op_test3
   + exception(error(domain_error(operator_specifier, yfy), _))
   # "[ISO-sics] current_op/3".
current_op_test3 :- current_op(_, yfy, _).

:- test current_op_test4
   + exception(error(type_error(atom, 0), _))
   # "[ISO-sics] current_op/3".
current_op_test4 :- current_op(_, 0, _).

:- test current_op_test5
   + exception(error(type_error(atom, 5), _))
   # "[ISO-sics] current_op/3".
current_op_test5 :- current_op(_, _, 5).

% ---------------------------------------------------------------------------
%! ## 8.14.5 char_conversion/2 ISOcore#p103

% NOTE: Incompatibilities in Ciao:
%
%  - Implement char_conversion/2 may be too costly. Unless it is
%    really necessary in some application, it will not be supported.
%
%    Recent searches in github only finds two uses! (which may be
%    implemented in other ways?):
%
%      https://github.com/JUrban/MPTP2
%      https://github.com/TPTPWorld/ServiceTools

% TODO:[JF] won't fix (unless somebody really need them)
char_conversion(_, _) :- fail.
current_char_conversion(_, _) :- fail.

:- test char_conversion_test1
   + (not_fails,
      setup(w_in(txt('a&b. &'),Prev)), cleanup(und(Prev)))
   # "[ISO] char_conversion/2: bug(wontfix)".

char_conversion_test1 :-
    with_chcvs(['&'-','], (read((a,b)), get_char(' '), get_char('&'))).

:- test char_conversion_test2
   + (not_fails,
      setup(w_in(txt('^b+c^'),Prev)), cleanup(und(Prev)))
   # "[ISO] char_conversion/2: bug(wontfix)".

char_conversion_test2 :-
    with_chcvs(['^'-''''], (read('b+c'), get_char(' '), get_char('^'))).

:- test char_conversion_test3
   + (not_fails,
      setup(w_in(txt("'A+c'+A."),Prev)), cleanup(und(Prev)))
   # "[ISO] char_conversion/2: bug(wontfix)".

char_conversion_test3 :-
    with_chcvs(['A'-'a'], read('A+c'+a)).

:- test char_conversion_test4(X, Y, Z) => (X=(a, a), Y='AAA', Z='a,a')
   + (not_fails,
      setup(w_in(txt("A&A. 'AAA'. ^A&A^."),Prev)), cleanup(und(Prev)))
# "[ISO] char_conversion/2: bug(wontfix)".

char_conversion_test4(X, Y, Z) :-
    with_chcvs(['&'-',','^'-'''','A'-'a'], (read(X), read(Y), read(Z))).

% TODO:[JF] weird test?
:- test char_conversion_test5
   + (not_fails,
      setup(w_in(txt("& ."),Prev)), cleanup(und(Prev)))
   # "[ISO] char_conversion/2: bug(wontfix)".

char_conversion_test5 :-
    with_chcvs(['&'-',','&'-'&'], (read('&'), \+current_char_conversion(_, _))).

:- test char_conversion_test6(X)
   + (not_fails,
      setup(w_in(txt("0'%%1."),Prev)), cleanup(und(Prev)))
# "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test6(X) :-
    with_chcvs(['%'-'+','^'-'\''], (read(X), X = (0'%) + 1)).

:- test char_conversion_test7(X) => (X=('%' +1))
   + (not_fails,
      setup(w_in(txt("'%'%1."),Prev)), cleanup(und(Prev)))
   # "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test7(X) :-
    with_chcvs(['%'-'+','^'-'\''], read(X)).

:- test char_conversion_test8(X) 
   + (not_fails,
      setup(w_in(txt('"%"%1.'),Prev)), cleanup(und(Prev)))
   # "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test8(X) :-
    with_chcvs(['%'-'+','^'-'\''], (read(X), X = "%" + 1)).

:- test char_conversion_test9(X) => ( X='.'(1, !))
   + (not_fails,
      setup(w_in(txt('1.#.'),Prev)), cleanup(und(Prev)))
# "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test9(X) :-
    with_ops([op(100, xfx, '.')], with_chcvs(['#'-'!'], read(X))).

:- test char_conversion_test10(X) => (X=('aa'+'bb^'))
   + (not_fails,
      setup(w_in(txt("^aa'+'bb^'."),Prev)), cleanup(und(Prev)))
# "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test10(X) :-
    with_chcvs(['%'-'+','^'-'\''], read(X)).

:- test char_conversion_test11(X, Y) => (X=(+), Y=(+))
   + (not_fails,
      setup(w_in(txt("+ .% ."),Prev)), cleanup(und(Prev)))
# "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test11(X, Y) :-
    with_chcvs(['%'-'+','^'-'\''],
                (set_prolog_flag(char_conversion, off),
                 read(X),
                 set_prolog_flag(char_conversion, on),
                 read(Y))).

:- test char_conversion_test12(X, Y) => (X=('-'('.+')), Y=end_of_file)
   + (not_fails,
      setup(w_in(txt("- .% ."),Prev)), cleanup(und(Prev)))
# "[ISO-sics] char_conversion/2: bug(wontfix)".

char_conversion_test12(X, Y) :-
    with_chcvs(['%'-'+','^'-'\''], (read(X), read(Y))).

%! ## 8.14.6 current_char_conversion/2 ISOcore#p104

:- test current_char_conversion_test1
   + (not_fails,
      setup(w_in(txt("'\\341\\'."),Prev)), cleanup(und(Prev)))
   # "[ISO] current_char_conversion/2: bug(wontfix)".

current_char_conversion_test1 :-
    read(Aacute),
    with_chcvs(['A'-'a', Aacute-'a'], findall(C, current_char_conversion(C, a), Result)),
    Result=['A', Aacute].

% ===========================================================================
%! # 8.15 Logic and control
%! ## 8.15.1 (\+)/1 ISOcore#p105

:- test not_test1 + fails
   # "[ISO] '\\+'/1".

not_test1 :- '\\+'(true).

:- test not_test2(X) : (X= !) + fails
   # "[ISO] '\\+'/1".

not_test2(X) :- '\\+'(X).

:- test not_test3(X) : (X= !)
   # "[ISO] '\\+'/1".

not_test3(X) :- '\\+'((X, fail)).

% TODO:[JF] ! illegal in -> part ; reimplement without findall/3 when fixed?
:-test not_test4(Result) => (Result=[1, 2])
  # "[ISO] '\\+'/1: bug()".

not_test4(Result) :- findall(X, ((X=1;X=2), '\\+'((!, fail))), Result).

:- test not_test5
   # "[ISO] '\\+'/1".

not_test5 :- '\\+'(4=5).

:- test not_test6(X) : (X=3)
	+ exception(error(type_error(callable, 3), Imp_def))
   # "[ISO] '\\+'/1".

not_test6(X) :- '\\+'(X).

:- test not_test7 + exception(error(instantiation_error, Imp_def))
   # "[ISO] '\\+'/1".

not_test7 :- '\\+'(_X).

:- test not_test8 + fails
   # "[ISO] '\\+'/1".

not_test8 :- '\\+'(X=f(X)).

%! ## 8.15.2 once/1 ISOcore#p105

:- test once_test1
   # "[ISO] once/1".

once_test1 :- once(!).

:- test once_test2(Result) => (Result=[1, 2])
   # "[ISO] once/1".

once_test2(Result) :- findall(X, (once(!), (X=1;X=2)), Result).

:- test once_test3
   # "[ISO] once/1".

once_test3 :- once(repeat).

:- test once_test4 + fails
   # "[ISO] once/1".

once_test4 :- once(fail).

:- test once_test5
   # "[ISO] once/1".

once_test5 :- once(X=f(X)).

:- test once_test6 + exception(error(type_error(callable, 3), _))
   # "[ISO-eddbali] once/1".

once_test6 :- once(3).

:- test once_test7 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] once/1".

once_test7 :- once(_).

% ---------------------------------------------------------------------------
%! ## 8.15.3 repeat/0 ISOcore#p105

% TODO:[JF] use try_n_sols?
% :- test repeat_test1 + current_output("hello").
% repeat_test1 :- repeat,write(hello),fails.

:- test repeat_test2 + fails
   # "[ISO] repeat/0".

repeat_test2 :- repeat, !, fail.

% ===========================================================================
%! # 8.16 Atomic term processing

% NOTE: Current issues in Ciao:
%
%  - Code and chars are still based on bytes rather than code points,
%    See `compilation_fact(fixed_utf8)`.

% ---------------------------------------------------------------------------
%! ## 8.16.1 atom_length/2 ISOcore#p106

:- test atomlength_test1(N) => (N=17)
   # "[ISO] atom_length/2".

atomlength_test1(N) :- atom_length('enchanted evening', N).

:- test atomlength_test2(N) => (N=17)
   # "[ISO] atom_length/2".

atomlength_test2(N) :- atom_length('enchanted\
 evening', N).

:- test atomlength_test3(N) => (N=0)
   # "[ISO] atom_length/2".

atomlength_test3(N) :- atom_length('', N).

:- test atomlength_test4(N) : (N=5) + fails
   # "[ISO] atom_length/2".

atomlength_test4(N) :- atom_length('scarlet', N).

:- test atomlength_test5
   + exception(error(instantiation_error, Imp_def))
   # "[ISO] atom_length/2".

atomlength_test5 :- atom_length(_Atom, 4).

:- test atomlength_test6
   + exception(error(type_error(atom, 1.23), Imp_def))
   # "[ISO] atom_length/2".

atomlength_test6 :- atom_length(1.23, 4).

:- test atomlength_test7
   + exception(error(type_error(integer, '4'), Imp_def))
   # "[ISO] atom_length/2".

atomlength_test7 :- atom_length(atom, '4').

% TODO:[JF] include missing check
:- test atomlength_test8
   + exception(error(domain_error(not_less_than_zero, -4), Imp_def))
   # "[ISO-eddbali] atom_length/2: bug()".

atomlength_test8 :- atom_length(atom, -4).

% TODO:[JF] requires utf8 codes
:- test atomlength_test9(L) => (L=11)
   + not_fails
   # "[ISO-sics] atom_length/2: bug()".
atomlength_test9(L) :- atom_length('Bartók Béla', L).

% ---------------------------------------------------------------------------
%! ## 8.16.2 atom_concat/2 ISOcore#p107

:- test atomconcat_test1(S3) => (S3='hello world')
   # "[ISO] atom_concat/2".

atomconcat_test1(S3) :- atom_concat('hello', ' world', S3).

:- test atomconcat_test2(T) => (T='small')
   # "[ISO] atom_concat/2".

atomconcat_test2(T) :- atom_concat(T, ' world', 'small world').

:- test atomconcat_test3 + fails
   # "[ISO] atom_concat/3".

atomconcat_test3 :- atom_concat('hello', ' world', 'small world').

:- test atomconcat_test4(Result)
   => ( S=[['', 'hello'],
           ['h', 'ello'],
           ['he', 'llo'],
           ['hel', 'lo'],
           ['hell', 'o'],
           ['hello', '']] )
   # "[ISO] atom_concat/2".

atomconcat_test4(Result) :-
    findall([T1, T2], atom_concat(T1, T2, 'hello'), Result).

:- test atomconcat_test5 + exception(error(instantiation_error, Imp_def))
   # "[ISO] atom_concat/2".

atomconcat_test5 :- atom_concat(small, _V2, _V4).

:- test atomconcat_test6 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] atom_concat/2".

atomconcat_test6 :- atom_concat(_T1, 'iso', _S).

:- test atomconcat_test7 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] atom_concat/2".

atomconcat_test7 :- atom_concat('iso', _T2, _S).

:- test atomconcat_test8(X, Y, S) : (X=f(a), Y='iso')
   + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] atom_concat/2".

atomconcat_test8(X, Y, S) :- atom_concat(X, Y, S).

:- test atomconcat_test9 + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] atom_concat/2".

atomconcat_test9 :- atom_concat('iso', f(a), _S).

:- test atomconcat_test10 + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] atom_concat/2".

atomconcat_test10 :- atom_concat(_T1, _T2, f(a)).

:- test atomconcat_test11(S) => (S='Bartók Béla')
   # "[ISO-sics] atom_concat/2".

atomconcat_test11(S) :- atom_concat('Bartók ', 'Béla', S).

:- test atomconcat_test12(T1) => (T1='Bartók ')
   # "[ISO-sics] atom_concat/2".

atomconcat_test12(T1) :- atom_concat(T1, 'Béla', 'Bartók Béla').

:- test atomconcat_test13(T2) => (T2='Béla')
   # "[ISO-sics] atom_concat/2".

atomconcat_test13(T2) :- atom_concat('Bartók ', T2, 'Bartók Béla').

% TODO:[JF] corrupted data breaks unit tests runner
:- test atomconcat_test14(Result)
   => ( Result=[['', 'Pécs'],
                ['P', 'écs'],
                ['Pé', 'cs'],
                ['Péc', 's'],
		['Pécs', '']] )
   + not_fails
   # "[ISO-sics] atom_concat/2: bug()".
:- if(defined(fixed_utf8)).
atomconcat_test14(Result) :-
    findall([T1, T2], atom_concat(T1, T2, 'Pécs'), Result).
:- else.
atomconcat_test14(_Result) :- throw(bug).
:- endif.

% ---------------------------------------------------------------------------
%! ## 8.16.3 sub_atom/5 ISOcore#p108

:- test subatom_test1(S) => (S='abrac')
   # "[ISO] sub_atom/5".

subatom_test1(S) :- sub_atom(abracadabra, 0, 5, _, S).

:- test subatom_test2(S) => (S='dabra')
   # "[ISO] sub_atom/5".

subatom_test2(S) :- sub_atom(abracadabra, _, 5, 0, S).

:- test subatom_test3(L, S) => (Y=5, S='acada')
   # "[ISO] sub_atom/5".

subatom_test3(L, S) :- sub_atom(abracadabra, 3, L, 3, S).

:- test subatom_test4(Result) => (Result=[[0, 9], [7, 2]])
   # "[ISO] sub_atom/5".

subatom_test4(Result) :-
    findall([B, A], sub_atom(abracadabra, B, 2, A, ab), Result).

:- test subatom_test5(S) => (S='an')
   # "[ISO] sub_atom/5".

subatom_test5(S) :- sub_atom(banana, 3, 2, _, S).

:- test subatom_test6(Result) => (Result=['cha', 'har', 'ari', 'rit', 'ity'])
   # "[ISO] sub_atom/5".

subatom_test6(Result) :-
    findall(S, sub_atom(charity, _, 3, _, S), Result).

:- test subatom_test7(Result)
   => ( Result=[[0, 0, ''],
                [0, 1, 'a'],
                [0, 2, 'ab'],
                [1, 0, ''],
		[1, 1, 'b'],
                [2, 0, '']] )
   # "[ISO] sub_atom/5".

subatom_test7(Result) :-
    findall([Start, Length, S], sub_atom(ab, Start, Length, _, S), Result).

:- test subatom_test8
   + exception(error(instantiation_error, _))
   # "[ISO-eddbali] sub_atom/5".

subatom_test8 :- sub_atom(_W, 3, 2, _Z, _S).

:- test subatom_test9
   + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] sub_atom/5".

subatom_test9 :- sub_atom(f(a), 2, 2, _Z, _S).

% TODO:[JF] missing type check on 5th argument
:- test subatom_test10
   + exception(error(type_error(atom, 2), _))
   # "[ISO-eddbali] sub_atom/5: bug()".

subatom_test10 :- sub_atom('Banana', 4, 2, _Z, 2).

% TODO:[JF] missing type check on 2nd argument
:- test subatom_test11
   + exception(error(type_error(integer, a), _))
   # "[ISO-eddbali] sub_atom/5: bug()".

subatom_test11 :- sub_atom('Banana', a, 2, _Z, _S).

% TODO:[JF] missing type check on 3rd argument
:- test subatom_test12
   + exception(error(type_error(integer, n), _))
   # "[ISO-eddbali] sub_atom/5: bug()".

subatom_test12 :- sub_atom('Banana', 4, n, _Z, _S).

% TODO:[JF] missing type check on 4th argument
:- test subatom_test13
   + exception(error(type_error(integer, m), _))
   # "[ISO-eddbali] sub_atom/5: bug()".

subatom_test13 :- sub_atom('Banana', 4, _Y, m, _S).

% TODO:[JF] missing type check on 2nd argument
:- test subatom_test14
   + exception(error(domain_error(not_less_than_zero, -2), _))
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test14 :- sub_atom('Banana', -2, 3, 4, _S).

% TODO:[JF] missing type check on 3rd argument
:- test subatom_test15
   + exception(error(domain_error(not_less_than_zero, -3), _))
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test15 :- sub_atom('Banana', 2, -3, 4, _S).

% TODO:[JF] missing type check on 4th argument
:- test subatom_test16
   + exception(error(domain_error(not_less_than_zero, -4), _))
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test16 :- sub_atom('Banana', 2, 3, -4, _S).

:- test subatom_test17(Z) => (Z=1)
   # "[ISO-sics] sub_atom/5".

subatom_test17(Z) :- sub_atom('Banana', 2, 3, Z, 'nan').

:- test subatom_test18(X) => (X=2)
   # "[ISO-sics] sub_atom/5".

subatom_test18(X) :- sub_atom('Banana', X, 3, 1, 'nan').

:- test subatom_test19(Y) => (Y=3)
   # "[ISO-sics] sub_atom/5".

subatom_test19(Y) :- sub_atom('Banana', 2, Y, 1, 'nan').

:- test subatom_test20(Y, Z) => (Y=3, Z=1)
   # "[ISO-sics] sub_atom/5".

subatom_test20(Y, Z) :- sub_atom('Banana', 2, Y, Z, 'nan').

:- test subatom_test21(X, Y) => (X=2, Y=3)
   # "[ISO-sics] sub_atom/5".

subatom_test21(X, Y) :- sub_atom('Banana', X, Y, 1, 'nan').

:- test subatom_test22 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test22 :- sub_atom('Banana', 2, 3, 1, 'ana').

:- test subatom_test23 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test23 :- sub_atom('Banana', 2, 3, 2, 'nan').

:- test subatom_test24 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test24 :- sub_atom('Banana', 2, 3, 2, _S).

:- test subatom_test25 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test25 :- sub_atom('Banana', 2, 3, 1, 'anan').

:- test subatom_test26 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test26 :- sub_atom('Banana', 0, 7, 0, _S).

:- test subatom_test27 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test27 :- sub_atom('Banana', 7, 0, 0, _S).

:- test subatom_test28 + fails
   # "[ISO-sics] sub_atom/5".

subatom_test28 :- sub_atom('Banana', 0, 0, 7, _S).

% TODO:[JF] fix utf8 support
:- test subatom_test31(Z, S) => (Z=5, S='ók')
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test31(Z, S) :- sub_atom('Bartók Béla', 4, 2, Z, S).

% TODO:[JF] fix utf8 support
:- test subatom_test32(Y, S) => (Y=2, S='ók')
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test32(Y, S) :- sub_atom('Bartók Béla', 4, Y, 5, S).

% TODO:[JF] fix utf8 support
:- test subatom_test33(X, S) => (X=4, S='ók')
   # "[ISO-sics] sub_atom/5: bug()".

subatom_test33(X, S) :- sub_atom('Bartók Béla', X, 2, 5, S).

:- test subatom_test34(Result)
   => (Result=[[0, 2, 'Pé'], [1, 1, 'éc'], [2, 0, 'cs']])
   + not_fails
   # "[ISO-sics] sub_atom/5: bug()".

:- if(defined(fixed_utf8)).
subatom_test34(Result) :-
    findall([X, Z, S], sub_atom('Pécs', X, 2, Z, S), Result).
:- else.
subatom_test34(_Result) :- throw(bug).
:- endif.

:- test subatom_test35(Result)
   => (Result=[[0, 4, 7], [7, 4, 0]])
   # "[ISO-sics] sub_atom/5".

subatom_test35(Result) :-
    findall([X, Y, Z], sub_atom('abracadabra', X, Y, Z, abra), Result).

% ---------------------------------------------------------------------------
%! ## 8.16.4 atom_chars/2 ISOcore#p108

:- test atomchars_test1(L) => (L=[])
   # "[ISO] atom_chars/2".

atomchars_test1(L) :- atom_chars('', L).

:- test atomchars_test2(L) => (L=['[', ']'])
   # "[ISO] atom_chars/2".

atomchars_test2(L) :- atom_chars([], L).

:- test atomchars_test3(L) => (L=[''''])
   # "[ISO] atom_chars/2".

atomchars_test3(L) :- atom_chars('''', L).

:- test atomchars_test4(L) => (L=['a', 'n', 't'])
   # "[ISO] atom_chars/2".

atomchars_test4(L) :- atom_chars('ant', L).

:- test atomchars_test5(Str) => (Str='sop')
   # "[ISO] atom_chars/2".

atomchars_test5(Str) :- atom_chars(Str, ['s', 'o', 'p']).

:- test atomchars_test6(X) => (X=['o', 'r', 't', 'h'])
   # "[ISO] atom_chars/2".

atomchars_test6(X) :- atom_chars('North', ['N'|X]).

:- test atomchars_test7 + fails
   # "[ISO] atom_chars/2".

atomchars_test7 :- atom_chars('soap', ['s', 'o', 'p']).

% TODO:[JF] missing checks
:- test atomchars_test8
   + exception(error(instantiation_error, _))
   # "[ISO] atom_chars/2: bug()".

atomchars_test8 :- atom_chars(_X, _Y).

:- test atomchars_test9
   + exception(error(instantiation_error, _))
   # "[ISO-eddbali] atom_chars/2".

atomchars_test9 :- atom_chars(_A, [a, _E, c]).

% TODO:[JF] missing checks
:- test atomchars_test10
   + exception(error(instantiation_error, _))
   # "[ISO-eddbali] atom_chars/2: bug()".

atomchars_test10 :- atom_chars(_A, [a, b|_L]).

:- test atomchars_test11
   + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] atom_chars/2".

atomchars_test11 :- atom_chars(f(a), _L).

% TODO:[JF] wrong checks
:- test atomchars_test12
   + exception(error(type_error(list, iso), _))
   # "[ISO-eddbali] atom_chars/2: bug()".

atomchars_test12 :- atom_chars(_A, iso).

% TODO:[JF] wrong checks
:- test atomchars_test13
   + exception(error(type_error(character, f(b)), _))
   # "[ISO-eddbali] atom_chars/2: bug()".

atomchars_test13 :- atom_chars(_A, [a, f(b)]).

% TODO:[JF] fix utf8 support
:- test atomchars_test14(L) => (L=['P', 'é', 'c', 's'])
   + not_fails
   # "[ISO-sics] atom_chars/2: bug()".

:- if(defined(fixed_utf8)).
atomchars_test14(L) :- atom_chars('Pécs', L).
:- else.
atomchars_test14(_L) :- throw(bug).
:- endif.

% TODO:[JF] fix utf8 support
:- test atomchars_test15(A) => (A='Pécs')
   + not_fails
   # "[ISO-sics] atom_chars/2: bug()".

atomchars_test15(A) :- atom_chars(A, ['P', 'é', 'c', 's']).

% ---------------------------------------------------------------------------
%! ## 8.16.5 atom_codes/2 ISOcore#p109

:- test atomcodes_test1(L) => (L=[])
   # "[ISO] atom_codes/2".

atomcodes_test1(L) :- atom_codes('', L).

:- test atomcodes_test2(L) => (L=[0'[, 0']])
   # "[ISO] atom_codes/2".

atomcodes_test2(L) :- atom_codes([], L).

:- test atomcodes_test3(L) => (L=[0''']) % '
   # "[ISO] atom_codes/2".

atomcodes_test3(L) :- atom_codes('''', L).

:- test atomcodes_test4(L) => (L=[0'a, 0'n, 0't])
   # "[ISO] atom_codes/2".

atomcodes_test4(L) :- atom_codes('ant', L).

:- test atomcodes_test5(Str) => (Str='sop')
   # "[ISO] atom_codes/2".

atomcodes_test5(Str) :- atom_codes(Str, [0's, 0'o, 0'p]).

:- test atomcodes_test6(X) => (X=[0'o, 0'r, 0't, 0'h])
   # "[ISO] atom_codes/2".

atomcodes_test6(X) :- atom_codes('North', [0'N|X]).

:- test atomcodes_test7 + fails
   # "[ISO] atom_codes/2".

atomcodes_test7 :- atom_codes('soap', [0's, 0'o, 0'p]).

:- test atomcodes_test8
   + exception(error(instantiation_error, _))
   # "[ISO] atom_codes/2".

atomcodes_test8 :- atom_codes(_X, _Y).

% TODO:[JF] update tests?
%%% Errors of atom_codes are corrected in both
%%% * ISO/IEC 13211-1:1995/Cor.1:2007(E) (page 4)
%%% * ISO/IEC 13211-1:1995/Cor.2:2012(E) (page 18)

:- test atomcodes_extra_errortest_1
   + exception(error(instantiation_error, _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_1 :- atom_codes(_, [1|_]).

:- test atomcodes_extra_errortest_2
   + exception(error(type_error(list, a), _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_2 :- atom_codes(_, a).

:- test atomcodes_extra_errortest_3
   + exception(error(instantiation_error, _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_3 :- atom_codes(_, [1,_]).

:- test atomcodes_extra_errortest_4
   + exception(error(type_error(integer, a), _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_4 :- atom_codes(_, [1,a]).

:- test atomcodes_extra_errortest_5
   + exception(error(representation_error(character_code), _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_5 :- atom_codes(_, [-1]).

:- test atomcodes_extra_errortest_6
   + exception(error(type_error(atom, 1), _ImplDep))
   # "[ISO] atom_codes/2".

atomcodes_extra_errortest_6 :- atom_codes(1, [0'1]).

:- test atomcodes_test9
   + exception(error(type_error(atom, f(a)), _))
   # "[ISO-eddbali] atom_codes/2".

atomcodes_test9 :- atom_codes(f(a), _L).

:- test atomcodes_test10
   + exception(error(type_error(list, 0'x), _))
   # "[ISO-eddbali] atom_codes/2".

atomcodes_test10 :- atom_codes(_, 0'x).

:- test atomcodes_test11
   + exception(error(representation_error(character_code), _))
   # "[ISO-eddbali] atom_codes/2".

atomcodes_test11 :- atom_codes(_X, [0'i, 0's, -1]).

% TODO:[JF] fix utf8 support
:- test atomcodes_test12(L) => (L=[0'P,0'é,0'c,0's])
   # "[ISO-sics] atom_codes/2: bug".

atomcodes_test12(L) :- atom_codes('Pécs',L).

% TODO:[JF] fix utf8 support
:- test atomcodes_test13(A) => (A='Pécs')
   # "[ISO-sics] atom_codes/2: bug".

atomcodes_test13(A) :- atom_codes(A,[0'P,0'é,0'c,0's]).

% TODO:[JF] missing atomcodes_test14 (max_char_code)
% TODO:[JF] missing atomcodes_test15 (max_char_code)

% TODO:[JF] fix type error
:- test atomcodes_test16
   + exception(error(representation_error(character_code), _))
   # "[ISO-sics] atom_codes/2: bug()".

atomcodes_test16 :- atom_codes(_A, [a, b, c]).

% ---------------------------------------------------------------------------
%! ## 8.16.6 char_code/2 ISOcore#p110

:- test charcode_test1(Code) => (Code=0'a)
   # "[ISO] char_code/2".

charcode_test1(Code) :- char_code('a', Code).

:- test charcode_test2(Str) => (Str=c)
   # "[ISO] char_code/2".

charcode_test2(Str) :- char_code(Str, 99).

:- test charcode_test3(Str) => (Str=c)
   # "[ISO] char_code/2".

charcode_test3(Str) :- char_code(Str, 0'c).

:- test charcode_test4(X)
   # "[ISO] char_code/2".

charcode_test4(X) :- char_code(X, 163).

:- test charcode_test5
   # "[ISO] char_code/2".

charcode_test5 :- char_code('b', 0'b).

% TODO:[JF] missing type check
:- test charcode_test6 + exception(error(type_error(character, ab), _))
   # "[ISO] char_code/2: bug()".

charcode_test6 :- char_code('ab', _Int).

:- test charcode_test7 + exception(error(instantiation_error, _))
   # "[ISO] char_code/2".

charcode_test7 :- char_code(_C, _I).

:- test charcode_test8 + exception(error(type_error(integer, x), _))
   # "[ISO-eddbali] char_code/2".

charcode_test8 :- char_code(a, x).

:- test charcode_test9
	+ exception(error(representation_error(character_code), _))
   # "[ISO-eddbali] char_code/2".

charcode_test9 :- char_code(_Str, -2).

% ---------------------------------------------------------------------------
%! ## 8.16.7 number_chars/2 ISOcore#p111

% NOTE: Current issues in Ciao:
%
%  - number_chars/2 and number_codes/2 do not accept leading blanks
%  - number_chars/2 and number_codes/2 do not parse hex, bin, oct numbers 

:- test numberchars_test1(L) => (L=['3', '3'])
   # "[ISO] number_chars/2".
numberchars_test1(L) :- number_chars(33, L).

:- test numberchars_test2
   # "[ISO] number_chars/2".
numberchars_test2 :- number_chars(33, ['3', '3']).

:- test numberchars_test3(N) => (N=33.0)
   # "[ISO] number_chars/2".
numberchars_test3(N) :- number_chars(33.0, Y), number_chars(N, Y).

:- test numberchars_test4(X) => (near(X, 3.3, 0.02))
   # "[ISO] number_chars/2".
numberchars_test4(X) :- number_chars(X, ['3', '.', '3', 'E', +, '0']).

:- test numberchars_test5 + fails
   # "[ISO] number_chars/2".
numberchars_test5 :- number_chars(3.3, ['3', '.', '3', 'E', +, '0']).

:- test numberchars_test6(A) => (A=(-25))
   # "[ISO] number_chars/2".
numberchars_test6(A) :- number_chars(A, [-, '2', '5']).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks
:- test numberchars_test7(A) => (A=3)
   + not_fails
   # "[ISO] number_chars/2: bug()".
numberchars_test7(A) :- number_chars(A, ['\n', ' ', '3']).

% TODO:[JF] it should report syntax error
:- test numberchars_test8
   + exception(error(syntax_error(_), _))
   # "[ISO] number_chars/2: bug()".
numberchars_test8 :- number_chars(_A, ['3', ' ']).

% TODO:[JF] number_chars/2 and number_codes/2 should accept hex numbers
:- test numberchars_test9(A) => (A=15)
   + not_fails
   # "[ISO] number_chars/2: bug()".
numberchars_test9(A) :- number_chars(A, ['0', x, f]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept codes
:- test numberchars_test10(A) => (A=0'a)
   + not_fails
   # "[ISO] number_chars/2: bug()".
numberchars_test10(A) :- number_chars(A, ['0', '''', a]).

:- test numberchars_test11(A) => (A=4.2)
   # "[ISO] number_chars/2".
numberchars_test11(A) :- number_chars(A, ['4', '.', '2']).

:- test numberchars_test12(A) => (A=4.2)
   # "[ISO] number_chars/2".
numberchars_test12(A) :- number_chars(A, ['4', '2', '.', '0', 'e', '-', '1']).

:- test numberchars_test13 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] number_chars/2".
numberchars_test13 :- number_chars(_X, _Y).

:- test numberchars_test14 + exception(error(type_error(number, a), _))
   # "[ISO-eddbali] number_chars/2".
numberchars_test14 :- number_chars(a, _Y).

% TODO:[JF] missing type check
:- test numberchars_test15
   + exception(error(type_error(list, 4), _))
   # "[ISO-eddbali] number_chars/2: bug()".
numberchars_test15 :- number_chars(_, 4).

% TODO:[JF] fix type check
:- test numberchars_test16
   + exception(error(type_error(character, 2), _))
   # "[ISO-eddbali] number_chars/2: bug()".
numberchars_test16 :- number_chars(_A, ['4', 2]).

:- test numberchars_test17
   + exception(error(instantiation_error, _))
   # "[ISO-sics] number_chars/2".
numberchars_test17 :- number_chars(_A, [a|_]).

:- test numberchars_test18
   + exception(error(instantiation_error, _))
   # "[ISO-sics] number_chars/2".
numberchars_test18 :- number_chars(_A, [a, _]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and oct numbers
:- test numberchars_test19(A) => (A=9)
   + not_fails
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test19(A) :- number_chars(A, [' ', '0', 'o', '1', '1']).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and hex numbers
:- test numberchars_test20(A) => (A=17)
   + not_fails
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test20(A) :- number_chars(A, [' ', '0', 'x', '1', '1']).               

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and bin numbers
:- test numberchars_test21(A) => (A=3)
   + not_fails
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test21(A) :- number_chars(A, [' ', '0', 'b', '1', '1']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong oct numbers
:- test numberchars_test22
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test22 :- number_chars(_A, ['0', 'o', '8']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong bin numbers
:- test numberchars_test23
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test23 :- number_chars(_A, [' ', 'b', '2']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong hex numbers
:- test numberchars_test24
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test24 :- number_chars(_A, [' ', 'x', 'g']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong numbers
:- test numberchars_test25
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test25 :- number_chars(_A, ['á']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong numbers
:- test numberchars_test26
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test26 :- number_chars(_A, ['a']).

% TODO:[JF] number_chars/2 and number_codes/2 should report wrong numbers
:- test numberchars_test27
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_chars/2: bug()".
numberchars_test27 :- number_chars(_A, ['0', 'x', '0', '.', '0']).

% ---------------------------------------------------------------------------
%! ## 8.16.8 number_codes/2 ISOcore#p112

% NOTE: see issues in number_chars/2

:- test numbercodes_test1(L) => (L=[0'3, 0'3])
   # "[ISO] number_codes/2".
numbercodes_test1(L) :- number_codes(33, L).

:- test numbercodes_test2
   # "[ISO] number_codes/2".
numbercodes_test2 :- number_codes(33, [0'3, 0'3]).

:- test numbercodes_test3(Y) => (number_codes(N, Y), N=33.0)
   # "[ISO] number_codes/2".
numbercodes_test3(Y) :- number_codes(33.0, Y).

:- test numbercodes_test4
   # "[ISO] number_codes/2".
numbercodes_test4 :- number_codes(33.0, [0'3|_L]).

:- test numbercodes_test5(A) => (A=(-25))
   # "[ISO] number_codes/2".
numbercodes_test5(A) :- number_codes(A, [0'-, 0'2, 0'5]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and bin numbers
:- test numbercodes_test6(A) => (A=3)
   + not_fails
   # "[ISO] number_codes/2: bug()".
numbercodes_test6(A) :- number_codes(A, [0' , 0'3]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept hex numbers
:- test numbercodes_test7(A) => (A=15)
   + not_fails
   # "[ISO] number_codes/2: bug()".
numbercodes_test7(A) :- number_codes(A, [0'0, 0'x, 0'f]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept char code numbers
:- test numbercodes_test8(A) => (A=0'a)
   + not_fails
   # "[ISO] number_codes/2: bug()".
numbercodes_test8(A) :- number_codes(A, [0'0, 0''', 0'a]).

:- test numbercodes_test9(A) => (A=4.2)
   # "[ISO] number_codes/2".
numbercodes_test9(A) :- number_codes(A, [0'4, 0'., 0'2]).

:- test numbercodes_test10(A) => (A=4.2)
   # "[ISO] number_codes/2".
numbercodes_test10(A) :- number_codes(A, [0'4, 0'2, 0'., 0'0, 0'e, 0'-, 0'1]).

:- test numbercodes_test11 + exception(error(instantiation_error, _))
   # "[ISO-eddbali] number_codes/2".
numbercodes_test11 :- number_codes(_, _).

:- test numbercodes_test12 + exception(error(type_error(number, a), _))
   # "[ISO-eddbali] number_codes/2".
numbercodes_test12 :- number_codes(a, _Y).

:- test numbercodes_test13 + exception(error(type_error(list, 4), _))
   # "[ISO-eddbali] number_codes/2".
numbercodes_test13 :- number_codes(_X, 4).

:- test numbercodes_test14
   + exception(error(representation_error(character_code), _))
   # "[ISO-eddbali] number_codes/2".
numbercodes_test14 :- number_codes(_X, [0'4, -1]).

:- test numbercodes_test15 + exception(error(instantiation_error, _))
   # "[ISO-sics] number_codes/2".
numbercodes_test15 :- number_codes(_X, [0'a|_]).

:- test numbercodes_test16 + exception(error(instantiation_error, _))
   # "[ISO-sics] number_codes/2".
numbercodes_test16 :- number_codes(_X, [0'a, _]).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and bin numbers
:- test numbercodes_test17(A, S) => (A=273, S=[50, 55, 51])
   + not_fails
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test17(A, S) :-
    number_chars(A, [' ', '0', 'x', '1', '1', '1']), % TODO:[JF] fixme
    number_codes(A, S).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and oct numbers
:- test numbercodes_test18(A, S) => (A=73, S=[55, 51])
   + not_fails
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test18(A, S) :-
    number_chars(A, [' ', '0', 'o', '1', '1', '1']), % TODO:[JF] fixme
    number_codes(A, S).

% TODO:[JF] number_chars/2 and number_codes/2 should accept leading blanks and bin numbers
:- test numbercodes_test19(A, S) => (A=7, S=[55])
   + not_fails
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test19(A, S) :-
    number_chars(A, [' ', '0', 'b', '1', '1', '1']), % TODO:[JF] fixme
    number_codes(A, S).

% TODO:[JF] fix
:- test numbercodes_test20(A) => (A=10)
   + not_fails
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test20(A) :- number_codes(A, "0'\\n").

% TODO:[JF] fix
:- test numbercodes_test21
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test21 :- number_codes(_X, "ä").

% TODO:[JF] fix
:- test numbercodes_test22
   + exception(error(syntax_error(_), _))
   # "[ISO-sics] number_codes/2: bug()".
numbercodes_test22 :- number_codes(_A, [0'0, 0'x, 0'0, 0'., 0'0]).

:- test numbercodes_extratest_1
   + exception(error(instantiation_error, _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_1 :- number_codes(_, [1|_]).

:- test numbercodes_extratest_2
   + exception(error(type_error(list, a), _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_2 :- number_codes(_, a).

:- test numbercodes_extratest_3
   + exception(error(instantiation_error, _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_3 :- number_codes(_, [1,_]).

:- test numbercodes_extratest_4
   + exception(error(type_error(integer, a), _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_4 :- number_codes(_, [1,a]).

:- test numbercodes_extratest_5
   + exception(error(representation_error(character_code), _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_5 :- number_codes(_, [-1]).

:- test numbercodes_extratest_6
   + exception(error(type_error(number, '1'), _))
   # "[ISO-ciao] number_codes/2".
numbercodes_extratest_6 :- number_codes('1', [0'1]).

% ===========================================================================
%! # 8.17 Implementation defined hooks
%! ## 8.17.1 set_prolog_flag/2 ISOcore#p112

% NOTE: Current issues in Ciao:
%
%  - 'debug' prolog flag is not implemented (off: turn off debugger,
%    on: switch on debugger in trace mode, if it was turned off)
%  - instantiation, type or domain errors
%  - modify errors on read-only flags

:- test setpflag_test1
   + not_fails
   # "[ISO] set_prolog_flag/2".
setpflag_test1 :-
    with_pflag(unknown, fail, current_prolog_flag(unknown, What)),
    What = fail.

% TODO:[JF] instantiation error
:- test setpflag_test2
   + exception(error(instantiation_error, _))
   # "[ISO] set_prolog_flag/2: bug()".
setpflag_test2 :- set_prolog_flag(_X, off).

% TODO:[JF] type error
:- test setpflag_test3
   + exception(error(type_error(atom, 5), _))
   # "[ISO] set_prolog_flag/2: bug()".
setpflag_test3 :- set_prolog_flag(5, decimals).

% TODO:[JF] domain error for unknown flag
:- test setpflag_test4
   + exception(error(domain_error(prolog_flag, date), _))
   # "[ISO] set_prolog_flag/2: bug()".
setpflag_test4 :- set_prolog_flag(date, 'July 1988').

% TODO:[JF] flag_value term should be flag name + flag value
:- test setpflag_test5
   + exception(error(domain_error(flag_value, debug+trace), _))
   # "[ISO] set_prolog_flag/2: bug()".
setpflag_test5 :- set_prolog_flag(debug, trace).

% TODO:[JF] modify error if flag is read-only
:- test setpflag_test6
   + exception(error(permission_error(modify, flag, max_arity), _))
   # "[ISO-eddbali] set_prolog_flag/2: bug()".
setpflag_test6 :- set_prolog_flag(max_arity, 40).

% ---------------------------------------------------------------------------
%! ## 8.17.2 current_prolog_flag/2 ISOcore#p113

% NOTE: Current issues in Ciao:
%
%  - some tests depend on unimplemented flags
%  - instantiation, type or domain errors

% TODO:[JF] add this flag?
:- test currentflag_test1
   + not_fails
   # "[ISO] current_prolog_flag/2: bug()".
currentflag_test1 :- current_prolog_flag(debug, off).

% TODO:[JF] arbitrary list
:- test currentflag_test2(Result)
   => (sublist([[max_arity,255],[unknown,error]], Result))
   # "[ISO] current_prolog_flag/2".
currentflag_test2(Result) :-
    findall([X, Y], current_prolog_flag(X, Y), Result).

:- test currentflag_test3
   + exception(error(type_error(atom, 5), _))
   # "[ISO] current_prolog_flag/2: bug()".
currentflag_test3 :- current_prolog_flag(5, _Y).

:- test currentflag_test4
   + not_fails
   # "[ISO-eddbali] current_prolog_flag/2".
currentflag_test4 :-
    with_pflag(unknown, warning, current_prolog_flag(unknown, warning)).

:- test currentflag_test5
   + fails
   # "[ISO-eddbali] current_prolog_flag/2".
currentflag_test5 :-
    with_pflag(unknown, warning, current_prolog_flag(unknown, error)).

% TODO:[JF] add this flag?
:- test currentflag_test6(V)
   => (V = off)
   + not_fails
   # "[ISO-eddbali] current_prolog_flag/2: bug()".
currentflag_test6(V) :- current_prolog_flag(debug, V).

% TODO:[JF] domain errors
:- test currentflag_test7
   + exception(error(domain_error(prolog_flag, warning), _))
   # "[ISO-eddbali] current_prolog_flag/2: bug()".
currentflag_test7 :- current_prolog_flag(warning, _Y).

% TODO:[JF] type error
:- test currentflag_test8
   + exception(error(type_error(atom, 1 + 2), _))
   # "[ISO-eddbali] current_prolog_flag/2: bug()".
currentflag_test8 :- current_prolog_flag(1 + 2, flag).

% ---------------------------------------------------------------------------
%! ## 8.17.3 halt/0 ISOcore#p113

% TODO: Let us trust that halt/0 and halt/1 effectively stops the process.
%   Testing those predicates require new comp properties. (JF)
:- if(defined(testing_halt)).
:- test halt_test1
   # "[ISO] halt/0".

halt_test1 :- halt.
:- endif.

%! ## 8.17.4 halt/1 ISOcore#p113

:- if(defined(testing_halt)).
:- test halt_test2
   # "[ISO] halt/1".

halt_test2 :- halt(1).
:- endif.

:- test halt_test3
   + exception(error(type_error(integer, a), _))
   # "[ISO] halt/1".

halt_test3 :- halt(a).

:- test halt_test4
   + exception(error(instantiation_error, _))
   # "[ISO-eddbali] halt/1".

halt_test4 :- halt(_).

% ===========================================================================
%! # 9.1 Simple arithmetic functors

% NOTE: Current issues in Ciao:
%
%  - Culprit term in type error evaluable must report `N/A` instead of
%    the culprit term (e.g., `type_error(evaluable, foo/3)` intead of
%    `type_error(evaluable, foo(a,b,c))`)
%    (see `"fix internals:error_term for type_error(evaluable)"` comments)
%  - Some arithmetic functors are not implemented (see comments).
%  - `xor/2` is implemented as `(#)/2`.
%
% NOTE: Incompatibilities in Ciao:
%
%  - For floating point computations, Ciao supports `0.Inf`, `-0.Inf`
%    and `0.Nan`, so we do not throw some `undefined` errors.
%    Other Prologs like GNU Prolog seems to do the same (with a
%    different representation).

%! ## 9.1.7 is/2 ISOcore#p117

:- test eval_test1(S) => (S=42)
   # "[ISO] arith '+'/2".

eval_test1(S) :- S is '+'(7, 35).

:- test eval_test2(S) => (S=14)
   # "[ISO] arith '+'/2".

eval_test2(S) :- S is '+'(0, 3 +11).

:- test eval_test3(S) => (near(S, 14.2000, 0.0001))
   # "[ISO] arith '+'/2".

eval_test3(S) :- S is '+'(0, 3.2 +11).

:- test eval_test4(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '+'/2".

eval_test4(S) :- S is '+'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '+'/2: bug()".

eval_test5(S) :- S is '+'(foo, 77).

:- test eval_test6(S) => (S=(-7))
   # "[ISO] arith '-'/2".

eval_test6(S) :- S is '-'(7).

:- test eval_test7(S) => (S=(8))
   # "[ISO] arith '-'/2".

eval_test7(S) :- S is '-'(3 -11).

:- test eval_test8(S) => (near(S, 7.8000, 0.0001))
   # "[ISO] arith '-'/2".

eval_test8(S) :- S is '-'(3.2 -11).

:- test eval_test9(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '-'/2".

eval_test9(S) :- S is '-'(_N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test10(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '-'/2: bug()".

eval_test10(S) :- S is '-'(foo).

:- test eval_test11(S) => (S=(-28))
   # "[ISO] arith '-'/2".

eval_test11(S) :- S is '-'(7, 35).

:- test eval_test12(S) => (S=6)
   # "[ISO] arith '-'/2".

eval_test12(S) :- S is '-'(20, 3 +11).

:- test eval_test13(S) => (near(S, -14.2000, 0.0001))
   # "[ISO] arith '-'/2".

eval_test13(S) :- S is '-'(0, 3.2 +11).

:- test eval_test14(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '-'/2".

eval_test14(S) :- S is '-'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test15(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '-'/2: bug()".

eval_test15(S) :- S is '-'(foo, 77).

:- test eval_test16(S) => (S=245)
   # "[ISO] arith '*'/2".

eval_test16(S) :- S is '*'(7, 35).

:- test eval_test17(S) : (X=0, Y=(3 +11)) => (S=0)
   # "[ISO] arith '*'/2".

eval_test17(S) :- S is '*'(0, 3 +11).

:- test eval_test18(S) => (near(S, 21.3, 0.0001))
   # "[ISO] arith '*'/2".

eval_test18(S) :- S is '*'(1.5, 3.2 +11).

:- test eval_test19(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '*'/2".

eval_test19(S) :- S is '*'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test20(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '*'/2: bug()".

eval_test20(S) :- S is '*'(foo, 77).

:- test eval_test21(S) => (S=0)
   # "[ISO-cor1] arith '//'/2".

eval_test21(S) :- S is '//'(7, 35).

:- test eval_test22(S) => (near(S, 0.2000, 0.0001))
   # "[ISO] arith '//'/2".

eval_test22(S) :- S is '/'(7.0, 35).

:- test eval_test23(S) => (S=10)
   # "[ISO-cor1] arith '//'/2".

eval_test23(S) :- S is '//'(140, 3+11).

:- test eval_test24(S) => (near(S, 1.42, 0.0001))
   # "[ISO-cor1] arith '/'/2".

eval_test24(S) :- S is '/'(20.164, 3.2+11).

:- test eval_test25(S)
   # "[ISO] arith '//'/2".

eval_test25(S) :- S is '//'(7, -3).

:- test eval_test26(S)
   # "[ISO] arith '//'/2".

eval_test26(S) :- S is '//'(-7, 3).

:- test eval_test27(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '/'/2".

eval_test27(S) :- S is '/'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test28(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '/'/2: bug()".

eval_test28(S) :- S is '/'(foo, 77).

% TODO:[JF] we support dividing 0.Inf
:- test eval_test29(S)
   + exception(error(evaluation_error(zero_divisor), _))
   # "[ISO-sics] arith '/'/2: bug(wontfix)".

eval_test29(S) :- S is '/'(3, 0).

% TODO:[JF] we support dividing 0.Inf
:- test eval_test29b(S)
   + exception(error(evaluation_error(zero_divisor), _))
   # "[ISO-ciao] arith '//'/2".

eval_test29b(S) :- S is '//'(3, 0).

:- test eval_test30(S) => (S=1)
   # "[ISO] arith mod/2".

eval_test30(S) :- S is mod(7, 3).

:- test eval_test31(S) => (S=0)
   # "[ISO] arith mod/2".

eval_test31(S) :- S is mod(0, 3 +11).

:- test eval_test32(S) => (S=(-1))
   # "[ISO] arith mod/2".

eval_test32(S) :- S is mod(7, -2).

:- test eval_test33(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith 'mod'/2".

eval_test33(S) :- S is mod(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test34(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith 'mod'/2: bug()".

eval_test34(S) :- S is mod(foo, 77).

:- test eval_test35(S) + exception(error(type_error(integer, 7.5), _))
   # "[ISO] arith mod/2".

eval_test35(S) :- S is mod(7.5, 2).

:- test eval_test36(S)
	+ exception(error(evaluation_error(zero_divisor), _))
   # "[ISO] arith mod/2".

eval_test36(S) :- S is mod(7, 0).

:- test eval_test37(S) => (S=7)
   # "[ISO] arith floor/1".

eval_test37(S) :- S is floor(7.4).

:- test eval_test38(S) => (S=(-1))
   # "[ISO] arith floor/1".

eval_test38(S) :- S is floor(-0.4).

:- test eval_test39(S) => (S=8)
   # "[ISO] arith round/1".

eval_test39(S) :- S is round(7.5).

:- test eval_test40(S) => (S=8)
   # "[ISO] arith round/1".

eval_test40(S) :- S is round(7.6).

:- test eval_test41(S) => (S=(-1))
   # "[ISO] arith round/1".

eval_test41(S) :- S is round(-0.6).

:- test eval_test42(S) + exception(error(instantiation_error, _))
   # "[ISO] arith round/2".

eval_test42(S) :- S is round(_X).

:- test eval_test43(S) => (S=0)
   # "[ISO] arith ceiling/1".

eval_test43(S) :- S is ceiling(-0.5).

:- test eval_test44(S) => (S=0)
   # "[ISO] arith ceiling/1".

eval_test44(S) :- S is truncate(-0.5).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test45(S) 
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith truncate/1: bug()".

eval_test45(S) :- S is truncate(foo).

:- test eval_test46(S) => (S=7.0)
   # "[ISO] arith float/1".

eval_test46(S) :- S is float(7).

:- test eval_test47(S) => (near(S, 7.3, 0.0001))
   # "[ISO] arith float/1".

eval_test47(S) :- S is float(7.3).

:- test eval_test48(S) => (S=1.0)
   # "[ISO] arith float/1".

eval_test48(S) :- S is float(5//3).

:- test eval_test49(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith float/1".

eval_test49(S) :- S is float(_X).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test50(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith float/1: bug()".

eval_test50(S) :- S is float(foo).

:- test eval_test51(S) => (S=7)
   # "[ISO] arith abs/1".

eval_test51(S) :- S is abs(7).

:- test eval_test52(S) => (S=8)
   # "[ISO] arith abs/1".

eval_test52(S) :- S is abs(3 -11).

:- test eval_test53(S) => (near(S, 7.8000, 0.0001))
   # "[ISO] arith abs/1".

eval_test53(S) :- S is abs(3.2 -11.0).

:- test eval_test54(S) + exception(error(instantiation_error, _))
   # "[ISO] arith abs/1".

eval_test54(S) :- S is abs(_N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test55(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith abs/1: bug()".

eval_test55(S) :- S is abs(foo).

:- test eval_test56(S) => (S=(5.0))
   # "[ISO] arith '/'/2".

eval_test56(S) :- S is '/'(10,2).

:- test eval_test57(S) => (S=(0.0))
   # "[ISO] arith '/'/2".

eval_test57(S) :- S is '/'(0,3+11).

:- test eval_test58(S) => (S=(-2.5))
   # "[ISO] arith '/'/2".

eval_test58(S) :- S is '/'(-5,2).

:- test eval_test59(S) => (S=(-0.1))
   # "[ISO] arith '/'/2".

eval_test59(S) :- S is '/'(1,-10).

:- test eval_test60(S) => (S=(0))
   # "[ISO] arith '//'/2".

eval_test60(S) :- S is '//'(0,3+11).

:- test eval_test61(S) => (S=(-1))
   # "[ISO] arith '//'/2".

eval_test61(S) :- S is '//'(-5,3).

:- test eval_test62(S) => (S=(0))
   # "[ISO] arith '//'/2".

eval_test62(S) :- S is '//'(1,-12).

% ===========================================================================
%! # 9.3 Other arithmetic functors
%! ## 9.3.1 arith **/2 ISOcore#p120

:- test power_test1(S) => (S=125.0000)
   # "[ISO] arith '**'/2".

power_test1(S) :- S is '**'(5, 3).

:- test power_test2(S) => (S=(-125.0000))
   # "[ISO] arith '**'/2".

power_test2(S) :- S is '**'(-5.0, 3).

:- test power_test3(S) => (S=0.2000)
   # "[ISO] arith '**'/2".

power_test3(S) :- S is '**'(5, -1).

:- test power_test4(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '**'/2".

power_test4(S) :- S is '**'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test power_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '**'/2: bug()".

power_test5(S) :- S is '**'(foo, 2).

:- test power_test6(S) => (S=125.0000)
   # "[ISO] arith '**'/2".

power_test6(S) :- S is '**'(5, 3.0).

:- test power_test7(S) => (S=1.0)
   # "[ISO] arith '**'/2".

power_test7(S) :- S is '**'(0.0, 0).

% ---------------------------------------------------------------------------
%! ## 9.3.2 arith sin/1 ISOcore#p120

:- test sin_test1(S) => (S=0.0)
   # "[ISO] arith sin/1".

sin_test1(S) :- S is sin(0.0).

:- test sin_test2(S) + exception(error(instantiation_error, _))
   # "[ISO] arith sin/1".

sin_test2(S) :- S is sin(_N).

:- test sin_test3(S) => (S=0.0)
   # "[ISO] arith sin/1".

sin_test3(S) :- S is sin(0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test sin_test4(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith sin/1: bug()".

sin_test4(S) :- S is sin(foo).

:- test sin_test5(PI, S) : (PI is atan(1.0) *4)
   => (near(S, 1.0000, 0.0001), near(PI, 3.14159, 0.0001))
   # "[ISO] arith sin/1".

sin_test5(PI, S) :- S is sin(PI/2.0).

% ---------------------------------------------------------------------------
%! ## 9.3.3 arith cos/1 ISOcore#p120

:- test cos_test1(S) => (S=1.0)
   # "[ISO] arith cos/1".

cos_test1(S) :- S is cos(0.0).

:- test cos_test2(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith cos/1".

cos_test2(S) :- S is cos(_N).

:- test cos_test3(S) => (S=1.0)
   # "[ISO] arith cos/1".

cos_test3(S) :- S is cos(0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test cos_test4(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith cos/1: bug()".

cos_test4(S) :- S is cos(foo).

:- test cos_test5(PI, S) : (PI is atan(1.0) *4)
   => (near(S, 0.0000, 0.02), near(PI, 3.14159, 0.02))
   # "[ISO] arith cos/1".

cos_test5(PI, S) :- S is cos(PI/2.0).

% ---------------------------------------------------------------------------
%! ## 9.3.3 arith atan/1 ISOcore#p121

:- test atan_test1(S) => (S=0.0)
   # "[ISO] arith atan/1".

atan_test1(S) :- S is atan(0.0).

:- test atan_test2(PI) => (near(PI, 3.14159, 0.02))
   # "[ISO] arith atan/1".

atan_test2(PI) :- PI is atan(1.0) *4.

:- test atan_test3(S) + exception(error(instantiation_error, _))
   # "[ISO] arith atan/1".

atan_test3(S) :- S is atan(_N).

:- test atan_test4(S) => (S=0.0)
   # "[ISO] arith atan/1".

atan_test4(S) :- S is atan(0.0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test atan_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith atan/1: bug()".

atan_test5(S) :- S is atan(foo).

% ---------------------------------------------------------------------------
%! ## 9.3.5 arith exp/1 ISOcore#p121

:- test exp_test1(S) => (S=1.0)
   # "[ISO] arith exp/1".

exp_test1(S) :- S is exp(0.0).

:- test exp_test2(S) => (near(S, 2.7818, 0.1))
   # "[ISO] arith exp/1".

exp_test2(S) :- S is exp(1.0).

:- test exp_test3(S) + exception(error(instantiation_error, _))
   # "[ISO] arith exp/1".

exp_test3(S) :- S is exp(_N).

:- test exp_test4(S) => (S=1.0)
   # "[ISO] arith exp/1".

exp_test4(S) :- S is exp(0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test exp_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith exp/1: bug()".

exp_test5(S) :- S is exp(foo).

% ---------------------------------------------------------------------------
%! ## 9.3.6 arith log/1 ISOcore#p121

:- test log_test1(S) => (S=0.0)
   # "[ISO] arith log/1".

log_test1(S) :- S is log(1.0).

:- test log_test2(S) => (near(S, 1.0000, 0.02))
   # "[ISO] arith log/1".

log_test2(S) :- S is log(2.71828).

:- test log_test3(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith log/1".

log_test3(S) :- S is log(_N).

% TODO:[JF] different behavior since we support 0.Inf; customize with a flag?
% TODO: what other prologs do?
%   evaluation_error(undefined)
%   evaluation_error(float_overflow)
%   S = -inf (gprolog)
%   S = -0.Inf (ciao)
:- test log_test4(S)
   + exception(error(evaluation_error(undefined), _))
   # "[ISO] arith log/2: bug(wontfix)".

log_test4(S) :- S is log(0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test log_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith log/1: bug()".

log_test5(S) :- S is log(foo).

% TODO:[JF] same as log_test4
:- test log_test6(S)
   + exception(error(evaluation_error(undefined), _))
   # "[ISO] arith log/1: bug(wontfix)".

log_test6(S) :- S is log(0.0).

% ---------------------------------------------------------------------------
%! ## 9.3.7 arith sqrt/1 ISOcore#p122

:- test sqrt_test1(S) => (S=0.0)
   # "[ISO] arith sqrt/1".

sqrt_test1(S) :- S is sqrt(0.0).

:- test sqrt_test2(S) => (S=1.0)
   # "[ISO] arith sqrt/1".

sqrt_test2(S) :- S is sqrt(1).

:- test sqrt_test3(X, S) : (X=1.21) => (near(S, 1.1000, 0.02))
   # "[ISO] arith sqrt/1".

sqrt_test3(X, S) :- S is sqrt(X).

:- test sqrt_test4(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith sqrt/1".

sqrt_test4(S) :- S is sqrt(_N).

% TODO:[JF] different behavior since we support 0.Nan; customize with a flag?
% TODO: what other prologs do?
%   evaluation_error(undefined)
%   S = nan (gprolog)
%   S = 0.Nan (ciao)
:- test sqrt_test5(S)
   + exception(error(evaluation_error(undefined), _))
   # "[ISO] arith sqrt/1: bug(wontfix)".

sqrt_test5(S) :- S is sqrt(-1.0).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test sqrt_test6(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith sqrt/1: bug()".

sqrt_test6(S) :- S is sqrt(foo).

% ---------------------------------------------------------------------------
%! ## 9.3.8 arith max/2 ISOcor2#p20

% NOTE: Current issues in Ciao:
%
%  - max/2 is not implemented
%  - some tests from ISOcor2 are missing

% TODO:[JF] implement max/2
:- test eval_test63(S) => (S=(3)) + no_exception
   # "[ISO-cor2] arith max/2: bug()".

eval_test63(S) :- S is max(2, 3).

% TODO:[JF] implement max/2
:- test eval_test64(S) + exception(error(instantiation_error, _))
   # "[ISO-cor2] arith max/2: bug()".

eval_test64(S) :- S is max(_N,3).

% TODO:[JF] implement max/2
:- test eval_test65(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-ciao] arith max/2: bug()".

eval_test65(S) :- S is max(3,foo).

% ---------------------------------------------------------------------------
%! ## 9.3.9 arith min/2 ISOcor2#p21

% NOTE: Current issues in Ciao:
%
%  - min/2 is not implemented
%  - some tests from ISOcor2 are missing

% TODO:[JF] implement min/2
:- test eval_test66(S) => (S=(2)) + no_exception
   # "[ISO] arith min/2: bug()".

eval_test66(S) :- S is min(2, 3).

% TODO:[JF] implement min/2
:- test eval_test67(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith min/2: bug()".

eval_test67(S) :- S is min(_N,3).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test eval_test68(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-ciao] arith min/2: bug()".

eval_test68(S) :- S is min(3,foo).

% ---------------------------------------------------------------------------
%! ## 9.3.10 arith (^)/2 ISOcor2#p22

% NOTE: Current issues in Ciao:
%
%  - (^)/2 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test69(S) + not_fails
   # "[ISO-cor2] arith ^/2: bug()".

eval_test69(S) :- S is 3^3.

% ---------------------------------------------------------------------------
%! ## 9.3.11 arith asin/1 ISOcor2#p24

% NOTE: Current issues in Ciao:
%
%  - asin/1 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test70(S) + not_fails
   # "[ISO-cor2] arith asin/1: bug()".

eval_test70(S) :- S is asin(0).

% ---------------------------------------------------------------------------
%! ## 9.3.12 arith acos/1 ISOcor2#p24

% NOTE: Current issues in Ciao:
%
%  - acos/1 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test71(S) + not_fails
   # "[ISO-cor2] arith acos/1: bug()".

eval_test71(S) :- S is acos(0).

% ---------------------------------------------------------------------------
%! ## 9.3.13 arith atan2/2 ISOcor2#p25

% NOTE: Current issues in Ciao:
%
%  - atan2/2 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test72(S) + not_fails
   # "[ISO-cor2] arith atan2/1: bug()".

eval_test72(S) :- S is atan2(0,0).

% ---------------------------------------------------------------------------
%! ## 9.3.14 arith tan/1 ISOcor2#p26

% NOTE: Current issues in Ciao:
%
%  - tan/1 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test73(S) + not_fails
   # "[ISO-cor2] arith tan/1: bug()".

eval_test73(S) :- S is tan(0).

% ---------------------------------------------------------------------------
%! ## 9.3.15 arith pi/0 ISOcor2#p26

% NOTE: Current issues in Ciao:
%
%  - pi/0 is not implemented
%  - tests from ISOcor2 are missing

% TODO:[JF] implement, this is a dummy test
:- test eval_test74(S) + not_fails
   # "[ISO-cor2] arith pi/0: bug()".

eval_test74(S) :- S is pi.

% ===========================================================================
%! # 9.4 Bitwise functors
%! ## 9.4.1 arith (>>)/2 ISOcore#p122

:- test bit_rl_test1(S) => (S=4)
   # "[ISO] arith '>>'/2".

bit_rl_test1(S) :- S is '>>'(16, 2).

:- test bit_rl_test2(S) => (S=4)
   # "[ISO] arith '>>'/2".

bit_rl_test2(S) :- S is '>>'(19, 2).

:- test bit_rl_test3(S) => (S=(-4))
   # "[ISO] arith '>>'/2".

bit_rl_test3(S) :- S is '>>'(-16, 2).

:- test bit_rl_test4(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '>>'/2".

bit_rl_test4(S) :- S is '>>'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test bit_rl_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '>>'/2: bug()".

bit_rl_test5(S) :- S is '>>'(foo, 2).

:- test bit_rl_test6(S) + exception(error(type_error(integer, 1.0), _))
   # "[ISO-sics] arith '>>'/2".

bit_rl_test6(S) :- S is '>>'(1.0, 2).

% ---------------------------------------------------------------------------
%! ## 9.4.2 arith (<<)/2 ISOcore#p123

:- test bit_lr_test1(S) => (S=64)
   # "[ISO] arith '<<'/2".

bit_lr_test1(S) :- S is '<<'(16, 2).

:- test bit_lr_test2(S) => (S=76)
   # "[ISO] arith '<<'/2".

bit_lr_test2(S) :- S is '<<'(19, 2).

:- test bit_lr_test3(S) => (S=(-64))
   # "[ISO] arith '<<'/2".

bit_lr_test3(S) :- S is '<<'(-16, 2).

:- test bit_lr_test4(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '<<'/2".

bit_lr_test4(S) :- S is '<<'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test bit_lr_test5(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '<<'/2: bug()".

bit_lr_test5(S) :- S is '<<'(foo, 2).

:- test bit_lr_test6(S) + exception(error(type_error(integer, 1.0), _))
   # "[ISO-sics] arith '<<'/2".

bit_lr_test6(S) :- S is '<<'(1.0, 2).

% ---------------------------------------------------------------------------
%! ## 9.4.3 arith (/\)/2 ISOcore#p123

:- test bit_and_test1(S) => (S=8)
   # "[ISO] arith '/\\'/2".

bit_and_test1(S) :- S is '/\\'(10, 12).

:- test bit_and_test2(S) => (S=8)
   # "[ISO] arith '/\'/2".

bit_and_test2(S) :- S is /\(10, 12).

:- test bit_and_test3(S) => (S=125)
   # "[ISO] arith '/\\'/2".

bit_and_test3(S) :- S is '/\\'(17*256 +125, 255).

:- test bit_and_test4(S) => (S=4)
   # "[ISO] arith '/\'/2".

bit_and_test4(S) :- S is /\(-10, 12).

:- test bit_and_test5(S) + exception(error(instantiation_error, _))
   # "[ISO] arith '/\\'/2".

bit_and_test5(S) :- S is '/\\'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test bit_and_test6(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '/\\'/2: bug()".

bit_and_test6(S) :- S is '/\\'(foo, 2).

:- test bit_and_test7(S) + exception(error(type_error(integer, 1.0), _))
   # "[ISO-sics] arith '/\\'/2".

bit_and_test7(S) :- S is '/\\'(1.0, 2).

% ---------------------------------------------------------------------------
%! ## 9.4.4 (\/)/2 ISOcore#p124

:- test bit_or_test1(S) => (S=14)
   # "[ISO] arith '\\/'/2".

bit_or_test1(S) :- S is '\\/'(10, 12).

:- test bit_or_test2(S) => (S=14)
   # "[ISO] arith '\/'/2".

bit_or_test2(S) :- S is \/(10, 12).

:- test bit_or_test3(S) => (S=255)
   # "[ISO] arith '\\/'/2".

bit_or_test3(S) :- S is '\\/'(125, 255).

:- test bit_or_test4(S) => (S=(-2))
   # "[ISO] arith '\/'/2".

bit_or_test4(S) :- S is \/(-10, 12).

:- test bit_or_test5(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '\\/'/2".

bit_or_test5(S) :- S is '\\/'(77, _N).

% TODO:[JF] fix internals:error_term for type_error(evaluable)
:- test bit_or_test6(S)
   + exception(error(type_error(evaluable, foo/0), _))
   # "[ISO-cor1] arith '\\/'/2: bug()".

bit_or_test6(S) :- S is '\\/'(foo, 2).

:- test bit_or_test7(S)
   + exception(error(type_error(integer, 1.0), _))
   # "[ISO-sics] arith '\\/'/2".

bit_or_test7(S) :- S is '\\/'(1.0, 2).

% ---------------------------------------------------------------------------
%! ## 9.4.5 arith (\)/1 ISOcore#p124

:- test bit_not_test1(S) => (S=10)
   # "[ISO] arith '\\'/1".

bit_not_test1(S) :- S is '\\'('\\'(10)).

:- test bit_not_test2(S) => (S=10)
   # "[ISO] arith '\\'/1".

bit_not_test2(S) :- S is \(\(10)).

:- test bit_not_test3(S)
   => (S=(-11))
   # "[ISO] arith '\'/1".

bit_not_test3(S) :- S is \(10).

:- test bit_not_test4(S)
   + exception(error(instantiation_error, _))
   # "[ISO] arith '\\'/2".

bit_not_test4(S) :- S is '\\'(_N).

:- test bit_not_test5(S)
   + exception(error(type_error(integer, 2.5), _))
   # "[ISO] arith '\\'/2".

bit_not_test5(S) :- S is '\\'(2.5).

:- test bit_not_test6(S)
   + exception(error(type_error(integer, 2.5), _))
   # "[ISO-sics] arith '\\'/2".

bit_not_test6(S) :- S is '\\'(2.5).

% ---------------------------------------------------------------------------
%! ## 9.4.6 arith xor/2 ISOcor2#p27

% NOTE: Current issues in Ciao:
%
%  - xor/2 is implemented but with other name ((#)/2)
%  - tests from ISOcor2 are missing

% TODO:[JF] rename # by xor
% TODO:[JF] add more tests
:- test xor_test1(S) + not_fails
   # "[ISO-cor2] arith xor/2: bug()".

xor_test1(S) :- S is xor(0,0).

% ===========================================================================
%! # 9.x Unbounded arithmetic

% These tests verifying the operation of unbounded based on logtalk
% tests.

:- test unbounded_test1(N) => (N=( 123456789012345678901234567890))
   # "[ISO-lg] arith '-'/2".

unbounded_test1(N) :- N is '-'( 123456789012345678901234567891, 1).

:- test unbounded_test2(N) => (N=(-1.3419876543210988e+34))
   # "[ISO-lg] arith '-'/2".

unbounded_test2(N) :- N is '-'( 123456789012345678901234567890, 13.42e+33).

:- test unbounded_test3(N) => (N=(123456789012345678901234567890))
   # "[ISO-lg] arith '-'/2".

unbounded_test3(N) :- N is '-'( 246913578024691357802469135780,123456789012345678901234567890).

:- test unbounded_test4(N) => (N=(-123456789012345678901234567890))
   # "[ISO-lg] arith '-'/1".

unbounded_test4(N):- N is '-'(1,123456789012345678901234567891).

:- test unbounded_test5(N) => (N=(123456789012345678901234567891))
   # "[ISO-lg] arith '+'/2".

unbounded_test5(N):- N is '+'(1,123456789012345678901234567890).

:- test unbounded_test6(N) => (N=(246913578024691357802469135780))
   # "[ISO-lg] arith '+'/2".

unbounded_test6(N):- N is '+'(123456789012345678901234567890,123456789012345678901234567890).

:- test unbounded_test7(N) => (N=(1.3420123456789013e+34))
   # "[ISO-lg] arith '+'/2".

unbounded_test7(N):- N is '+'(123456789012345678901234567890,13.42e+33).

:- test unbounded_test8(N) => (N=(370370367037037036703703703670))
   # "[ISO-lg] arith '*'/2".

unbounded_test8(N):- N is '*'(123456789012345678901234567890,3).

:- test unbounded_test9(N) => (N=(15241578753238836750495351562536198787501905199875019052100))
   # "[ISO-lg] arith '*'/2".

unbounded_test9(N):- N is '*'(123456789012345678901234567890,123456789012345678901234567890).

:- test unbounded_test10(N) => (N=( 1.656790108545679e+63))
   # "[ISO-lg] arith '*'/2".

unbounded_test10(N):- N is '*'(123456789012345678901234567890,13.42e+33).

:- test unbounded_test11(N) => (N=(41152263004115226300411522630))
   # "[ISO-lg] arith '//'/2".

unbounded_test11(N):- N is '//'(123456789012345678901234567890,3).

:- test unbounded_test12(N) => (N=(0))
   # "[ISO-lg] arith '-'/2".

unbounded_test12(N):- N is '//'(3,123456789012345678901234567890).

:- test unbounded_test13(N) => (N=( 41152263004115226300411522630))
   # "[ISO-lg] arith '//'/2".

unbounded_test13(N):- N is '//'(15241578753238836750495351562536198787501905199875019052100, 370370367037037036703703703670).

:- test unbounded_test14(N) => (N=(4.115226300411523e+28))
   # "[ISO-lg] arith '/'/2".

unbounded_test14(N):- N is '/'(123456789012345678901234567890,3).

:- test unbounded_test15(N) => (N=( 2.4300000218700003e-29))
   # "[ISO-lg] arith '/'/2".

unbounded_test15(N):- N is '/'(3,123456789012345678901234567890).

:- test unbounded_test16(N) => (N=( 3.0000000000000004))
   # "[ISO-lg] arith '/'/2".

unbounded_test16(N):- N is '/'(370370367037037036703703703670,123456789012345678901234567890).

:- test unbounded_test17(N) => (N=( 2.7598388005740465e-05))
   # "[ISO-lg] arith '/'/2".

unbounded_test17(N):- N is '/'(370370367037037036703703703670,13.42e+33).
