:- module(iso_tests_common, _, [iso_strict]).

%:- use_module(library(streams)).
%:- use_module(library(write)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates from Stdprolog that allow the different kind of writings
% in a file needed in the tests

write_contents(text, Atoms, S) :-
    ( atom(Atoms) -> write(S, Atoms)
    ; write_list(Atoms, S)
    ).
write_contents(binary, Bytes, S) :-
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% These predicates check if one element a list is included in other list

find_on_list([],     _CP).
find_on_list([P|Ps], CP) :-
    look(P, CP),
    find_on_list(Ps, CP).

look(_P, []) :- fail.
look(P,  [CP|CPs]) :-
    ;(->(P=CP, true), look(P, CPs)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: this duplicates stream_utils:read_string_to_end/2 because that
% module does not use iso_strict; remove once aliases, etc. are
% integrated into the Ciao standard libraries.

% The read_no_term/2 predicate is used to read a sequence of
% characters from an input stream S to the end of the file and unify
% this sequence with Cs. This predicate is implemented using the
% auxiliary predicate read_string_to_end/2.

read_no_term(S,Cs):-
    read_string_to_end(S,Cs).

read_string_to_end(Stream, String) :-
    current_input(OldIn),
    set_input(Stream),
    read_string_to_end_(String),
    set_input(OldIn).

read_string_to_end_(L) :-
    get_code(C),
    read_string_to_end__(C, L).

read_string_to_end__(-1, []) :- !.
read_string_to_end__(C, [C|L]) :-
    read_string_to_end_(L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


my_list_of(0, _, []).
my_list_of(N, A, [A|L]) :-
    N > 0,
    N1 is N-1,
    my_list_of(N1, A, L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% This predicate open a file and write in it the content of String 
open_and_write(File, Mode, S, Ops, Type, String) :-
    display(user_error, open_and_write(File, Mode, S, Ops, Type, String)), nl(user_error),
    open(File, Mode, S, Ops),
    write_contents(Type, String, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% This predicate open a file and set the stream associated to this
% file as the input stream
open_to_read(File, Mode, Sc, Sn, Ops) :-
    open(File, Mode, Sn, Ops),
    current_input(Sc),
    set_input(Sn).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% This predicate sets the stream Sc as input and closes the stream Sn
close_instreams(Sc, Sn) :-
    set_input(Sc),
    close(Sn).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% This predicate sets the stream Sc as output and closes the stream Sn
close_outstreams(Sc, Sn) :-
    set_output(Sc),
    close(Sn).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% These predicates check if the path of the file File_name is include
% in the list that is passed as the other argument of the predicates
find_path([], _File_name) :- fail.

find_path([L|Ls], File_name) :-
    ;(->(\+var(L), ;(->(File_name=L, true), find_path(Ls, File_name))),
        false).
