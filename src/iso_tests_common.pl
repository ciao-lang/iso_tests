:- module(iso_tests_common, _, [iso_strict]).

%:- use_module(library(streams)).
%:- use_module(library(write)).

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

% TODO: simplify
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

% TODO: simplify
read_bytes_to_end(Stream, String) :-
    current_input(OldIn),
    set_input(Stream),
    read_bytes_to_end_(String),
    set_input(OldIn).

read_bytes_to_end_(L) :-
    get_byte(C),
    read_bytes_to_end__(C, L).

read_bytes_to_end__(-1, []) :- !.
read_bytes_to_end__(C, [C|L]) :-
    read_bytes_to_end_(L).


