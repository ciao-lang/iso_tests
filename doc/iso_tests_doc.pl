:- module(_, [], [assertions]).

:- doc(filetype, application).

:- doc(title, "ISO standard tests for Ciao").
:- doc(author, "The Ciao Development Team").
:- doc(author, "Lorea Galech").
:- doc(author, "Edison Mera").

:- doc(summary, "The file iso_tests.pl has a set of test assertions 
which have been developed according to examples used in the ISO
standard for PROLOG and therefore, all the tests meet the standard.

The battery of tests contained in the file `iso_tests.pl` is based in the
application `Stdprolog` developed by Péter Szabó  and Péter
Szeredi from the Department of Computer Science and Information Technology at
the Budapest University of Technology and Economics.
The `Stdprolog` application contains all the tests based on the examples of the
ISO standard and a set of tests obtained from SICStus and `eddbali`. Most of
the tests included in `Stdprolog` have also been included in the file `iso_tests.pl`, 
except for the tests that do not make sense when applied to Ciao.
The tests from SICStus and `eddbali` have also been included becuase it is
interesting to do test certain characteristics that are common to many systems 
supporting Prolog but that go beyond those established by the standard.").

:- doc(module,
"The battery of tests is organized in such way that the tests for each 
predicates are grouped together, but there is a separation between the ISO
standard tests and the SICStus and `eddbali` ones.

Each one of the tests in iso_tests.pl has the following format:
```
:- test test_name : (preconditions) => (postconditions) + properties
:- test_name : tested_predicate
```
Where the preconditions, postconditions, and properties fields are optional.

Each one of the tests developed comes with a brief explanation, which should 
be useful to understand the relevance of the tests.

If the results that Ciao gets through `Stdprolog` are compared to the results
obtained by Ciao with this new battery of tests, we can observe that Ciao gets
much better results with the second one, even when both applications execute
the same tests over the same predicates. This is because a  multitude of tests in
`Stdprolog` fail due to reasons external to the test in question (for example,
there is an error reading from a file or it is assumed that Ciao behaves in a
specific way in the execution of a predicate, that is not necessarily standard). 
This kind of error does not happen in the new implementation; if a test fails 
it is because it  does not work as expected.

Once all of the tests have been implemented it is now time to analyze
the reasons why some of the tests do not succeed in Ciao.

# Case 1

The most common cause why a test does not succeed in Ciao is because
the format of the error raised does not match the format specified by
the ISO standard for that error.

According to the ISO standard, when an error occurs, the actual goal
should be changed by the target:

    throw(error(Error_term,Imp_dep) where
    - Error_term is a term that supplies information about the error.
    - Imp_dep is an implementation-defined term.

**Syntax error**:

    term_test3,term_test4,term_test5,opnotation_test1,opnotation_test3,
    opnotation_test5,opnotation_test7,read_test5,read_test6,read_test22.
 
 - ISO standard format: `error(syntax_error(Imp_dep_atom),Imp_dep)`.
 - Ciao format: `error(syntax_error(Ln0,Ln1,Msg,Errorloc),Imp_dep)`.
 
**Type error**:

    -Cases for control constructs(Higher-order support; iso_tests.pl): call_test14, call_test15.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): asserta_test5, asserta_test6, assertz_test5,
    assertz_test6.
    
    -Cases for atomic term processing(Classic Prolog predicates; iso_tests.pl): atomchars_test13, numberchars_test16. 

 - Predicate call/1 (pag 44 standard)

    - ISO standard format: `error(type_error(callable,G),Imp_dep)`.
      where `G` represents the goal.
    - Ciao format: `error(type_error(callable,G),Imp_dep)`
      where `G` represents a partial goal.

   For example if the predicate is call((write(3),1)) the Ciao error would be
   type_error(callable,1) instead of type_error(callable,(write(3),1)).


 - Predicates asserta/1 and assertz/1 (pag 79 standard)
        ISO standard format: error(type_error(callable,Head),Imp_dep)
        or error(type_error(callable,Body),Imp_dep).            
       Ciao format: error(type_error(clause,Clause),Imp_dep).
   
   For example if the predicate is asserta((foo :- 4)) the Ciao error would be
   type_error(clause,(foo:-4)) instead of type_error(callable,(4)).


 - Predicate atom_chars/2 (pag 108 standard), when Atom is a
        variable and an element E of the list List is neither a
        variable nor a one-char atom: 
        ISO standard format: error(type_error(character,E),Imp_dep)    
       Ciao format: error(type_error(atom,E),Imp_dep).
   
   For example if the predicate is atom_chars(_A,[f(b)]) the Ciao error would be
   type_error(atom,f(b)) instead of type_error(character,f(b)).

 - Predicate number_chars/2 (pag 111 standard), when an
        element E of the list List is not a one-char atom: 
        ISO standard format: error(type_error(character,E),Imp_dep)    
       Ciao format: error(type_error(atom,E),Imp_dep).
   
   For example if the predicate is number_chars(_A,['4',2]) the Ciao error would be
   type_error(atom,2) instead of type_error(character,2).


 - Predicate get_char(S_or_a,Char) (pag 91 standard), when
        Char is neither a variable nor an in-character: 
        ISO standard format: type_error(in_character,Char).
       Ciao format: type_error(atom,Char).
   
   For example if the predicate is get_chars(user_input,1) the Ciao error would be
   type_error(atom,1) instead of type_error(in_character,1).

 - Predicate peek_char(S_or_a,Char) (pag 93 standard), when
        Char is neither a variable nor an in-character: 
        ISO standard format: type_error(in_character,Char).
       Ciao format: type_error(atom,Char).
   
   For example if the predicate is peek_char(user_input,1) the Ciao error would be
   type_error(atom,1) instead of type_error(in_character,1).
   
**Permission error**:

   -Cases for clause retrieval and information(Dynamic predicates; iso_tests.pl): clause_test9, clause_test10.

   -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): setinput_test5, setoutput_test5,
   flush_output_test5.  
   
   -Cases for character input/output(Classic Prolog predicates, ISO Prolog compatibility layer; iso_tests.pl): getchar_test11,
   getchar_test12, getchar_test18, getcode_test29, getcode_test31, peekchar_test12, peekcode_test13, peekchar_test19,
   peekcode_test29, peekcode_test31, nl_test12, putchar_test16, putcode_test21.
 
   -Cases for byte input/output(ISO Prolog compatibility layer; iso_tests.pl): getbyte_test5, getbyte_test11, getbyte_test13,
   peekbyte_test5, peekbyte_test11, peekbyte_test13, putbyte_test8.

   -Cases for term input/output(Classic Prolog predicates; iso_tests.pl): read_test15, read_test20, write_test20.

 - Predicate clause/2 (pag 77 standard) when the predicate
        indicator Pred of Head is that of a private procedure:
        ISO standard format: error(permission_error(access,private_procedure,Pred),Imp_dep)    
       Ciao format:error(permission_error(modify,static_procedure,Pred),Imp_dep).


 - Predicate set_input/1 (pag 87 standard) when the target
        stream is an output stream.
        ISO standard format: error(permission_error(input,stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(access,stream,S_or_a),Imp_dep).


 - Predicate set_output/1 (pag 87 standard) when the target
        stream is an input stream.
        ISO standard format: error(permission_error(output,stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(modify,stream,S_or_a),Imp_dep).


 - Predicate flush_output/1 (pag 89 standard) when the
        target stream is an input stream.
        ISO standard format: error(permission_error(output,stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(modify,stream,S_or_a),Imp_dep).


 - Predicate get_char/2,get_code/2,peek_char/2,peek_code/2
        (pag 91 and 93 standard),when the target stream is an output stream:
        ISO standard format: error(permission_error(input,stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(access,stream,S_or_a),Imp_dep).


 - Predicate get_char/2,get_code/2,peek_code/2,peek_char2
        (pag 91 and 93 standard), when the target stream has stream
        properties end_of_stream(past) and eof_action(error).
        ISO standard format: error(permission_error(input,past_end_of_stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(access,past_end_of_stream,S_or_a),Imp_dep).


 - Predicate put_char/2,put_code/2,nl/1 (pag 94 standard)
        when the target stream is an input stream.
        ISO standard format: error(permission_error(output,stream,S_or_a),Imp_dep)    
       Ciao format: error(permission_error(modify,stream,S_or_a),Imp_dep).

 - Predicate get_byte/2 and peek_byte (pag 96 and 97
        standard, when the target stream is an output stream.
        ISO standard format: error(permission_error(input,stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(access,stream,S_or_a),Imp_dep).


 - Predicate get_byte/2 and peek_byte/2 (pag 96 and 97 standard),
        when the stream has stream properties end_of_stream(past) and
        eof_action(error).
        ISO standard format: error(permission_error(input,past_end_of_stream,S_or_a),Imp_dep)    
       Ciao format:error(permission_error(access,past_end_of_stream,S_or_a),Imp_dep).


 - Predicate put_byte/2 (pag 97 standard) when the target
        stream is a input stream.
        ISO standard format: error(permission_error(output,stream,S_or_a),Imp_dep)    
       Ciao format: error(permission_error(modify,stream,S_or_a),Imp_dep).


 - Predicate read/2 (pag 99 standard) when the target stream
        is an output stream.
        ISO standard format: error(permission_error(input,stream,S_or_a),Imp_dep)    
       Ciao format: error(permission_error(access,stream,S_or_a),Imp_dep).


 - Predicate read/2 (pag 99 standard) when the target stream
        has properties end_of_stream(past) and eof_action(error).
        ISO standard format: error(permission_error(input,past_end_of_stream,S_or_a),Imp_dep)    
       Ciao format: error(permission_error(access,past_end_of_stream,S_or_a),Imp_dep)


 - Predicate write/2 (pag 100 standard) when the target
        stream is an input stream.
        ISO standard format: error(permission_error(output,stream,S_or_a),Imp_dep)    
       Ciao format: error(permission_error(modify,stream,S_or_a),Imp_dep).

**Domain error**:

   -Cases of stream selection and control: currentinput_test2, currentoutput_test2.

 - Predicate current_input/2 (pag 86 standard) when the target
        stream is neither a variable nor a stream.
        ISO standard format: error(domain_error(stream,Stream),Imp_dep)    
       Ciao format: error(domain_error(stream_or_alias,Stream),Imp_dep).


 - Predicate  current_output/2 (pag 86 standard) when the target
        stream is neither a variable nor a stream.
        ISO standard format: error(domain_error(stream,Stream),Imp_dep)    
       Ciao format: error(domain_error(stream_or_alias,Stream),Imp_dep).

# Case 2

There are several tests in which an error is expected but in
Ciao the execution of the test just fails. Can be grouped into:

    -Arithmetic cases(Basic data types and properties, Arithmetic; iso_tests.pl: eval_test5, eval_test10, eval_test15, eval_test20,
    eval_test28, eval_test34, eval_test45,eval_test50, eval_test55, power_test5,
    sin_test4, cos_test4, atan_test5, exp_test5, log_test5, sqrt_test6.

    -Cases for term creation(Basic term manipulation; iso_tests_basic_term.pl): functor_test12, functor_test13, functor_test14,
    functor_test15, functor_test16, functor_test17, functor_test18, argument_test8, argument_test9, argument_test10, argument_test11,
    argument_test13, argument_test14, argument_test16.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): retract_test9, retract_test10, abolish_test2,
    abolish_test3, abolish_test4, abolish_test8, abolish_test10, abolish_test11, abolish_test12, abolish_test13, abolish_test14.

    -Cases for atomic term processing(Conversion between constants and strings, Classic Prolog predicates; iso_tests.pl): atomlength_test8,
    subatom_test10, subatom_test11, subatom_test12, subatom_test13, subatom_test14, subatom_test15, subatom_test16, atomchars_test12,
    charcode_test6, numberchars_test8, numberchars_test15, numberchars_test22, numberchars_test23, numberchars_test24,
    numberchars_test25, numberchars_test26, numberchars_test27, numbercodes_test21.

    -Cases for clause retrieval and information(Dynamic predicates; iso_tests.pl): clause_test7, clause_test8,
    clause_test12, currentpredicate_test6, currentpredicate_test7, currentpredicate_test8.

    -Cases for stream selection and control(Stream handling and operations, ISO Prolog compatibility layer; iso_tests.pl): currentinput_test4, currentoutput_test4,
    stream_property_test3, stream_property_test4.

    -Cases for character input/output(Classic Prolog predicates, ISO Prolog compatibility layer; iso_tests.pl): peekcode_test24, peekcode_test25, peekcode_test26,
     putchar_test8, getcode_test24.

    -Cases for byte input/output(ISO Prolog compatibility layer; iso_tests.pl): getbyte_test7, getbyte_test8, peekbyte_test8. 

    -Cases for Term input/output(Classic Prolog predicates; iso_tests.pl): current_op_test2, current_op_test3, current_op_test4,
    current_op_test5.

    -Cases for implementation defined hooks(iso_tests.pl): setflag_test2, setflag_test3, setflag_test4,
    setflag_test5, setflag_test6, currentflag_test3, currentflag_test7, currentflag_test8.

    -Cases for bitwise functors(Evaluable functors; iso_tests.pl): bit_rl_test4, bit_rl_test5, bit_lr_test5,
    bit_and_test6, bit_or_test6.

    -Cases for control constructs(Higher-order support; iso_tests.pl): call_test13.

    -Cases for all solutions(Aggregates: gathering predicate solutions; iso_tests.pl): findall_test9, setof_test29.

    -Cases for arithmetic comparison(Arithmetic; iso_tests.pl, iso_tests_arithmetic): arithmetic_comparision_test20.

# Case 3

The execution of a predicate raises a different error to the one specified
by the standard. According to the ISO standard, when more than one error
condition is satisfied, the error that is reported by the Prolog processor is
implementation dependent.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): asserta_test4, assertz_test4.

    -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): open_test8, open_test10, close_test2.

    -Cases for character input/output(Classic Prolog predicates; iso_tests.pl): peekchar_test22.

    -Cases for term input/output(Packages and language extension, Classic Prolog predicates; iso_tests.pl): op_test3, write_test20, read_test21.

 - Predicate asserta/1
          According to the ISO standard, when the head of the clause is a
          variable, the compiler should raise the following error:
          instantiation_error. But in Ciao the raised error is type_error(clause,head).
          Example: asserta(_).

 - Predicate assertaz/1
          According to the ISO standard, when the head of the clause is a
          variable, the compiler should raise the following error:
          instantiation_error. But in Ciao the raised error is
          type_error(clause,head).
          Example: assertz(_).

 - Predicate open(Souce_sink,Mode,Stream,Options).
          According to the ISO standard when Options is a partial list or
          a list with an element E which is a variable the compiler should
          raise the error: instantiation_error.
          But in Ciao the raised error is domain_error(open_option_list,Options).
          Example: open(f,write,_,[type(text),_]).

 - Predicate open(Souce_sink,Mode,Stream,Options).
          According to the ISO standard when Options is neither a partial
          list nor a list the compiler should raise the error:
          type_error(list,Options). But in Ciao the raised error is
          domain_error(open_option_list,Options).
          Example: open(f,write,_,type(text)).

 - Predicate close/1
          According to the ISO standard, when the target stream is a
          variable the compilar should raise the following error:
          instantiation_error. But in Ciao the raised error is
          domain_error(stream_or_alias,Stream).
          Example: close(_).

 - Predicate get_char/1,get_code/1
          According to the ISO standard, when the target stream is a
          variable the compilar should raise the following error:
          instantiation_error. But in Ciao the raised error is
          domain_error(stream_or_alias,Stream).
          Example: close(_).

 - Predicate get_char/2,get_code
          According to the ISO standard, when the rntity input from the
          target stream is not a character the compilar should raise the following error:
          representation_error(character). But in Ciao the raised error is
          domain_error(character_code_list,Char).
          Example: get_char(S,_) where S is an input associated to a
          binary file that contains [0] and that was open in with options
          type(text).

  - Predicate put_code(Code)
          According to the ISO standard, when Code is an integer but not a
          character code the compiler should raise the following error:
          representation_error(character_code). But in Ciao the raised error is
          type_error(byte,-1).
          Example: put_code(-2).

  - Predicate read_term(Term,Ops)
          According to the ISO standard, when Term breaches the
          implementation definit limit specified by the flag max_arity the
          compiler should raise the following error:
          representation_error(max_arity). But in Ciao the raised error is
          syntax_error(_,_,[maximum arity exceeded],_).
    
  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Priority is neither a
         variable nor an integer the compiler should raise the following error:
         type_error(integer,Priority). But in Ciao the raised error is
         domain_error(operator_priority,Priority)
         Example: op(max,xfy,++).


  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Priority is neither a
         variable nor an integer the compiler should raise the following error:
         type_error(integer,Priority). But in Ciao the raised error is
         domain_error(operator_priority,Priority)
         Example: op(max,xfy,++).


  - Predicate atom_codes(Atom,List)
         According to the ISO standard, when Atom is a variable and List is neither a
         variable nor a partial list the compiler should raise the following error:
         type_error(list,List). But in Ciao the raised error is
         domain_error(character_code_list,List)
         Example: atom_codes(_,0'x).


  - Predicate atom_codes(Atom,List)
         According to the ISO standard, when Atom is a variable and an
         element E of the list List is neither a variable nor a character
         code,the compiler should raise the following error:
         representation_error(character_code). But in Ciao the raised error is
         domain_error(character_code_list,List))
         Example: atom_codes(_,[0'i,0's,-1]).


  - Predicate char_codes(Char,Code)
         According to the ISO standard, when Code is neither a variable nor
         a character code,the compiler should raise the following error:
         representation_error(character_code). But in Ciao the raised error is
         permission_error(modify,stream,S_or_a).
         Example: atom_codes(_,-2).


  - Predicate number_codes(Number,List)
         According to the ISO standard, when Number is a variable and
         List is neither a list nor a partial list, the compiler should
         raise the following error:
         type_error(list,List). But in Ciao the raised error is
         domain_error(character_code_list,4).
         Example: number_codes(_,4).


  - Predicate number_codes(Number,List)
         According to the ISO standard, when an element E of the list
         List is not a character code,the compiler should raise the
         following error:representation_error(character_code). 
         But in Ciao the raised error is
         domain_error(character_code_list,List))
         Example: number_codes(_,[0'4,-1]).


  - Predicate write(Stream,Term)
         According to the ISO standard, when the target stream is
         associated with an input stream, the compiler should raise the
         following error: permission_error(output,stream,S_or_a). 
         But in Ciao the raised error is
         permission_error(modify,stream,S_or_a))
         Example: write(S,a), where S = user_input.


  - Predicate peek_char(S_or_a,Char)
         According to the ISO standard, when the next entity to be input
         from the target stream is not a character the compiler should raise the
         following error: representation_error(character). 
         But in Ciao the raised error is
         domain_error(character_code_list,Char))
         Example:  peek_char(S,_) where S  is associated to a binary file
         that contains [0].

# Case 4

The execution of a predicate that according to the standard should succeed,
fails in Ciao. 

    -Cases for clause retrieval and information(Dynamic predicates; iso_tests.pl): clause_test1, clause_test2.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): retract_test3, retract_test4,
    retract_test8.

    -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): stream_property_test5, stream_property_test6.

    -Cases for  atomic term processing(Classic Prolog predicates, Conversion between constants and strings; iso_tests.pl): numberchars_test7, numberchars_test9,
    numberchars_test10, numberchars_test19, numberchars_test20, numberchars_test21, numbercodes_test6, numbercodes_test7,
    numbercodes_test8, numbercodes_test17, numbercodes_test18, numbercodes_test19.
     
    -Cases for implementation defined hooks(iso_tests.pl): currentflag_test1, currentflag_test6.

# Case 5

The execution of a predicate should raise an error but the execution of the
test succeeds.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): abolish_test5, abolish_test9.

    -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): open_test7, open_test14. 

    -Cases for term input/output(Packages and language extension; iso_tests.pl): op_test10, op_test12, op_test13, op_test19, 

    -Arithmetic cases(Arithmetic; iso_tests.pl): log_test4, log_test6, sqrt_test5.
      

  - Predicate abolish(Pred)
         According to the ISO standard, when the predicate indicator Pred
         is that of a static procedure the compiler should raise the
         following error: permission_error(modify,static_procedure,Pred). 
         But in Ciao the execution succeeds.THIS is to say, Ciao allows
         abolish static predicates.
         Example: abolish(abolish/1).


  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Op_specifier is a specifier
         such that Operator would have an invalid set of specifiers the
         compiler should raise the following error:permission_error(create,operator,Operator). 
         But in Ciao the execution succeeds.
         Example: the execution of op(30,xfy,++),op(50,yf,++) it
         should raise an error because there cannot be an infix and a
         postfix operator with the same name.

  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Operator is neither a
         partial list nor a list nor an atom the compiler should raise
         the following error: type_error(list,Operator). 
         But in Ciao the execution succeeds.
         Example: op(30,xfy,_).

  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Operator is a partial list
         or a list with an element E which is a variable the compiler should raise
         the following error: instantiation_error. 
         But in Ciao the execution succeeds.
         Example: op(30,xfy,[a|_]).


  - Predicate op(Priority,Op_specifier,Operator)
         According to the ISO standard, when Operator is ',' or an
         element of the Operator list is ',' the compiler should raise
         the following error: permission_error(modify,operator,','). 
         But in Ciao the execution succeeds.
         Example: op(100,xfx,',').


  - Predicate (/)/2
         According to the ISO standard, when in the predicate /(X,Y) , if
         Y=0 the compiler should raise the following error:
         evaluation_error(zero_divisor). 
         But in Ciao the execution returns 0.inf
         Example: S is  /(3,0).

  - Predicate (mod)/2
         According to the ISO standard the arguments of the predicate mod/2 are just defined
         in the integers domain so the execution of a predicate mod where
         at least one of its arguments is not an integer should raise the following error:
         type_error(integer,Integer). 
         But in Ciao the execution succeeds
         Example: S is mod(7.5,2).


  - Predicate log/1
         According to the ISO standard if the value of X in the predicate
         log(X) is zero or negative the compiler should raise the
         following error: evaluation_error(undefined). 
         But in Ciao the execution succeeds
         Example: S is log(0).


  - Predicate sqrt/1
         According to the ISO standard if the value of X in the predicate
         sqrt(X) is  negative the compiler should raise the following
         error: evaluation_error(undefined). 
         But in Ciao the execution succeeds
         Example: S is sqrt(-1.0).


  - Predicate >>/2
         According to the ISO standard if the value of N in the predicate
         >>(N,S) is not an integer and N is not a variable the compiler
         should raise the following error: type_error(integer,N). 
         But in Ciao the execution succeeds
         Example: L is '>>'(1.0,2)


  - Predicate <</2
         According to the ISO standard if the value of B1 in the predicate
         <<(B1,B2) is not an integer and B1 is not a variable the compiler
         should raise the following error: type_error(integer,B1). 
         But in Ciao the execution succeeds
         Example: L is '<<'(1.0,2).



  - Predicate '/\\'/2
         According to the ISO standard if the value of B1 in the predicate
         '/\\'(B1,B2) is not an integer and B1 is not a variable the compiler
         should raise the following error: type_error(integer,B1). 
         But in Ciao the execution succeeds
         Example: S is '/\\'(1.0,2).


  - Predicate '\\/'/2 
         According to the ISO standard if the value of B1 in the predicate
         '/\\'(B1,B2) is not an integer and B1 is not a variable the compiler
         should raise the following error: type_error(integer,B1). 
         But in Ciao the execution succeeds
         Example: S is '\\/'(1.0,2).

  - Predicate '\\'/2 
         According to the ISO standard if the value of B1 in the predicate
         '\\'(B1) is not an integer and B1 is not a variable the compiler
         should raise the following error: type_error(integer,B1). 
         But in Ciao the execution succeeds
         Example: S is '\\'(2.5).

  - Predicate catch/3
         According to the ISO standard the execution of
         catch(true,C,write(demoen)),throw(bla) should raise a system
         error but in Ciao it raises an exception(bla). 

# Case 6

Another causes of the failures of the tests in Ciao is that within
the execution of a test either in the pre-condition, in the execution
of the tests or in the post-conditions, a predicate, that is in the
ISO standard is needed, but this predicate is either not implementated
or does not fulfill the whole funcionality established for it in the
standard. This is the case in the following predicates:

   -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): at_end_of_stream_test1, at_end_of_stream_test2,
   at_end_of_stream_test3, at_end_of_stream_test4, at_end_of_stream_test5, at_end_of_stream_test6, at_end_of_stream_test7, set_stream_position_test1,
   set_stream_position_test2, set_stream_position_test3.

   -Cases for Term input/output(Stricter ISO-Prolog package; iso_tests.pl): char_conversion_test1, char_conversion_test2, char_conversion_test3,
   char_conversion_test4, char_conversion_test5, char_conversion_test6, char_conversion_test7, char_conversion_test8, char_conversion_test9,
   char_conversion_test10, char_conversion_test11, char_conversion_test12, current_char_conversion_test.

   -Cases for implementation defined hooks(Runtime system control and flags; iso_tests.pl): current_prolog_flag/2. 

# Case 7

Ciao adds more information to a predicate created by the user than the one
that the standard considers.

This is the case of the following tests:

    -Cases for clause retrieval and information(Dynamic predicates; iso_tests.pl): clause_test3, clause_test4, clause_test5.

    -Cases for clause creation and destruction(Dynamic predicates; iso_tests.pl): asserta_test7, assertz_test7, retract_test11.

For example, the postcondition of the following tests is expecting
that the variable Body is equal to insect(I) where insect(I) is a user
defined predicate:

    :- test clause_test3(I,Body) => (Body=insect(I)).
    clause_test3(I,Body) :- clause(legs(I,6),Body).

But when this test is executed the following error occurrs:

    postcondition_fail( $:(term_basic:=(iso_test:insect(_14508),insect(_14508))))

The information iso_test: has been added in front of insect(_).

# Case 8

The execution of the predicate call_test7 in Ciao gets two results but
according to the ISO standard it should get just one.

Assuming the database:

    a(1).
    a(2).

The execution of `call(Z=!,a(X),Z)` should just return `X=1,Z=!` but in
Ciao it also returns `X=2,Z=!`. 

Instead, if `call(a(X),!)` is executed in Ciao it is just returned
`X=1,Z=1`.

Therefore, looking at these two examples I think that there may be a
problem with the assignmnt of values to a variable in the predicate
call.
        
# Case 9

The execution of some tests does not succeed because there are some issues
related to the stream manipulation in the assertions tests:

 - These issues provoke that some of the tests do not produce the
   expected result or they do not raise the expected error.

   These tests are:

        -Cases for character input/output(Classic Prolog predicates, Stream handling and operations; iso_tests.pl): putchar_test1, putcode_test3, putchar_test5.

        -Cases for byte input/output(Stream handling and operations, ISO Prolog compatibility layer; iso_tests.pl): putbyte_test1, putbyte_test2.

        -Cases for term input/output(Classic Prolog predicates; iso_tests.pl): write_test2, write_test5.

   For example the following test should raise an error but
   succeeds:

        :- test setinput_test4(S1) :
        (open(foo,write,S,[]),close(S),open(foo,read,S1,[]),close(S1))
        + exception(error(existence_error(stream,S1),Imp_dep)).

        setinput_test4(S1) :- set_input(S1).

 - These issues provoke that the execution of some of the tests aborts
   the execution of the whole battery of tests.  I have chosen to
   comment out these tests until this issue is fixed because in other
   case it would be impossible to execute the battery of tests.

   These tests are:                       

      -Cases for atomic term processing(Conversion between constants and strings; iso_tests.pl): atomcodes_test12, atomcodes_test13.

   Example: 
    - if the test is expressed as:

        :- test getchar_test17(S) : (open(foo,write,S,[]),close(S)) +
        exception(error(existence_error(stream,S),Imp_dep)).
        getchar_test17(S) :- get_char(S,_) 

      the execution of the battery of tests is aborted

    - But if the test is expressed as followig the same problem is not
      found and the test succeeds.

        :- test getchar_test17 : (open(foo,write,S,[]),close(S),get_char(S,_)) +
        exception(error(existence_error(stream,S),Imp_dep)).
        getchar_test17.
            
# Case 10

The standard does not establish what to do with those non-ASCII characters
but the `Stdprolog` developers added some tests from SICStus and `eddbali` try to
check Ciao's behave in this aspect. It seems that Ciao does not work as they
expected but it does not mind that Ciao does not meet the standard in this
aspect since this one does not establish anything about it. I have chosen to
leave them among the other tests but may be it would be better just take them away.

These tests are: 

    -Cases for atomic term processing(Conversion between constants and strings; iso_tests.pl): subatom_test32, subatom_test33, subatom_test34,
    atomcodes_test12, atomcodes_test13.

Example:
    :- test subatom_test34(Result) => (Result=[[0,2,'Pé'],[1,1,'éc'],[2,0,'cs']]).
    subatom_test34(Result) :- findall([X,Z,S],sub_atom('Pécs',X,2,Z,S),Result).

# Case 11

There are some tests that are only executed if UTF-8 is used, otherwise their
execution is ignored. We can detect these tests by the header: if(defined(fixed_utf8)).

These tests are:

     -Cases for atomic term processing(Conversion between constants and strings, Classic Prolog predicates; iso_tests.pl): atomconcat_test14, subatom_test34, atomchars_test14,
     atomchars_test15.

Example:

     :- if(defined(fixed_utf8)).
     %test14 
     :- test atomconcat_test14(Result)
	=> ( Result=[['', 'Pécs'], ['P', 'écs'], ['Pé', 'cs'], ['Péc', 's'],
		['Pécs', '']] )
    atomconcat_test14(Result) :-
	findall([T1, T2], atom_concat(T1, T2, 'Pécs'), Result).
    :- endif.

# Case 12

I have changed the expected result for some of the tests to accomodate
them to Ciao. According to the standard when more than one error
condition is satisfied, the error that is reported by the Prolog
processor is implementation dependent. In some tests, Ciao raises a
error different to the one specified by the standard but I have
realised that the error that Ciao raises is due to another error
condition that happens in the test. Therefore, I have changed the
expected error of the test from the one specified by the standars to
the one that Ciao raises.  I think the most appropiate solution would
be that the assertions test would allow specification of more than one
expected error. Until this is completed I have chosen the solution
explained above.

This change has been done in the following tests:
 - open_test5
 - open_test9
 - open_test13
 - putcode_test9
 - putcode_test10
 - op_test15 (either error e or i, pp 101 of the standard)
 - op_test16 (either error e or i, pp 101 of the standard)   

# Case 13

The predicate open/4 in Ciao does not have implemented the stream options
therefore, open/4 does the same as open/3. This fact made a multitude of test
fail for several reasons:

 - Some tests try to check that the compiler raises the adecuate error
   when the stream options specified in a open predicate are not
   adecuate. For example: open(f,write,S,[type(text)|_]) succeeds in
   Ciao.

   This problem occurs in the following tests:
    
    - open_test17   

 - Since the stream options with which a file may be opened are ignored
   in Ciao, it is not possible to specify an alias for the stream
   associated to the open file. It provokes that a multitude of tests
   that use the alias specified when the file is opened fail in Ciao. 

   This problem occurs in the following tests:    

    -Cases for stream selection and control(Stream handling and operations; iso_tests.pl): open_test2, flush_output_test6.

    -Cases for character input/output(Classic Prolog predicates, ISO Prolog compatibility layer; iso_tests.pl) : getchar_test3, getcode_test4, getchar_test5,
    getcode_test6, getchar_test9, getcode_test10, peekchar_test3, peekcode_test4, peekchar_test5, peekcode_test6, peekchar_test7, peekcode_test8, peekchar_test9,
    peekcode_test10, peekchar_test11, peekchar_test20, putchar_test2, putchar_test4, putchar_test6, getchar_test7, getcode_test8.

    -Cases for byte input/output(ISO Prolog compatibility layer; iso_tests.pl): getbyte_test2, getbyte_test3, getbyte_test4,
    peekbyte_test2, peekbyte_test3, peekbyte_test4, putbyte_test3.
    
    -Cases for term input/output(Classic Prolog predicates; iso_tests.pl): read_test2, read_test3.


 - There are side effects because open/4 does the same as open/3;
   for example, in the preconditions of some tests a binary file or
   a file with a determinate eof_action has to be opened in such a
   way that the execution of the predicate that we are trying to
   check should raise a specific error. As these stream options are
   not implemented in Ciao the execution of the test does not
   behave as the test is expected, and therefore the test fails.

   This problem occurs in the following tests:

    -Cases for character input/output(Classic Prolog predicates, ISO Prolog compatibility layer; iso_tests.pl): getchar_test19, getcode_test30, getcode_test33,
    putchar_test17, putcode_test22.

    -Cases for byte input/output(ISO Prolog compatibility layer; iso_tests.pl): peekbyte_test30, peekbyte_test33, getbyte_test12,
    peekbyte_test12, putbyte_test9.
   
    -Cases for term input/output(Classic Prolog predicates; iso_tests.pl): read_test18, read_test19.

 - Another error related with the stream options of the predicate
   open/4 is that the one of these options allow specification of the effect of
   attempting to input from a stream whose stream position is
   past_end_of_stream. This effect is specified by the option
   eof_action(Action). This makes some of the tests, that should
   succeed,raise an error in Ciao (and consequently the test fails).

   This problem occurs in the following tests:

    -Cases os stream selection and control: getchar_test21, getcode_test32.

# Case 14

The predicate close/2 in Ciao does not have implemented the close options therefore,
close/2 does the same as close/1. This fact made that a multitude of test fail:

 - Some tests try to check that the compiler raises the adecuate error
   when the close options specified in a open predicate are not
   adecuate. For example: close(Sc,_) succeeds in Ciao.

   This problem occurs in the following tests:

        -Cases for stream selection and control(ISO Prolog compatibility layer; iso_tests.pl): close_test3, close_test4, close_test5
        close_test6, close_test7.  

# Case 15

The execution of the predicates peek_char(S_or_a,Char) and
get_char(S_or_a,Char), when stream position of the target stream is
end_of_file it only succeeds if the atom end_of_file unifies with
Char. It seems that in Ciao the end of a file is denoted by -1. This
is correct,however the predicate peek_char is not able to recognize
that -1 is equal to end_of_file. Therefore, if the predicates
peek_char or get_char are used to attempt to read a character from a
stream with positon end_of_file the following error will occurr:

    domain_error(character_code_list,[-1]).

There are two thing that need to be said about it:

 - First of all,when Char is not a character, the error that should be
   raised is representation_error(character),not
   domain_error(character_code_list,[-1]); the one that Ciao raises.

 - and Ciao should have a mechanism to equal end_of_file to -1 because
   if not either peek_char/2 or peek_code/2 are going to raise one
   error when they attempt to read from a stream with position
   end_of_stream.

This problem occurs in the following tests:
    
    -Cases for character input/output(Classic Prolog predicates; iso_tests.pl): getchar_test20.

# Case 16

Error `Malformed body`:

 - The execution of the test cut_test10 provokes an error for
   malformed body (exactly in \+(\+(|))), but the syntax of this test
   is correct according to the standard. This test is included in the
   battery of tests but the test is commented out to avoid its
   execution.

 - The execution of the test ifthenelse_test9 provokes an error for
   malformed body but the syntax of this test is correct according to
   the standard. This test is included in the battery of tests but it
   is commented out to avoid its execution.

   I have chosen to comment out these tests because in other cases
   they abort the execution of the whole battery of tests.

 - The tests not_test2,not_test3 and not_test6 also provoke an error
   for malfomed body:
   Example:

       :- test not_test2 + fails.
       not_test2 :- '\\+'(!).

   But the next equivalent test does not have this problem:

       :- test not_test2(X) : (X=!) + fails.
       not_test2(X) :- '\\+'(X).

   In this case I have chosen to write these tests in the second way
   to avoid the problem of malformed body.

# Case 17

the result of executing current_output(S) is S=user_output but when the
predicate stream_property is used to get the streams that are open for output
(stream_property(S,output)) it does not return in S user_output (the alias)
but the streams associated to the user_output. It can mean  that some of the
tests do not succeeds because in Ciao the comparission between user_output
(alias) and S (the stream associated to the user output) fails. This is what
happens in the test stream_property_test2.

# Case 18

The test atomchars_test8 is ignored but the predicate that this test
executes succeeds in Ciao. [TODO: issues of assertion tests]?

    atom_chars(_,_).

# Case 19

The execution of the test repeat_test1 is commented out because in
Ciao there is no way yet to limit the execution of a predicate for a
limited period of time, therefore it would be executing forever. A
possible solution would be to establish a time-out for these predicate
but until it is done I have left this test commeted.

# Case 20

Side effects of the execution of some tests:

 - The execution of the tests op_test18 and op_test19 should,
   according to the standard, raise an error but they succeed in
   Ciao. It provokes that the priority of the operator ',' be
   changed. Due to this the test current_op_test1 fails since this
   test checks that the priority of the operator ',' is the default
   established in the standard.

 - The result of executing the test getchar_test15 is modified because
   of the execution of the test getchar_test14. The test
   getchar_test14 executes the predicate get_char(1) where the target
   stream is user_input. This test fails because Char is not an
   in_character. The problem is that in the test getchar_test16, the
   predicate that is executed is get_char(user_input,1) the target
   stream is also user_input, after the execution of getchar_test15,
   has position past_end_of_stream. This provokes that the error
   raised by Ciao is a
   permission_error(access,past_end_of_stream,user_input) instead of
   type_error(in_character,1) that is the expected error and the one
   that would be obtenied if the test getchar_test14 was not been
   executed before.

 - The same as the explained above happens with the tests
   getcode_test24 getcode_test25 and getcode_26, where the result of
   getcode_test25 is modified because of the execution of
   getcode_test25, and with the tests peekchar_test15 and
   peekchar_tes16

# Case 21

There are some arity mismatch issues. 

This problem occurrs in the following tests:

    - currentflag_test1

The test op_test1 and op_test9 also provoke an arity mismatch error
but surprisingly both tests succeed. As this arity mismatch error does
not affect the execution of the other tests these two tests have not
been changed.

# NON IMPLEMENTED TESTS

According to the ISO standard the value of the flag 'bounded' is
implementation defined. If the value of this flag is true, integer arithmetic
is performed correctly only if the operands and mathematically correct result
all lie in the closed_interval (min_integer,max_integer). If the value of this
flag is false, integer arithmetic is always permormed correctly and a goal
current_prolog_flag(max_integer,N) or current_prolog_flag(min_integer,N) will
fail. In Ciao the value of this flag is false, therefore I have chosen not to
include those tests from the standard that checks the max_integer or
min_integer defined since these tests do not have importance in Ciao.

These tests, specified in the page 118 form the ISO standard, are:

    - eval56
    - eval57
    - eval58
    - eval59
    - eval60

# POSSIBLE FUNCIONALITIES TO ADD TO THE ASSERTION TESTS

Altough most of the tests succeed in Ciao I believe it would be beneficial to add some funcionality to the assertion
tests that allow:

 - Check the postconditions of a test even when it has
   failed. Sometimes the expected result for a test is
   failure. However, if a test fails it does not mean that the
   postconditions do not have to be checked. The postconditions allow
   to check that the changes carried out by a test are the changes
   that are expected, in such a way that even when the expected result
   of a test is failure and the test fails, this test should only be
   considered to have failed if it does not meet the postcondition
   established for it.

   Example: read_test4

      - It should be a good a idea to be able to specify more than one
        error for one test. Sometimes, in the execution of one
        predicate, it meets more than one error condition so it is an
        implementation dependent decision which one to raise. It is
        because of this reason I think it would be a good idea to
        allow specification of all the possible errors that a test
        might expect.
").
