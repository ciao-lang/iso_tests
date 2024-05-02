:- bundle(iso_tests).
% An ISO Prolog test suite for Ciao
version('1.23.0'). % (same as 'core')
depends([
  ciaodbg_extra
]).
alias_paths([
  iso_tests = src
]).
lib('src').
manual('iso_tests', [main='doc/SETTINGS.pl']).
