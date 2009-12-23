#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;

BEGIN { plan tests => 23 }
BEGIN { require "t/test_utils.pl"; }

use Verilog::Language;
ok(1);

ok (Verilog::Language::is_keyword("input"));
ok (!Verilog::Language::is_keyword("not_input"));
ok (Verilog::Language::is_compdirect("`define"));

ok (Verilog::Language::language_standard() eq '1800-2009');
ok (Verilog::Language::language_standard('1800-2009') eq '1800-2009');
ok (Verilog::Language::is_keyword("checker"));
ok (Verilog::Language::language_standard('1800-2005') eq '1800-2005');
ok (!Verilog::Language::is_keyword("checker"));
ok (Verilog::Language::is_keyword("do"));
ok (Verilog::Language::language_standard('1364-2005') eq '1364-2005');
ok (Verilog::Language::is_keyword("uwire"));
ok (Verilog::Language::language_standard(2001) eq '1364-2001');
ok (!Verilog::Language::is_keyword("uwire"));
ok (Verilog::Language::is_keyword("generate"));
ok (Verilog::Language::language_standard(1995) eq '1364-1995');
ok (!Verilog::Language::is_keyword("generate"));

ok (Verilog::Language::strip_comments("he/**/l/**/lo") eq "hello");
ok (Verilog::Language::strip_comments("he//xx/*\nllo") eq "he\nllo");
ok (Verilog::Language::strip_comments("he/*xx//..*/llo") eq "hello");
ok (Verilog::Language::strip_comments("he\"//llo\"") eq "he\"//llo\"");

ok ( Verilog::Language::is_gateprim("buf"));
ok (!Verilog::Language::is_gateprim("else"));
