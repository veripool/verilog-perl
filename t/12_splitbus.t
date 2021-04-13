#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2021 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { plan tests => 5 }
BEGIN { require "./t/test_utils.pl"; }

use Verilog::Language;
ok(1, "use");

array_ck (['none',
	   ],
	Verilog::Language::split_bus
	  ("none"));

array_ck (['ff[1]',
	   'ff[2]',
	   ],
	Verilog::Language::split_bus
	  ("ff[1:2]"));

array_ck (['ff[5]e',
	   'ff[3]e',
	   'ff[1]e',
	   'ff[4]e',
	   ],
	Verilog::Language::split_bus
	  ("ff[5:1:2,4]e"));

array_ck (['ff[3]  bar [10] end',
	   'ff[2]  bar [9] end',
	   'ff[1]  bar [8] end',
	   'ff[3]  bar [7] end',
	   'ff[2]  bar [6] end',
	   'ff[1]  bar [5] end',
	   'ff[3]  bar [4] end',
	   'ff[2]  bar [3] end',
	   ],
	Verilog::Language::split_bus
	  ("ff[3:1]  bar [4'ha:3] end"));

sub array_ck {
    my $checkref = shift;
    my @got = @_;
    is_deeply(\@got, $checkref);
}
