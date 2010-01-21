#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2009-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;

BEGIN { plan tests => 3 }
BEGIN { require "t/test_utils.pl"; }

use Verilog::Std;
ok(1);

ok (Verilog::Std::std() =~ /endpackage/);

# Make sure data sticks around
ok (Verilog::Std::std() =~ /endpackage/);
