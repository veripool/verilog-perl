#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2021 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 2 }
BEGIN { require "./t/test_utils.pl"; }

# bug300
my $cmd = "${PERL} ./vhier --input-files -y verilog t_86_vhier_tick.v";
my $out = `$cmd`;
is($?,0,$cmd);
like($out, qr//, $cmd);
