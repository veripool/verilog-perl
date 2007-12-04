#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2007-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { require "t/test_utils.pl"; }
my @execs = glob ("blib/script/[a-z]*");
plan tests => (2 * ($#execs+1));

foreach my $exe (@execs) {
    print "Doc test of: $exe\n";
    ok (-e $exe);
    my $help = `$PERL $exe --help 2>&1`;
    if ($exe =~ /vsplitmodule/) {
	skip("vsplitmodule is only example (harmless)",1);
    } else {
	ok ($help =~ /DISTRIBUTION/);
    }
}
