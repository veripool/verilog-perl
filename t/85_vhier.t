#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vhier...\n";

vhier ("t/85_vhier_cells.out",   "--cells");
vhier ("t/85_vhier_inpfiles.out",   "--input-files");
vhier ("t/85_vhier_modfiles.out",   "--module-files");

sub vhier {
    my $checkname = shift;
    my $flags = shift;

    my $out = "test_dir/vhier.v";
    run_system ("${PERL} vhier ${flags} --nomissing -y verilog v_hier_top.v -o $out");
    ok(-r $out);
    #run_system ("/bin/cp $out $checkname");
    ok(files_identical ($checkname, $out));
}
