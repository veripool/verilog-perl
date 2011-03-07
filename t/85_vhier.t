#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2011 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 10 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vhier...\n";

vhier ("t/85_vhier_cells.out",	    "--cells");
vhier ("t/85_vhier_inpfiles.out",   "--input-files");
vhier ("t/85_vhier_resolvefiles.out","--resolve-files");
vhier ("t/85_vhier_modfiles.out",   "--module-files --language 2001");
vhier ("t/85_vhier_topmodule.out",  "--module-files --top-module v_hier_sub");

sub vhier {
    my $checkname = shift;
    my $flags = shift;

    my $out = "test_dir/vhier.v";
    my $cmd = "${PERL} ./vhier ${flags} --nomissing -y verilog v_hier_top.v -o $out";
    run_system ($cmd);
    ok(-r $out, "vhier outputted from: $cmd");
    #run_system ("/bin/cp $out $checkname");
    ok(files_identical ($checkname, $out), "vhier file compare");
}
