#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2016 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 17 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vhier...\n";

vhier ("t/85_vhier_cells.out",	    "--cells");
vhier ("t/85_vhier_inpfiles.out",   "--input-files");
vhier ("t/85_vhier_resolvefiles.out","--resolve-files");
vhier ("t/85_vhier_modfiles.out",   "--module-files --language 2001");
vhier ("t/85_vhier_topmodule.out",  "--module-files --top-module v_hier_sub");
vhier ("t/85_vhier_forest.out",	    "--forest --instance");
vhier ("t/85_vhier_skiplist.out",   "--forest --instance --skiplist t/85_vhier_skiplist.dat");
vhier ("t/85_vhier_xml.out",	    "--xml --cells --input-files --module-files --missing-modules");
check_valid_xml("test_dir/vhier.out");

sub vhier {
    my $checkname = shift;
    my $flags = shift;

    my $out = "test_dir/vhier.out";
    my $cmd = "${PERL} ./vhier ${flags} --nomissing -y verilog v_hier_top.v -o $out";
    run_system ($cmd);
    ok(-r $out, "vhier outputted from: $cmd");
    #run_system ("/bin/cp $out $checkname");
    ok(files_identical ($out, $checkname), "vhier file compare");
}

sub check_valid_xml {
    my $filename = shift;
  SKIP: {
      if ((eval("use XML::Simple; 1;")||0) == 1) {
	  my $xs = new XML::Simple('ForceArray' => [qw(entry)],);
	  ok ($xs->XMLin($filename), "Validate XML");
      } else {
	  skip("author only XML test (harmless)",1);
      }
    }
}
