#!/usr/bin/perl -w
# $Revision: 1.17 $$Date$$Author$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2005 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 4 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vpm...\n";

# Preprocess the files
mkdir "test_dir/.vpm", 0777;
run_system ("${PERL} vpm --nostop -o test_dir/.vpm --date -y verilog/");
ok(1);
ok(-r 'test_dir/.vpm/pli.v');

my $orig_lines = lines_in("verilog/example.v");
my $new_lines = lines_in("test_dir/.vpm/example.v");
print "Line count: $orig_lines =? $new_lines\n";
ok($orig_lines==$new_lines);

# Build the model
unlink "simv";
chdir 'test_dir';
if ($ENV{VCS_HOME} && -r "$ENV{VCS_HOME}/bin/vcs") {
    run_system (# We use VCS, insert your simulator here
		"$ENV{VCS_HOME}/bin/vcs"
		# vpm uses `pli to point to the hiearchy of the pli module
		." +define+pli=pli"
		# vpm uses `__message_on to point to the message on variable
		." +define+__message_on=pli.message_on"
		# Read files from .vpm BEFORE reading from other directories
		." +librescan +libext+.v -y .vpm"
		# Finally, read the needed top level file
		." .vpm/example.v"
		);
    # Execute the model (VCS is a compiled simulator)
    run_system ("./simv");
    unlink ("./simv");
    ok(1);
}
elsif ($ENV{CDS_INCISIVE_HOME} && -d $ENV{CDS_INCISIVE_HOME}) {
    run_system ("ncverilog"
		." -q"
		# vpm uses `pli to point to the hiearchy of the pli module
		." +define+pli=pli"
		# vpm uses `__message_on to point to the message on variable
		." +define+__message_on=pli.message_on"
		# Read files from .vpm BEFORE reading from other directories
		." +librescan +libext+.v -y .vpm"
		# Finally, read the needed top level file
		." .vpm/example.v"
		);
    ok(1);
}
else {
    warn "\n";
    warn "*** You do not seem to have VCS or NC-Verilog installed, not running rest of test.\n";
    warn "*** (If you do not own VCS/NC-Verilog, ignore this warning).\n";
    skip(1,1);
}
chdir '..';

sub lines_in {
    my $filename = shift;
    my $fh = IO::File->new($filename) or die "%Error: $! $filename";
    my @lines = $fh->getlines();
    return $#lines;
}
