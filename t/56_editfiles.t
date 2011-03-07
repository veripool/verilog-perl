#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2007-2011 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;
use File::Copy;

BEGIN { plan tests => 9 }
BEGIN { require "t/test_utils.pl"; }

BEGIN { use Verilog::EditFiles; }
ok(1);

{   #Editing
    my $split = Verilog::EditFiles->new();
    ok(1, "new");

    my $edfile = "test_dir/56_editfiles.v";

    $split->edit_file
	(filename => "t/56_editfiles.v",
	 write_filename => $edfile,
	 cb=>sub {
	     my $wholefile = shift;
	     $wholefile =~ s%inside_module%replaced_inside_module%mg;
	     return $wholefile;
	 });
    ok(1, "edit_file");
    ok(files_identical($edfile, "t/56_editfiles_edit.out"), "diff");
}
{
    unlink (glob("test_dir/editout/*.v"));
    my $split = Verilog::EditFiles->new
	(program => "56_editfiles.t",
	 outdir => "test_dir/editout",
	 translate_synthesis => 1,
	 lint_header => "// lint_checking HEADER\n",
	 celldefine => 1,
	 );
    $split->read_and_split(glob("t/56_editfiles.v"));
    ok(1, "read_and_split");
    $split->write_files();
    ok(1, "write_files");
    ok(files_identical("test_dir/editout/a.v", "t/56_editfiles_a.out"), "diff");
    ok(files_identical("test_dir/editout/b.v", "t/56_editfiles_b.out"), "diff");
    $split->write_lint();
    ok(1, "write_lint");
}
