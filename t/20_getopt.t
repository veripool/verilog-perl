#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2020 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;
use Cwd;

BEGIN { plan tests => 15 }
BEGIN { require "./t/test_utils.pl"; }

use Verilog::Getopt;
ok(1, "use");

$Verilog::Getopt::Debug = 1;

my $opt = new Verilog::Getopt;
ok(1, "new");

$ENV{DOT} = ".";
is($opt->file_substitute('Fred/$DOT/$NOT_SET_IN_ENV/$DOT'), 'Fred/./$NOT_SET_IN_ENV/.');

my @param = qw ( +libext+t
		 +incdir+t
		 +define+foo=bar
		 +define+foo2
		 +define+foo3=3+foo4
		 -v libdir
		 -y moddir
		 -Dbaz=bar
		 -Iincdir2
		 -f $DOT/t/20_getopt.opt
		 -F $DOT/t/20_getopt.opt
		 passthru
		 );

my @left = $opt->parameter(@param);
print join(" ",@left),"\n";
is ($#left, 0);	# passthru

ok ($opt->defvalue('read_opt_file'));

my $fp = $opt->file_path('20_getopt.t');
print "fp $fp\n";
ok (($fp eq (Cwd::abs_path("t")."/20_getopt.t"))
    || ($fp eq "t/20_getopt.t"));

my @out = $opt->get_parameters();
print "OUT: ",(join(" ",@out)),"\n";
is ($#out, 19);

{
    my $opt2 = new Verilog::Getopt ();
    my @left2 = $opt2->parameter(@out);
    print "LEFT: ",join(" ",@left2),"\n";
    my @out2 = $opt->get_parameters();
    print "LEFT: ",join(" ",@out2),"\n";
    is_deeply(\@out2, [qw(+define+baz=bar +define+foo=bar +define+foo2
                          +define+foo3=3  +define+foo4
                          +define+read_opt_file=1
 			  +libext+.v+t +incdir+. +incdir+t +incdir+incdir2
 			  -y . -y moddir -y y_library_path -y t/y_library_path -v libdir)]);
}

{
    my $opt2 = new Verilog::Getopt (gcc_style=>1, vcs_style=>0);
    my @left2 = $opt2->parameter(@param);
    print "LEFT: ",join(" ",@left2),"\n";
    is_deeply(\@left2, [qw(+libext+t +incdir+t +define+foo=bar +define+foo2
                           +define+foo3=3+foo4
                           -v libdir -y moddir -y y_library_path -y y_library_path passthru)]);
}

{
    my $opt2 = new Verilog::Getopt (gcc_style=>0, vcs_style=>1);
    my @left2 = $opt2->parameter(@param);
    print "LEFT: ",join(" ",@left2),"\n";
    is_deeply(\@left2, [qw(-Dbaz=bar -Iincdir2 -Dread_opt_file=1 -Dread_opt_file=1 passthru)]);
}

{
    my $opt2 = new Verilog::Getopt (gcc_style=>0, vcs_style=>1);
    {
	local $SIG{__WARN__} = sub {},
	my @left2 = $opt2->parameter("+define+foo=bar", "+define+foo=baz");
    }
    my @out2 = $opt2->get_parameters();
    is_deeply($out2[0], qw(+define+foo=baz));
}

$opt->map_directories(sub{s![a-z]!x!; $_});
ok(1);

ok($opt->file_skip_special(".svn"));
ok(!$opt->file_skip_special("svn"));
ok($opt->file_skip_special("foo/bar/baz/CVS"));
