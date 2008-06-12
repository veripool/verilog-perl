#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2007-2008 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { require "t/test_utils.pl"; }
eval { use ExtUtils::Manifest; };
my $manifest = ExtUtils::Manifest::maniread();
plan tests => (1 + (keys %{$manifest}));
ok(1);

foreach my $filename (keys %{$manifest}) {
    print "Space test of: $filename\n";
    my $wholefile = wholefile($filename);
    if ($wholefile
	&& $wholefile !~ /[ \t]+\n/
	&& $wholefile !~ /^[ \t]*[ ]+\t/) {
	ok(1);
    } elsif ($filename =~ m!\.out!) {
	skip(1,"File doesn't need check; harmless");
    } else {
	warn "%Error: $filename: Bad indentation\n";
	ok(0);
    }
}
