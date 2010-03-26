#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2010-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;
use warnings;

if (!$ENV{VERILATOR_AUTHOR_SITE}) {
    plan tests => 1;
    skip("author only test (harmless)",1);
} else {
    eval "use Test::YAML::Meta;";
    if ($@) {
	plan tests => 1;
	skip("Test::YAML::Meta not installed so ignoring check (harmless)",1);
    } else {
	meta_yaml_ok();
    }
}
