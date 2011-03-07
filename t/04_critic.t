#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2011 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;
use warnings;

if (!$ENV{VERILATOR_AUTHOR_SITE} || $ENV{HARNESS_NO_CRITIC}) {
    plan tests => 1;
    skip("author only test (harmless)",1);
} else {
    eval "use Test::Perl::Critic;";
    if ($@) {
	plan tests => 1;
	skip("Test::Perl::Critic not installed so ignoring check (harmless)",1);
    } else {
	#-profile => "t/04_critic.rc"
	Test::Perl::Critic->import( -verbose=>9,
				    -exclude=>['ProhibitExplicitReturnUndef',
					       'ProhibitNoStrict',
					       'ProhibitStringyEval'],
	    );
	all_critic_ok();
    }
}
