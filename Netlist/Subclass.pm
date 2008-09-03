# Verilog - Verilog Perl Interface
######################################################################
#
# Copyright 2000-2008 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
######################################################################

package Verilog::Netlist::Subclass;
use Verilog::Netlist::Logger;
use Class::Struct;
require Exporter;
$VERSION = '3.041';
@ISA = qw(Exporter);
@EXPORT = qw(structs);
use strict;

# Maybe in the future.  For now all users of this must do it themselves
#struct ('Verilog::Netlist::Subclass'
#	 =>[name     	=> '$', #'	# Name of the element
#	    filename 	=> '$', #'	# Filename this came from
#	    lineno	=> '$', #'	# Linenumber this came from
#	    logger	=> '%',		# Logger object, or undef
#	    userdata	=> '%',		# User information
#	    ]);

######################################################################
#### Member functions

sub fileline {
    my $self = shift;
    return ($self->filename||"").":".($self->lineno||"");
}

######################################################################
#### Error Handling

our $_Subclass_Logger_Warned;

sub logger {
    my $self = shift;
    # This provides forward compatibility to derived classes written before
    # Verilog-Perl 3.041.  At some point this function will be removed; all
    # new derived classes should provide an override for this function.
    if (!$_Subclass_Logger_Warned) {
	warn "-Info: Object class missing logger method, update the package?: ".ref($self)."\n";
	$_Subclass_Logger_Warned = Verilog::Netlist::Logger->new();
    }
    return $_Subclass_Logger_Warned;
}

sub errors {
    my $self = shift;
    return $self->logger->errors;
}
sub warnings {
    my $self = shift;
    return $self->logger->warnings;
}

# Methods
sub info {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->info($objref,@_);
}

sub warn {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->warn($objref,@_);
}

sub error {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->error($objref,@_);
}

sub exit_if_error {
    my $self = shift;
    return $self->logger->exit_if_error(@_);
}

sub unlink_if_error {
    my $self = shift;
    # Not documented; Depreciated in Verilog-Perl 3.041.
    # Applications should call the logger object's unlink_if_error directly.
    return $self->logger->unlink_if_error(@_);
}

######################################################################
######################################################################
######################################################################
# DANGER WILL ROBINSON!
# Prior to perl 5.6, Class::Struct's new didn't bless the arguments,
# or allow parameter initialization!  We'll override it!

sub structs {
    my $func = shift;
    Class::Struct::struct (@_);
    my $baseclass = $_[0];
    (my $overclass = $baseclass) =~ s/::Struct$//;
    if ($] < 5.006) {
	# Now override what class::struct created
	eval "
            package $overclass;
            sub ${func} {
		my \$class = shift;
		my \$self = new $baseclass;
		bless \$self, \$class;
		while (\@_) {
		    my \$param = shift; my \$value = shift;
		    eval (\"\\\$self->\$param(\\\$value);\");  # Slow, sorry.
		}
		return \$self;
	    }";
    } else {
	#print \"NEW \",join(' ',\@_),\"\\n\";
	eval "
            package $overclass;
            sub ${func} {
		my \$class = shift;
		my \$self = new $baseclass (\@_);
		bless \$self, \$class;
	    }";
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Subclass - Common routines for all classes

=head1 SYNOPSIS

  use Verilog::Netlist::Subclass;
  package Verilog::Netlist::Something;
  @ISA = qw(Verilog::Netlist::Subclass);

  ...

  $self->info("We're here\n");
  $self->warn("Things look bad\n");
  $self->error("Things are even worse\n");
  $self->exit_if_error();

=head1 DESCRIPTION

The Verilog::Netlist::Subclass is used as a base class for all
Verilog::Netlist::* structures.  It is mainly used so that $self->warn()
and $self->error() will produce consistent results.

=head1 MEMBER FUNCTIONS

=over 4

=item $self->error (I<Text...>)

Print an error in a standard format.

=item $self->errors()

Return number of errors detected.

=item $self->exit_if_error()

Exits the program if any errors were detected.

=item $self->filename()

The filename number the entity was created in.

=item $self->info (I<Text...>)

Print a informational in a standard format.

=item $self->lineno()

The line number the entity was created on.

=item $self->logger()

The class to report errors using, generally a Verilog::Netlist::Logger
object.

=item $self->userdata (I<key>)
=item $self->userdata (I<key>, I<data>)

Sets (with two arguments) or retrieves the specified key from an opaque
hash.  This may be used to store application data on the specified node.

=item $self->warn (I<Text...>)

Print a warning in a standard format.

=item $self->warnings()

Return number of warnings detected.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2008 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist>

=cut
