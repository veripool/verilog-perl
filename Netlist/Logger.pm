# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Logger;
require Exporter;
use vars qw($VERSION);
use strict;

$VERSION = '3.466';

# We don't use Verilog::Netlist::Subclass, as this is called from it!

######################################################################
#### Constructors

sub new {
    my $class = shift;
    my $self = {
	_warnings => 0,
	_errors	=> 0,
	_error_unlink_files => {},
	@_
    };
    bless $self, $class;
    return $self;
}

######################################################################
#### Accessors

sub errors {
    my $self = shift;
    $self->{_errors} = shift if $#_>=0;
    return $self->{_errors};
}
sub warnings {
    my $self = shift;
    $self->{_warnings} = shift if $#_>=0;
    return $self->{_warnings};
}

######################################################################
#### Error Handling

sub info {
    my $self = shift;
    my $objref = shift;
    CORE::warn "-Info: ".$objref->fileline.": ".join('',@_);
}

sub warn {
    my $self = shift;
    my $objref = shift;
    CORE::warn "%Warning: ".$objref->fileline.": ".join('',@_);
    $self->warnings($self->warnings+1);
}

sub error {
    my $self = shift;
    my $objref = shift;
    CORE::warn "%Error: ".$objref->fileline.": ".join('',@_);
    $self->errors($self->errors+1);
}

sub exit_if_error {
    my $self = shift;
    my %params = @_;
    my $allow = $params{allow} || "";
    if ($self->errors || ($self->warnings && $allow !~ /warning/)) {
	CORE::warn "Exiting due to errors\n";
	exit(10);
    }
    return ($self->errors + $self->warnings);
}

sub unlink_if_error {
    my $self = shift;
    $self->{_error_unlink_files}{$_[0]} = 1;
}

sub error_unlink {
    my $self = shift;
    foreach my $file (keys %{$self->{_error_unlink_files}}) {
	unlink $file;
	delete $self->{_error_unlink_files}{$file};
    }
}

sub DESTROY {
    my $self = shift;
    my $has_err = $? || $self->errors || $self->warnings;
    if ($has_err) {
	$self->error_unlink;
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Logger - Error collection and reporting

=head1 SYNOPSIS

  use Verilog::Netlist::Logger;

  ...

  my $self = Verilog::Netlist::Logger->new();
  $self->info("We're here\n");
  $self->warn("Things look bad\n");
  $self->error("Things are even worse\n");
  $self->exit_if_error();

=head1 DESCRIPTION

The Verilog::Netlist::Logger is used to report all errors detected by
Verilog::Netlist::* structures.  By default, Verilog::Netlist creates a new
Logger object, and passes it down to all contained objects.  Users may
create their own logger objects to catch or otherwise handle error
messages.

=head1 MEMBER FUNCTIONS

=over 4

=item $self->error(object, I<Text...>)

Print an error about the object in a standard format.  The object must have
a fileline method.

=item $self->exit_if_error([allow=>'warning'])

Exits the program if any errors were detected.  Optionally specify
allow=>'warning' to ignore warnings.

=item $self->info(I<Text...>)

Print an informational about the object in a standard format.  The object
must have a fileline method.

=item $self->lineno()

The line number the entity was created on.

=item $self->unlink_if_error(I<filename>)

Requests the given file be deleted if any errors are detected when the
Logger object is destroyed.  Used for temporary files.

=item $self->warn(I<Text...>)

Print a warning about the object in a standard format.  The object must
have a fileline method.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2019 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist>,
L<Verilog::Netlist::Subclass>

=cut
