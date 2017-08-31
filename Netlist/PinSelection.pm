# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::PinSelection;

use vars qw($VERSION);
use strict;
use warnings;

$VERSION = '3.427';

######################################################################
#### Methods

## Constructor
sub new {
    my ($class, $netname, $msb, $lsb) = @_;

    my $self = bless({}, $class);
    $self->{_netname} = $netname;
    $self->{_msb} = $msb;
    $self->{_lsb} = $lsb;
    return $self;
}

## Standard accessors
sub netname {
    # ($self, $new) = @_;
    $_[0]->{_netname} = $_[1] if (@_ == 2);
    return $_[0]->{_netname};
}

sub lsb {
    # ($self, $new) = @_;
    $_[0]->{_lsb} = $_[1] if (@_ == 2);
    return $_[0]->{_lsb};
}

sub msb {
    # ($self, $new) = @_;
    $_[0]->{_msb} = $_[1] if (@_ == 2);
    return $_[0]->{_msb};
}

## Member functions
sub bracketed_msb_lsb {
    my $self = shift;
    my $out = "";
    # Handle sized constant numbers (e.g., 7'b0) distinctively
    # but leave unsized constants (msb/lsb undefined) alone.
    if ($self->netname =~ /^'/) {
	$out .= $self->msb + 1 if defined($self->msb);
	$out .= $self->netname;
    } else {
	$out .= $self->netname;
	if (defined($self->msb)) {
	    if ($self->msb == $self->lsb) {
		$out .= "[".$self->msb."]";
	    } else {
		$out .= "[".$self->msb.":".$self->lsb."]";
	    }
	}
    }
    return $out;
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::PinSelection

=head1 DESCRIPTION

Verilog::Netlist::PinSelection objects are used by Verilog::Netlist::Pin
to define ranges of nets attached to the respective pin of a cell.

=head1 ACCESSORS

=over 4

=item $self->netname

Name of the respective net, or, if use_pinselects is disabled, the string
representation of the whole pin value. In the case of a sized constant only
the part following the ' is stored while the width is encoded in the msb
and lsb fields.

=item $self->lsb

Least significent bit of the underlying net within the selection.

=item $self->msb

Most significent bit of the underlying net within the selection.

=back

=head1 MEMBER FUNCTIONS

=over 4

=item $self->bracketed_msb_lsb

Returns the common string representation of a vectored net, e.g. netA[15:8].

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2017 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Stefan Tauner <tauner@technikum-wien.at>
Wilson Snyder <wsnyder@wsnyder.org>

# =head1 SEE ALSO

# L<Verilog-Perl>,
# L<Verilog::Netlist>
# L<Verilog::Netlist::Pin>

=cut
