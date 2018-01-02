# Verilog - Verilog Perl Modport
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::ModPort;

use Verilog::Netlist;
use Verilog::Netlist::Net;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::ModPort::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.448';

structs('new',
	'Verilog::Netlist::ModPort::Struct'
	=>[name     	=> '$', #'	# Name of the module
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   module	=> '$', #'	# Interface is a member of
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   comment	=> '$', #'	# Comment provided by user
	   _ports	=> '%',		# hash of Verilog::Netlist::Ports
	   _portsordered=> '@',		# list of Verilog::Netlist::Ports as ordered in list of ports
	   _nets	=> '%',		# hash of Verilog::Netlist::Nets
	   ]);

sub delete {
    my $self = shift;
    foreach my $oref ($self->nets) {
	$oref->delete;
    }
    foreach my $oref ($self->ports) {
	$oref->delete;
    }
    my $h = $self->module->{_modports};
    delete $h->{$self->name};
    return undef;
}

######################################################################

sub netlist { return $_[0]->module->netlist; }

sub is_top {}  # Ignored, for module compatibility

sub keyword { return 'modport'; }

sub logger {
    return $_[0]->netlist->logger;
}

sub find_net {
    my $self = shift;
    my $search = shift;
    my $rtn = $self->_nets->{$search}||"";
    #print "FINDNET ",$self->name, " SS $search  $rtn\n";
    return $self->_nets->{$search} || $self->_nets->{"\\".$search." "};
}
sub find_port {
    my $self = shift;
    my $search = shift;
    return $self->_ports->{$search} || $self->_ports->{"\\".$search." "};
}
sub find_port_by_index {
    my $self = shift;
    my $myindex = shift;
    # @{$self->_portsordered}[$myindex-1] returns the name of
    # the port in the module at this index.  Then, this is
    # used to find the port reference via the port hash
    return $self->_ports->{@{$self->_portsordered}[$myindex-1]};
}

sub attrs_sorted {
    return (sort {$a cmp $b} @{$_[0]->attrs});
}
sub nets {
    return (values %{$_[0]->_nets});
}
sub nets_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_nets}));
}
sub ports {
    return (values %{$_[0]->_ports});
}
sub ports_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_ports}));
}
sub ports_ordered {
    my $self = shift;
    return map {$self->_ports->{$_}} @{$self->_portsordered};
}

sub nets_and_ports_sorted {
    return Verilog::Netlist::Module::nets_and_ports_sorted(@_);
}

sub new_attr {
    my $self = shift;
    my $clean_text = shift;
    push @{$self->attrs}, $clean_text;
}

sub new_net {
    my $self = shift;
    # @_ params
    # Create a new net under this
    my $netref = new Verilog::Netlist::Net (direction=>'net', data_type=>'wire',
					    @_,
					    module=>$self, );
    $self->_nets ($netref->name(), $netref);
    return $netref;
}

sub new_port {
    my $self = shift;
    # @_ params
    # Create a new port under this module
    my $portref = new Verilog::Netlist::Port (@_, module=>$self,);
    $self->_ports ($portref->name(), $portref);
    return $portref;
}

sub _link {
    my $self = shift;
    # Ports create nets, so link ports before nets
    foreach my $oref ($self->ports) {
	$oref->_link();
    }
}

sub lint {
    my $self = shift;
    if ($self->netlist->{use_vars}) {
	foreach my $oref ($self->ports) {
	    $oref->lint();
	}
    }
}

sub verilog_text {
    my $self = shift;
    my @out = "modport ".$self->name." (\n";
    my $indent = "   ";
    # Port list
    my $comma="";
    push @out, $indent;
    foreach my $oref ($self->ports_sorted) {
	push @out, $comma, $oref->verilog_text;
	$comma = ", ";
    }
    push @out, ");\n";
    push @out, "endmodport\n";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"ModPort:",$self->name(),"  File:",$self->filename(),"\n";
    if (!$norecurse) {
	foreach my $oref ($self->ports_sorted) {
	    $oref->dump($indent+2);
	}
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::ModPort - ModPort within a Verilog Interface

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $interface = $netlist->find_interface('name');
  my $modport =  $interface->find_modport('name')

=head1 DESCRIPTION

A Verilog::Netlist::ModPort object is created by
Verilog::Netlist::Interface for every modport under the interface.

=head1 METHODS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->dump

Prints debugging information for this modport.

=item $self->find_port(I<name>)

Returns Verilog::Netlist::Net matching given name.

=item $self->find_port_by_index

Returns the port name associated with the given index.

=item $self->module

Returns Verilog::Netlist::Interface the ModPort belongs to.

=item $self->lint

Checks the modport for errors.

=item $self->name

The name of the modport.

=item $self->netlist

Reference to the Verilog::Netlist the modport is under.

=item $self->nets

Returns list of references to Verilog::Netlist::Net in the interface.

=item $self->nets_sorted

Returns list of name sorted references to Verilog::Netlist::Net in the
interface.

=item $self->nets_and_ports_sorted

Returns list of name sorted references to Verilog::Netlist::Net and
Verilog::Netlist::Port in the modport.

=item $self->ports

Returns list of references to Verilog::Netlist::Port in the modport.

=item $self->ports_ordered

Returns list of references to Verilog::Netlist::Port in the modport
sorted by pin number.

=item $self->ports_sorted

Returns list of references to Verilog::Netlist::Port in the modport
sorted by name.

=item $self->verilog_text

Returns verilog code which represents this modport.  Returned as an array
that must be joined together to form the final text string.  The netlist
must be already ->link'ed for this to work correctly.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2018 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist::Interface>
L<Verilog::Netlist>

=cut
