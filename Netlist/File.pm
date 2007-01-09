# Verilog - Verilog Perl Interface
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::File;
use Class::Struct;
use Carp;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::File::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.361';
use strict;

structs('new',
	'Verilog::Netlist::File::Struct'
	=>[name		=> '$', #'	# Filename this came from
	   basename	=> '$', #'	# Basename of the file
	   netlist	=> '$', #'	# Netlist is a member of
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   comment	=> '$', #'	# Comment provided by user
	   is_libcell	=> '$',	#'	# True if is a library cell
	   # For special procedures
	   _modules	=> '%',		# For autosubcell_include
	   ]);
	
######################################################################
######################################################################
#### Read class

package Verilog::Netlist::File::Parser;
use Verilog::SigParser;
use Verilog::Preproc;
use strict;
use vars qw (@ISA);
@ISA = qw (Verilog::SigParser);

sub new {
    my $class = shift;
    my %params = (@_);	# filename=>

    # A new file; make new information
    $params{fileref} or die "%Error: No fileref parameter?";
    $params{netlist} = $params{fileref}->netlist;
    my $parser = $class->SUPER::new (%params,
				     modref=>undef,	# Module being parsed now
				     cellref=>undef,	# Cell being parsed now
				     _cmtref=>undef,	# Object to attach comments to
				     );
    
    my @opt;
    push @opt, (options=>$params{netlist}{options}) if $params{netlist}{options};
    my $meta = $params{metacomment};
    if ($meta) {
	die "%Error: 'metacomment' arg of Netlist or read_file() must be a hash,"
	    unless (ref($meta) eq 'HASH');
	push @opt, metacomments=>[ grep({ $meta->{$_} } keys %$meta) ];
	push @opt, keep_comments=>1;
    } elsif ($params{netlist}{keep_comments}) {
	push @opt, keep_comments=>$params{netlist}{keep_comments};
    } else {
	push @opt, keep_comments=>0;
    }
    push @opt, keep_whitespace=>0;
    my $preproc = Verilog::Preproc->new(@opt);
    $preproc->open($params{filename});
    $parser->parse_preproc_file ($preproc);
    return $parser;
}

sub module {
    my $self = shift;
    my $keyword = shift;
    my $module = shift;
    my $orderref = shift;
    my $in_celldefine = shift;

    my $fileref = $self->{fileref};
    my $netlist = $self->{netlist};
    print "Module $module\n" if $Verilog::Netlist::Debug;

    $self->{modref} = $netlist->new_module
	 (name=>$module,
	  is_libcell=>($fileref->is_libcell() || $in_celldefine),
	  filename=>$self->filename, lineno=>$self->lineno);
    $fileref->_modules($module, $self->{modref});
    $self->{_cmtref} = $self->{modref};
}

sub port {
    my $self = shift;
    my $name = shift;
    push @{$self->{modref}->_portsordered}, $name;
}

sub attribute {
    my $self = shift;
    my $keyword = shift;
    my $text = shift;

    my $modref = $self->{modref};
    my ($category, $name, $eql, $rest);
    if ($text =~ m!^([\$A-Za-z]\w*)\s+ (\w+) (\s*=\s*)? (.*) !x) {
	($category, $name, $eql, $rest) = ($1, $2, ($3 || ""), $4);
	if ($eql ne "") { $eql = "="; }
	my $cleaned = ($category ." ". $name . $eql . $rest);

	if ($Verilog::Netlist::Debug) {
	    printf +("%d: Attribute %s, '%s'\n",
		     $self->lineno, $keyword, $cleaned);
	}
	# Treat as module-level if attribute appears before any declarations.
	if ($keyword eq "module") {
	    return $self->warn("Ignored '$category $name' attribute before end of '$keyword' statement")
		unless $modref;
	    my $attr = $modref->new_attr ($cleaned);
	}
    }
}

sub signal_decl {
    my $self = shift;
    my $inout = shift;
    my $netname = shift;
    my $vector = shift;
    my $array = shift;
    my $signed = shift;
    print " Sig $netname $inout\n" if $Verilog::Netlist::Debug;

    my $msb;
    my $lsb;
    if ($vector && $vector =~ /\[(.*):(.*)\]/) {
	$msb = $1; $lsb = $2;
    } elsif ($vector && $vector =~ /\[(.*)\]/) {
	$msb = $lsb = $1;
    }

    my $modref = $self->{modref};
    if (!$modref) {
	return $self->error ("Signal declaration outside of module definition", $netname);
    }

    if ($inout eq "reg" || $inout eq "trireg"
	|| $inout eq "wire" || $inout eq "wand" || $inout eq "wor"
	|| $inout eq "tri" || $inout eq "triand" || $inout eq "trior"
	|| $inout eq "tri0" || $inout eq "tri1"
	|| $inout eq "supply0" || $inout eq "supply1"
	) {
	my $net = $modref->find_net ($netname);
	$net or $net = $modref->new_net
	    (name=>$netname,
	     filename=>$self->filename, lineno=>$self->lineno,
	     simple_type=>1, type=>$inout, array=>$array,
	     comment=>undef, msb=>$msb, lsb=>$lsb,
	     signed=>$signed,
	     );
	$net->type($inout);  # If it's already declared as in/out etc, mark the type
	$self->{_cmtref} = $net;
    }
    elsif ($inout =~ /(inout|in|out)(put|)$/) {
	my $dir = $1;
	##
	my $net = $modref->find_net ($netname);
	$net or $net = $modref->new_net
	    (name=>$netname,
	     filename=>$self->filename, lineno=>$self->lineno,
	     simple_type=>1, type=>'wire', array=>$array,
	     comment=>undef, msb=>$msb, lsb=>$lsb,
	     signed=>$signed,
	     );
	$self->{_cmtref} = $net;
	##
	my $port = $modref->new_port
	    (name=>$netname,
	     filename=>$self->filename, lineno=>$self->lineno,
	     direction=>$dir, type=>'wire',
	     array=>$array, comment=>undef,);
    }
    else {
	return $self->error ("Strange signal type: $inout", $inout);
    }
}

sub instant {
    my $self = shift;
    my $submodname = shift;
    my $instname = shift;
    my $params = shift;

    print " Cell $instname\n" if $Verilog::Netlist::Debug;
    my $modref = $self->{modref};
    if (!$modref) {
	 return $self->error ("CELL outside of module definition", $instname);
    }
    $self->{cellref} = $modref->new_cell
	 (name=>$instname, 
	  filename=>$self->filename, lineno=>$self->lineno,
	  submodname=>$submodname, params=>$params,);
    $self->{_cmtref} = $self->{cellref};
}

sub pin {
    my $self = shift;
    my $pin = shift;
    my $net = shift;
    my $number = shift;
    my $hasnamedports = shift;

    print "   Pin $pin  $net $number \n" if $Verilog::Netlist::Debug;
    my $cellref = $self->{cellref};
    if (!$cellref) {
	return $self->error ("PIN outside of cell definition", $net);
    }
    my $pinref = $cellref->new_pin (name=>$pin,
				    portname=>$pin,
				    portnumber=>$number,
				    pinnamed=>$hasnamedports,
				    filename=>$self->filename, lineno=>$self->lineno,
				    netname=>$net, );
    # If any pin uses call-by-name, then all are assumed to use call-by-name
    $cellref->byorder(1) if !$hasnamedports;
    $self->{_cmtref} = $pinref;
}

sub ppdefine {
    my $self = shift;
    my $defvar = shift;
    my $definition = shift;
    if ($self->{netlist}{options}) {
	$self->{netlist}{options}->defvalue($defvar,$definition);
    }
}

sub ppinclude {
    my $self = shift;
    my $defvar = shift;
    my $definition = shift;
    $self->error("No `includes yet.\n");
}

sub keyword {
    # OVERRIDE Verilog::Parse calls when keyword occurs
    my $self = shift;	# Parser invoked
    $self->SUPER::keyword(@_);
    $self->{_cmtref} = undef;
}

sub comment {
    my $self = shift;
    # OVERRIDE Verilog::Parse calls when comment occurs
    $self->SUPER::comment(@_);
    my $text = shift;	# Includes comment delimiters
    if ($self->{_cmtref}) {
	my $old = $self->{_cmtref}->comment();
	if (defined $old) { $old .= "\n"; } else { $old=""; }
	$old .= $text;
	$self->{_cmtref}->comment($old);
    }
}

sub error {
    my $self = shift;
    my $text = shift;

    my $fileref = $self->{fileref};
    # Call Verilog::Netlist::Subclass's error reporting, it will track # errors
    $fileref->error ($self, "$text\n");
}

sub warn {
    my $self = shift;
    my $text = shift;

    my $fileref = $self->{fileref};
    $fileref->warn ($self, "$text\n");
}

package Verilog::Netlist::File;

######################################################################
######################################################################
#### Functions

sub read {
    my %params = (lookup_type=>'module',
		  @_);	# netlist=>, filename=>, per-file options

    my $filename = $params{filename} or croak "%Error: ".__PACKAGE__."::read_file (filename=>) parameter required, stopped";
    my $netlist = $params{netlist} or croak ("Call Verilog::Netlist::read_file instead,");

    my $filepath = $netlist->resolve_filename($filename, $params{lookup_type});
    if (!$filepath) {
	if ($params{error_self}) { $params{error_self}->error("Cannot find $filename\n"); }
	elsif (!defined $params{error_self}) { die "%Error: Cannot find $filename\n"; }  # 0=suppress error
	return undef;
    }
    print __PACKAGE__."::read_file $filepath\n" if $Verilog::Netlist::Debug;

    my $fileref = $netlist->new_file (name=>$filepath,
				      is_libcell=>$params{is_libcell}||0,
				      );

    my $parser = Verilog::Netlist::File::Parser->new
	( fileref=>$fileref,
	  filename=>$filepath,	# for ->read
	  metacomment=>($params{metacomment} || $netlist->{metacomment}),
	  keep_comments=>($params{keep_comments} || $netlist->{keep_comments}),
	  );
    return $fileref;
}

sub _link {
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"File:",$self->name(),"\n";
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::File - File containing Verilog code

=head1 SYNOPSIS

  use Verilog::Netlist;

  my $nl = new Verilog::Netlist;
  my $fileref = $nl->read_file (filename=>'filename');

=head1 DESCRIPTION

Verilog::Netlist::File allows Verilog files to be read and written.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->basename

The filename of the file with any path and . suffix stripped off.

=item $self->name

The filename of the file.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->read

Generally called as $netlist->read_file.  Pass a hash of parameters.  Reads
the filename=> parameter, parsing all instantiations, ports, and signals,
and creating Verilog::Netlist::Module structures.

=item $self->dump

Prints debugging information for this file.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.com/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2006 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
