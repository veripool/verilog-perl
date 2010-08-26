# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::File;
use Carp;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::File::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.302';

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
	   _interfaces	=> '%',		# For autosubcell_include
	   _modules	=> '%',		# For autosubcell_include
	   ]);

######################################################################
######################################################################
#### Read class

package Verilog::Netlist::File::Parser;
use Verilog::SigParser;
use Verilog::Preproc;
use base qw (Verilog::SigParser);
use strict;

sub new {
    my $class = shift;
    my %params = (preproc => "Verilog::Preproc",
		  @_);	# filename=>

    my $preproc_class = $params{preproc};
    delete $params{preproc}; # Remove as preproc doesn't need passing down to Preprocessor

    # A new file; make new information
    $params{fileref} or die "%Error: No fileref parameter?";
    $params{netlist} = $params{fileref}->netlist;
    my $parser = $class->SUPER::new (%params,
				     modref=>undef,	# Module being parsed now
				     cellref=>undef,	# Cell being parsed now
				     _cmtref=>undef,	# Object to attach comments to
				     # Must parse all files in same compilation unit with
				     # same symbol_table, or a package won't exist for link()
				     symbol_table => $params{netlist}->{symbol_table},
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
    push @opt, keep_whitespace=>1;  # So we don't loose newlines
    push @opt, include_open_nonfatal=>1 if $params{netlist}{include_open_nonfatal};
    my $preproc = $preproc_class->new(@opt);
    $preproc->open($params{filename});
    $parser->parse_preproc_file ($preproc);
    return $parser;
}

sub contassign {
    my $self = shift;
    my $keyword = shift;
    my $lhs = shift;
    my $rhs = shift;

    print " ContAssign $keyword $lhs\n" if $Verilog::Netlist::Debug;
    my $modref = $self->{modref};
    if (!$modref) {
	 return $self->error ("CONTASSIGN outside of module definition", $lhs);
    }
    $modref->new_contassign
	 (filename=>$self->filename, lineno=>$self->lineno,
	  keyword=>$keyword, lhs=>$lhs, rhs=>$rhs);
}

sub defparam {
    my $self = shift;
    my $keyword = shift;
    my $lhs = shift;
    my $rhs = shift;

    print " Defparam $keyword $lhs\n" if $Verilog::Netlist::Debug;
    my $modref = $self->{modref};
    if (!$modref) {
	 return $self->error ("DEFPARAM outside of module definition", $lhs);
    }
    $modref->new_defparam
	 (filename=>$self->filename, lineno=>$self->lineno,
	  keyword=>$keyword, lhs=>$lhs, rhs=>$rhs);
}

sub interface {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;

    my $fileref = $self->{fileref};
    my $netlist = $self->{netlist};
    print "Interface $name\n" if $Verilog::Netlist::Debug;

    $self->{modref} = $netlist->new_interface
	 (name=>$name,
	  filename=>$self->filename, lineno=>$self->lineno);
    $fileref->_interfaces($name, $self->{modref});
    $self->{_cmtref} = $self->{modref};
}

sub modport {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;

    print " Modport $name\n" if $Verilog::Netlist::Debug;
    my $modref = $self->{modref};
    if (!$modref) {
	return $self->error ("MODPORT outside of interface definition", $name);
    }
    $self->{_modportref} = $modref->new_modport
	 (name=>$name,
	  filename=>$self->filename, lineno=>$self->lineno);
    $self->{_cmtref} = $self->{modref};
}

sub module {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $orderref = shift;
    my $in_celldefine = shift;

    my $fileref = $self->{fileref};
    my $netlist = $self->{netlist};
    print "Module $name\n" if $Verilog::Netlist::Debug;

    $self->{modref} = $netlist->new_module
	 (name=>$name, keyword=>$keyword,
	  is_libcell=>($fileref->is_libcell() || $in_celldefine),
	  filename=>$self->filename, lineno=>$self->lineno);
    $fileref->_modules($name, $self->{modref});
    $self->{_cmtref} = $self->{modref};
}

sub program {
    my $self = shift;
    $self->module(@_);
}

sub endinterface {
    my $self = shift;
    $self->endmodule(@_);
}

sub endmodport {
    my $self = shift;
    $self->{_cmtref} = $self->{modref};
    $self->{_modportref} = undef;
}

sub endmodule {
    my $self = shift;
    $self->{_cmtref} = undef;  # Assume all module comments are inside the module, not after
    $self->{modref} = undef;
}

sub endprogram {
    my $self = shift;
    $self->endmodule(@_);
}

sub attribute {
    my $self = shift;
    my $text = shift||'';

    my $modref = $self->{modref};
    my ($category, $name, $eql, $rest);
    if ($text =~ m!^([\$A-Za-z]\w*)\s+ (\w+) (\s*=\s*)? (.*) !x) {
	($category, $name, $eql, $rest) = ($1, $2, ($3 || ""), $4);
	if ($eql ne "") { $eql = "="; }
	my $cleaned = ($category ." ". $name . $eql . $rest);

	if ($Verilog::Netlist::Debug) {
	    printf +("%d: Attribute '%s'\n",
		     $self->lineno, $cleaned);
	}
	# Treat as module-level if attribute appears before any declarations.
	if ($modref) {
	    my $attr = $modref->new_attr ($cleaned);
	}
    }
}

sub port {
    my $self = shift;
    my $name = shift;
    my $objof = shift;
    my $direction = shift;
    my $type = shift;
    my $array = shift;
    my $pinnum = shift;

    return if !($objof eq 'module' || $objof eq 'interface' || $objof eq 'modport');

    my $underref = $self->{_modportref} || $self->{modref};

    if ($pinnum) {  # Else a "input" etc outside the "(...)"s
	$underref->_portsordered($pinnum-1, $name);  # -1 because [0] has first pin
    }
    if ($direction) {  # Else just a pin number without declaration
	my $port = $underref->new_port
	    (name=>$name,
	     filename=>$self->filename, lineno=>$self->lineno,
	     direction=>$direction, data_type=>$type,
	     array=>$array, comment=>undef,);
    }
}

sub var {
    my $self = shift;
    #use Data::Dumper; print " DEBUG: var callback: ",Dumper(\@_);
    my $decl_type = shift;
    my $name = shift;
    my $objof = shift;
    my $net_type = shift;
    my $data_type = shift;
    my $array = shift;
    my $value = shift;
    print " Sig $name dt=$decl_type nt=$net_type d=$data_type\n" if $Verilog::Netlist::Debug;

    return if !($objof eq 'module' || $objof eq 'interface' || $objof eq 'modport');

    my $msb;
    my $lsb;
    if ($data_type && $data_type =~ /\[(.*):(.*)\]/) {
	$msb = $1; $lsb = $2;
    } elsif ($data_type && $data_type =~ /\[(.*)\]/) {
	$msb = $lsb = $1;
    }

    my $underref = $self->{_modportref} || $self->{modref};
    if (!$underref) {
	return $self->error ("Signal declaration outside of module definition", $name);
    }

    my $signed = ($data_type =~ /signed/);

    my $net = $underref->find_net ($name);
    $net or $net = $underref->new_net
	(name=>$name,
	 filename=>$self->filename, lineno=>$self->lineno,
	 simple_type=>1, data_type=>$data_type, array=>$array,
	 comment=>undef, msb=>$msb, lsb=>$lsb,
	 net_type=>$net_type, decl_type=>$decl_type,
	 signed=>$signed, value=>$value,
	);
    $net->data_type($data_type);  # If it was declared earlier as in/out etc
    # (from a single non-typed input/output stmt), remark the type now
    $self->{_cmtref} = $net;
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

sub endcell {
    my $self = shift;
    $self->{_cmtref} = $self->{cellref};  # Comments after cell decl go to the cell
}

sub parampin {
    my $self = shift;
    my $pin = shift;
    my $conn = shift;
    my $number = shift;

    my $prev = $self->{cellref}->params();
    $prev .= ", " if $prev;
    $prev .= ($pin ? ".$pin($conn)" : $conn);
    $self->{cellref}->params($prev);
}

sub pin {
    my $self = shift;
    my $pin = shift;
    my $net = shift;
    my $number = shift;
    my $hasnamedports = (($pin||'') ne '');
    $pin = "pin".$number if !$hasnamedports;

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
    # Note we use_cb_keyword only if comments are parsed!
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

# sub operator {   ... Disabled by new(use_cmt_operator => 0)
# sub number {   ... Disabled by new(use_cmt_number => 0)
# sub string {   ... Disabled by new(use_cmt_string => 0)
# sub symbol {   ... Disabled by new(use_cmt_symbol => 0)

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

sub delete {
    my $self = shift;
    $self->netlist(undef);  # Break circular
}

sub logger {
    my $self = shift;
    return $self->netlist->logger;
}

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

    my $keep_cmt = ($params{keep_comments} || $netlist->{keep_comments});
    my $parser = Verilog::Netlist::File::Parser->new
	( fileref=>$fileref,
	  filename=>$filepath,	# for ->read
	  metacomment=>($params{metacomment} || $netlist->{metacomment}),
	  keep_comments => $keep_cmt,
	  use_vars=>($params{use_vars} || $netlist->{use_vars}),
	  preproc=>($params{preproc} || $netlist->{preproc}),
	  # Callbacks we need; disable unused for speed
	  use_cb_attribute => 1,
	  use_cb_comment => $keep_cmt,
	  use_cb_keyword => $keep_cmt,
	  use_cb_number  => 0,
	  use_cb_operator => 0,
	  use_cb_string => 0,
	  use_cb_symbol => 0,
	  );
    return $fileref;
}

sub link {
    # For backward compatibility for SystemC child class, call _link
    $_[0]->_link(@_);
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

Verilog::Netlist::File allows Verilog::Netlist objects to be read and
written in Verilog format.

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

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2010 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
