// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009-2012 by Wilson Snyder.

`include "v_sv_pkg.v"

interface v_sv_intf;
   v_sv_pkg::byte_t byte_port;
   v_sv_intf2 subintf(.*);
endinterface

interface v_sv_intf2;
   v_sv_pkg::byte_t byte_port;
   modport Master(input data, output addr);
endinterface
