// DESCRIPTION: Verilog::Preproc: Example source code
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2010 by Wilson Snyder.

`define EMPTY_TRUE
`ifndef EMPTY_TRUE
  `error "Empty is still true"
`endif

`define A
`ifdef A
  $display("1A");
 `ifdef C
  $display("%Error: 2C");
 `elsif A
  $display("2A");
  `ifdef C
  $display("%Error: 3C");
  `elsif B
  $display("%Error: 3B");
  `else
  $display("3AELSE");
  `endif
 `else
  $display("%Error: 2ELSE");
 `endif
`elsif B
  $display("%Error: 1B");
  `ifdef A
  $display("%Error: noC");
  `elsif A
  $display("%Error: noB");
  `else
  $display("%Error: noELSE");
  `endif
`elsif C
  $display("%Error: 1C");
`else
  $display("%Error: 1ELSE");
`endif
