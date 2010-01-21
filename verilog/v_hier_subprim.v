// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2010 by Wilson Snyder.

// surefire lint_off UDPUNS

primitive v_hier_prim (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   a
   );
   output q;
   input a;

   table
      0 : 1;
      1 : 0;
   endtable

endprimitive

`celldefine
module bug27070();
  `define W 4
  parameter TAP = `W'b1001;
endmodule
`endcelldefine
