// DESCRIPTION: vpm: Example pli file for vpm program
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2005 by Wilson Snyder.

`timescale 1ns/1ns

module pli;
   // A module called PLI is required, to contain the error counts
   // This is required with the vpm --nostop option, which this example uses
   // By default (--stop), this file isn't needed at all

   integer errors; initial errors = 0;
   integer warnings; initial warnings = 0;

   // Normally this would be 0 at startup, then become 1 after reset deasserts
   // This prevents false assertion checks during reset
   integer message_on; initial message_on = 1;

   always @ (errors or warnings) begin
`ifdef OPTIONAL_EXIT_ON_WARNING
      if (errors!=0 || warnings!=0) begin
	 $info (0, "Errors/warnings found, exiting!\n");
	 $finish;
      end
`else
      if (errors!=0) begin
	 $info (0, "Errors found, exiting!\n");
	 $finish;
      end
      else if (warnings!=0) begin
	 $info (0, {"Warnings found, ","consider stopping!\n"});
      end
`endif
   end

endmodule
