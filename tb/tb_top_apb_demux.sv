`timescale 1ns/1ps

module tb_top_apb_demux;

    // Bus from APB Master
    logic        psel_i;
    logic [31:0] paddr_i;
    logic        pwrite_i;
    logic        penable_i;
    logic [31:0] pwdata_i;
    logic [31:0] prdata_o;
    logic        pready_o;
    logic        pslverr_o;

    // Bus to APB Slaves
    logic        psel_o    [8];
    logic [31:0] paddr_o   [8];
    logic        pwrite_o  [8];
    logic        penable_o [8];
    logic [31:0] pwdata_o  [8];
    logic [31:0] prdata_i  [8];
    logic        pready_i  [8];
    logic        pslverr_i [8];

    top_apb_demux top_apb_demux_inst (
        .psel_i    (psel_i),
        .paddr_i   (paddr_i),
        .pwrite_i  (pwrite_i),
        .penable_i (penable_i),
        .pwdata_i  (pwdata_i),
        .prdata_o  (prdata_o),
        .pready_o  (pready_o),
        .pslverr_o (pslverr_o),

        .psel_o    (psel_o),
        .paddr_o   (paddr_o),
        .pwrite_o  (pwrite_o),
        .penable_o (penable_o),
        .pwdata_o  (pwdata_o),
        .prdata_i  (prdata_i),
        .pready_i  (pready_i),
        .pslverr_i (pslverr_i)
    );

    logic clk = 0;

    initial begin
        forever #10 clk = ~clk;
    end

    task do_write(logic [31:0] addr, logic [31:0] data);
        @(posedge clk);
        psel_i = 1'b1;
        pwrite_i = 1'b1;
        paddr_i = addr;
        pwdata_i = data;
        penable_i = 1'b0;
        
        @(posedge clk);
        penable_i = 1'b1;
        
        wait(pready_o == 1'b1);
        @(posedge clk);
        psel_i = 1'b0;
        penable_i = 1'b0;
        
        // $display("[WRITE] Time: %0t, Addr: h'%h, Data: h'%h", $time, paddr_o, pwdata_o);
    endtask
    
    task do_read(logic [31:0] addr);
        @(posedge clk);
        psel_i = 1'b1;
        pwrite_i = 1'b0;
        paddr_i = addr;
        penable_i = 1'b0;
        
        @(posedge clk);
        penable_i = 1'b1;
        
        wait(pready_o == 1'b1);
        @(posedge clk);
        psel_i = 1'b0;
        penable_i = 1'b0;
        
        // $display("[READ] Time: %0t, Addr: h'%h, Data: h'%h", $time, addr, prdata_o);
    endtask

    // Slaves
    initial begin
        foreach (pslverr_i[i]) begin
            pslverr_i[i] = 1'b0;
            prdata_i[i] = 32'hCAFE_BEE0 + i;
            pready_i[i] = 1'b1; 
        end
    end

    initial begin
        psel_i = 0;
        penable_i = 0;
        paddr_i = '0;
        pwdata_i = 0;
        pwrite_i = 0;
        
        #50;
        
        do_write(32'h0000_1000, 32'h1234_5678);
        do_write(32'h1000_2000, 32'hABCD_EF01);  
        do_write(32'h2000_3000, 32'h55AA_AA55);
        
        do_read(32'h0000_1001);
        do_read(32'h1000_2000);
        do_read(32'h2000_3000);
        do_read(32'h4000_0001);
        do_read(32'h5000_0010);
        do_read(32'h7000_0020);
        
        do_write(32'h6000_00F0, 32'h55AA_AA55);
        do_write(32'h6000_00F0, 32'h5555);
        #50;
        $finish;
    end
    // generate
    //     for (genvar i = 0; i < 8; i++) begin : slave_assertions
    //         property penable_after_pready;
    //             @(posedge clk) psel_o[i] && penable_o[i] && pready_i[i] |=> !penable_o[i];
    //         endproperty
    //         assert_penable_after_pready: assert property (penable_after_pready)
    //             else begin
    //                 $error("Penable has high value after handshake");
    //                 $stop;
    //             end

    //         property penable_only_with_psel;
    //             @(posedge clk) penable_o[i] |-> psel_o[i];
    //         endproperty
    //         assert_penable_only_with_psel: assert property (penable_only_with_psel)
    //             else begin
    //                 $error("Penable without psel");
    //                 $stop;
    //             end
    //     end
    // endgenerate
endmodule