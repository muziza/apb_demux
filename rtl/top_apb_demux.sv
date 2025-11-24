`timescale 1ns/1ps

module top_apb_demux #(
    parameter int APB_SLAVE_COUNT = 8,
    parameter int APB_ADDR_WIDTH = 32,
    parameter int APB_DATA_WIDTH = 32,
    parameter [APB_ADDR_WIDTH-1:0] BASE_ADDR [APB_SLAVE_COUNT] = '{
        'h0000_0000, 'h1000_0000, 'h2000_0000, 'h3000_0000,
        'h4000_0000, 'h5000_0000, 'h6000_0000, 'h7000_0000
    },
    parameter [APB_ADDR_WIDTH-1:0] ADDR_SIZE [APB_SLAVE_COUNT] = '{
        'h0000_1000, 'h0000_1000, 'h0000_1000, 'h0000_1000,
        'h0000_1000, 'h0000_1000, 'h0000_1000, 'h0000_1000
    }
)(
    // Bus from APB Master
    input  logic                      psel_i,
    input  logic [APB_ADDR_WIDTH-1:0] paddr_i,
    input  logic                      pwrite_i,
    input  logic                      penable_i,
    input  logic [APB_DATA_WIDTH-1:0] pwdata_i,
    output logic [APB_DATA_WIDTH-1:0] prdata_o,
    output logic                      pready_o,
    output logic                      pslverr_o,

    // Bus to APB Slaves
    output logic                      psel_o    [APB_SLAVE_COUNT],
    output logic [APB_ADDR_WIDTH-1:0] paddr_o   [APB_SLAVE_COUNT],
    output logic                      pwrite_o  [APB_SLAVE_COUNT],
    output logic                      penable_o [APB_SLAVE_COUNT],
    output logic [APB_DATA_WIDTH-1:0] pwdata_o  [APB_SLAVE_COUNT],
    input  logic [APB_DATA_WIDTH-1:0] prdata_i  [APB_SLAVE_COUNT],
    input  logic                      pready_i  [APB_SLAVE_COUNT],
    input  logic                      pslverr_i [APB_SLAVE_COUNT]
);

    logic [APB_ADDR_WIDTH-1:0] start_addr [APB_SLAVE_COUNT];
    logic [APB_ADDR_WIDTH-1:0] end_addr   [APB_SLAVE_COUNT];

    generate
        for (genvar i = 0; i < APB_SLAVE_COUNT; ++i) begin : range_calc
            assign start_addr[i] = BASE_ADDR[i];
            assign end_addr[i] = BASE_ADDR[i] + ADDR_SIZE[i];
        end
    endgenerate

    // Compare range logic
    logic [APB_SLAVE_COUNT-1:0] in_range;
    // always_comb begin
    //     if (psel_i) begin
    //         in_range = '0;
    //         for (int i = 0; i < APB_SLAVE_COUNT; ++i) begin
    //             if (paddr_i >= start_addr[i] && paddr_i <= end_addr[i]) begin
    //                 in_range[i] = 1'b1;
    //             end else begin
    //                 in_range[i] = 1'b0;
    //             end
    //         end
    //     end else begin
    //         in_range = '0;
    //     end
    // end

    logic [APB_ADDR_WIDTH-1:0] paddr;
    always_comb begin
        if (psel_i) begin
            in_range = '0;
            for (int i = 0; i < APB_SLAVE_COUNT; ++i) begin
                paddr = paddr_i ^ BASE_ADDR[i];
                if (paddr <= ADDR_SIZE[i]) begin
                    in_range[i] = 1'b1;
                end else begin
                    in_range[i] = 1'b0;
                end
            end
        end else begin
            in_range = '0;
        end
    end

    logic [$clog2(APB_SLAVE_COUNT+1)-1:0] bit_count;
    always_comb begin
        bit_count = '0;
        for (int i = 0; i < APB_SLAVE_COUNT; i++) begin
            bit_count = bit_count + in_range[i];
        end
    end

    // Onehot check logic
    logic [APB_SLAVE_COUNT:0] en;
    always_comb begin
        if (bit_count == 1) begin
            en = {1'b0, in_range};
        end else if (psel_i) begin
            en = '0;
            en[APB_SLAVE_COUNT] = 1'b1;
        end
    end

    // DEMUX logic
    always_comb begin
        for (int i = 0; i < APB_SLAVE_COUNT; i++) begin
            if (en[i]) begin
                psel_o[i] = psel_i;
                penable_o[i] = penable_i;
            end else begin
                psel_o[i] = 0;
                penable_o[i] = 0;
            end
        end
    end

    // Not control signals for all slaves
    generate
        for (genvar i = 0; i < APB_SLAVE_COUNT; ++i) begin : not_ctrl_signals_connect
            assign paddr_o[i] = paddr_i;
            assign pwdata_o[i] = pwdata_i;
            assign pwrite_o[i] = pwrite_i;
        end
    endgenerate

    // MUX logic
    always_comb begin
        pslverr_o = 1'b0;
        prdata_o = 'b0;
        pready_o = 1'b0;
        if (en[APB_SLAVE_COUNT]) begin
            prdata_o = 'b0;
            pready_o = 1'b1;
            pslverr_o = 1'b1;
        end else begin
            for (int i = 0; i < APB_SLAVE_COUNT; ++i) begin
                if (en[i]) begin
                    prdata_o = prdata_i[i];
                    pready_o = pready_i[i];
                    pslverr_o = pslverr_i[i];
                    break;
                end 
                // else begin
                // end
            end
        end
    end

endmodule