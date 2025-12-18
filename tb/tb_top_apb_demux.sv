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

    top_apb_demux #(
        .BASE_ADDR('{
            32'h0000_0000, 32'h1000_0000, 32'h2000_0000, 32'h3000_0000,
            32'h4000_0000, 32'h5000_0000, 32'h6000_0000, 32'h7000_0000}),
        .ADDR_SIZE('{
            32'h0000_1000, 32'h0000_1000, 32'h0000_1000, 32'h0000_1000,
            32'h0000_1000, 32'h0000_1000, 32'h0000_1000, 32'h0000_1000})
    ) top_apb_demux_inst (
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
    int error_count = 0;
    mailbox#(logic [31:0]) write_mbx;
    mailbox#(logic [31:0]) read_mbx;
    mailbox#(logic [31:0]) data_mbx;

    initial begin
        forever #10 clk = ~clk;
    end

    logic [7:0] slave_penable;
    assign slave_penable[0] = penable_o[0];
    assign slave_penable[1] = penable_o[1];
    assign slave_penable[2] = penable_o[2];
    assign slave_penable[3] = penable_o[3];
    assign slave_penable[4] = penable_o[4];
    assign slave_penable[5] = penable_o[5];
    assign slave_penable[6] = penable_o[6];
    assign slave_penable[7] = penable_o[7];

    logic [7:0] slave_psel;
    assign slave_psel[0] = psel_o[0];
    assign slave_psel[1] = psel_o[1];
    assign slave_psel[2] = psel_o[2];
    assign slave_psel[3] = psel_o[3];
    assign slave_psel[4] = psel_o[4];
    assign slave_psel[5] = psel_o[5];
    assign slave_psel[6] = psel_o[6];
    assign slave_psel[7] = psel_o[7];

    task do_write(logic [31:0] addr, logic [31:0] data);
        logic [7:0] slave_select;

        @(posedge clk);
        psel_i = 1'b1;
        pwrite_i = 1'b1;
        paddr_i = addr;
        pwdata_i = data;
        penable_i = 1'b0;

        // Выбор слейва
        slave_select = '0;
        for (int i = 0; i < 8; i++) begin
            if ( (addr >= top_apb_demux_inst.BASE_ADDR[i]) == (top_apb_demux_inst.BASE_ADDR[i] + top_apb_demux_inst.ADDR_SIZE[i] > addr) ) begin
                slave_select[i] = 1;
            end
        end

        @(posedge clk);
        penable_i = 1'b1;

        @(posedge clk);
        wait(pready_o == 1'b1);

        psel_i = 1'b0;
        penable_i = 1'b0;

        if (!$onehot(slave_select)) begin // проверка выставления ошибки
            if (!pslverr_o) begin
                $error("No one slave was selected. PSLVERR_O must be HIGH");
                error_count++;
            end
            if (!$onehot0(slave_select)) begin
                slave_select = '0;
            end
            if (slave_psel != slave_select) begin // если не совпадет выбор слейвов
                $error("Uncorrect choice slaves. E xpected: b'%0b | Real: b'%0b", slave_select, slave_psel);
                error_count++;
            end
        end else begin // проверка передачи данных
            foreach (slave_select[i]) begin
                if (slave_select[i]) begin
                    if (penable_o[i] !== 1) begin
                        $error("Write: PENABLE mismatch when must be HIGH: Expected b'%0b | Real b'%0b on slave %0d", 1, penable_o[i], i);
                        error_count++;
                    end
                    if (pwrite_o[i] !== 1) begin
                        $error("Write: PWRITE mismatch: Expected b'%0b | Real b'%0b on slave %0d", 1, pwrite_o[i], i);
                        error_count++;
                    end
                    if (paddr_o[i] !== addr) begin
                        $error("Write: PADDR mismatch: Expected h'%0h | Real h'%0h on slave %0d", addr, paddr_o[i], i);
                        error_count++;
                    end
                    if (pwdata_o[i] !== data) begin
                        $error("Write: PWDATA mismatch: Expected h'%0h | Real h'%0h on slave %0d", data, pwdata_o[i], i);
                        error_count++;
                    end
                end
            end
        end

    endtask

    task do_read(logic [31:0] addr);
        logic [7:0] slave_select;
        int slave_idx;
        bit has_error = 0;

        @(posedge clk);
        psel_i = 1'b1;
        pwrite_i = 1'b0;
        paddr_i = addr;
        penable_i = 1'b0;

        // Выбор слейва
        slave_select = '0;
        for (int i = 0; i < 8; i++) begin
            if ( (addr >= top_apb_demux_inst.BASE_ADDR[i]) == (top_apb_demux_inst.BASE_ADDR[i] + top_apb_demux_inst.ADDR_SIZE[i] > addr) ) begin
                slave_select[i] = 1;
            end
        end

        @(posedge clk);
        penable_i = 1'b1;

        @(posedge clk);
        wait(pready_o == 1'b1);

        if (!$onehot(slave_select)) begin // проверка выставления ошибки
            has_error = 1;
            if (!pslverr_o) begin
                $error("No one slave was selected. PSLVERR_O must be HIGH. Addr: h'%0h", addr);
                error_count++;
            end
            if (!$onehot0(slave_select)) begin
                slave_select = '0;
            end
            if (slave_psel != slave_select) begin // если не совпадет выбор слейвов
                $error("Uncorrect choice slaves. Expected: b'%0b | Real: b'%0b", slave_select, slave_psel);
                error_count++;
            end
        end else begin // проверка передачи данных
            foreach (slave_select[i]) begin
                if (slave_select[i]) begin
                    if (penable_o[i] !== 1) begin
                        $error("Read: PENABLE mismatch when must be HIGH: Expected b'%0b | Real b'%0b on slave %0d", 1, penable_o[i], i);
                        error_count++;
                    end
                    if (pwrite_o[i] !== 0) begin
                        $error("Read: PWRITE mismatch: Expected b'%0b | Real b'%0b on slave %0d", 0, pwrite_o[i], i);
                        error_count++;
                    end
                    if (paddr_o[i] !== addr) begin
                        $error("Read: PADDR mismatch: Expected h'%0h | Real h'%0h on slave %0d", addr, paddr_o[i], i);
                        error_count++;
                    end
                    slave_idx = i;
                end
            end
        end

        psel_i = 1'b0;
        penable_i = 1'b0;
        if (!has_error) begin // есди ошибка данные не важны
            if (prdata_o !== prdata_i[slave_idx]) begin
                $error("Read: PRDATA mismatch: Expected h'%0h | Real h'%0h from slave %0d", prdata_i[slave_idx], prdata_o, slave_idx);
            end
        end

    endtask

    function void randomize_data(int iters = 5);
        logic [31:0] addr;
        logic [31:0] data;
        for (int i = 0; i < iters; ++i) begin
            if (!std::randomize(addr) with {
                addr[31:16] dist {
                16'h0000 :/ 10,
                16'h1000 :/ 10,
                16'h2000 :/ 10,
                16'h3000 :/ 10,
                16'h4000 :/ 10,
                16'h5000 :/ 10,
                16'h6000 :/ 10,
                16'h7000 :/ 10,
                [16'h8000 : 16'hFFFF] :/ 2
            };
                addr[15:00] < 16'h2000;
            }) begin
                $fatal("Can't randomize addr");
            end
            write_mbx.try_put(addr);
            read_mbx.try_put(addr);

            if (!std::randomize(data)) begin
                $fatal("Can't randomize data");
            end
            data_mbx.try_put(data);
        end
    endfunction

    task set_random_addr(int iters = 5);
        logic [31:0] addr;
        logic [31:0] data;
        write_mbx = new();
        read_mbx = new();
        data_mbx = new();

        randomize_data(10);

        for (int i = 0; i < iters; ++i) begin
            write_mbx.try_get(addr);
            data_mbx.try_get(data);
            do_write(addr, data);
        end
        for (int i = 0; i < iters; ++i) begin
            read_mbx.try_get(addr);
            do_read(addr);
        end
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

        set_random_addr(10);

        #50;
        $display("Total Error: %0d", error_count);
        $finish;
    end

    property penable_after_pready;
        @(posedge clk) disable iff (!psel_i) psel_i && !penable_i |=> penable_i;
    endproperty
    assert property (penable_after_pready) else
        $error("PENABLE must be high after");


    property only_one_slave_selected;
        @(posedge clk) $onehot0(slave_psel);
    endproperty
    assert property (only_one_slave_selected) else
        $error("[SVA] Many slaves");

    generate
        for (genvar i = 0; i < 8; i++) begin : slave_assertions
            property psel_penable_sequence;
                @(posedge clk) disable iff (!psel_o[i]) psel_o[i] && !penable_o[i] |=> penable_o[i];
            endproperty
            assert property (psel_penable_sequence) else
                $error("[SVA] PENABLE must be high after PSEL");

        end
    endgenerate
endmodule
