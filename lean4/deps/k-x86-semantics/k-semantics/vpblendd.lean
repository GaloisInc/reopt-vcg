def vpblendd1 : instruction :=
  definst "vpblendd" $ do
    pattern fun (v_2701 : imm int) (v_2702 : reg (bv 128)) (v_2703 : reg (bv 128)) (v_2704 : reg (bv 128)) => do
      v_6451 <- eval (handleImmediateWithSignExtend v_2701 8 8);
      v_6453 <- getRegister v_2703;
      v_6455 <- getRegister v_2702;
      setRegister (lhs.of_reg v_2704) (concat (mux (isBitClear v_6451 4) (extract v_6453 0 32) (extract v_6455 0 32)) (concat (mux (isBitClear v_6451 5) (extract v_6453 32 64) (extract v_6455 32 64)) (concat (mux (isBitClear v_6451 6) (extract v_6453 64 96) (extract v_6455 64 96)) (mux (isBitClear v_6451 7) (extract v_6453 96 128) (extract v_6455 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2714 : imm int) (v_2715 : reg (bv 256)) (v_2716 : reg (bv 256)) (v_2717 : reg (bv 256)) => do
      v_6480 <- eval (handleImmediateWithSignExtend v_2714 8 8);
      v_6482 <- getRegister v_2716;
      v_6484 <- getRegister v_2715;
      setRegister (lhs.of_reg v_2717) (concat (mux (isBitClear v_6480 0) (extract v_6482 0 32) (extract v_6484 0 32)) (concat (mux (isBitClear v_6480 1) (extract v_6482 32 64) (extract v_6484 32 64)) (concat (mux (isBitClear v_6480 2) (extract v_6482 64 96) (extract v_6484 64 96)) (concat (mux (isBitClear v_6480 3) (extract v_6482 96 128) (extract v_6484 96 128)) (concat (mux (isBitClear v_6480 4) (extract v_6482 128 160) (extract v_6484 128 160)) (concat (mux (isBitClear v_6480 5) (extract v_6482 160 192) (extract v_6484 160 192)) (concat (mux (isBitClear v_6480 6) (extract v_6482 192 224) (extract v_6484 192 224)) (mux (isBitClear v_6480 7) (extract v_6482 224 256) (extract v_6484 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2696 : imm int) (v_2695 : Mem) (v_2697 : reg (bv 128)) (v_2698 : reg (bv 128)) => do
      v_15128 <- eval (handleImmediateWithSignExtend v_2696 8 8);
      v_15130 <- getRegister v_2697;
      v_15132 <- evaluateAddress v_2695;
      v_15133 <- load v_15132 16;
      setRegister (lhs.of_reg v_2698) (concat (mux (isBitClear v_15128 4) (extract v_15130 0 32) (extract v_15133 0 32)) (concat (mux (isBitClear v_15128 5) (extract v_15130 32 64) (extract v_15133 32 64)) (concat (mux (isBitClear v_15128 6) (extract v_15130 64 96) (extract v_15133 64 96)) (mux (isBitClear v_15128 7) (extract v_15130 96 128) (extract v_15133 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2709 : imm int) (v_2708 : Mem) (v_2710 : reg (bv 256)) (v_2711 : reg (bv 256)) => do
      v_15152 <- eval (handleImmediateWithSignExtend v_2709 8 8);
      v_15154 <- getRegister v_2710;
      v_15156 <- evaluateAddress v_2708;
      v_15157 <- load v_15156 32;
      setRegister (lhs.of_reg v_2711) (concat (mux (isBitClear v_15152 0) (extract v_15154 0 32) (extract v_15157 0 32)) (concat (mux (isBitClear v_15152 1) (extract v_15154 32 64) (extract v_15157 32 64)) (concat (mux (isBitClear v_15152 2) (extract v_15154 64 96) (extract v_15157 64 96)) (concat (mux (isBitClear v_15152 3) (extract v_15154 96 128) (extract v_15157 96 128)) (concat (mux (isBitClear v_15152 4) (extract v_15154 128 160) (extract v_15157 128 160)) (concat (mux (isBitClear v_15152 5) (extract v_15154 160 192) (extract v_15157 160 192)) (concat (mux (isBitClear v_15152 6) (extract v_15154 192 224) (extract v_15157 192 224)) (mux (isBitClear v_15152 7) (extract v_15154 224 256) (extract v_15157 224 256)))))))));
      pure ()
    pat_end
