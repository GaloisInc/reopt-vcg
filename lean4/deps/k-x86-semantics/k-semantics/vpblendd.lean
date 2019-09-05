def vpblendd1 : instruction :=
  definst "vpblendd" $ do
    pattern fun (v_2674 : imm int) (v_2676 : reg (bv 128)) (v_2677 : reg (bv 128)) (v_2678 : reg (bv 128)) => do
      v_6424 <- eval (handleImmediateWithSignExtend v_2674 8 8);
      v_6426 <- getRegister v_2677;
      v_6428 <- getRegister v_2676;
      setRegister (lhs.of_reg v_2678) (concat (mux (isBitClear v_6424 4) (extract v_6426 0 32) (extract v_6428 0 32)) (concat (mux (isBitClear v_6424 5) (extract v_6426 32 64) (extract v_6428 32 64)) (concat (mux (isBitClear v_6424 6) (extract v_6426 64 96) (extract v_6428 64 96)) (mux (isBitClear v_6424 7) (extract v_6426 96 128) (extract v_6428 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2687 : imm int) (v_2688 : reg (bv 256)) (v_2689 : reg (bv 256)) (v_2690 : reg (bv 256)) => do
      v_6453 <- eval (handleImmediateWithSignExtend v_2687 8 8);
      v_6455 <- getRegister v_2689;
      v_6457 <- getRegister v_2688;
      setRegister (lhs.of_reg v_2690) (concat (mux (isBitClear v_6453 0) (extract v_6455 0 32) (extract v_6457 0 32)) (concat (mux (isBitClear v_6453 1) (extract v_6455 32 64) (extract v_6457 32 64)) (concat (mux (isBitClear v_6453 2) (extract v_6455 64 96) (extract v_6457 64 96)) (concat (mux (isBitClear v_6453 3) (extract v_6455 96 128) (extract v_6457 96 128)) (concat (mux (isBitClear v_6453 4) (extract v_6455 128 160) (extract v_6457 128 160)) (concat (mux (isBitClear v_6453 5) (extract v_6455 160 192) (extract v_6457 160 192)) (concat (mux (isBitClear v_6453 6) (extract v_6455 192 224) (extract v_6457 192 224)) (mux (isBitClear v_6453 7) (extract v_6455 224 256) (extract v_6457 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2668 : imm int) (v_2669 : Mem) (v_2670 : reg (bv 128)) (v_2671 : reg (bv 128)) => do
      v_15101 <- eval (handleImmediateWithSignExtend v_2668 8 8);
      v_15103 <- getRegister v_2670;
      v_15105 <- evaluateAddress v_2669;
      v_15106 <- load v_15105 16;
      setRegister (lhs.of_reg v_2671) (concat (mux (isBitClear v_15101 4) (extract v_15103 0 32) (extract v_15106 0 32)) (concat (mux (isBitClear v_15101 5) (extract v_15103 32 64) (extract v_15106 32 64)) (concat (mux (isBitClear v_15101 6) (extract v_15103 64 96) (extract v_15106 64 96)) (mux (isBitClear v_15101 7) (extract v_15103 96 128) (extract v_15106 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2681 : imm int) (v_2682 : Mem) (v_2683 : reg (bv 256)) (v_2684 : reg (bv 256)) => do
      v_15125 <- eval (handleImmediateWithSignExtend v_2681 8 8);
      v_15127 <- getRegister v_2683;
      v_15129 <- evaluateAddress v_2682;
      v_15130 <- load v_15129 32;
      setRegister (lhs.of_reg v_2684) (concat (mux (isBitClear v_15125 0) (extract v_15127 0 32) (extract v_15130 0 32)) (concat (mux (isBitClear v_15125 1) (extract v_15127 32 64) (extract v_15130 32 64)) (concat (mux (isBitClear v_15125 2) (extract v_15127 64 96) (extract v_15130 64 96)) (concat (mux (isBitClear v_15125 3) (extract v_15127 96 128) (extract v_15130 96 128)) (concat (mux (isBitClear v_15125 4) (extract v_15127 128 160) (extract v_15130 128 160)) (concat (mux (isBitClear v_15125 5) (extract v_15127 160 192) (extract v_15130 160 192)) (concat (mux (isBitClear v_15125 6) (extract v_15127 192 224) (extract v_15130 192 224)) (mux (isBitClear v_15125 7) (extract v_15127 224 256) (extract v_15130 224 256)))))))));
      pure ()
    pat_end
