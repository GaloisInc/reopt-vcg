def vpblendw1 : instruction :=
  definst "vpblendw" $ do
    pattern fun (v_2726 : imm int) (v_2728 : reg (bv 128)) (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_6760 <- eval (handleImmediateWithSignExtend v_2726 8 8);
      v_6762 <- getRegister v_2729;
      v_6764 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2730) (concat (mux (isBitClear v_6760 0) (extract v_6762 0 16) (extract v_6764 0 16)) (concat (mux (isBitClear v_6760 1) (extract v_6762 16 32) (extract v_6764 16 32)) (concat (mux (isBitClear v_6760 2) (extract v_6762 32 48) (extract v_6764 32 48)) (concat (mux (isBitClear v_6760 3) (extract v_6762 48 64) (extract v_6764 48 64)) (concat (mux (isBitClear v_6760 4) (extract v_6762 64 80) (extract v_6764 64 80)) (concat (mux (isBitClear v_6760 5) (extract v_6762 80 96) (extract v_6764 80 96)) (concat (mux (isBitClear v_6760 6) (extract v_6762 96 112) (extract v_6764 96 112)) (mux (isBitClear v_6760 7) (extract v_6762 112 128) (extract v_6764 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2739 : imm int) (v_2740 : reg (bv 256)) (v_2741 : reg (bv 256)) (v_2742 : reg (bv 256)) => do
      v_6809 <- eval (handleImmediateWithSignExtend v_2739 8 8);
      v_6810 <- eval (isBitClear v_6809 0);
      v_6811 <- getRegister v_2741;
      v_6813 <- getRegister v_2740;
      v_6816 <- eval (isBitClear v_6809 1);
      v_6820 <- eval (isBitClear v_6809 2);
      v_6824 <- eval (isBitClear v_6809 3);
      v_6828 <- eval (isBitClear v_6809 4);
      v_6832 <- eval (isBitClear v_6809 5);
      v_6836 <- eval (isBitClear v_6809 6);
      v_6840 <- eval (isBitClear v_6809 7);
      setRegister (lhs.of_reg v_2742) (concat (mux v_6810 (extract v_6811 0 16) (extract v_6813 0 16)) (concat (mux v_6816 (extract v_6811 16 32) (extract v_6813 16 32)) (concat (mux v_6820 (extract v_6811 32 48) (extract v_6813 32 48)) (concat (mux v_6824 (extract v_6811 48 64) (extract v_6813 48 64)) (concat (mux v_6828 (extract v_6811 64 80) (extract v_6813 64 80)) (concat (mux v_6832 (extract v_6811 80 96) (extract v_6813 80 96)) (concat (mux v_6836 (extract v_6811 96 112) (extract v_6813 96 112)) (concat (mux v_6840 (extract v_6811 112 128) (extract v_6813 112 128)) (concat (mux v_6810 (extract v_6811 128 144) (extract v_6813 128 144)) (concat (mux v_6816 (extract v_6811 144 160) (extract v_6813 144 160)) (concat (mux v_6820 (extract v_6811 160 176) (extract v_6813 160 176)) (concat (mux v_6824 (extract v_6811 176 192) (extract v_6813 176 192)) (concat (mux v_6828 (extract v_6811 192 208) (extract v_6813 192 208)) (concat (mux v_6832 (extract v_6811 208 224) (extract v_6813 208 224)) (concat (mux v_6836 (extract v_6811 224 240) (extract v_6813 224 240)) (mux v_6840 (extract v_6811 240 256) (extract v_6813 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2720 : imm int) (v_2721 : Mem) (v_2722 : reg (bv 128)) (v_2723 : reg (bv 128)) => do
      v_15417 <- eval (handleImmediateWithSignExtend v_2720 8 8);
      v_15419 <- getRegister v_2722;
      v_15421 <- evaluateAddress v_2721;
      v_15422 <- load v_15421 16;
      setRegister (lhs.of_reg v_2723) (concat (mux (isBitClear v_15417 0) (extract v_15419 0 16) (extract v_15422 0 16)) (concat (mux (isBitClear v_15417 1) (extract v_15419 16 32) (extract v_15422 16 32)) (concat (mux (isBitClear v_15417 2) (extract v_15419 32 48) (extract v_15422 32 48)) (concat (mux (isBitClear v_15417 3) (extract v_15419 48 64) (extract v_15422 48 64)) (concat (mux (isBitClear v_15417 4) (extract v_15419 64 80) (extract v_15422 64 80)) (concat (mux (isBitClear v_15417 5) (extract v_15419 80 96) (extract v_15422 80 96)) (concat (mux (isBitClear v_15417 6) (extract v_15419 96 112) (extract v_15422 96 112)) (mux (isBitClear v_15417 7) (extract v_15419 112 128) (extract v_15422 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2733 : imm int) (v_2734 : Mem) (v_2735 : reg (bv 256)) (v_2736 : reg (bv 256)) => do
      v_15461 <- eval (handleImmediateWithSignExtend v_2733 8 8);
      v_15462 <- eval (isBitClear v_15461 0);
      v_15463 <- getRegister v_2735;
      v_15465 <- evaluateAddress v_2734;
      v_15466 <- load v_15465 32;
      v_15469 <- eval (isBitClear v_15461 1);
      v_15473 <- eval (isBitClear v_15461 2);
      v_15477 <- eval (isBitClear v_15461 3);
      v_15481 <- eval (isBitClear v_15461 4);
      v_15485 <- eval (isBitClear v_15461 5);
      v_15489 <- eval (isBitClear v_15461 6);
      v_15493 <- eval (isBitClear v_15461 7);
      setRegister (lhs.of_reg v_2736) (concat (mux v_15462 (extract v_15463 0 16) (extract v_15466 0 16)) (concat (mux v_15469 (extract v_15463 16 32) (extract v_15466 16 32)) (concat (mux v_15473 (extract v_15463 32 48) (extract v_15466 32 48)) (concat (mux v_15477 (extract v_15463 48 64) (extract v_15466 48 64)) (concat (mux v_15481 (extract v_15463 64 80) (extract v_15466 64 80)) (concat (mux v_15485 (extract v_15463 80 96) (extract v_15466 80 96)) (concat (mux v_15489 (extract v_15463 96 112) (extract v_15466 96 112)) (concat (mux v_15493 (extract v_15463 112 128) (extract v_15466 112 128)) (concat (mux v_15462 (extract v_15463 128 144) (extract v_15466 128 144)) (concat (mux v_15469 (extract v_15463 144 160) (extract v_15466 144 160)) (concat (mux v_15473 (extract v_15463 160 176) (extract v_15466 160 176)) (concat (mux v_15477 (extract v_15463 176 192) (extract v_15466 176 192)) (concat (mux v_15481 (extract v_15463 192 208) (extract v_15466 192 208)) (concat (mux v_15485 (extract v_15463 208 224) (extract v_15466 208 224)) (concat (mux v_15489 (extract v_15463 224 240) (extract v_15466 224 240)) (mux v_15493 (extract v_15463 240 256) (extract v_15466 240 256)))))))))))))))));
      pure ()
    pat_end
