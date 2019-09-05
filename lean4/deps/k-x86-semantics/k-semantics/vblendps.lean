def vblendps1 : instruction :=
  definst "vblendps" $ do
    pattern fun (v_2858 : imm int) (v_2860 : reg (bv 128)) (v_2861 : reg (bv 128)) (v_2862 : reg (bv 128)) => do
      v_5250 <- eval (handleImmediateWithSignExtend v_2858 8 8);
      v_5252 <- getRegister v_2861;
      v_5254 <- getRegister v_2860;
      setRegister (lhs.of_reg v_2862) (concat (mux (isBitClear v_5250 4) (extract v_5252 0 32) (extract v_5254 0 32)) (concat (mux (isBitClear v_5250 5) (extract v_5252 32 64) (extract v_5254 32 64)) (concat (mux (isBitClear v_5250 6) (extract v_5252 64 96) (extract v_5254 64 96)) (mux (isBitClear v_5250 7) (extract v_5252 96 128) (extract v_5254 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2871 : imm int) (v_2872 : reg (bv 256)) (v_2873 : reg (bv 256)) (v_2874 : reg (bv 256)) => do
      v_5279 <- eval (handleImmediateWithSignExtend v_2871 8 8);
      v_5281 <- getRegister v_2873;
      v_5283 <- getRegister v_2872;
      setRegister (lhs.of_reg v_2874) (concat (mux (isBitClear v_5279 0) (extract v_5281 0 32) (extract v_5283 0 32)) (concat (mux (isBitClear v_5279 1) (extract v_5281 32 64) (extract v_5283 32 64)) (concat (mux (isBitClear v_5279 2) (extract v_5281 64 96) (extract v_5283 64 96)) (concat (mux (isBitClear v_5279 3) (extract v_5281 96 128) (extract v_5283 96 128)) (concat (mux (isBitClear v_5279 4) (extract v_5281 128 160) (extract v_5283 128 160)) (concat (mux (isBitClear v_5279 5) (extract v_5281 160 192) (extract v_5283 160 192)) (concat (mux (isBitClear v_5279 6) (extract v_5281 192 224) (extract v_5283 192 224)) (mux (isBitClear v_5279 7) (extract v_5281 224 256) (extract v_5283 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2852 : imm int) (v_2853 : Mem) (v_2854 : reg (bv 128)) (v_2855 : reg (bv 128)) => do
      v_9474 <- eval (handleImmediateWithSignExtend v_2852 8 8);
      v_9476 <- getRegister v_2854;
      v_9478 <- evaluateAddress v_2853;
      v_9479 <- load v_9478 16;
      setRegister (lhs.of_reg v_2855) (concat (mux (isBitClear v_9474 4) (extract v_9476 0 32) (extract v_9479 0 32)) (concat (mux (isBitClear v_9474 5) (extract v_9476 32 64) (extract v_9479 32 64)) (concat (mux (isBitClear v_9474 6) (extract v_9476 64 96) (extract v_9479 64 96)) (mux (isBitClear v_9474 7) (extract v_9476 96 128) (extract v_9479 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2865 : imm int) (v_2866 : Mem) (v_2867 : reg (bv 256)) (v_2868 : reg (bv 256)) => do
      v_9498 <- eval (handleImmediateWithSignExtend v_2865 8 8);
      v_9500 <- getRegister v_2867;
      v_9502 <- evaluateAddress v_2866;
      v_9503 <- load v_9502 32;
      setRegister (lhs.of_reg v_2868) (concat (mux (isBitClear v_9498 0) (extract v_9500 0 32) (extract v_9503 0 32)) (concat (mux (isBitClear v_9498 1) (extract v_9500 32 64) (extract v_9503 32 64)) (concat (mux (isBitClear v_9498 2) (extract v_9500 64 96) (extract v_9503 64 96)) (concat (mux (isBitClear v_9498 3) (extract v_9500 96 128) (extract v_9503 96 128)) (concat (mux (isBitClear v_9498 4) (extract v_9500 128 160) (extract v_9503 128 160)) (concat (mux (isBitClear v_9498 5) (extract v_9500 160 192) (extract v_9503 160 192)) (concat (mux (isBitClear v_9498 6) (extract v_9500 192 224) (extract v_9503 192 224)) (mux (isBitClear v_9498 7) (extract v_9500 224 256) (extract v_9503 224 256)))))))));
      pure ()
    pat_end
