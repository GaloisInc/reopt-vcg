def vblendpd1 : instruction :=
  definst "vblendpd" $ do
    pattern fun (v_2857 : imm int) (v_2861 : reg (bv 128)) (v_2862 : reg (bv 128)) (v_2863 : reg (bv 128)) => do
      v_5229 <- eval (handleImmediateWithSignExtend v_2857 8 8);
      v_5231 <- getRegister v_2862;
      v_5233 <- getRegister v_2861;
      setRegister (lhs.of_reg v_2863) (concat (mux (isBitClear v_5229 6) (extract v_5231 0 64) (extract v_5233 0 64)) (mux (isBitClear v_5229 7) (extract v_5231 64 128) (extract v_5233 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2870 : imm int) (v_2871 : reg (bv 256)) (v_2872 : reg (bv 256)) (v_2873 : reg (bv 256)) => do
      v_5248 <- eval (handleImmediateWithSignExtend v_2870 8 8);
      v_5250 <- getRegister v_2872;
      v_5252 <- getRegister v_2871;
      setRegister (lhs.of_reg v_2873) (concat (mux (isBitClear v_5248 4) (extract v_5250 0 64) (extract v_5252 0 64)) (concat (mux (isBitClear v_5248 5) (extract v_5250 64 128) (extract v_5252 64 128)) (concat (mux (isBitClear v_5248 6) (extract v_5250 128 192) (extract v_5252 128 192)) (mux (isBitClear v_5248 7) (extract v_5250 192 256) (extract v_5252 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2851 : imm int) (v_2852 : Mem) (v_2855 : reg (bv 128)) (v_2856 : reg (bv 128)) => do
      v_9463 <- eval (handleImmediateWithSignExtend v_2851 8 8);
      v_9465 <- getRegister v_2855;
      v_9467 <- evaluateAddress v_2852;
      v_9468 <- load v_9467 16;
      setRegister (lhs.of_reg v_2856) (concat (mux (isBitClear v_9463 6) (extract v_9465 0 64) (extract v_9468 0 64)) (mux (isBitClear v_9463 7) (extract v_9465 64 128) (extract v_9468 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2864 : imm int) (v_2865 : Mem) (v_2866 : reg (bv 256)) (v_2867 : reg (bv 256)) => do
      v_9477 <- eval (handleImmediateWithSignExtend v_2864 8 8);
      v_9479 <- getRegister v_2866;
      v_9481 <- evaluateAddress v_2865;
      v_9482 <- load v_9481 32;
      setRegister (lhs.of_reg v_2867) (concat (mux (isBitClear v_9477 4) (extract v_9479 0 64) (extract v_9482 0 64)) (concat (mux (isBitClear v_9477 5) (extract v_9479 64 128) (extract v_9482 64 128)) (concat (mux (isBitClear v_9477 6) (extract v_9479 128 192) (extract v_9482 128 192)) (mux (isBitClear v_9477 7) (extract v_9479 192 256) (extract v_9482 192 256)))));
      pure ()
    pat_end
