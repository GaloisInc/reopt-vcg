def vblendpd1 : instruction :=
  definst "vblendpd" $ do
    pattern fun (v_2832 : imm int) (v_2834 : reg (bv 128)) (v_2835 : reg (bv 128)) (v_2836 : reg (bv 128)) => do
      v_5202 <- eval (handleImmediateWithSignExtend v_2832 8 8);
      v_5204 <- getRegister v_2835;
      v_5206 <- getRegister v_2834;
      setRegister (lhs.of_reg v_2836) (concat (mux (isBitClear v_5202 6) (extract v_5204 0 64) (extract v_5206 0 64)) (mux (isBitClear v_5202 7) (extract v_5204 64 128) (extract v_5206 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2845 : imm int) (v_2846 : reg (bv 256)) (v_2847 : reg (bv 256)) (v_2848 : reg (bv 256)) => do
      v_5221 <- eval (handleImmediateWithSignExtend v_2845 8 8);
      v_5223 <- getRegister v_2847;
      v_5225 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2848) (concat (mux (isBitClear v_5221 4) (extract v_5223 0 64) (extract v_5225 0 64)) (concat (mux (isBitClear v_5221 5) (extract v_5223 64 128) (extract v_5225 64 128)) (concat (mux (isBitClear v_5221 6) (extract v_5223 128 192) (extract v_5225 128 192)) (mux (isBitClear v_5221 7) (extract v_5223 192 256) (extract v_5225 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2826 : imm int) (v_2827 : Mem) (v_2828 : reg (bv 128)) (v_2829 : reg (bv 128)) => do
      v_9436 <- eval (handleImmediateWithSignExtend v_2826 8 8);
      v_9438 <- getRegister v_2828;
      v_9440 <- evaluateAddress v_2827;
      v_9441 <- load v_9440 16;
      setRegister (lhs.of_reg v_2829) (concat (mux (isBitClear v_9436 6) (extract v_9438 0 64) (extract v_9441 0 64)) (mux (isBitClear v_9436 7) (extract v_9438 64 128) (extract v_9441 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2839 : imm int) (v_2840 : Mem) (v_2841 : reg (bv 256)) (v_2842 : reg (bv 256)) => do
      v_9450 <- eval (handleImmediateWithSignExtend v_2839 8 8);
      v_9452 <- getRegister v_2841;
      v_9454 <- evaluateAddress v_2840;
      v_9455 <- load v_9454 32;
      setRegister (lhs.of_reg v_2842) (concat (mux (isBitClear v_9450 4) (extract v_9452 0 64) (extract v_9455 0 64)) (concat (mux (isBitClear v_9450 5) (extract v_9452 64 128) (extract v_9455 64 128)) (concat (mux (isBitClear v_9450 6) (extract v_9452 128 192) (extract v_9455 128 192)) (mux (isBitClear v_9450 7) (extract v_9452 192 256) (extract v_9455 192 256)))));
      pure ()
    pat_end
