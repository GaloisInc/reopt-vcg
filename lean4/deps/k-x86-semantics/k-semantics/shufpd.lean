def shufpd1 : instruction :=
  definst "shufpd" $ do
    pattern fun (v_3101 : imm int) (v_3099 : reg (bv 128)) (v_3100 : reg (bv 128)) => do
      v_5962 <- eval (handleImmediateWithSignExtend v_3101 8 8);
      v_5964 <- getRegister v_3099;
      v_5969 <- getRegister v_3100;
      setRegister (lhs.of_reg v_3100) (concat (mux (isBitSet v_5962 6) (extract v_5964 0 64) (extract v_5964 64 128)) (mux (isBitSet v_5962 7) (extract v_5969 0 64) (extract v_5969 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3096 : imm int) (v_3095 : Mem) (v_3094 : reg (bv 128)) => do
      v_9094 <- eval (handleImmediateWithSignExtend v_3096 8 8);
      v_9096 <- evaluateAddress v_3095;
      v_9097 <- load v_9096 16;
      v_9102 <- getRegister v_3094;
      setRegister (lhs.of_reg v_3094) (concat (mux (isBitSet v_9094 6) (extract v_9097 0 64) (extract v_9097 64 128)) (mux (isBitSet v_9094 7) (extract v_9102 0 64) (extract v_9102 64 128)));
      pure ()
    pat_end
