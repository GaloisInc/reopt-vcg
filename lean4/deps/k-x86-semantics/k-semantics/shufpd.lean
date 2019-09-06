def shufpd1 : instruction :=
  definst "shufpd" $ do
    pattern fun (v_3127 : imm int) (v_3128 : reg (bv 128)) (v_3129 : reg (bv 128)) => do
      v_5417 <- eval (handleImmediateWithSignExtend v_3127 8 8);
      v_5419 <- getRegister v_3128;
      v_5424 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3129) (concat (mux (isBitSet v_5417 6) (extract v_5419 0 64) (extract v_5419 64 128)) (mux (isBitSet v_5417 7) (extract v_5424 0 64) (extract v_5424 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3123 : imm int) (v_3122 : Mem) (v_3124 : reg (bv 128)) => do
      v_8487 <- eval (handleImmediateWithSignExtend v_3123 8 8);
      v_8489 <- evaluateAddress v_3122;
      v_8490 <- load v_8489 16;
      v_8495 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3124) (concat (mux (isBitSet v_8487 6) (extract v_8490 0 64) (extract v_8490 64 128)) (mux (isBitSet v_8487 7) (extract v_8495 0 64) (extract v_8495 64 128)));
      pure ()
    pat_end
