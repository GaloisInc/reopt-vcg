def movb1 : instruction :=
  definst "movb" $ do
    pattern fun (v_3168 : imm int) (v_3169 : reg (bv 8)) => do
      setRegister (lhs.of_reg v_3169) (handleImmediateWithSignExtend v_3168 8 8);
      pure ()
    pat_end;
    pattern fun (v_3177 : reg (bv 8)) (v_3178 : reg (bv 8)) => do
      v_6212 <- getRegister v_3177;
      setRegister (lhs.of_reg v_3178) v_6212;
      pure ()
    pat_end;
    pattern fun (v_3156 : imm int) (v_3157 : Mem) => do
      v_7966 <- evaluateAddress v_3157;
      store v_7966 (handleImmediateWithSignExtend v_3156 8 8) 1;
      pure ()
    pat_end;
    pattern fun (v_3161 : reg (bv 8)) (v_3160 : Mem) => do
      v_7969 <- evaluateAddress v_3160;
      v_7970 <- getRegister v_3161;
      store v_7969 v_7970 1;
      pure ()
    pat_end;
    pattern fun (v_3173 : Mem) (v_3174 : reg (bv 8)) => do
      v_9902 <- evaluateAddress v_3173;
      v_9903 <- load v_9902 1;
      setRegister (lhs.of_reg v_3174) v_9903;
      pure ()
    pat_end
