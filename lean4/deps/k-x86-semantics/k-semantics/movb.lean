def movb1 : instruction :=
  definst "movb" $ do
    pattern fun (v_3241 : imm int) (v_3240 : reg (bv 8)) => do
      setRegister (lhs.of_reg v_3240) (handleImmediateWithSignExtend v_3241 8 8);
      pure ()
    pat_end;
    pattern fun (v_3254 : reg (bv 8)) (v_3255 : reg (bv 8)) => do
      v_5759 <- getRegister v_3254;
      setRegister (lhs.of_reg v_3255) v_5759;
      pure ()
    pat_end;
    pattern fun (v_3210 : imm int) (v_3209 : Mem) => do
      v_7501 <- evaluateAddress v_3209;
      store v_7501 (handleImmediateWithSignExtend v_3210 8 8) 1;
      pure ()
    pat_end;
    pattern fun (v_3218 : reg (bv 8)) (v_3217 : Mem) => do
      v_7507 <- evaluateAddress v_3217;
      v_7508 <- getRegister v_3218;
      store v_7507 v_7508 1;
      pure ()
    pat_end;
    pattern fun (v_3245 : Mem) (v_3246 : reg (bv 8)) => do
      v_8955 <- evaluateAddress v_3245;
      v_8956 <- load v_8955 1;
      setRegister (lhs.of_reg v_3246) v_8956;
      pure ()
    pat_end
